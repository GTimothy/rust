use std::fmt::Write;

use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{CrateNum, DefId, LocalDefId};
use rustc_hir::definitions::DisambiguatedDefPathData;
use rustc_span::{Symbol, symbol};

use crate::ty::print::{PrettyPrinter, PrintError, Printer};
use crate::ty::{self, GenericArg, Ty, TyCtxt};

/// A printer implementing mostly `PrettyPrinter` but which takes into account a `use_site` in order
/// to find minimized paths to a type and it's arguments.
struct ScopeAwareTyPrinter<'tcx> {
    tcx: TyCtxt<'tcx>,
    use_site: rustc_hir::def_id::LocalDefId, // module accessibility is checked against
    path: String,
}

impl Write for ScopeAwareTyPrinter<'_> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.path.push_str(s);
        Ok(())
    }
}

impl<'tcx> PrettyPrinter<'tcx> for ScopeAwareTyPrinter<'tcx> {
    fn generic_delimiters(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<(), PrintError>,
    ) -> Result<(), PrintError> {
        write!(self, "<")?;
        f(self)?;
        write!(self, ">")?;
        Ok(())
    }

    fn should_print_optional_region(&self, _region: ty::Region<'tcx>) -> bool {
        false
    }
}

impl<'tcx> super::Printer<'tcx> for ScopeAwareTyPrinter<'tcx> {
    fn tcx<'a>(&'a self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn print_region(&mut self, _region: ty::Region<'tcx>) -> Result<(), PrintError> {
        write!(self, "'_")
    }
    fn print_crate_name(&mut self, cnum: CrateNum) -> Result<(), PrintError> {
        self.path.push_str(self.tcx.crate_name(cnum).as_str());
        Ok(())
    }

    fn print_type(&mut self, ty: Ty<'tcx>) -> Result<(), PrintError> {
        // try to resolve some `DefId` this `ty` can be named by, generically across kinds.
        let def_id_and_args: Option<(DefId, &'tcx [GenericArg<'tcx>])> = match *ty.kind() {
            ty::Adt(adt_def, args) => Some((adt_def.did(), args)),
            ty::Foreign(def_id) => Some((def_id, ty::List::empty())),
            ty::FnDef(def_id, args) => Some((def_id, args.skip_binder().as_slice())),
            ty::Dynamic(preds, _) => preds.principal().map(|principal| {
                let tr = principal.skip_binder();
                (tr.def_id, tr.args.as_slice())
            }),
            ty::Alias(_, alias) => match alias.kind {
                ty::AliasTyKind::Projection { def_id }
                | ty::AliasTyKind::Inherent { def_id }
                | ty::AliasTyKind::Free { def_id } => Some((def_id, alias.args)),
                ty::AliasTyKind::Opaque { .. } => None,
            },
            _ => None,
        };

        if let Some((def_id, args)) = def_id_and_args
            && let Some((path, is_alias)) =
                find_visible_type_name(self.tcx, self.use_site, ty, def_id)
        {
            self.path.push_str(&path);
            // skip processing any generic arguments when the alias match already accounts for them
            if !is_alias && !args.is_empty() {
                return self.generic_delimiters(|cx| cx.comma_sep(args.iter().copied()));
            }
            return Ok(());
        }
        // fallback on pretty printing.
        self.pretty_print_type(ty)
    }
    fn print_dyn_existential(
        &mut self,
        predicates: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    ) -> Result<(), PrintError> {
        self.pretty_print_dyn_existential(predicates)
    }

    fn print_const(&mut self, ct: ty::Const<'tcx>) -> Result<(), PrintError> {
        self.pretty_print_const(ct, false)
    }

    fn print_path_with_simple(
        &mut self,
        print_prefix: impl FnOnce(&mut Self) -> Result<(), PrintError>,
        disambiguated_data: &DisambiguatedDefPathData,
    ) -> Result<(), PrintError> {
        print_prefix(self)?;
        write!(self.path, "::{}", disambiguated_data.data)
    }

    fn print_path_with_impl(
        &mut self,
        print_prefix: impl FnOnce(&mut Self) -> Result<(), PrintError>,
        self_ty: Ty<'tcx>,
        trait_ref: Option<ty::TraitRef<'tcx>>,
    ) -> Result<(), PrintError> {
        self.pretty_print_path_with_impl(
            |cx| {
                print_prefix(cx)?;
                cx.path.push_str("::");
                Ok(())
            },
            self_ty,
            trait_ref,
        )
    }

    fn print_path_with_generic_args(
        &mut self,
        print_prefix: impl FnOnce(&mut Self) -> Result<(), PrintError>,
        args: &[GenericArg<'tcx>],
    ) -> Result<(), PrintError> {
        print_prefix(self)?;
        if !args.is_empty() {
            self.generic_delimiters(|cx| cx.comma_sep(args.iter().copied()))
        } else {
            Ok(())
        }
    }

    fn print_path_with_qualified(
        &mut self,
        self_ty: Ty<'tcx>,
        trait_ref: Option<ty::TraitRef<'tcx>>,
    ) -> Result<(), PrintError> {
        self.pretty_print_path_with_qualified(self_ty, trait_ref)
    }
}

/// find an alias, definition or use import of a *nameable* `Ty` in the n, n-1 and n+1
/// module hierarchy where n is the module where `use_site` is located.
/// Only suggests shorthand to `Ty` that are visible from `use_site`.
/// If an alias is found it includes the generic arguments; otherwise this also reduces each generic
/// argument in turn.
/// This allows for very short, valid paths for suggestions.
pub fn scope_aware_ty_string<'tcx>(
    tcx: TyCtxt<'tcx>,
    use_site: LocalDefId,
    ty: Ty<'tcx>,
) -> String {
    let mut p = ScopeAwareTyPrinter { tcx, use_site, path: String::new() };
    p.print_type(ty).unwrap();
    p.path
}

/// If a match is found, returns a types' path `String` and an alias `bool` that is true if the
/// `String` is an alias.
/// The path is greedily looked for in the `use_site` module, then the module's children, then
/// parent module and the parent's children.
/// The alias `bool` is information useful when deciding to process any generic arguments of a `Ty`
/// (i.e. when alias is `true`, we may skip the generic arguments).
///
/// Returns None if no match is found.
fn find_visible_type_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    use_site: LocalDefId,
    ty: Ty<'tcx>,
    def_id: DefId,
) -> Option<(String, bool)> {
    let full_len = tcx.def_path(def_id).data.len() + 1; // +1 for the crate root

    let accept = |segments: &[Symbol]| -> Option<String> {
        if segments.len() > full_len {
            return None;
        }
        Some(segments.iter().map(Symbol::as_str).collect::<Vec<_>>().join("::"))
    };

    // current module (the module directly containing `use_site`)
    let current_module = tcx.parent_module_from_def_id(use_site).to_local_def_id();

    if let Some((name, is_alias)) = find_match_in(tcx, current_module, ty, def_id, use_site) {
        if let Some(tn) = accept(&[name]) {
            return Some((tn, is_alias));
        }
    }

    // children modules of the current module
    for child in tcx.module_children_local(current_module) {
        if let Res::Def(DefKind::Mod, child_mod_id) = child.res
            && let Some(local_child_id) = child_mod_id.as_local()
            && let Some((name, is_alias)) = find_match_in(tcx, local_child_id, ty, def_id, use_site)
        {
            return accept(&[child.ident.name, name]).map(|p| (p, is_alias));
        }
    }

    // parent module and its children
    let parent_module = tcx.parent_module_from_def_id(current_module).to_local_def_id();

    if let Some((name, is_alias)) = find_match_in(tcx, parent_module, ty, def_id, use_site) {
        if let Some(tn) = accept(&[symbol::kw::Super, name]) {
            return Some((tn, is_alias));
        }
    }

    for child in tcx.module_children_local(parent_module) {
        if let Res::Def(DefKind::Mod, child_mod_id) = child.res
            && let Some(local_child_id) = child_mod_id.as_local()
            && let Some((name, is_alias)) = find_match_in(tcx, local_child_id, ty, def_id, use_site)
        {
            return accept(&[symbol::kw::Super, child.ident.name, name]).map(|p| (p, is_alias));
        }
    }

    None
}

/// Look for a match for `ty` (with DefId `def_id`) in `module` that is visible from `use_site`.
/// Returns the matching child's name and whether it's a `TyAlias` hit or not.
fn find_match_in<'tcx>(
    tcx: TyCtxt<'tcx>,
    module: LocalDefId,
    ty: Ty<'tcx>,
    def_id: DefId,
    use_site: LocalDefId,
) -> Option<(Symbol, bool)> {
    if tcx.def_kind(def_id) == DefKind::AssocTy {
        let trait_id = tcx.trait_item_of(def_id)?;
        return tcx
            .module_children_local(module)
            .iter()
            .find(|child| {
                child.res.opt_def_id() == Some(trait_id)
                    && child.vis.is_accessible_from(use_site, tcx)
            })
            .map(|child| (child.ident.name, false));
    }

    tcx.module_children_local(module).iter().find_map(|child| match child.res {
        Res::Def(DefKind::TyAlias, alias_def_id)
            if child.vis.is_accessible_from(use_site, tcx)
                && tcx.type_of(alias_def_id).instantiate_identity().skip_norm_wip() == ty =>
        {
            Some((child.ident.name, true))
        }
        Res::Def(
            DefKind::Struct | DefKind::Enum | DefKind::Union | DefKind::Trait | DefKind::Fn,
            child_def_id,
        ) if child_def_id == def_id && child.vis.is_accessible_from(use_site, tcx) => {
            Some((child.ident.name, false))
        }
        _ => None,
    })
}
