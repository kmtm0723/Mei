/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.DenseBasisTransport.Linear.Basic
public import Mei.Topology.Sheaves.LocallyConstant

/-!
# Comparing transport sections with the semimodule-valued sheaf

The linear enrichment of a transport sheaf retains its original sections and
restrictions. Canonical section isomorphisms make this comparison available
without exposing either representation. Locally bijective restrictions of the
original sheaf become locally isomorphic restrictions of its linear enrichment.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r

namespace Mei.DenseBasisTransport

variable {X : TopCat.{u}} {S : Set X} {M : Type v}
  (T : DenseBasisTransport S M) (R : Type r) [Semiring R]
  [AddCommMonoid M] [Module R M] [T.IsAdditive] [T.PreservesSMul R]

/-- The linear transport sheaf has the original transport-section semimodule,
identified by the existing public presheaf comparisons. -/
def semimoduleSheafSectionsIso (U : Opens X) :
    (T.semimoduleSheaf R).obj.obj (op U) ≅
      SemimoduleCat.of R (T.sheaf.presheaf.obj (op U)) :=
  eqToIso (by rw [T.semimoduleSheaf_obj, T.semimodulePresheaf_obj])

/-- Restriction in the linear sheaf is the original linear restriction under
the canonical section isomorphisms. -/
theorem semimoduleSheaf_map {U V : Opens X} (hVU : V ≤ U) :
    (T.semimoduleSheaf R).obj.map (homOfLE hVU).op =
      (T.semimoduleSheafSectionsIso R U).hom ≫
        SemimoduleCat.ofHom (T.restrictionLinearMap R hVU) ≫
          (T.semimoduleSheafSectionsIso R V).inv := by
  let hf := T.semimoduleSheaf_obj R
  have hn := congrArg (fun q => q ≫ eqToHom (T.semimodulePresheaf_obj R (op V)))
    ((eqToHom hf).naturality (homOfLE hVU).op)
  rw [T.semimodulePresheaf_map] at hn
  apply (cancel_mono (T.semimoduleSheafSectionsIso R V).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [semimoduleSheafSectionsIso, eqToIso.hom, eqToHom_app, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.comp_id] using hn

/-- Local bijectivity of transport-section restrictions gives local restriction
isomorphisms of the semimodule-valued transport sheaf. -/
theorem exists_isIso_restrictions_semimoduleSheaf
    [T.sheaf.HasLocallyBijectivePreconnectedRestrictions] (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∀ (V : Opens X) (hVU : V ≤ U),
      (V : Set X).Nonempty → IsPreconnected (V : Set X) →
        IsIso ((T.semimoduleSheaf R).obj.map (homOfLE hVU).op) := by
  obtain ⟨U, hxU, hU⟩ :=
    TopCat.Sheaf.HasLocallyBijectivePreconnectedRestrictions.exists_bijective_restrictions
      (F := T.sheaf) x
  refine ⟨U, hxU, fun V hVU hne hconn => ?_⟩
  have hb : Function.Bijective (T.restrictionLinearMap R hVU) := by
    have he : (T.restrictionLinearMap R hVU : _ → _) =
        T.sheaf.presheaf.map (homOfLE hVU).op :=
      funext (T.restrictionLinearMap_apply R hVU)
    rw [he]
    exact hU V hVU hne hconn
  have : IsIso (SemimoduleCat.ofHom (T.restrictionLinearMap R hVU)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  rw [T.semimoduleSheaf_map]
  infer_instance

end Mei.DenseBasisTransport
