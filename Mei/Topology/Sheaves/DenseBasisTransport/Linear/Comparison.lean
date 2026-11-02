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

Locally bijective restrictions of a transport sheaf become locally isomorphic
restrictions of its linear enrichment, on the original transport-section carriers.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r

namespace Mei.DenseBasisTransport

variable {X : TopCat.{u}} {S : Set X} {M : Type v}
  (T : DenseBasisTransport S M) (R : Type r) [Semiring R]
  [AddCommMonoid M] [Module R M] [T.IsAdditive] [T.PreservesSMul R]

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
  rw [T.semimoduleSheaf_obj, T.semimodulePresheaf_map]
  have : IsIso (SemimoduleCat.ofHom (T.restrictionLinearMap R hVU)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  infer_instance

end Mei.DenseBasisTransport
