/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.DirectLimit
public import Mei.Algebra.Lie.Graded.Shifted.Map
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Map

/-!
# Equivariant maps of global completed BCH coefficients

A degree-preserving equivariant linear map intertwines the global completed BCH
actions. The map need not be injective: cancellation of whole components is
compatible with the action. This is the coefficient-map supplier for gluing
coefficient systems in the shifted setting.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M N L : Type*} [AddCommGroup Γ] [DecidableEq Γ]
  [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M] [LieRingModule L N] [LieModule R L N]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) (𝓝 : Γ → Submodule R N)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [SetLike.GradedBracket ℒ 𝓝]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  (f : M →ₗ[R] N) (hf : ∀ q, ℳ q ≤ (𝓝 q).comap f)
  (hequiv : ∀ (x : L) (a : M), f ⁅x, a⁆ = ⁅x, f a⁆)

include hequiv

/-- Equivariant coefficient maps commute with the global action, including when
noninjective maps cancel homogeneous components. -/
theorem shiftedDirectLimitMap_shiftedDirectLimitBCHAction
    (g : d.completedBCHGroup ℒ) (x : d.ShiftedDirectLimit ℳ) :
    d.shiftedDirectLimitMap ℳ 𝓝 f hf (d.shiftedDirectLimitBCHAction ℒ ℳ g x) =
      d.shiftedDirectLimitBCHAction ℒ 𝓝 g (d.shiftedDirectLimitMap ℳ 𝓝 f hf x) := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit ℳ x
  rw [shiftedDirectLimitBCHAction_toShiftedDirectLimit,
    shiftedDirectLimitMap_toShiftedDirectLimit,
    shiftedDirectLimitMap_toShiftedDirectLimit,
    shiftedDirectLimitBCHAction_toShiftedDirectLimit]
  apply congrArg (d.toShiftedDirectLimit 𝓝 s)
  have h (hf' : ∀ q, ℳ q ≤ (𝓝 (PositiveDegreeMap.id d q)).comap f) :=
    (PositiveDegreeMap.id d).shiftedCompletionMap_completedBCHAction
      ℳ 𝓝 (d.coefficientOrigin s) (GradedLieHom.id ℒ) f hf'
      (fun x a => by simpa only [GradedLieHom.id_apply] using hequiv x a) g a
  -- Normalize the opaque identity degree map before comparing the restricted maps.
  let I : PositiveDegreeMap d d :=
    { toAddMonoidHom := AddMonoidHom.id Γ
      map_mem := fun h => h
      map_ne_zero := fun _ h => h
      modulus := id
      monotone_modulus := monotone_id
      degree_gt := fun _ _ h => h }
  have hI : PositiveDegreeMap.id d = I :=
    PositiveDegreeMap.ext (fun q => PositiveDegreeMap.id_apply q)
      (fun k => PositiveDegreeMap.id_modulus k)
  simp only [GradedLieHom.completedMap_id, MonoidHom.id_apply] at h
  rw [hI] at h
  have hm : I.shiftedMap ℳ 𝓝 (d.coefficientOrigin s) f hf =
      d.shiftedCoefficientMap ℳ 𝓝 (d.coefficientOrigin s) f hf := by
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    simp only [PositiveDegreeMap.coe_shiftedMap, coe_shiftedCoefficientMap]
  simpa only [PositiveDegreeMap.shiftedCompletionMap_def,
    completionCoefficientMap_eq_completionMap, hm, I, AddMonoidHom.id_apply] using h hf

end Mei.PositiveDegrees
