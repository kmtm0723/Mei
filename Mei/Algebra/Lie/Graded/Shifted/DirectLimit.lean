/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit
public import Mei.Algebra.Lie.Graded.Shifted.Support

/-!
# Completed BCH actions on global shifted coefficients

The completed action of a positive graded Lie algebra descends through translated
support inclusions to the module direct limit. This supplies chart-independent
coefficient actions for signed wall products, including arbitrary completed labels
and coefficients. No multiplication or degree-zero unit is needed.

This implements the global coefficient-action supplier in the
[shifted coefficient roadmap](https://github.com/yuma-mizuno/TauCetiRoadmap/blob/mei/TauCetiRoadmap/ScatteringDiagrams/README.md#51-graded-actions-and-shifted-coefficient-modules).
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R L M : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ]

private def shiftedBCHDirectLimitEquiv (H : d.completedBCHGroup ℒ) :
    d.ShiftedDirectLimit ℳ ≃ₗ[R] d.ShiftedDirectLimit ℳ :=
  Module.DirectLimit.congr
    (fun s => (d.shiftedLieFiltration ℒ ℳ (d.coefficientOrigin s)).completedBCHAction d ℒ H)
    (by
      intro s t h
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, PositiveDegrees.coefficientInclusion_eq]
      exact (d.shiftedCompletedInclusion_completedBCHAction ℒ ℳ
        (d.coefficientOrigin s) (d.coefficientOrigin t)
        (d.coefficientOrigin_sub_mem h) H x).symm)

private theorem shiftedBCHDirectLimitEquiv_apply (H : d.completedBCHGroup ℒ)
    (s : Multiset d.monoid) (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    shiftedBCHDirectLimitEquiv d ℒ ℳ H (d.toShiftedDirectLimit ℳ s x) =
      d.toShiftedDirectLimit ℳ s
        ((d.shiftedLieFiltration ℒ ℳ (d.coefficientOrigin s)).completedBCHAction d ℒ H x) := by
  simp only [shiftedBCHDirectLimitEquiv, PositiveDegrees.toShiftedDirectLimit_apply]
  apply Module.DirectLimit.congr_apply_of

private theorem shiftedBCHDirectLimitEquiv_mul (H K : d.completedBCHGroup ℒ) :
    shiftedBCHDirectLimitEquiv d ℒ ℳ (H * K) =
      shiftedBCHDirectLimitEquiv d ℒ ℳ H * shiftedBCHDirectLimitEquiv d ℒ ℳ K := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨s, a, ha⟩ := d.exists_toShiftedDirectLimit ℳ x
  rw [← ha]
  simp only [LinearEquiv.mul_apply, shiftedBCHDirectLimitEquiv_apply,
    ((d.shiftedLieFiltration ℒ ℳ (d.coefficientOrigin s)).completedBCHAction d ℒ).map_mul]

/-- Completed BCH labels act on the direct limit by compatible shifted actions. -/
def shiftedDirectLimitBCHAction : d.completedBCHGroup ℒ →*
    (d.ShiftedDirectLimit ℳ ≃ₗ[R] d.ShiftedDirectLimit ℳ) :=
  MonoidHom.mk' (shiftedBCHDirectLimitEquiv d ℒ ℳ) (shiftedBCHDirectLimitEquiv_mul d ℒ ℳ)

/-- The direct-limit action restricts to the original action in every multiset chart. -/
@[simp]
theorem shiftedDirectLimitBCHAction_toShiftedDirectLimit (H : d.completedBCHGroup ℒ)
    (s : Multiset d.monoid) (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    shiftedDirectLimitBCHAction d ℒ ℳ H (d.toShiftedDirectLimit ℳ s x) =
      d.toShiftedDirectLimit ℳ s
        ((d.shiftedLieFiltration ℒ ℳ (d.coefficientOrigin s)).completedBCHAction d ℒ H x) :=
  shiftedBCHDirectLimitEquiv_apply d ℒ ℳ H s x

/-- Any containing chart gives an equivariant embedding of the arbitrary-origin action. -/
theorem shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart (H : d.completedBCHGroup ℒ)
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) :
    shiftedDirectLimitBCHAction d ℒ ℳ H (d.toShiftedDirectLimitOfChart ℳ p s hp x) =
      d.toShiftedDirectLimitOfChart ℳ p s hp
        ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ H x) := by
  simp only [PositiveDegrees.toShiftedDirectLimitOfChart_apply,
    shiftedDirectLimitBCHAction_toShiftedDirectLimit]
  exact congrArg (d.toShiftedDirectLimit ℳ s)
    (d.shiftedCompletedInclusion_completedBCHAction ℒ ℳ p
      (d.coefficientOrigin s) hp H x).symm

/-- Inverse labels induce the inverse direct-limit action. -/
@[simp]
theorem shiftedDirectLimitBCHAction_inv (H : d.completedBCHGroup ℒ) :
    shiftedDirectLimitBCHAction d ℒ ℳ (H⁻¹) = (shiftedDirectLimitBCHAction d ℒ ℳ H).symm :=
  map_inv (shiftedDirectLimitBCHAction d ℒ ℳ) H

end Mei.PositiveDegrees
