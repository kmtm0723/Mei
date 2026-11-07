/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Action
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

/-- Completed BCH labels act on the direct limit by compatible shifted actions. -/
def shiftedDirectLimitBCHAction : d.completedBCHGroup ℒ →*
    (d.ShiftedDirectLimit ℳ ≃ₗ[R] d.ShiftedDirectLimit ℳ) :=
  d.shiftedDirectLimitAction ℳ
    (fun p => (d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ)
    (d.shiftedCompletedInclusion_completedBCHAction ℒ ℳ)

/-- The direct-limit action restricts to the original action in every multiset chart. -/
@[simp]
theorem shiftedDirectLimitBCHAction_toShiftedDirectLimit (H : d.completedBCHGroup ℒ)
    (s : Multiset d.monoid) (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    shiftedDirectLimitBCHAction d ℒ ℳ H (d.toShiftedDirectLimit ℳ s x) =
      d.toShiftedDirectLimit ℳ s
        ((d.shiftedLieFiltration ℒ ℳ (d.coefficientOrigin s)).completedBCHAction d ℒ H x) :=
  d.shiftedDirectLimitAction_toShiftedDirectLimit ℳ _ _ H s x

/-- Any containing chart gives an equivariant embedding of the arbitrary-origin action. -/
theorem shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart (H : d.completedBCHGroup ℒ)
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) :
    shiftedDirectLimitBCHAction d ℒ ℳ H (d.toShiftedDirectLimitOfChart ℳ p s hp x) =
      d.toShiftedDirectLimitOfChart ℳ p s hp
        ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ H x) :=
  d.shiftedDirectLimitAction_toShiftedDirectLimitOfChart ℳ _ _ H p s hp x

/-- Inverse labels induce the inverse direct-limit action. -/
@[simp]
theorem shiftedDirectLimitBCHAction_inv (H : d.completedBCHGroup ℒ) :
    shiftedDirectLimitBCHAction d ℒ ℳ (H⁻¹) = (shiftedDirectLimitBCHAction d ℒ ℳ H).symm :=
  map_inv (shiftedDirectLimitBCHAction d ℒ ℳ) H

end Mei.PositiveDegrees
