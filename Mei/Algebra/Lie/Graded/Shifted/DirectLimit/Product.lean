/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.DirectLimit
public import Mei.Algebra.Lie.Graded.Shifted.Product
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.NonUnital

/-!
# Global completed BCH actions preserve products

A graded derivation action descends to multiplication on global coefficients.
The coefficient algebra may be noncommutative, and only a graded multiplication
is required: the original unit need not belong to the degree-zero piece.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R L A : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [Ring A] [Algebra R A] [LieRingModule L A] [LieModule R L A]
  [IsDerivationAction L A] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (𝒜 : Γ → Submodule R A)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition 𝒜] [SetLike.GradedBracket ℒ 𝒜]
  [SetLike.GradedMul 𝒜]

/-- Completed BCH labels preserve the global product without a graded unit. -/
theorem shiftedDirectLimitBCHAction_map_mul (g : d.completedBCHGroup ℒ)
    (x y : d.ShiftedDirectLimit 𝒜) :
    d.shiftedDirectLimitBCHAction ℒ 𝒜 g (x * y) =
      d.shiftedDirectLimitBCHAction ℒ 𝒜 g x * d.shiftedDirectLimitBCHAction ℒ 𝒜 g y := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 x
  obtain ⟨t, b, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 y
  rw [toShiftedDirectLimit_mul, shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart,
    completedBCHAction_shiftedCompletionMul, shiftedDirectLimitBCHAction_toShiftedDirectLimit,
    shiftedDirectLimitBCHAction_toShiftedDirectLimit, toShiftedDirectLimit_mul]

end Mei.PositiveDegrees
