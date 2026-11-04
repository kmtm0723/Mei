/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Assoc

/-!
# The nonunital algebra of global shifted coefficients

The global bilinear product and its associativity law make the existing module
direct limit a nonunital ring. Scalar multiplication commutes and associates with
this product. The additive group and module structures are the original direct-limit
structures; no unit or degree-zero assumption is introduced here.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R A : Type*} [AddCommGroup Γ] [CommRing R] [Ring A] [Algebra R A]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (𝒜 : Γ → Submodule R A)
  [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜]

instance instNonUnitalRingShiftedDirectLimit : NonUnitalRing (d.ShiftedDirectLimit 𝒜) where
  __ := (inferInstance : AddCommGroup (d.ShiftedDirectLimit 𝒜))
  mul x y := d.shiftedDirectLimitMul 𝒜 x y
  mul_assoc := d.shiftedDirectLimitMul_assoc 𝒜
  left_distrib a b c := (d.shiftedDirectLimitMul 𝒜 a).map_add b c
  right_distrib a b c := congrArg (fun f => f c) ((d.shiftedDirectLimitMul 𝒜).map_add a b)
  zero_mul a := congrArg (fun f => f a) (d.shiftedDirectLimitMul 𝒜).map_zero
  mul_zero a := (d.shiftedDirectLimitMul 𝒜 a).map_zero

/-- The ring multiplication is the descended completed bilinear product. -/
theorem shiftedDirectLimitMul_eq_mul (x y : d.ShiftedDirectLimit 𝒜) :
    d.shiftedDirectLimitMul 𝒜 x y = x * y := (rfl)

instance instSMulCommClassShiftedDirectLimit :
    SMulCommClass R (d.ShiftedDirectLimit 𝒜) (d.ShiftedDirectLimit 𝒜) where
  smul_comm r x y := (map_smul (d.shiftedDirectLimitMul 𝒜 x) r y).symm

instance instIsScalarTowerShiftedDirectLimit :
    IsScalarTower R (d.ShiftedDirectLimit 𝒜) (d.ShiftedDirectLimit 𝒜) where
  smul_assoc r x y := by
    change d.shiftedDirectLimitMul 𝒜 (r • x) y = r • d.shiftedDirectLimitMul 𝒜 x y
    rw [map_smul, LinearMap.smul_apply]

end Mei.PositiveDegrees
