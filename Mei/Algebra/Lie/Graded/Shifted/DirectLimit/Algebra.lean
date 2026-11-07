/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.DirectLimit.Product
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Unit

/-!
# Global completed BCH algebra actions

If the original unit has degree zero, the global linear action of each completed
BCH label is an algebra automorphism. Product preservation is supplied by the
nonunital result; the unit law follows from invertibility of that multiplicative map.
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
  [SetLike.GradedMonoid 𝒜]

private def shiftedBCHDirectLimitAlgEquiv (g : d.completedBCHGroup ℒ) :
    d.ShiftedDirectLimit 𝒜 ≃ₐ[R] d.ShiftedDirectLimit 𝒜 :=
  let e := d.shiftedDirectLimitBCHAction ℒ 𝒜 g
  let m : d.ShiftedDirectLimit 𝒜 ≃* d.ShiftedDirectLimit 𝒜 :=
    { e.toEquiv with map_mul' := d.shiftedDirectLimitBCHAction_map_mul ℒ 𝒜 g }
  AlgEquiv.ofLinearEquiv e m.map_one (d.shiftedDirectLimitBCHAction_map_mul ℒ 𝒜 g)

private theorem shiftedBCHDirectLimitAlgEquiv_mul (g h : d.completedBCHGroup ℒ) :
    d.shiftedBCHDirectLimitAlgEquiv ℒ 𝒜 (g * h) =
      d.shiftedBCHDirectLimitAlgEquiv ℒ 𝒜 g * d.shiftedBCHDirectLimitAlgEquiv ℒ 𝒜 h := by
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun e : d.ShiftedDirectLimit 𝒜 ≃ₗ[R] d.ShiftedDirectLimit 𝒜 => e x)
    ((d.shiftedDirectLimitBCHAction ℒ 𝒜).map_mul g h)

/-- Completed BCH labels act on global coefficients by algebra automorphisms. -/
def shiftedDirectLimitBCHAlgAction : d.completedBCHGroup ℒ →*
    (d.ShiftedDirectLimit 𝒜 ≃ₐ[R] d.ShiftedDirectLimit 𝒜) :=
  MonoidHom.mk' (d.shiftedBCHDirectLimitAlgEquiv ℒ 𝒜)
    (d.shiftedBCHDirectLimitAlgEquiv_mul ℒ 𝒜)

/-- The algebra action has the original global linear action as underlying map. -/
@[simp]
theorem shiftedDirectLimitBCHAlgAction_apply (g : d.completedBCHGroup ℒ)
    (x : d.ShiftedDirectLimit 𝒜) :
    d.shiftedDirectLimitBCHAlgAction ℒ 𝒜 g x = d.shiftedDirectLimitBCHAction ℒ 𝒜 g x := by
  -- Both constructors retain the underlying linear map.
  rfl

/-- Arbitrary-origin chart embeddings intertwine the completed algebra action. -/
theorem shiftedDirectLimitBCHAlgAction_toShiftedDirectLimitOfChart (g : d.completedBCHGroup ℒ)
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (x : d.ShiftedCoefficients 𝒜 p) :
    d.shiftedDirectLimitBCHAlgAction ℒ 𝒜 g
        (d.toShiftedDirectLimitOfChart 𝒜 p s hp x) =
      d.toShiftedDirectLimitOfChart 𝒜 p s hp
        ((d.shiftedLieFiltration ℒ 𝒜 p).completedBCHAction d ℒ g x) := by
  rw [shiftedDirectLimitBCHAlgAction_apply,
    shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart]

/-- Inverting the label reverses its global algebra action. -/
@[simp]
theorem shiftedDirectLimitBCHAlgAction_inv (g : d.completedBCHGroup ℒ) :
    d.shiftedDirectLimitBCHAlgAction ℒ 𝒜 g⁻¹ = (d.shiftedDirectLimitBCHAlgAction ℒ 𝒜 g).symm :=
  map_inv (d.shiftedDirectLimitBCHAlgAction ℒ 𝒜) g

end Mei.PositiveDegrees
