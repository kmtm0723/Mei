/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Units
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Embedding
public import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Monomial units in global quantum coefficients

The finite coefficient embedding transports quantum monomials and their units
into the algebra of coefficients supported in a translate of the positive
monoid. The formulas retain the diagonal correction for arbitrary bilinear
forms. Conjugation by these units is an algebra automorphism of all global
coefficients, including infinite families; its value on finite monomials is the
skew-character rescaling.

The positive-difference spanning hypothesis is explicit. This is part of
[quantum coefficients](https://github.com/yuma-mizuno/TauCetiRoadmap/blob/mei/TauCetiRoadmap/ScatteringDiagrams/README.md#43-quantum-coefficients).
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)
  (hspan : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b)

private local instance : Ring (QuantumMonoidAlgebra q β) := inferInstance
private local instance : Algebra R (QuantumMonoidAlgebra q β) := inferInstance
private local instance : AddCommGroup (QuantumMonoidAlgebra q β) := inferInstance
private local instance : Module R (QuantumMonoidAlgebra q β) := inferInstance
private local instance : DirectSum.Decomposition (grade q β) := inferInstance
private local instance : Ring (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : Algebra R (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : Module R (d.ShiftedDirectLimit (grade q β)) := inferInstance

/-- An ordinary quantum monomial viewed as a global coefficient. -/
def directLimitMonomial (p : Γ) : d.ShiftedDirectLimit (grade q β) :=
  d.toShiftedDirectLimitAlgHom (grade q β) hspan (monomial q β p)

/-- The global monomial is computed by the original algebra embedding. -/
theorem directLimitMonomial_eq (p : Γ) :
    directLimitMonomial q β d hspan p =
      d.toShiftedDirectLimitAlgHom (grade q β) hspan (monomial q β p) := (rfl)

/-- Monomials remain units under the finite coefficient embedding. -/
def directLimitMonomialUnit (p : Γ) : (d.ShiftedDirectLimit (grade q β))ˣ :=
  Units.map (d.toShiftedDirectLimitAlgHom (grade q β) hspan).toMonoidHom (monomialUnit q β p)

/-- The global monomial is the value of its transported unit. -/
@[simp]
theorem coe_directLimitMonomialUnit (p : Γ) :
    (directLimitMonomialUnit q β d hspan p : d.ShiftedDirectLimit (grade q β)) =
      directLimitMonomial q β d hspan p := by
  change (d.toShiftedDirectLimitAlgHom (grade q β) hspan)
    (monomialUnit q β p : QuantumMonoidAlgebra q β) = _
  rw [coe_monomialUnit]
  rfl

/-- The global inverse has the same nonalternating diagonal correction. -/
@[simp]
theorem coe_directLimitMonomialUnit_inv (p : Γ) :
    (↑(directLimitMonomialUnit q β d hspan p)⁻¹ : d.ShiftedDirectLimit (grade q β)) =
      ((q ^ β p p : Rˣ) : R) • directLimitMonomial q β d hspan (-p) := by
  change (d.toShiftedDirectLimitAlgHom (grade q β) hspan)
    (↑(monomialUnit q β p)⁻¹ : QuantumMonoidAlgebra q β) = _
  rw [coe_monomialUnit_inv, _root_.map_smul]
  rfl

/-- Global monomial multiplication retains the full bilinear quantum phase. -/
@[simp]
theorem directLimitMonomial_mul (p r : Γ) :
    directLimitMonomial q β d hspan p * directLimitMonomial q β d hspan r =
      ((q ^ β p r : Rˣ) : R) • directLimitMonomial q β d hspan (p + r) := by
  simp only [directLimitMonomial, ← map_mul, monomial_mul, _root_.map_smul]

/-- The zero global monomial is the global algebra unit. -/
@[simp]
theorem directLimitMonomial_zero : directLimitMonomial q β d hspan 0 = 1 := by
  simp only [directLimitMonomial, monomial_zero, map_one]

/-- Right conjugation by a monomial acts on every global coefficient. -/
def directLimitMonomialRightConj (p : Γ) :
    d.ShiftedDirectLimit (grade q β) ≃ₐ[R] d.ShiftedDirectLimit (grade q β) :=
  MulSemiringAction.toAlgAut (ConjAct (d.ShiftedDirectLimit (grade q β))ˣ) R
    (d.ShiftedDirectLimit (grade q β))
    (ConjAct.toConjAct (directLimitMonomialUnit q β d hspan p)⁻¹)

/-- The right-conjugation convention places the inverse unit on the left. -/
theorem directLimitMonomialRightConj_apply (p : Γ)
    (x : d.ShiftedDirectLimit (grade q β)) :
    directLimitMonomialRightConj q β d hspan p x =
      (↑(directLimitMonomialUnit q β d hspan p)⁻¹ : d.ShiftedDirectLimit (grade q β)) * x *
        directLimitMonomial q β d hspan p := by
  rw [← coe_directLimitMonomialUnit]
  change (↑(directLimitMonomialUnit q β d hspan p)⁻¹ : d.ShiftedDirectLimit (grade q β)) *
    x * ↑((directLimitMonomialUnit q β d hspan p)⁻¹)⁻¹ = _
  rw [inv_inv]

/-- Global right conjugation on finite monomials depends only on the skew form. -/
@[simp]
theorem directLimitMonomialRightConj_monomial (p n : Γ) :
    directLimitMonomialRightConj q β d hspan p (directLimitMonomial q β d hspan n) =
      ((q ^ (β n p - β p n) : Rˣ) : R) • directLimitMonomial q β d hspan n := by
  rw [directLimitMonomialRightConj_apply]
  have h := congrArg (d.toShiftedDirectLimitAlgHom (grade q β) hspan)
    (monomialUnit_inv_mul_monomial_mul q β p n)
  simpa only [map_mul, coe_monomialUnit_inv, coe_monomialUnit, _root_.map_smul,
    coe_directLimitMonomialUnit_inv, directLimitMonomial] using h

end Mei.QuantumMonoidAlgebra
