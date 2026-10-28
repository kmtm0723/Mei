/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Basic
public import Mei.LinearAlgebra.GradedModule.Shifted
public import Mei.LinearAlgebra.ModuleFiltration.Equiv
public import Mei.Algebra.DirectSum.Degree.Map

/-!
# Translation equivalences for shifted quantum coefficients

Left multiplication by a quantum monomial translates coefficient support from
`s + P` to `(p + s) + P`. For an alternating form its inverse is multiplication
by the opposite monomial. Relative degrees are unchanged, so this equivalence
extends to all completed shifted coefficients. The ambient shifts may have
negative degree; no positivity or injectivity assumption on them is used.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (P : AddSubmonoid Γ) (p s : Γ)

/-- A monomial translates the support of a shifted coefficient module. -/
theorem monomial_mul_mem_shiftedSubmodule {x : QuantumMonoidAlgebra q β}
    (hx : x ∈ shiftedSubmodule (grade q β) P s) :
    monomial q β p * x ∈ shiftedSubmodule (grade q β) P (p + s) := by
  have h : shiftedSubmodule (grade q β) P s ≤
      (shiftedSubmodule (grade q β) P (p + s)).comap
        (LinearMap.mul R (QuantumMonoidAlgebra q β) (monomial q β p)) := by
    rw [shiftedSubmodule_def]
    refine iSup_le fun n y hy => ?_
    have hp : monomial q β p ∈ grade q β p :=
      (mem_grade_iff q β p _).mpr ⟨1, one_smul _ _⟩
    exact le_shiftedSubmodule (grade q β) P (p + s) n.property
      (by simpa only [add_assoc, LinearMap.mul_apply'] using SetLike.mul_mem_graded hp hy)
  exact h hx

/-- Multiplication by a monomial is a linear equivalence between translated supports. -/
def shiftedMonomialEquiv (hβ : β.IsAlt) :
    shiftedSubmodule (grade q β) P s ≃ₗ[R]
      shiftedSubmodule (grade q β) P (p + s) where
  toFun x := ⟨monomial q β p * x, monomial_mul_mem_shiftedSubmodule q β P p s x.property⟩
  invFun y := ⟨monomial q β (-p) * y, by
    simpa only [neg_add_cancel_left] using
      monomial_mul_mem_shiftedSubmodule q β P (-p) (p + s) y.property⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    rw [← mul_assoc]
    have hi : monomial q β (-p) * monomial q β p = 1 := by
      simpa only [neg_neg] using monomial_mul_neg q β hβ (-p)
    rw [hi, one_mul]
  right_inv y := by
    apply Subtype.ext
    dsimp
    rw [← mul_assoc, monomial_mul_neg q β hβ p, one_mul]
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' r x := Subtype.ext (mul_smul_comm _ _ _)

/-- The translation equivalence is left multiplication on underlying coefficients. -/
@[simp]
theorem coe_shiftedMonomialEquiv (hβ : β.IsAlt)
    (x : shiftedSubmodule (grade q β) P s) :
    (shiftedMonomialEquiv q β P p s hβ x : QuantumMonoidAlgebra q β) =
      monomial q β p * x := (rfl)

/-- Translation preserves the relative homogeneous index. -/
theorem shiftedMonomialEquiv_mem_shiftedGrading (hβ : β.IsAlt) {n : Γ}
    {x : shiftedSubmodule (grade q β) P s}
    (hx : x ∈ shiftedGrading (grade q β) P s n) :
    shiftedMonomialEquiv q β P p s hβ x ∈ shiftedGrading (grade q β) P (p + s) n := by
  rw [mem_shiftedGrading] at hx ⊢
  rw [coe_shiftedMonomialEquiv]
  have hp : monomial q β p ∈ grade q β p :=
    (mem_grade_iff q β p _).mpr ⟨1, one_smul _ _⟩
  simpa only [add_assoc] using SetLike.mul_mem_graded hp hx

variable (d : PositiveDegrees Γ)

/-- Arbitrary translation identifies every relative filtration term exactly. -/
theorem comap_shiftedFiltration_shiftedMonomialEquiv (hβ : β.IsAlt) (k : ℕ) :
    ((d.shiftedFiltration (grade q β) (p + s)).submodule k).comap
        (shiftedMonomialEquiv q β d.monoid p s hβ).toLinearMap =
      (d.shiftedFiltration (grade q β) s).submodule k := by
  classical
  cases k with
  | zero => simp
  | succ k =>
    rw [d.shiftedFiltration_succ (grade q β) (p + s) k,
      d.shiftedFiltration_succ (grade q β) s k,
      d.degreeSubmodule_eq_degreeTail, d.degreeSubmodule_eq_degreeTail]
    exact (shiftedMonomialEquiv q β d.monoid p s hβ).toLinearMap.comap_degreeTail_eq_of_injective
      (shiftedGrading (grade q β) d.monoid s)
      (shiftedGrading (grade q β) d.monoid (p + s))
      (shiftedMonomialEquiv q β d.monoid p s hβ).injective
      (fun _ _ hx => shiftedMonomialEquiv_mem_shiftedGrading q β d.monoid p s hβ hx)
      d.degree (k + 1)

/-- Quantum monomial translation extends to all shifted completed coefficients. -/
def shiftedCompletedMonomialEquiv (hβ : β.IsAlt) :
    d.ShiftedCoefficients (grade q β) s ≃ₗ[R]
      d.ShiftedCoefficients (grade q β) (p + s) :=
  (d.shiftedFiltration (grade q β) s).completionEquiv
    (d.shiftedFiltration (grade q β) (p + s))
    (shiftedMonomialEquiv q β d.monoid p s hβ)
    (comap_shiftedFiltration_shiftedMonomialEquiv q β p s d hβ)

/-- The completed equivalence agrees with multiplication on original shifted coefficients. -/
@[simp]
theorem shiftedCompletedMonomialEquiv_of (hβ : β.IsAlt)
    (x : shiftedSubmodule (grade q β) d.monoid s) :
    shiftedCompletedMonomialEquiv q β p s d hβ ((d.shiftedFiltration (grade q β) s).of x) =
      (d.shiftedFiltration (grade q β) (p + s)).of
        (shiftedMonomialEquiv q β d.monoid p s hβ x) := by
  exact ModuleFiltration.completionEquiv_of _ _ _ _ x

/-- Monomial translation preserves and reflects every completed relative order. -/
@[simp]
theorem shiftedCompletedMonomialEquiv_mem_completedFiltration_iff (hβ : β.IsAlt)
    (k : ℕ) (x : d.ShiftedCoefficients (grade q β) s) :
    shiftedCompletedMonomialEquiv q β p s d hβ x ∈
        (d.shiftedFiltration (grade q β) (p + s)).completedFiltration.submodule k ↔
      x ∈ (d.shiftedFiltration (grade q β) s).completedFiltration.submodule k :=
  ModuleFiltration.completionEquiv_mem_completedFiltration_iff _ _ _ _ k x

end Mei.QuantumMonoidAlgebra
