/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Action
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Completion
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.TwistedAction

/-!
# Quantum ray actions on arbitrary shifted coefficients

In coordinates `z^p b`, conjugation by a positive ray series has left factor
`(z^p)⁻¹ H(z^n) z^p = H(q^(β(n,p) - β(p,n)) z^n)` and right factor `H(z^n)⁻¹`.
Here `(z^p)⁻¹ = q^(β(p,p)) z^(-p)`. For an alternating form the diagonal
factor is one and the skew exponent becomes `2 β(n,p)`.
The corresponding linear action is defined on the entire shifted completion,
without any positivity assumption on `p`, and preserves every relative order.
The shift does not contribute to relative degree.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)

/-- Conjugating a ray generator by the opposite shift gives the positive rescaling exponent. -/
theorem monomial_conj_ray (hβ : β.IsAlt) (n p : Γ) :
    monomial q β (-p) * monomial q β n * monomial q β p =
      ((q ^ (2 * β n p) : Rˣ) : R) • monomial q β n := by
  have h := congrArg (fun a => monomial q β (-p) * a)
    (monomial_semiconjBy q β hβ n p).eq
  have hi : monomial q β (-p) * monomial q β p = 1 := by
    simpa only [neg_neg] using monomial_mul_neg q β hβ (-p)
  simpa only [← mul_assoc, hi, one_mul] using h.symm

variable (d : PositiveDegrees Γ)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)

private local instance : Ring (positiveSubalgebra q β d.monoid) := inferInstance
private local instance : Algebra R (positiveSubalgebra q β d.monoid) := inferInstance
private local instance : Ring (F).completion := inferInstance
private local instance : Semiring (F).completion := (inferInstance : Ring (F).completion).toSemiring
private local instance : Monoid (F).completion := (inferInstance : Ring (F).completion).toMonoid
private local instance : One (F).completion := ⟨(inferInstance : Ring (F).completion).one⟩
private local instance : Algebra R (F).completion := inferInstance
private local instance : Module R (F).completion := inferInstance
private local instance : Mul (F).completion := ⟨(inferInstance : Ring (F).completion).mul⟩

/-- Unit ray series act linearly on every translated coefficient completion. -/
def shiftedRayAction (n : d.monoid) (hn : 0 < d.degree n) (p : Γ) :
    (PowerSeries R)ˣ →*
      (d.ShiftedCoefficients (grade q β) p ≃ₗ[R] d.ShiftedCoefficients (grade q β) p) where
  toFun H :=
    ((positiveCompletionShiftEquiv q β d p).symm.trans
      ((F).completedTwistedSeriesAction
        (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
        ((q ^ (β n p - β p n) : Rˣ) : R) H)).trans
      (positiveCompletionShiftEquiv q β d p)
  map_one' := by ext x; simp
  map_mul' H K := by ext x; simp

/-- The skew part of the bilinear form determines translated ray conjugation. -/
theorem shiftedRayAction_coordinates_skew (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) (a : (F).completion) :
    shiftedRayAction q β d n hn p H (positiveCompletionShiftEquiv q β d p a) =
      positiveCompletionShiftEquiv q β d p
        ((F).completedAeval
            (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
            (PowerSeries.rescale ((q ^ (β n p - β p n) : Rˣ) : R) (H : PowerSeries R)) * a *
          (F).completedAeval
            (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
            (↑(H⁻¹) : PowerSeries R)) := by
  simp only [shiftedRayAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, AlgFiltration.completedTwistedSeriesAction_apply]

/-- Shifted ray conjugation has the twisted left factor in positive coordinates. -/
theorem shiftedRayAction_coordinates (hβ : β.IsAlt) (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) (a : (F).completion) :
    shiftedRayAction q β d n hn p H (positiveCompletionShiftEquiv q β d p a) =
      positiveCompletionShiftEquiv q β d p
        ((F).completedAeval
            (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
            (PowerSeries.rescale ((q ^ (2 * β n p) : Rˣ) : R) (H : PowerSeries R)) * a *
          (F).completedAeval
            (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
            (↑(H⁻¹) : PowerSeries R)) := by
  simpa only [← hβ.neg_eq n p, sub_neg_eq_add, two_mul] using
    shiftedRayAction_coordinates_skew q β d n hn p H a

/-- At shift zero, the shifted action recovers the positive algebra ray automorphism. -/
theorem shiftedRayAction_zero (n : d.monoid)
    (hn : 0 < d.degree n) (H : (PowerSeries R)ˣ) (a : (F).completion) :
    shiftedRayAction q β d n hn 0 H (positiveCompletionShiftEquiv q β d 0 a) =
      positiveCompletionShiftEquiv q β d 0
        (completedRayAction q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn H a) := by
  have h := shiftedRayAction_coordinates_skew q β d n hn 0 H a
  refine h.trans (congrArg (positiveCompletionShiftEquiv q β d 0) ?_)
  have h₀ : PowerSeries.rescale ((q ^ (β n (0 : Γ) - β 0 n) : Rˣ) : R)
      (H : PowerSeries R) = H := by simp
  simp only [completedRayAction, AlgFiltration.completedSeriesAction_apply]
  exact congrArg (fun b => b * a * (F).completedAeval
    (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
    (↑(H⁻¹) : PowerSeries R))
      (congrArg ((F).completedAeval
        (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)) h₀)

/-- The base monomial transforms by the scalar ray ratio even at a negative shift. -/
theorem shiftedRayAction_base (hβ : β.IsAlt) (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) :
    shiftedRayAction q β d n hn p H (positiveCompletionShiftEquiv q β d p 1) =
      positiveCompletionShiftEquiv q β d p
        ((F).completedAeval
          (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
          (PowerSeries.rescale ((q ^ (2 * β n p) : Rˣ) : R) (H : PowerSeries R) *
            (↑(H⁻¹) : PowerSeries R))) := by
  refine (shiftedRayAction_coordinates q β d hβ n hn p H 1).trans ?_
  apply congrArg (positiveCompletionShiftEquiv q β d p)
  rw [mul_one]
  exact ((F).completedAeval
    (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)).map_mul'
      _ _ |>.symm

/-- Reversing a wall crossing gives the inverse shifted ray action. -/
@[simp]
theorem shiftedRayAction_inv (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) :
    shiftedRayAction q β d n hn p (H⁻¹) =
      (shiftedRayAction q β d n hn p H).symm :=
  map_inv (shiftedRayAction q β d n hn p) H

/-- Every relative filtration term is preserved and reflected by the shifted ray action. -/
@[simp]
theorem shiftedRayAction_mem_iff (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) (k : ℕ)
    (a : d.ShiftedCoefficients (grade q β) p) :
    shiftedRayAction q β d n hn p H a ∈
        (d.shiftedFiltration (grade q β) p).completedFiltration.submodule k ↔
      a ∈ (d.shiftedFiltration (grade q β) p).completedFiltration.submodule k := by
  let e := positiveCompletionShiftEquiv q β d p
  let x := completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn
  let c : R := ((q ^ (β n p - β p n) : Rˣ) : R)
  have h₁ := positiveCompletionShiftEquiv_mem_iff q β d p k
    ((F).completedTwistedSeriesAction x c H (e.symm a))
  have h₂ := (F).completedTwistedSeriesAction_mem_iff x c H k (e.symm a)
  have h₃ := positiveCompletionShiftEquiv_mem_iff q β d p k (e.symm a)
  have he : positiveCompletionShiftEquiv q β d p (e.symm a) = a := e.apply_symm_apply a
  have h₄ := Iff.of_eq (congrArg
    (fun y => y ∈ (d.shiftedFiltration (grade q β) p).completedFiltration.submodule k) he)
  exact h₁.trans (h₂.trans (h₃.symm.trans h₄))

end Mei.QuantumMonoidAlgebra
