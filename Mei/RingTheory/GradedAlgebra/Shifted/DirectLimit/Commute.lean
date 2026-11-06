/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.NonUnital

/-!
# Commutativity of global shifted coefficients

Commutativity of the ambient coefficient algebra passes to the global shifted
coefficient ring. The argument represents two global elements in one chart and
tests their completed product on finite quotient representatives. It does not
require a graded unit, a spanning positive monoid, or finite support.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R A : Type*} [AddCommGroup Γ] [CommRing R] [Ring A] [Algebra R A]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (𝒜 : Γ → Submodule R A)
  [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜]

omit [DecidableEq Γ] [DirectSum.Decomposition 𝒜] in
private theorem shiftedCompletionMul_comm_same_origin
    (hcomm : ∀ a b : A, Commute a b) (p : Γ) (x y : d.ShiftedCoefficients 𝒜 p) :
    d.shiftedCompletionMul 𝒜 p p x y = d.shiftedCompletionMul 𝒜 p p y x := by
  apply (d.shiftedFiltration 𝒜 (p + p)).completion_ext
  intro k
  obtain ⟨a, ha⟩ := ((d.shiftedFiltration 𝒜 p).submodule (k + 1)).mkQ_surjective
    ((d.shiftedFiltration 𝒜 p).projection k x)
  obtain ⟨b, hb⟩ := ((d.shiftedFiltration 𝒜 p).submodule (k + 1)).mkQ_surjective
    ((d.shiftedFiltration 𝒜 p).projection k y)
  rw [d.projection_shiftedCompletionMul 𝒜 p p k x y a b ha hb,
    d.projection_shiftedCompletionMul 𝒜 p p k y x b a hb ha]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simpa only [coe_shiftedMul] using (hcomm a b).eq

/-- Commuting finite coefficients give commuting global coefficients, including
infinite families in arbitrary negative charts. No graded unit is required. -/
theorem commute_shiftedDirectLimit (hcomm : ∀ a b : A, Commute a b)
    (x y : d.ShiftedDirectLimit 𝒜) : Commute x y := by
  obtain ⟨s, a, b, ha, hb⟩ := Module.DirectLimit.exists_of₂ x y
  have ha' : d.toShiftedDirectLimit 𝒜 s a = x :=
    (d.toShiftedDirectLimit_apply 𝒜 s a).trans ha
  have hb' : d.toShiftedDirectLimit 𝒜 s b = y :=
    (d.toShiftedDirectLimit_apply 𝒜 s b).trans hb
  change x * y = y * x
  rw [← ha', ← hb', toShiftedDirectLimit_mul, toShiftedDirectLimit_mul]
  exact congrArg _ (d.shiftedCompletionMul_comm_same_origin 𝒜 hcomm
    (d.coefficientOrigin s) a b)

end Mei.PositiveDegrees
