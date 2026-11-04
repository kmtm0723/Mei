/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit

/-!
# Associativity of global shifted coefficient multiplication

Every global coefficient has a completed chart representative. The arbitrary-origin
product formula reduces associativity to the existing associativity law of shifted
completed products; chart independence removes the two parenthesizations of origins.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R A : Type*} [AddCommGroup Γ] [CommRing R] [Ring A] [Algebra R A]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (𝒜 : Γ → Submodule R A)
  [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜]

omit [SetLike.GradedMul 𝒜] in
omit [DirectSum.Decomposition 𝒜] in
private theorem toShiftedDirectLimitOfChart_cast (p q : Γ) (h : p = q)
    (s t : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (hq : q - d.coefficientOrigin t ∈ d.monoid) (x : d.ShiftedCoefficients 𝒜 p) :
    d.toShiftedDirectLimitOfChart 𝒜 q t hq (cast (congrArg (d.ShiftedCoefficients 𝒜) h) x) =
      d.toShiftedDirectLimitOfChart 𝒜 p s hp x := by
  cases h
  exact d.toShiftedDirectLimitOfChart_eq 𝒜 p t s hq hp x

/-- Multiplication of global coefficients is associative. -/
theorem shiftedDirectLimitMul_assoc (x y z : d.ShiftedDirectLimit 𝒜) :
    d.shiftedDirectLimitMul 𝒜 (d.shiftedDirectLimitMul 𝒜 x y) z =
      d.shiftedDirectLimitMul 𝒜 x (d.shiftedDirectLimitMul 𝒜 y z) := by
  obtain ⟨s, x, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 x
  obtain ⟨t, y, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 y
  obtain ⟨u, z, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 z
  let p := d.coefficientOrigin s
  let q := d.coefficientOrigin t
  let r := d.coefficientOrigin u
  have hl : (p + q) + r - d.coefficientOrigin ((s + t) + u) ∈ d.monoid := by
    rw [coefficientOrigin_add, coefficientOrigin_add]
    simp only [p, q, r, sub_self, zero_mem]
  have hr : p + (q + r) - d.coefficientOrigin (s + (t + u)) ∈ d.monoid := by
    rw [coefficientOrigin_add, coefficientOrigin_add]
    simp only [p, q, r, sub_self, zero_mem]
  have hc := d.toShiftedDirectLimitOfChart_cast 𝒜 ((p + q) + r) (p + (q + r))
    (add_assoc p q r) ((s + t) + u) (s + (t + u)) hl hr
    (d.shiftedCompletionMul 𝒜 (p + q) r (d.shiftedCompletionMul 𝒜 p q x y) z)
  have ha := congrArg (d.toShiftedDirectLimitOfChart 𝒜 (p + (q + r)) (s + (t + u)) hr)
    (d.shiftedCompletionMul_assoc 𝒜 p q r x y z)
  have hchart (v : Multiset d.monoid)
      (a : d.ShiftedCoefficients 𝒜 (d.coefficientOrigin v)) :
      d.toShiftedDirectLimit 𝒜 v a =
        d.toShiftedDirectLimitOfChart 𝒜 (d.coefficientOrigin v) v (by simp) a := by
    rw [toShiftedDirectLimitOfChart_apply, shiftedCompletedInclusion_refl]
  simp only [hchart, shiftedDirectLimitMul_toShiftedDirectLimitOfChart]
  exact hc.symm.trans ha

end Mei.PositiveDegrees
