/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Component

/-!
# Support inclusions in direct-limit coefficients

An inclusion between translated supports does not change the represented global
coefficient, even when different containing multiset charts are chosen. The
injective ambient-component realization proves this without index transports.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ]

omit [DecidableEq Γ] in
/-- Adding chart indices adds their origins. -/
theorem coefficientOrigin_add (s t : Multiset d.monoid) :
    d.coefficientOrigin (s + t) = d.coefficientOrigin s + d.coefficientOrigin t := by
  simp only [coefficientOrigin_eq_neg_sum, Multiset.sum_add, AddSubmonoid.coe_add, neg_add]

/-- Enlarging an arbitrary support leaves its global coefficient unchanged. -/
theorem toShiftedDirectLimitOfChart_inclusion (p q : Γ)
    (hpq : p - q ∈ d.monoid) (s t : Multiset d.monoid)
    (hps : p - d.coefficientOrigin s ∈ d.monoid)
    (hqt : q - d.coefficientOrigin t ∈ d.monoid) (x : d.ShiftedCoefficients ℳ p) :
    d.toShiftedDirectLimitOfChart ℳ q t hqt (d.shiftedCompletedInclusion ℳ p q hpq x) =
      d.toShiftedDirectLimitOfChart ℳ p s hps x := by
  apply d.shiftedDirectLimitComponents_injective ℳ
  funext u
  simp only [shiftedDirectLimitComponents_toShiftedDirectLimitOfChart,
    shiftedHomogeneousComponent_inclusion]

end Mei.PositiveDegrees
