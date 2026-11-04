/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Nilpotent.Exp

/-!
# Nilpotent exponentials in trivial square-zero extensions

In a trivial square-zero extension `TrivSqZeroExt R M` over `ℚ`, Mathlib's finite exponential
`IsNilpotent.exp` of `inr m` is `1 + inr m` (`IsNilpotent.exp_inr`). This is the algebraic
counterpart of Mathlib's `TrivSqZeroExt.exp_inr` for the analytic exponential.
-/

public section

open TrivSqZeroExt

namespace IsNilpotent

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M] [Module ℚ R] [Module ℚ M]

/-- The finite exponential of `inr m` in a trivial square-zero extension is `1 + inr m`. -/
@[simp]
theorem exp_inr (m : M) : exp (inr m : TrivSqZeroExt R M) = 1 + inr m := by
  rw [exp_eq_sum (k := 2) (by rw [sq, inr_mul_inr])]
  simp [Finset.sum_range_succ]

end IsNilpotent
