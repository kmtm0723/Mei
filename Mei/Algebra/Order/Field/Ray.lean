/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rays in the coordinate plane

In a linearly ordered field, `a² + b² > 0` as soon as `a ≠ 0` or `b ≠ 0`. For such `(a, b)`,
the points `-t (a, b)` with `t ≥ 0` are exactly the points `(p, q)` of the line
`a q = b p` with `a p + b q ≤ 0`.
-/

public section

namespace Mei

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b p q : K}

/-- A sum of two squares is positive unless both terms vanish. -/
theorem sq_add_sq_pos_of_ne_zero_or_ne_zero (h : a ≠ 0 ∨ b ≠ 0) : 0 < a ^ 2 + b ^ 2 := by
  rcases h with h | h
  · exact add_pos_of_pos_of_nonneg (pow_pos (abs_pos.mpr h) 2 |>.trans_eq (sq_abs a))
      (sq_nonneg b)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg a)
      (pow_pos (abs_pos.mpr h) 2 |>.trans_eq (sq_abs b))

/-- The ray `-ℝ≥0 (a, b)` is the half of the line `a q = b p` on which `a p + b q ≤ 0`. -/
theorem exists_nonneg_eq_neg_mul_iff (h : a ≠ 0 ∨ b ≠ 0) :
    (∃ t : K, 0 ≤ t ∧ p = -(t * a) ∧ q = -(t * b)) ↔ a * q - b * p = 0 ∧ a * p + b * q ≤ 0 := by
  have hpos := sq_add_sq_pos_of_ne_zero_or_ne_zero h
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩
    refine ⟨by ring, ?_⟩
    have : a * -(t * a) + b * -(t * b) = -(t * (a ^ 2 + b ^ 2)) := by ring
    rw [this, neg_nonpos]
    exact mul_nonneg ht hpos.le
  · rintro ⟨hq, hs⟩
    refine ⟨-(a * p + b * q) / (a ^ 2 + b ^ 2), div_nonneg (by linarith) hpos.le, ?_, ?_⟩
    · field_simp
      linear_combination (-b) * hq
    · field_simp
      linear_combination a * hq

end Mei
