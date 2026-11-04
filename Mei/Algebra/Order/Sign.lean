/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Basic.Sign.Basic

/-!
# Signs of small perturbations

In a linearly ordered additive group, adding an element of smaller absolute value does not
change the sign: if `|e| < |a|`, then `sign (a + e) = sign a` and `sign (a - e) = sign a`.
-/

public section

namespace Mei

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a e : α}

/-- A perturbation of smaller absolute value does not change the sign. -/
theorem sign_add_of_abs_lt (h : |e| < |a|) : SignType.sign (a + e) = SignType.sign a := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [abs_of_neg ha] at h
    have : a + e < 0 := by
      have := le_abs_self e
      calc a + e ≤ a + |e| := add_le_add_right this a
        _ < a + -a := add_lt_add_right h a
        _ = 0 := add_neg_cancel a
    rw [sign_neg ha, sign_neg this]
  · exact absurd h (not_lt.mpr (by simp))
  · rw [abs_of_pos ha] at h
    have : 0 < a + e := by
      have := neg_abs_le e
      calc 0 = a + -a := (add_neg_cancel a).symm
        _ < a + -|e| := add_lt_add_right (neg_lt_neg h) a
        _ ≤ a + e := add_le_add_right this a
    rw [sign_pos ha, sign_pos this]

/-- Subtracting an element of smaller absolute value does not change the sign. -/
theorem sign_sub_of_abs_lt (h : |e| < |a|) : SignType.sign (a - e) = SignType.sign a := by
  rw [sub_eq_add_neg]
  exact sign_add_of_abs_lt (by rwa [abs_neg])

end Mei
