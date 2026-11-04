/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Inverse powers of `1 - X` are not polynomials

Over a nontrivial commutative ring, Mathlib's `PowerSeries.invOneSubPow S d`, the inverse of
`(1 - X) ^ d`, is not the image of a polynomial when `d ≠ 0`
(`Polynomial.coe_ne_invOneSubPow`): a polynomial inverse of `(1 - X) ^ d` would give `0 = 1`
on evaluation at `1`.
-/

public section

namespace Polynomial

variable {S : Type*} [CommRing S] [Nontrivial S]

/-- For `d ≠ 0`, the inverse of `(1 - X) ^ d` is not a polynomial. -/
theorem coe_ne_invOneSubPow (p : S[X]) {d : ℕ} (hd : d ≠ 0) :
    (p : PowerSeries S) ≠ PowerSeries.invOneSubPow S d := by
  intro hp
  have hmul : p * (1 - X) ^ d = 1 := by
    apply coe_injective
    rw [coe_mul, coe_pow, coe_sub, coe_one, coe_X, hp,
      ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow, Units.inv_eq_val_inv, Units.mul_inv]
  simpa [hd] using congrArg (eval 1) hmul

end Polynomial
