/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The variable of rational functions is not a constant

Over an integral domain `K`, the variable `X` of `RatFunc K` differs from every constant
`C c`. Since `RatFunc K` is a field, every ring homomorphism out of it to a nontrivial
semiring is injective, so no such homomorphism identifies `X` with a constant. In
particular no ring homomorphism `K(X) → S` to a nontrivial semiring sends `X` to `1`, in
contrast with evaluation of polynomials or Laurent polynomials at `1`.
-/

public section

namespace Mei.RatFunc

open _root_.RatFunc

variable {K : Type*} [CommRing K] [IsDomain K]

/-- The variable of rational functions is not a constant. -/
theorem X_ne_C (c : K) : (X : RatFunc K) ≠ C c := by
  rw [← algebraMap_X, ← algebraMap_C]
  exact (IsFractionRing.injective (Polynomial K) (RatFunc K)).ne (Polynomial.X_ne_C c)

/-- The variable of rational functions is not `1`. -/
theorem X_ne_one : (X : RatFunc K) ≠ 1 := by
  simpa only [map_one] using X_ne_C (1 : K)

variable {S : Type*} [Semiring S] [Nontrivial S]

/-- No ring homomorphism from rational functions to a nontrivial semiring identifies the
variable with the image of a constant. -/
theorem ringHom_X_ne_C (φ : RatFunc K →+* S) (c : K) : φ X ≠ φ (C c) :=
  φ.injective.ne (X_ne_C c)

/-- No ring homomorphism from rational functions to a nontrivial semiring sends the
variable to `1`. -/
theorem ringHom_X_ne_one (φ : RatFunc K →+* S) : φ X ≠ 1 := by
  simpa only [map_one] using ringHom_X_ne_C φ (1 : K)

end Mei.RatFunc
