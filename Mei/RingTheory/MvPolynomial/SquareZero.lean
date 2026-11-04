/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# The ring `ℚ[t₀, t₁]/(t₀², t₁²)`

`Mei.SquareZeroPolynomial₂` is the quotient of the rational polynomial ring in two variables
by the squares of the variables. The classes `t₀, t₁` of the variables square to zero, while
`t₀ t₁` does not vanish.
-/

public section

noncomputable section

namespace Mei

/-- The ring `ℚ[t₀, t₁]/(t₀², t₁²)`. -/
abbrev SquareZeroPolynomial₂ : Type :=
  MvPolynomial (Fin 2) ℚ ⧸
    (Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2} : Ideal (MvPolynomial (Fin 2) ℚ))

namespace SquareZeroPolynomial₂

/-- The classes `t₀, t₁` of the two variables. -/
def gen (j : Fin 2) : SquareZeroPolynomial₂ :=
  Ideal.Quotient.mk _ (MvPolynomial.X j)

/-- The classes of the variables square to zero. -/
theorem gen_mul_self (j : Fin 2) : gen j * gen j = 0 := by
  rw [gen, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  fin_cases j
  · exact Ideal.subset_span (Set.mem_insert _ _)
  · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

end SquareZeroPolynomial₂

end Mei
