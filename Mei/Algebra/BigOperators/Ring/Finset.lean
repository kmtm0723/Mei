/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude Code
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Factoring sums over finite families of functions

The sum of a product over functions with freely varying coordinates factors into a fixed
product and a power of the common local sum.
-/

public section

namespace Finset

/-- If the local sum on each free coordinate is `Q` and the fixed local factors there are
one, summing over all free choices multiplies the fixed product by `Q ^ #O`. -/
theorem sum_piFinset_factor {ι α R : Type*} [Fintype ι] [DecidableEq ι]
    [CommSemiring R] (f : ι → α → R) (O : Finset ι) (T : Finset α) (Q : R)
    (hQ : ∀ k ∈ O, ∑ j ∈ T, f k j = Q) (g : ι → α) (h₀ : ∀ k ∈ O, f k (g k) = 1) :
    ∑ γ ∈ Fintype.piFinset (fun k ↦ if k ∈ O then T else {g k}), ∏ k, f k (γ k) =
      (∏ k, f k (g k)) * Q ^ #O := by
  classical
  rw [← prod_univ_sum]
  have h₁ : ∀ k, ∑ j ∈ (if k ∈ O then T else {g k}), f k j =
      if k ∈ O then Q * f k (g k) else f k (g k) := by
    intro k
    split_ifs with hk
    · rw [hQ k hk, h₀ k hk, mul_one]
    · rw [sum_singleton]
  rw [prod_congr rfl fun k _ ↦ h₁ k, prod_ite, prod_mul_distrib, ← prod_mul_prod_compl
    (univ.filter (· ∈ O)), compl_filter]
  rw [prod_congr rfl fun k hk ↦ h₀ k (mem_filter.mp hk).2, prod_const_one, one_mul,
    prod_const, filter_mem_eq_inter, univ_inter]
  ring

end Finset
