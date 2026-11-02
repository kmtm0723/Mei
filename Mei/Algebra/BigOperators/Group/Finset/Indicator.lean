/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Indicator

/-!
# Constant weights on finite disjoint covers

A weight supported on a set can be computed by summing the same weight over a
finite disjoint cover. The pieces need no geometric or topological hypotheses.
-/

public section

namespace Set

open Classical in
/-- Splitting a support into a finite disjoint cover preserves a fixed additive
weight at every point. -/
theorem ite_mem_eq_sum_of_pairwise_disjoint {α β ι : Type*} [AddCommMonoid β]
    [Fintype ι] (A : ι → Set α) (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    {D : Set α} (hcover : ⋃ j, A j = D) (x : α) (b : β) :
    (if x ∈ D then b else 0) = ∑ j, if x ∈ A j then b else 0 := by
  classical
  simpa [Set.indicator, hcover] using
    (Finset.indicator_biUnion_apply Finset.univ A (f := fun _ => b)
      (hdisj.set_pairwise _) x)

end Set
