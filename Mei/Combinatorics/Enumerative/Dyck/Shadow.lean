/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Combinatorics.Enumerative.Dyck.Grading

/-!
# Sizes of total shadows

For any grading `γ` of the maximal Dyck path of `(d₁, d₂)`, with totals `p = ∑ γ_V` and
`q = ∑ γ_H`, the total horizontal shadow has `min d₂ q` edges and the total vertical shadow has
`min d₁ p` edges. No compatibility is assumed.

A vertical edge lies in the total horizontal shadow exactly when it is a matched sink for the
horizontal grades on the cycle of edges, in the sense of `Mei.CyclicMatching`. The vertical
statement is the same count on the reversed cycle, obtained by negating edge indices.
-/

public section

open Finset Mei.CyclicMatching

namespace Mei.MaximalDyckPath

variable {d₁ d₂ : ℕ}

variable (γ : Edge d₁ d₂ → ℕ)

/-- Vertical balance is the vanishing of the weight with vertical sinks. -/
theorem verticalBalanced_iff (h e : Edge d₁ d₂) :
    VerticalBalanced γ h e ↔
      ∑ k ∈ cyclicIcc h e, CyclicMatching.weight (verticalEdges d₁ d₂) γ k = 0 := by
  rw [verticalBalanced_iff_card_eq_sum, sum_weight_eq, compl_verticalEdges, sub_eq_zero,
    eq_comm, Nat.cast_inj]

/-- Horizontal balance is the vanishing of the weight with horizontal sinks. -/
theorem horizontalBalanced_iff (e v : Edge d₁ d₂) :
    HorizontalBalanced γ e v ↔
      ∑ k ∈ cyclicIcc e v, CyclicMatching.weight (horizontalEdges d₁ d₂) γ k = 0 := by
  rw [horizontalBalanced_iff_card_eq_sum, sum_weight_eq, compl_horizontalEdges, sub_eq_zero,
    eq_comm,
    Nat.cast_inj]

/-- The total horizontal shadow is the set of matched vertical sinks. -/
theorem totalHorizontalShadow_eq :
    totalHorizontalShadow γ = {v ∈ verticalEdges d₁ d₂ | Matched (verticalEdges d₁ d₂) γ v} := by
  ext v
  rw [mem_filter, mem_totalHorizontalShadow, matched_iff_forall]
  simp only [mem_horizontalShadow, verticalBalanced_iff, ← compl_verticalEdges, mem_compl]
  constructor
  · rintro ⟨h, hh, hv, hall⟩
    exact ⟨hv, h, hh, hall⟩
  · rintro ⟨hv, h, hh, hall⟩
    exact ⟨h, hh, hv, hall⟩

/-- A vertical edge lies in the total horizontal shadow exactly when some subpath ending at it,
of length at least two, carries at least as much horizontal grade as it has vertical edges. -/
theorem mem_totalHorizontalShadow_iff {v : Edge d₁ d₂} :
    v ∈ totalHorizontalShadow γ ↔ v ∈ verticalEdges d₁ d₂ ∧
      ∃ u, u ≠ v ∧ #(cyclicIcc u v ∩ verticalEdges d₁ d₂) ≤
        ∑ h ∈ cyclicIcc u v ∩ horizontalEdges d₁ d₂, γ h := by
  rw [totalHorizontalShadow_eq, mem_filter]
  refine and_congr_right fun hv ↦ ?_
  have : NeZero (d₁ + d₂) := ⟨v.pos.ne'⟩
  rw [matched_iff_exists_nonneg _ _ hv]
  simp only [sum_weight_eq, compl_verticalEdges, sub_nonneg, Nat.cast_le]

/-- **Total horizontal shadow.** It has `min d₂ q` edges. -/
theorem card_totalHorizontalShadow :
    #(totalHorizontalShadow γ) = min d₂ (horizontalTotal γ) := by
  rw [totalHorizontalShadow_eq, card_matched, card_verticalEdges, compl_verticalEdges,
    horizontalTotal_eq]

/-- Horizontal balance on the reversed cycle, using the common cycle reflection API. -/
private theorem horizontalBalanced_iff_reflect (e v : Edge d₁ d₂) :
    HorizontalBalanced γ e v ↔
      ∑ k ∈ cyclicIcc (-v) (-e),
        CyclicMatching.weight (reflect (verticalEdges d₁ d₂)) (γ ∘ Neg.neg) k = 0 := by
  rw [sum_weight_reflect, neg_neg, neg_neg, compl_verticalEdges, horizontalBalanced_iff]

/-- The total vertical shadow is the reflection of the set of matched reflected horizontal
sinks. -/
private theorem totalVerticalShadow_eq :
    totalVerticalShadow γ = {x ∈ reflect (verticalEdges d₁ d₂) |
      Matched (reflect (verticalEdges d₁ d₂)) (γ ∘ Neg.neg) x}.map
        (Equiv.neg (Edge d₁ d₂)).toEmbedding := by
  ext k
  have : NeZero (d₁ + d₂) := ⟨k.pos.ne'⟩
  rw [mem_totalVerticalShadow, mem_map_equiv, Equiv.neg_symm, Equiv.neg_apply, mem_filter,
    mem_reflect, neg_neg, matched_iff_forall]
  constructor
  · rintro ⟨v, hv, hk⟩
    obtain ⟨hkH, hall⟩ := (mem_verticalShadow γ).mp hk
    refine ⟨notMem_verticalEdges_of_mem hkH, -v, ?_, fun e' he' ↦ ?_⟩
    · rwa [mem_reflect, neg_neg, not_not]
    · have h₁ : (v - -e').val < (v - k).val := by
        simpa only [sub_eq_add_neg, neg_neg, add_comm] using he'
      have := hall (-e') h₁
      rwa [horizontalBalanced_iff_reflect, neg_neg] at this
  · rintro ⟨hkH, h', hh', hall⟩
    have hv : -h' ∈ verticalEdges d₁ d₂ := by
      rwa [mem_reflect, not_not] at hh'
    have hkH' : k ∈ horizontalEdges d₁ d₂ := by
      rwa [← compl_verticalEdges, mem_compl]
    refine ⟨-h', hv, (mem_verticalShadow γ).mpr ⟨hkH', fun e he ↦ ?_⟩⟩
    rw [horizontalBalanced_iff_reflect, neg_neg]
    apply hall (-e)
    simpa only [sub_eq_add_neg, neg_neg, add_comm] using he

/-- **Total vertical shadow.** It has `min d₁ p` edges. -/
theorem card_totalVerticalShadow : #(totalVerticalShadow γ) = min d₁ (verticalTotal γ) := by
  rw [totalVerticalShadow_eq, card_map, card_matched, card_reflect, compl_verticalEdges,
    card_horizontalEdges]
  simp only [Function.comp_apply, sum_compl_reflect, ← verticalTotal_eq]

end Mei.MaximalDyckPath
