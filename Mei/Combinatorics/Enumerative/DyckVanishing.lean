/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Combinatorics.Enumerative.DyckShadow

/-!
# Vanishing of the shadowed compatible grading sums

A grading of the maximal Dyck path of `(d₁, d₂)` is compatible exactly when no horizontal edge
`h` and vertical edge `v` lie in each other's local shadows. The double cycle lemmas of
`Mei.CyclicMatching` produce such a pair in the following situations:

* `p ≥ d₁` and `q ≥ d₂` (`not_compatible_of_le`, from `Mei.CyclicMatching.exists_mutual`);
* `p ≥ d₁` and the vertical support lies in the total horizontal shadow
  (`not_compatible_of_verticalSupport_subset`);
* `q ≥ d₂` and the horizontal support lies in the total vertical shadow
  (`not_compatible_of_horizontalSupport_subset`).

Consequently, off `(0, 0)`, `C₊(p, q) = 0` whenever `p ≥ d₁` and `C₋(p, q) = 0` whenever
`q ≥ d₂`. These are the parts of the vanishing conditions (V) of the rank-two polynomial formula
lying outside the rectangle `p < d₁`, `q < d₂`.
-/

public section

open Finset Mei.CyclicMatching Polynomial

namespace Mei.MaximalDyckPath

variable {d₁ d₂ : ℕ} (γ : Edge d₁ d₂ → ℕ)

/-- Horizontal balance is the vanishing of the weight with horizontal sinks. -/
theorem horizontalBalanced_iff_weight (e v : Edge d₁ d₂) :
    HorizontalBalanced γ e v ↔
      ∑ k ∈ cyclicIcc e v, CyclicMatching.weight (horizontalEdges d₁ d₂) γ k = 0 := by
  rw [HorizontalBalanced, sum_weight_eq, compl_horizontalEdges, sub_eq_zero, eq_comm,
    Nat.cast_inj]

/-- A grading is compatible exactly when no horizontal edge and vertical edge lie in each
other's local shadows. -/
theorem compatible_iff_forall_not_mem_shadow :
    Compatible γ ↔ ∀ h ∈ horizontalEdges d₁ d₂, ∀ v ∈ verticalEdges d₁ d₂,
      ¬(v ∈ horizontalShadow γ h ∧ h ∈ verticalShadow γ v) := by
  refine forall₂_congr fun h hh ↦ forall₂_congr fun v hv ↦ ?_
  rw [mem_horizontalShadow, mem_verticalShadow]
  simp only [hh, hv, true_and, not_and_or, not_forall, not_not, exists_prop]

/-- A horizontal edge and a vertical edge that see each other, in the form produced by the double
cycle lemmas, witness incompatibility. -/
private theorem not_compatible_of_exists
    (H : ∃ h ∉ verticalEdges d₁ d₂, ∃ v ∈ verticalEdges d₁ d₂,
      (∀ e, (e - h).val < (v - h).val →
        ∑ k ∈ cyclicIcc h e, CyclicMatching.weight (verticalEdges d₁ d₂) γ k ≠ 0) ∧
      ∀ e, (v - e).val < (v - h).val →
        ∑ k ∈ cyclicIcc e v, CyclicMatching.weight (verticalEdges d₁ d₂)ᶜ γ k ≠ 0) :
    ¬Compatible γ := by
  obtain ⟨h, hh, v, hv, hfwd, hbwd⟩ := H
  rw [compatible_iff_forall_not_mem_shadow]
  have hhH : h ∈ horizontalEdges d₁ d₂ := by rw [← compl_verticalEdges, mem_compl]; exact hh
  refine fun hall ↦ hall h hhH v hv ⟨?_, ?_⟩
  · rw [mem_horizontalShadow]
    exact ⟨hv, fun e he hbal ↦ hfwd e he ((verticalBalanced_iff γ h e).mp hbal)⟩
  · rw [mem_verticalShadow]
    refine ⟨hhH, fun e he hbal ↦ ?_⟩
    rw [horizontalBalanced_iff_weight, ← compl_verticalEdges] at hbal
    exact hbwd e he hbal

/-- **Compatible gradings are small in some direction.** If `p ≥ d₁` and `q ≥ d₂`, with
`(d₁, d₂) ≠ (0, 0)`, the grading is not compatible. -/
theorem not_compatible_of_le (hd : 0 < d₁ + d₂) (hp : d₁ ≤ verticalTotal γ)
    (hq : d₂ ≤ horizontalTotal γ) : ¬Compatible γ := by
  have : NeZero (d₁ + d₂) := ⟨hd.ne'⟩
  exact not_compatible_of_exists γ (exists_mutual (verticalEdges d₁ d₂) γ γ
    (by rw [card_verticalEdges, compl_verticalEdges, ← horizontalTotal_eq]; exact hq)
    (by rw [compl_verticalEdges, card_horizontalEdges, ← verticalTotal_eq]; exact hp))

/-- If `p ≥ d₁ > 0` and every vertical edge of nonzero grade lies in the total horizontal
shadow, the grading is not compatible. -/
theorem not_compatible_of_verticalSupport_subset (hd₁ : 0 < d₁) (hp : d₁ ≤ verticalTotal γ)
    (hs : verticalSupport γ ⊆ totalHorizontalShadow γ) : ¬Compatible γ := by
  have : NeZero (d₁ + d₂) := ⟨by omega⟩
  refine not_compatible_of_exists γ (exists_mutual_of_forall_matched (verticalEdges d₁ d₂) γ γ
    ?_ (fun v hv hγ ↦ ?_) ?_)
  · rw [compl_verticalEdges, ← card_pos, card_horizontalEdges]
    exact hd₁
  · have := hs ((mem_verticalSupport γ).mpr ⟨hv, hγ⟩)
    rw [totalHorizontalShadow_eq, mem_filter] at this
    exact this.2
  · rw [compl_verticalEdges, card_horizontalEdges, ← verticalTotal_eq]
    exact hp

/-- If `q ≥ d₂ > 0` and every horizontal edge of nonzero grade lies in the total vertical
shadow, the grading is not compatible. -/
theorem not_compatible_of_horizontalSupport_subset (hd₂ : 0 < d₂)
    (hq : d₂ ≤ horizontalTotal γ) (hs : horizontalSupport γ ⊆ totalVerticalShadow γ) :
    ¬Compatible γ := by
  have : NeZero (d₁ + d₂) := ⟨by omega⟩
  refine not_compatible_of_exists γ (exists_mutual_of_forall_matched_rev (verticalEdges d₁ d₂) γ
    γ ?_ (fun h hh hγ ↦ ?_) ?_)
  · rw [← card_pos, card_verticalEdges]
    exact hd₂
  · have hhH : h ∈ horizontalEdges d₁ d₂ := by rw [← compl_verticalEdges, mem_compl]; exact hh
    obtain ⟨v, hv, hsh⟩ := (mem_totalVerticalShadow γ).mp
      (hs ((mem_horizontalSupport γ).mpr ⟨hhH, hγ⟩))
    refine ⟨v, hv, fun e he hsum ↦ ((mem_verticalShadow γ).mp hsh).2 e he ?_⟩
    rw [horizontalBalanced_iff_weight, ← compl_verticalEdges]
    exact hsum
  · rw [card_verticalEdges, compl_verticalEdges, ← horizontalTotal_eq]
    exact hq

variable {S : Type*} [CommSemiring S] (P₁ P₂ : S[X])

/-- **(V) for `C₊` in the region `p ≥ d₁`.** Off `(0, 0)`, `C₊(p, q) = 0` when `p ≥ d₁`. -/
theorem cplus_eq_zero_of_le {p q : ℕ} (hp : d₁ ≤ p) (h0 : (p, q) ≠ (0, 0)) :
    cplus d₁ d₂ P₁ P₂ p q = 0 := by
  rw [cplus_def]
  refine sum_eq_zero fun γ hγ ↦ absurd hγ ?_
  rw [mem_filter, not_and]
  rintro - ⟨hc, rfl, rfl, hs⟩
  rcases Nat.eq_zero_or_pos d₁ with hd₁ | hd₁
  · subst hd₁
    -- Without horizontal edges both totals vanish.
    have hH : horizontalEdges 0 d₂ = ∅ := by rw [← card_eq_zero, card_horizontalEdges]
    have hp0 : verticalTotal γ = 0 := by
      rw [verticalTotal_eq]
      refine sum_eq_zero fun v hv ↦ by_contra fun hγ ↦ ?_
      obtain ⟨h, hh, -⟩ := (mem_totalHorizontalShadow γ).mp
        (hs ((mem_verticalSupport γ).mpr ⟨hv, hγ⟩))
      rw [hH] at hh
      exact notMem_empty h hh
    have hq0 : horizontalTotal γ = 0 := by rw [horizontalTotal_eq, hH, sum_empty]
    exact h0 (by rw [hp0, hq0])
  · exact not_compatible_of_verticalSupport_subset γ hd₁ hp hs hc

/-- **(V) for `C₋` in the region `q ≥ d₂`.** Off `(0, 0)`, `C₋(p, q) = 0` when `q ≥ d₂`. -/
theorem cminus_eq_zero_of_le {p q : ℕ} (hq : d₂ ≤ q) (h0 : (p, q) ≠ (0, 0)) :
    cminus d₁ d₂ P₁ P₂ p q = 0 := by
  rw [cminus_def]
  refine sum_eq_zero fun γ hγ ↦ absurd hγ ?_
  rw [mem_filter, not_and]
  rintro - ⟨hc, rfl, rfl, hs⟩
  rcases Nat.eq_zero_or_pos d₂ with hd₂ | hd₂
  · subst hd₂
    -- Without vertical edges both totals vanish.
    have hV : verticalEdges d₁ 0 = ∅ := by rw [← card_eq_zero, card_verticalEdges]
    have hq0 : horizontalTotal γ = 0 := by
      rw [horizontalTotal_eq]
      refine sum_eq_zero fun h hh ↦ by_contra fun hγ ↦ ?_
      obtain ⟨v, hv, -⟩ := (mem_totalVerticalShadow γ).mp
        (hs ((mem_horizontalSupport γ).mpr ⟨hh, hγ⟩))
      rw [hV] at hv
      exact notMem_empty v hv
    have hp0 : verticalTotal γ = 0 := by rw [verticalTotal_eq, hV, sum_empty]
    exact h0 (by rw [hp0, hq0])
  · exact not_compatible_of_horizontalSupport_subset γ hd₂ hq hs hc

end Mei.MaximalDyckPath
