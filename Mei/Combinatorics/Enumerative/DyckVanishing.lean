/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Combinatorics.Enumerative.DyckShadow

/-!
# Compatible gradings cannot be large in both directions

A grading of the maximal Dyck path of `(d₁, d₂)` is compatible exactly when no horizontal edge
`h` and vertical edge `v` lie in each other's local shadows. By the double cycle lemma
`Mei.CyclicMatching.exists_mutual`, such a pair exists as soon as `p ≥ d₁` and `q ≥ d₂`, so a
compatible grading has `p < d₁` or `q < d₂` (for `(d₁, d₂) ≠ (0, 0)`).

Consequently the vanishing conditions (V) of the rank-two polynomial formula hold in the region
`q ≥ d₂` for `C₊` and in the region `p ≥ d₁` for `C₋`: off `(0, 0)`, `C₊(p, q) = 0` when
`q ≥ d₂` and `d₁ q ≤ d₂ p`, and `C₋(p, q) = 0` when `p ≥ d₁` and `d₂ p ≤ d₁ q`.
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

/-- **Compatible gradings are small in some direction.** If `p ≥ d₁` and `q ≥ d₂`, with
`(d₁, d₂) ≠ (0, 0)`, the grading is not compatible. -/
theorem not_compatible_of_le (hd : 0 < d₁ + d₂) (hp : d₁ ≤ verticalTotal γ)
    (hq : d₂ ≤ horizontalTotal γ) : ¬Compatible γ := by
  have : NeZero (d₁ + d₂) := ⟨hd.ne'⟩
  rw [compatible_iff_forall_not_mem_shadow]
  obtain ⟨h, hh, v, hv, hfwd, hbwd⟩ := exists_mutual (verticalEdges d₁ d₂) γ γ
    (by rw [card_verticalEdges, compl_verticalEdges, ← horizontalTotal_eq]; exact hq)
    (by rw [compl_verticalEdges, card_horizontalEdges, ← verticalTotal_eq]; exact hp)
  have hhH : h ∈ horizontalEdges d₁ d₂ := by rw [← compl_verticalEdges, mem_compl]; exact hh
  refine fun hall ↦ hall h hhH v hv ⟨?_, ?_⟩
  · rw [mem_horizontalShadow]
    exact ⟨hv, fun e he hbal ↦ hfwd e he ((verticalBalanced_iff γ h e).mp hbal)⟩
  · rw [mem_verticalShadow]
    refine ⟨hhH, fun e he hbal ↦ ?_⟩
    rw [horizontalBalanced_iff_weight, ← compl_verticalEdges] at hbal
    exact hbwd e he hbal

/-- With no edges, the only totals are `(0, 0)`. -/
private theorem totals_eq_zero_of_card (hd : d₁ + d₂ = 0) :
    verticalTotal γ = 0 ∧ horizontalTotal γ = 0 := by
  have hV : verticalEdges d₁ d₂ = ∅ := by
    rw [← card_eq_zero, card_verticalEdges]; omega
  have hH : horizontalEdges d₁ d₂ = ∅ := by
    rw [← card_eq_zero, card_horizontalEdges]; omega
  rw [verticalTotal_eq, horizontalTotal_eq, hV, hH]
  simp

variable {S : Type*} [CommSemiring S] (P₁ P₂ : S[X])

/-- **(V) for `C₊` in the region `q ≥ d₂`.** Off `(0, 0)`, `C₊(p, q) = 0` when `q ≥ d₂` and
`d₁ q ≤ d₂ p`. -/
theorem cplus_eq_zero_of_le {p q : ℕ} (hq : d₂ ≤ q) (hpq : d₁ * q ≤ d₂ * p)
    (h0 : (p, q) ≠ (0, 0)) : cplus d₁ d₂ P₁ P₂ p q = 0 := by
  rw [cplus_def]
  refine sum_eq_zero fun γ hγ ↦ absurd hγ ?_
  rw [mem_filter, not_and]
  rintro - ⟨hc, rfl, rfl, -⟩
  rcases Nat.eq_zero_or_pos d₂ with hd₂ | hd₂
  · subst hd₂
    rcases Nat.eq_zero_or_pos d₁ with hd₁ | hd₁
    · subst hd₁
      obtain ⟨h₁, h₂⟩ := totals_eq_zero_of_card γ rfl
      exact h0 (by rw [h₁, h₂])
    · have hq0 : horizontalTotal γ = 0 := by
        rw [zero_mul] at hpq
        exact (mul_eq_zero.mp (Nat.eq_zero_of_le_zero hpq)).resolve_left hd₁.ne'
      have hV : verticalEdges d₁ 0 = ∅ := by rw [← card_eq_zero, card_verticalEdges]
      have hp0 : verticalTotal γ = 0 := by rw [verticalTotal_eq, hV, sum_empty]
      exact h0 (by rw [hp0, hq0])
  · have hp : d₁ ≤ verticalTotal γ :=
      Nat.le_of_mul_le_mul_left (le_trans (Nat.mul_comm d₂ d₁ ▸ Nat.mul_le_mul_left d₁ hq) hpq)
        hd₂
    exact not_compatible_of_le γ (by omega) hp hq hc

/-- **(V) for `C₋` in the region `p ≥ d₁`.** Off `(0, 0)`, `C₋(p, q) = 0` when `p ≥ d₁` and
`d₂ p ≤ d₁ q`. -/
theorem cminus_eq_zero_of_le {p q : ℕ} (hp : d₁ ≤ p) (hpq : d₂ * p ≤ d₁ * q)
    (h0 : (p, q) ≠ (0, 0)) : cminus d₁ d₂ P₁ P₂ p q = 0 := by
  rw [cminus_def]
  refine sum_eq_zero fun γ hγ ↦ absurd hγ ?_
  rw [mem_filter, not_and]
  rintro - ⟨hc, rfl, rfl, -⟩
  rcases Nat.eq_zero_or_pos d₁ with hd₁ | hd₁
  · subst hd₁
    rcases Nat.eq_zero_or_pos d₂ with hd₂ | hd₂
    · subst hd₂
      obtain ⟨h₁, h₂⟩ := totals_eq_zero_of_card γ rfl
      exact h0 (by rw [h₁, h₂])
    · have hp0 : verticalTotal γ = 0 := by
        rw [zero_mul] at hpq
        exact (mul_eq_zero.mp (Nat.eq_zero_of_le_zero hpq)).resolve_left hd₂.ne'
      have hH : horizontalEdges 0 d₂ = ∅ := by rw [← card_eq_zero, card_horizontalEdges]
      have hq0 : horizontalTotal γ = 0 := by rw [horizontalTotal_eq, hH, sum_empty]
      exact h0 (by rw [hp0, hq0])
  · have hq : d₂ ≤ horizontalTotal γ :=
      Nat.le_of_mul_le_mul_left (le_trans (Nat.mul_comm d₁ d₂ ▸ Nat.mul_le_mul_left d₂ hp) hpq)
        hd₁
    exact not_compatible_of_le γ (by omega) hp hq hc

end Mei.MaximalDyckPath
