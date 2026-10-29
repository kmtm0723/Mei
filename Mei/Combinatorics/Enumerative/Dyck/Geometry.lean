/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mei.Combinatorics.Enumerative.Dyck.Basic
public import Mei.Combinatorics.Enumerative.CyclicMatching

/-!
# Cyclic windows of maximal Dyck paths

Prefix bounds give strict slope bounds for the horizontal and vertical edge counts of cyclic
windows. These geometric results do not depend on a grading or its vanishing theory.
-/

public section

open DyckStep Finset Mei.CyclicMatching

namespace Mei.MaximalDyckPath

variable {d₁ d₂ : ℕ}

/-! ### The path stays near the diagonal -/

/-- The edges with step `s`. -/
private abbrev stepEdges (d₁ d₂ : ℕ) (s : DyckStep) : Finset (Edge d₁ d₂) :=
  univ.filter fun k ↦ step k = s

/-- The number of edges of step `s` before position `a`. -/
private abbrev countBefore (d₁ d₂ : ℕ) (s : DyckStep) (a : ℕ) : ℕ :=
  #((stepEdges d₁ d₂ s).filter fun k ↦ k.val < a)

private theorem countBefore_succ (s : DyckStep) (e : Edge d₁ d₂) :
    countBefore d₁ d₂ s (e.val + 1) = countBefore d₁ d₂ s e.val + if step e = s then 1 else 0 := by
  have hsplit : (stepEdges d₁ d₂ s).filter (fun k ↦ k.val < e.val + 1) =
      (stepEdges d₁ d₂ s).filter (fun k ↦ k.val < e.val) ∪
        (stepEdges d₁ d₂ s).filter (fun k ↦ k = e) := by
    rw [← filter_or]
    exact filter_congr fun k _ ↦ by rw [Fin.ext_iff]; omega
  rw [countBefore, countBefore, hsplit, card_union_of_disjoint (disjoint_filter.mpr
    fun k _ h₁ h₂ ↦ by rw [h₂] at h₁; omega), filter_eq']
  split_ifs with h₁ h₂ h₂ <;> simp_all

/-- Counting edges before `a` is counting steps in the first `a` steps of the path. -/
private theorem countBefore_eq (s : DyckStep) (a : ℕ) :
    countBefore d₁ d₂ s a = ((maximalDyckPath d₁ d₂).take a).count s := by
  induction a with
  | zero => simp
  | succ a ih =>
    by_cases ha : a < d₁ + d₂
    · have := countBefore_succ s (⟨a, ha⟩ : Edge d₁ d₂)
      simp only at this
      rw [this, ih, List.take_add_one,
        List.getElem?_eq_getElem (by rw [length_maximalDyckPath]; exact ha)]
      simp only [Option.toList_some, List.count_append, List.count_singleton, step_def,
        beq_iff_eq]
    · have hfull : ∀ b, d₁ + d₂ ≤ b → countBefore d₁ d₂ s b = #(stepEdges d₁ d₂ s) := by
        intro b hb
        rw [countBefore, filter_true_of_mem fun k _ ↦ by omega]
      rw [hfull (a + 1) (by omega), ← hfull a (by omega), ih]
      have hlen : (maximalDyckPath d₁ d₂).length ≤ a := by
        rw [length_maximalDyckPath]; omega
      simp only [List.take_of_length_le hlen,
        List.take_of_length_le (hlen.trans (Nat.le_succ a))]

/-- The lattice distance `d₂ x - d₁ y` of a vertex below the diagonal is in `[0, d₁ + d₂)`. -/
private theorem countBefore_bounds (hd : 0 < d₁ + d₂) (a : ℕ) :
    d₁ * countBefore d₁ d₂ D a ≤ d₂ * countBefore d₁ d₂ U a ∧
      d₂ * countBefore d₁ d₂ U a < d₁ * countBefore d₁ d₂ D a + (d₁ + d₂) := by
  rw [countBefore_eq, countBefore_eq]
  exact mul_count_take_maximalDyckPath_le_and_lt hd a

/-- Membership in a step-filtered cyclic window, separated into wrapping and ordinary cases. -/
private theorem mem_step_window (s : DyckStep) (h e k : Edge d₁ d₂) :
    k ∈ cyclicIcc h e ∩ stepEdges d₁ d₂ s ↔ step k = s ∧
      if e < h then h.val ≤ k.val ∨ k.val ≤ e.val else h.val ≤ k.val ∧ k.val ≤ e.val := by
  simp only [mem_inter, mem_filter, mem_univ, true_and, mem_cyclicIcc_iff_le_or_lt,
    Fin.le_def, Fin.lt_def]
  split_ifs <;> grind

/-- A cyclic window, counted by step type, from the counts before its endpoints. -/
private theorem card_cyclicIcc_inter (s : DyckStep) (h e : Edge d₁ d₂) :
    #(cyclicIcc h e ∩ stepEdges d₁ d₂ s) + countBefore d₁ d₂ s h.val =
      countBefore d₁ d₂ s (e.val + 1) + if e < h then #(stepEdges d₁ d₂ s) else 0 := by
  rw [← card_union_add_card_inter]
  split_ifs with heh
  · rw [Fin.lt_def] at heh
    rw [add_comm (countBefore d₁ d₂ s (e.val + 1))]
    congr 1
    · congr 1
      ext k
      have hw := mem_step_window s h e k
      simp only [mem_union, mem_inter, mem_filter, mem_univ, true_and] at hw ⊢
      grind [Fin.le_def, Fin.lt_def]
    · congr 1
      ext k
      have hw := mem_step_window s h e k
      simp only [mem_inter, mem_filter, mem_univ, true_and] at hw ⊢
      grind [Fin.le_def, Fin.lt_def]
  · rw [Fin.lt_def, not_lt] at heh
    have hinter : (cyclicIcc h e ∩ stepEdges d₁ d₂ s) ∩
        (stepEdges d₁ d₂ s).filter (fun k ↦ k.val < h.val) = ∅ := by
      ext k
      have hw := mem_step_window s h e k
      simp only [mem_inter, mem_filter, mem_univ, true_and,
        notMem_empty, iff_false] at hw ⊢
      grind [Fin.le_def, Fin.lt_def]
    rw [hinter, card_empty, add_zero, add_zero]
    congr 1
    ext k
    have hw := mem_step_window s h e k
    simp only [mem_union, mem_inter, mem_filter, mem_univ, true_and] at hw ⊢
    grind [Fin.le_def, Fin.lt_def]

private theorem stepEdges_U : stepEdges d₁ d₂ U = horizontalEdges d₁ d₂ := by
  ext; simp

private theorem stepEdges_D : stepEdges d₁ d₂ D = verticalEdges d₁ d₂ := by
  ext; simp

/-- The scaled counts in a cyclic window are the differences of the endpoint prefix counts. -/
private theorem scaled_window_counts (h e : Edge d₁ d₂) :
    d₂ * #(cyclicIcc h e ∩ horizontalEdges d₁ d₂) + d₂ * countBefore d₁ d₂ U h.val +
        d₁ * countBefore d₁ d₂ D (e.val + 1) =
      d₁ * #(cyclicIcc h e ∩ verticalEdges d₁ d₂) + d₁ * countBefore d₁ d₂ D h.val +
        d₂ * countBefore d₁ d₂ U (e.val + 1) := by
  have hH := card_cyclicIcc_inter U h e
  have hV := card_cyclicIcc_inter D h e
  simp only [stepEdges_U, stepEdges_D, card_horizontalEdges, card_verticalEdges] at hH hV
  have e₁ := congrArg (d₂ * ·) hH
  have e₂ := congrArg (d₁ * ·) hV
  simp only [mul_add, mul_ite, mul_zero] at e₁ e₂
  split_ifs at e₁ e₂ <;> nlinarith

/-- **Windows ending at a vertical edge.** From a horizontal edge `h` to a vertical edge `e`,
`d₂ #H < d₂ + d₁ #V`. -/
theorem mul_card_horizontal_lt (h : Edge d₁ d₂) (e : Edge d₁ d₂) (he : e ∈ verticalEdges d₁ d₂) :
    d₂ * #(cyclicIcc h e ∩ horizontalEdges d₁ d₂) <
      d₂ + d₁ * #(cyclicIcc h e ∩ verticalEdges d₁ d₂) := by
  have hd : 0 < d₁ + d₂ := h.pos
  have hcounts := scaled_window_counts h e
  have hsU := countBefore_succ U e
  have hsD := countBefore_succ D e
  rw [mem_verticalEdges] at he
  simp only [he, reduceCtorEq, ↓reduceIte, add_zero] at hsU hsD
  have b₁ := countBefore_bounds hd h.val
  have b₂ := countBefore_bounds hd e.val
  have e₃ := congrArg (d₂ * ·) hsU
  have e₄ := congrArg (d₁ * ·) hsD
  simp only [mul_add, mul_one] at e₃ e₄
  linarith

/-- **Windows starting at a horizontal edge.** From a horizontal edge `h` to a vertical edge
`v`, `d₁ #V < d₁ + d₂ #H`. -/
theorem mul_card_vertical_lt (h : Edge d₁ d₂) (hh : h ∈ horizontalEdges d₁ d₂) (v : Edge d₁ d₂) :
    d₁ * #(cyclicIcc h v ∩ verticalEdges d₁ d₂) <
      d₁ + d₂ * #(cyclicIcc h v ∩ horizontalEdges d₁ d₂) := by
  have hd : 0 < d₁ + d₂ := h.pos
  have hcounts := scaled_window_counts h v
  have hsU := countBefore_succ U h
  have hsD := countBefore_succ D h
  rw [mem_horizontalEdges] at hh
  simp only [hh, reduceCtorEq, ↓reduceIte, add_zero] at hsU hsD
  have b₁ := countBefore_bounds hd (h.val + 1)
  have b₂ := countBefore_bounds hd (v.val + 1)
  have e₃ := congrArg (d₂ * ·) hsU
  have e₄ := congrArg (d₁ * ·) hsD
  simp only [mul_add, mul_one] at e₃ e₄
  linarith

end Mei.MaximalDyckPath
