/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Combinatorics.Enumerative.DyckShadow

/-!
# The vanishing conditions (V) for shadowed compatible grading sums

A grading of the maximal Dyck path of `(d₁, d₂)` is compatible exactly when no horizontal edge
`h` and vertical edge `v` lie in each other's local shadows. We prove the vanishing conditions
(V) of the rank-two polynomial formula: off `(0, 0)`,

* `cplus_eq_zero`: `C₊(p, q) = 0` when `d₁ q ≤ d₂ p`;
* `cminus_eq_zero`: `C₋(p, q) = 0` when `d₂ p ≤ d₁ q`.

Outside the rectangle `p < d₁`, `q < d₂` this follows from the double cycle lemmas of
`Mei.CyclicMatching`, which produce a pair of edges in each other's shadows:

* `not_compatible_of_le`: `p ≥ d₁` and `q ≥ d₂`;
* `not_compatible_of_verticalSupport_subset`: `p ≥ d₁`, and the vertical support lies in the
  total horizontal shadow; this gives `cplus_eq_zero_of_le`, `C₊(p, q) = 0` for `p ≥ d₁`;
* `not_compatible_of_horizontalSupport_subset`: the dual, giving `cminus_eq_zero_of_le`.

Inside the rectangle we use the shape of the path. Every prefix with `x` horizontal and `y`
vertical steps satisfies `d₁ y ≤ d₂ x < d₁ y + d₁ + d₂`
(`Mei.count_take_maximalDyckPath`), so a subpath from a horizontal to a vertical edge has
`d₂ #H < d₂ + d₁ #V` (`mul_card_horizontal_lt`) and `d₁ #V < d₁ + d₂ #H`
(`mul_card_vertical_lt`). The slope comparison `Mei.CyclicMatching.mul_sum_lt_of_forall_matched`
then gives `d₂ p < d₁ q` for every grading counted by `C₊(p, q)` with `q < d₂`, and dually.
-/

public section

open DyckStep Finset Mei.CyclicMatching Polynomial

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
        List.getElem?_eq_getElem (by rw [length_maximalDyckPath]; exact ha), Option.toList_some,
        List.count_append, List.count_singleton, step_eq_getElem]
      simp only [beq_iff_eq]
    · have hfull : ∀ b, d₁ + d₂ ≤ b → countBefore d₁ d₂ s b = #(stepEdges d₁ d₂ s) := by
        intro b hb
        rw [countBefore, filter_true_of_mem fun k _ ↦ by omega]
      rw [hfull (a + 1) (by omega), ← hfull a (by omega), ih,
        List.take_of_length_le (by rw [length_maximalDyckPath]; omega),
        List.take_of_length_le (by rw [length_maximalDyckPath]; omega)]

/-- The lattice distance `d₂ x - d₁ y` of a vertex below the diagonal is in `[0, d₁ + d₂)`. -/
private theorem countBefore_bounds (hd : 0 < d₁ + d₂) (a : ℕ) :
    d₁ * countBefore d₁ d₂ D a ≤ d₂ * countBefore d₁ d₂ U a ∧
      d₂ * countBefore d₁ d₂ U a < d₁ * countBefore d₁ d₂ D a + (d₁ + d₂) := by
  rw [countBefore_eq, countBefore_eq]
  exact count_take_maximalDyckPath hd a

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
      simp only [mem_union, mem_inter, mem_filter, mem_univ, true_and, mem_cyclicIcc_iff,
        Fin.le_def, Fin.lt_def]
      by_cases hs : step k = s <;> simp [hs]
      omega
    · congr 1
      ext k
      simp only [mem_inter, mem_filter, mem_univ, true_and, mem_cyclicIcc_iff, Fin.le_def,
        Fin.lt_def]
      by_cases hs : step k = s <;> simp [hs]
      omega
  · rw [Fin.lt_def, not_lt] at heh
    have hinter : (cyclicIcc h e ∩ stepEdges d₁ d₂ s) ∩
        (stepEdges d₁ d₂ s).filter (fun k ↦ k.val < h.val) = ∅ := by
      ext k
      simp only [mem_inter, mem_filter, mem_univ, true_and, mem_cyclicIcc_iff, Fin.le_def,
        Fin.lt_def, notMem_empty, iff_false]
      by_cases hs : step k = s <;> simp [hs]
      omega
    rw [hinter, card_empty, add_zero, add_zero]
    congr 1
    ext k
    simp only [mem_union, mem_inter, mem_filter, mem_univ, true_and, mem_cyclicIcc_iff,
      Fin.le_def, Fin.lt_def]
    by_cases hs : step k = s <;> simp [hs]
    omega

/-- **Windows ending at a vertical edge.** From a horizontal edge `h` to a vertical edge `e`,
`d₂ #H < d₂ + d₁ #V`. -/
theorem mul_card_horizontal_lt (h : Edge d₁ d₂) (e : Edge d₁ d₂) (he : e ∈ verticalEdges d₁ d₂) :
    d₂ * #(cyclicIcc h e ∩ horizontalEdges d₁ d₂) <
      d₂ + d₁ * #(cyclicIcc h e ∩ verticalEdges d₁ d₂) := by
  have hd : 0 < d₁ + d₂ := h.pos
  have hH := card_cyclicIcc_inter U h e
  have hV := card_cyclicIcc_inter D h e
  have hsU := countBefore_succ U e
  have hsD := countBefore_succ D e
  rw [mem_verticalEdges] at he
  simp only [he, reduceCtorEq, ↓reduceIte, add_zero] at hsU hsD
  have b₁ := countBefore_bounds hd h.val
  have b₂ := countBefore_bounds hd e.val
  rw [show stepEdges d₁ d₂ U = horizontalEdges d₁ d₂ by ext; simp] at hH
  rw [show stepEdges d₁ d₂ D = verticalEdges d₁ d₂ by ext; simp] at hV
  rw [card_horizontalEdges] at hH
  rw [card_verticalEdges] at hV
  have e₁ := congrArg (d₂ * ·) hH
  have e₂ := congrArg (d₁ * ·) hV
  have e₃ := congrArg (d₂ * ·) hsU
  have e₄ := congrArg (d₁ * ·) hsD
  simp only [mul_add, mul_ite, mul_zero, mul_one] at e₁ e₂ e₃ e₄
  split_ifs at e₁ e₂ <;> linarith

/-- **Windows starting at a horizontal edge.** From a horizontal edge `h` to a vertical edge
`v`, `d₁ #V < d₁ + d₂ #H`. -/
theorem mul_card_vertical_lt (h : Edge d₁ d₂) (hh : h ∈ horizontalEdges d₁ d₂) (v : Edge d₁ d₂) :
    d₁ * #(cyclicIcc h v ∩ verticalEdges d₁ d₂) <
      d₁ + d₂ * #(cyclicIcc h v ∩ horizontalEdges d₁ d₂) := by
  have hd : 0 < d₁ + d₂ := h.pos
  have hH := card_cyclicIcc_inter U h v
  have hV := card_cyclicIcc_inter D h v
  have hsU := countBefore_succ U h
  have hsD := countBefore_succ D h
  rw [mem_horizontalEdges] at hh
  simp only [hh, reduceCtorEq, ↓reduceIte, add_zero] at hsU hsD
  have b₁ := countBefore_bounds hd (h.val + 1)
  have b₂ := countBefore_bounds hd (v.val + 1)
  rw [show stepEdges d₁ d₂ U = horizontalEdges d₁ d₂ by ext; simp] at hH
  rw [show stepEdges d₁ d₂ D = verticalEdges d₁ d₂ by ext; simp] at hV
  rw [card_horizontalEdges] at hH
  rw [card_verticalEdges] at hV
  have e₁ := congrArg (d₂ * ·) hH
  have e₂ := congrArg (d₁ * ·) hV
  have e₃ := congrArg (d₂ * ·) hsU
  have e₄ := congrArg (d₁ * ·) hsD
  simp only [mul_add, mul_ite, mul_zero, mul_one] at e₁ e₂ e₃ e₄
  split_ifs at e₁ e₂ <;> linarith

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

/-- In a compatible grading, a vertical edge `v` in the local shadow of a horizontal edge `h`
is separated from it by a horizontally balanced final subpath. -/
private theorem exists_balanced_of_compatible {γ : Edge d₁ d₂ → ℕ} (hc : Compatible γ)
    {h : Edge d₁ d₂} (hh : h ∉ verticalEdges d₁ d₂) {v : Edge d₁ d₂} (hv : v ∈ verticalEdges d₁ d₂)
    (hfwd : ∀ e, (e - h).val < (v - h).val →
      ∑ k ∈ cyclicIcc h e, CyclicMatching.weight (verticalEdges d₁ d₂) γ k ≠ 0) :
    ∃ e, (v - e).val < (v - h).val ∧
      ∑ k ∈ cyclicIcc e v, CyclicMatching.weight (verticalEdges d₁ d₂)ᶜ γ k = 0 := by
  have hhH : h ∈ horizontalEdges d₁ d₂ := by rw [← compl_verticalEdges, mem_compl]; exact hh
  have hsh : v ∈ horizontalShadow γ h := (mem_horizontalShadow γ).mpr
    ⟨hv, fun e he hbal ↦ hfwd e he ((verticalBalanced_iff γ h e).mp hbal)⟩
  have hnot : h ∉ verticalShadow γ v := fun hm ↦
    (compatible_iff_forall_not_mem_shadow γ).mp hc h hhH v hv ⟨hsh, hm⟩
  rw [mem_verticalShadow] at hnot
  push Not at hnot
  obtain ⟨e, he, hbal⟩ := hnot hhH
  exact ⟨e, he, by rw [compl_verticalEdges, ← horizontalBalanced_iff_weight]; exact hbal⟩

/-- In a compatible grading, a horizontal edge `h` in the local shadow of a vertical edge `v` is
separated from it by a vertically balanced initial subpath. -/
private theorem exists_balanced_of_compatible' {γ : Edge d₁ d₂ → ℕ} (hc : Compatible γ)
    {h : Edge d₁ d₂} (hh : h ∉ verticalEdges d₁ d₂) {v : Edge d₁ d₂} (hv : v ∈ verticalEdges d₁ d₂)
    (hbwd : ∀ e, (v - e).val < (v - h).val →
      ∑ k ∈ cyclicIcc e v, CyclicMatching.weight (verticalEdges d₁ d₂)ᶜ γ k ≠ 0) :
    ∃ e, (e - h).val < (v - h).val ∧
      ∑ k ∈ cyclicIcc h e, CyclicMatching.weight (verticalEdges d₁ d₂) γ k = 0 := by
  have hhH : h ∈ horizontalEdges d₁ d₂ := by rw [← compl_verticalEdges, mem_compl]; exact hh
  have hsh : h ∈ verticalShadow γ v := (mem_verticalShadow γ).mpr
    ⟨hhH, fun e he hbal ↦ hbwd e he (by
      rw [compl_verticalEdges, ← horizontalBalanced_iff_weight]; exact hbal)⟩
  have hnot : v ∉ horizontalShadow γ h := fun hm ↦
    (compatible_iff_forall_not_mem_shadow γ).mp hc h hhH v hv ⟨hm, hsh⟩
  rw [mem_horizontalShadow] at hnot
  push Not at hnot
  obtain ⟨e, he, hbal⟩ := hnot hv
  exact ⟨e, he, (verticalBalanced_iff γ h e).mp hbal⟩

/-- **(V) for `C₊`.** Off `(0, 0)`, `C₊(p, q) = 0` when `d₁ q ≤ d₂ p`. -/
theorem cplus_eq_zero {p q : ℕ} (h0 : (p, q) ≠ (0, 0)) (hpq : d₁ * q ≤ d₂ * p) :
    cplus d₁ d₂ P₁ P₂ p q = 0 := by
  rcases le_or_gt d₁ p with hp | hp
  · exact cplus_eq_zero_of_le P₁ P₂ hp h0
  rw [cplus_def]
  refine sum_eq_zero fun γ hγ ↦ absurd hγ ?_
  rw [mem_filter, not_and]
  rintro - ⟨hc, rfl, rfl, hs⟩
  have hd : 0 < d₁ + d₂ := by omega
  have : NeZero (d₁ + d₂) := ⟨hd.ne'⟩
  have hq : horizontalTotal γ < d₂ := by
    by_contra hq
    push Not at hq
    have h₁ : d₁ * d₂ ≤ d₂ * verticalTotal γ := (Nat.mul_le_mul_left d₁ hq).trans hpq
    have hd₂ : d₂ = 0 := Nat.eq_zero_of_le_zero (by nlinarith)
    subst hd₂
    have hV : verticalEdges d₁ 0 = ∅ := by rw [← card_eq_zero, card_verticalEdges]
    have hp0 : verticalTotal γ = 0 := by rw [verticalTotal_eq, hV, sum_empty]
    rw [hp0, mul_zero, Nat.le_zero, Nat.mul_eq_zero] at hpq
    exact h0 (by rw [hp0, hpq.resolve_left (by omega)])
  -- With no horizontal grade, the total horizontal shadow and hence `p` vanish.
  have hq0 : horizontalTotal γ ≠ 0 := by
    intro hq0
    have hempty : totalHorizontalShadow γ = ∅ := by
      rw [← card_eq_zero, card_totalHorizontalShadow, hq0, _root_.min_zero]
    have hp0 : verticalTotal γ = 0 := by
      rw [verticalTotal_eq]
      refine sum_eq_zero fun v hv ↦ by_contra fun hγ ↦ ?_
      have := hs ((mem_verticalSupport γ).mpr ⟨hv, hγ⟩)
      rw [hempty] at this
      exact notMem_empty v this
    exact h0 (by rw [hp0, hq0])
  have hlt := mul_sum_lt_of_forall_matched (verticalEdges d₁ d₂) γ γ d₂ d₁
    (fun h hh e he ↦ by
      rw [compl_verticalEdges]
      exact mul_card_horizontal_lt h e he)
    (fun h hh v hv hfwd ↦ exists_balanced_of_compatible hc hh hv hfwd)
    (fun v hv hγ ↦ by
      have := hs ((mem_verticalSupport γ).mpr ⟨hv, hγ⟩)
      rw [totalHorizontalShadow_eq, mem_filter] at this
      exact this.2)
    (by rw [compl_verticalEdges, ← horizontalTotal_eq, card_verticalEdges]; exact hq)
    (by rw [compl_verticalEdges, ← horizontalTotal_eq]; exact hq0)
  rw [← verticalTotal_eq, compl_verticalEdges, ← horizontalTotal_eq] at hlt
  omega

/-- **(V) for `C₋`.** Off `(0, 0)`, `C₋(p, q) = 0` when `d₂ p ≤ d₁ q`. -/
theorem cminus_eq_zero {p q : ℕ} (h0 : (p, q) ≠ (0, 0)) (hpq : d₂ * p ≤ d₁ * q) :
    cminus d₁ d₂ P₁ P₂ p q = 0 := by
  rcases le_or_gt d₂ q with hq | hq
  · exact cminus_eq_zero_of_le P₁ P₂ hq h0
  rw [cminus_def]
  refine sum_eq_zero fun γ hγ ↦ absurd hγ ?_
  rw [mem_filter, not_and]
  rintro - ⟨hc, rfl, rfl, hs⟩
  have hd : 0 < d₁ + d₂ := by omega
  have : NeZero (d₁ + d₂) := ⟨hd.ne'⟩
  have hp : verticalTotal γ < d₁ := by
    by_contra hp
    push Not at hp
    have h₁ : d₂ * d₁ ≤ d₁ * horizontalTotal γ := (Nat.mul_le_mul_left d₂ hp).trans hpq
    have hd₁ : d₁ = 0 := Nat.eq_zero_of_le_zero (by nlinarith)
    subst hd₁
    have hH : horizontalEdges 0 d₂ = ∅ := by rw [← card_eq_zero, card_horizontalEdges]
    have hq0 : horizontalTotal γ = 0 := by rw [horizontalTotal_eq, hH, sum_empty]
    rw [hq0, mul_zero, Nat.le_zero, Nat.mul_eq_zero] at hpq
    exact h0 (by rw [hq0, hpq.resolve_left (by omega)])
  -- With no vertical grade, the total vertical shadow and hence `q` vanish.
  have hp0 : verticalTotal γ ≠ 0 := by
    intro hp0
    have hempty : totalVerticalShadow γ = ∅ := by
      rw [← card_eq_zero, card_totalVerticalShadow, hp0, _root_.min_zero]
    have hq0 : horizontalTotal γ = 0 := by
      rw [horizontalTotal_eq]
      refine sum_eq_zero fun h hh ↦ by_contra fun hγ ↦ ?_
      have := hs ((mem_horizontalSupport γ).mpr ⟨hh, hγ⟩)
      rw [hempty] at this
      exact notMem_empty h this
    exact h0 (by rw [hp0, hq0])
  have hlt := mul_sum_lt_of_forall_matched_rev (verticalEdges d₁ d₂) γ γ d₁ d₂
    (fun h hh v hv ↦ by
      rw [compl_verticalEdges]
      exact mul_card_vertical_lt h (by rw [← compl_verticalEdges, mem_compl]; exact hh) v)
    (fun h hh v hv hbwd ↦ exists_balanced_of_compatible' hc hh hv hbwd)
    (fun h hh hγ ↦ by
      have hhH : h ∈ horizontalEdges d₁ d₂ := by
        rw [← compl_verticalEdges, mem_compl]; exact hh
      obtain ⟨v, hv, hsh⟩ := (mem_totalVerticalShadow γ).mp
        (hs ((mem_horizontalSupport γ).mpr ⟨hhH, hγ⟩))
      refine ⟨v, hv, fun e he hsum ↦ ((mem_verticalShadow γ).mp hsh).2 e he ?_⟩
      rw [horizontalBalanced_iff_weight, ← compl_verticalEdges]
      exact hsum)
    (by rw [← verticalTotal_eq, compl_verticalEdges, card_horizontalEdges]; exact hp)
    (by rw [← verticalTotal_eq]; exact hp0)
  rw [← verticalTotal_eq, compl_verticalEdges, ← horizontalTotal_eq] at hlt
  omega

end Mei.MaximalDyckPath
