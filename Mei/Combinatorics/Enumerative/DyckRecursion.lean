/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Combinatorics.Enumerative.DyckShadow
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# The recursion (R) for the shadowed grading sums

For a grading `γ` of the maximal Dyck path of `(d₁, d₂)`, compatibility only depends on the
vertical grades inside the total horizontal shadow (`compatible_congr_of_horizontal`): a pair
`h, v` with `v` in the local shadow of `h` only looks at edges between `h` and `v`, and those
vertical edges are all shadowed. Dually it only depends on the horizontal grades inside the
total vertical shadow (`compatible_congr_of_vertical`).

So the compatible gradings with totals `(p, q)` are obtained from those counted by
`C₊(p - s, q)` by grading freely the `d₂ - min(d₂, q)` vertical edges outside the total
horizontal shadow, which has `min(d₂, q)` edges. With `P₁(0) = 1` this gives

  `∑_{s ≤ p} [x^s] P₁^{d₂ - min(d₂, q)} C₊(p - s, q) = compatibleSum p q`

(`sum_coeff_mul_cplus`), the weight sum of all compatible gradings with totals `(p, q)`, and
dually for `C₋` (`sum_coeff_mul_cminus`). Together they give the recursion (R) of the rank-two
polynomial formula (`sum_coeff_mul_cplus_eq_sum_coeff_mul_cminus`). For `q ≥ d₂` the power is
`P₁ ^ 0 = 1`, matching `π_{d₂ - q, s}(P₁) = [s = 0]` for negative exponents.
-/

public section

open DyckStep Finset Polynomial Mei.CyclicMatching

namespace Mei.MaximalDyckPath

variable {d₁ d₂ : ℕ}

section Truncation

/-- Vertical balance only depends on the horizontal grades. -/
theorem verticalBalanced_congr {γ γ' : Edge d₁ d₂ → ℕ}
    (hH : ∀ k ∈ horizontalEdges d₁ d₂, γ k = γ' k) (h e : Edge d₁ d₂) :
    VerticalBalanced γ h e ↔ VerticalBalanced γ' h e := by
  rw [VerticalBalanced, VerticalBalanced, sum_congr rfl fun k hk ↦ hH k (mem_inter.mp hk).2]

/-- Horizontal balance on `ev` only depends on the vertical grades on `ev`. -/
theorem horizontalBalanced_congr {γ γ' : Edge d₁ d₂ → ℕ} {e v : Edge d₁ d₂}
    (hV : ∀ k ∈ cyclicIcc e v ∩ verticalEdges d₁ d₂, γ k = γ' k) :
    HorizontalBalanced γ e v ↔ HorizontalBalanced γ' e v := by
  rw [HorizontalBalanced, HorizontalBalanced, sum_congr rfl hV]

/-- Horizontal balance only depends on the vertical grades. -/
theorem horizontalBalanced_congr' {γ γ' : Edge d₁ d₂ → ℕ}
    (hV : ∀ k ∈ verticalEdges d₁ d₂, γ k = γ' k) (e v : Edge d₁ d₂) :
    HorizontalBalanced γ e v ↔ HorizontalBalanced γ' e v :=
  horizontalBalanced_congr fun k hk ↦ hV k (mem_inter.mp hk).2

/-- Vertical balance on `he` only depends on the horizontal grades on `he`. -/
theorem verticalBalanced_congr' {γ γ' : Edge d₁ d₂ → ℕ} {h e : Edge d₁ d₂}
    (hH : ∀ k ∈ cyclicIcc h e ∩ horizontalEdges d₁ d₂, γ k = γ' k) :
    VerticalBalanced γ h e ↔ VerticalBalanced γ' h e := by
  rw [VerticalBalanced, VerticalBalanced, sum_congr rfl hH]

/-- The local horizontal shadows only depend on the horizontal grades. -/
theorem horizontalShadow_congr {γ γ' : Edge d₁ d₂ → ℕ}
    (hH : ∀ k ∈ horizontalEdges d₁ d₂, γ k = γ' k) (h : Edge d₁ d₂) :
    horizontalShadow γ h = horizontalShadow γ' h := by
  ext k
  simp only [mem_horizontalShadow, verticalBalanced_congr hH]

/-- The local vertical shadows only depend on the vertical grades. -/
theorem verticalShadow_congr {γ γ' : Edge d₁ d₂ → ℕ}
    (hV : ∀ k ∈ verticalEdges d₁ d₂, γ k = γ' k) (v : Edge d₁ d₂) :
    verticalShadow γ v = verticalShadow γ' v := by
  ext k
  simp only [mem_verticalShadow, horizontalBalanced_congr' hV]

theorem totalHorizontalShadow_congr {γ γ' : Edge d₁ d₂ → ℕ}
    (hH : ∀ k ∈ horizontalEdges d₁ d₂, γ k = γ' k) :
    totalHorizontalShadow γ = totalHorizontalShadow γ' := by
  ext k
  simp only [mem_totalHorizontalShadow, horizontalShadow_congr hH]

theorem totalVerticalShadow_congr {γ γ' : Edge d₁ d₂ → ℕ}
    (hV : ∀ k ∈ verticalEdges d₁ d₂, γ k = γ' k) :
    totalVerticalShadow γ = totalVerticalShadow γ' := by
  ext k
  simp only [mem_totalVerticalShadow, verticalShadow_congr hV]

/-- **Compatibility only sees the shadowed vertical grades.** Two gradings with the same
horizontal grades that agree on the total horizontal shadow are compatible together. -/
theorem compatible_congr_of_horizontal {γ γ' : Edge d₁ d₂ → ℕ}
    (hH : ∀ k ∈ horizontalEdges d₁ d₂, γ k = γ' k)
    (hV : ∀ k ∈ totalHorizontalShadow γ, γ k = γ' k) : Compatible γ ↔ Compatible γ' := by
  refine forall₂_congr fun h hh ↦ forall₂_congr fun v hv ↦ ?_
  simp only [verticalBalanced_congr hH]
  by_cases hA : ∃ e, (e - h).val < (v - h).val ∧ VerticalBalanced γ' h e
  · exact iff_of_true (Or.inl hA) (Or.inl hA)
  have hsh : v ∈ horizontalShadow γ h := (mem_horizontalShadow γ).mpr
    ⟨hv, fun e he hb ↦ hA ⟨e, he, (verticalBalanced_congr hH h e).mp hb⟩⟩
  refine or_congr_right (exists_congr fun e ↦ and_congr_right fun he ↦
    horizontalBalanced_congr fun k hk ↦ hV k ?_)
  have hev : e ∈ cyclicIcc h v := by
    rw [mem_cyclicIcc, ← val_sub_le_val_sub_iff]
    exact he.le
  have hkv := mem_cyclicIcc.mp (cyclicIcc_subset_of_mem hev (mem_inter.mp hk).1)
  rw [mem_horizontalShadow] at hsh
  rw [mem_totalHorizontalShadow]
  exact ⟨h, hh, (mem_horizontalShadow γ).mpr
    ⟨(mem_inter.mp hk).2, fun e' he' ↦ hsh.2 e' (lt_of_lt_of_le he' hkv)⟩⟩

/-- **Compatibility only sees the shadowed horizontal grades.** Two gradings with the same
vertical grades that agree on the total vertical shadow are compatible together. -/
theorem compatible_congr_of_vertical {γ γ' : Edge d₁ d₂ → ℕ}
    (hV : ∀ k ∈ verticalEdges d₁ d₂, γ k = γ' k)
    (hH : ∀ k ∈ totalVerticalShadow γ, γ k = γ' k) : Compatible γ ↔ Compatible γ' := by
  refine forall₂_congr fun h hh ↦ forall₂_congr fun v hv ↦ ?_
  simp only [horizontalBalanced_congr' hV]
  by_cases hB : ∃ e, (v - e).val < (v - h).val ∧ HorizontalBalanced γ' e v
  · exact iff_of_true (Or.inr hB) (Or.inr hB)
  have hsh : h ∈ verticalShadow γ v := (mem_verticalShadow γ).mpr
    ⟨hh, fun e he hb ↦ hB ⟨e, he, (horizontalBalanced_congr' hV e v).mp hb⟩⟩
  refine or_congr_left (exists_congr fun e ↦ and_congr_right fun he ↦
    verticalBalanced_congr' fun k hk ↦ hH k ?_)
  have hkv : (v - k).val ≤ (v - h).val := by
    rw [val_sub_le_val_sub_iff]
    exact (mem_cyclicIcc.mp (mem_inter.mp hk).1).trans he.le
  rw [mem_verticalShadow] at hsh
  rw [mem_totalVerticalShadow]
  exact ⟨v, hv, (mem_verticalShadow γ).mpr
    ⟨(mem_inter.mp hk).2, fun e' he' ↦ hsh.2 e' (lt_of_lt_of_le he' hkv)⟩⟩

end Truncation

section Recursion

variable {S : Type*} [CommSemiring S] (P₁ P₂ : S[X])

variable (d₁ d₂) in
/-- The weight sum of all compatible gradings with totals `(p, q)`. -/
def compatibleSum (p q : ℕ) : S :=
  ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Compatible γ ∧ verticalTotal γ = p ∧
    horizontalTotal γ = q, weight P₁ P₂ γ

theorem compatibleSum_def (p q : ℕ) :
    compatibleSum d₁ d₂ P₁ P₂ p q =
      ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Compatible γ ∧ verticalTotal γ = p ∧
        horizontalTotal γ = q, weight P₁ P₂ γ :=
  (rfl)

/-- The local factor of an edge in the generating function of gradings by `p`. -/
private noncomputable def factorV (k : Edge d₁ d₂) (j : ℕ) : S[X] :=
  if step k = D then C (P₁.coeff j) * X ^ j else C (P₂.coeff j)

/-- The local factor of an edge in the generating function of gradings by `q`. -/
private noncomputable def factorH (k : Edge d₁ d₂) (j : ℕ) : S[X] :=
  if step k = D then C (P₁.coeff j) else C (P₂.coeff j) * X ^ j

private theorem filter_step_eq_D :
    (univ.filter fun k : Edge d₁ d₂ ↦ step k = D) = verticalEdges d₁ d₂ := by
  ext
  simp

private theorem filter_step_ne_D :
    (univ.filter fun k : Edge d₁ d₂ ↦ ¬step k = D) = horizontalEdges d₁ d₂ := by
  ext k
  simp only [mem_filter, mem_univ, true_and, mem_horizontalEdges]
  cases step k <;> simp

private theorem prod_factorV (γ : Edge d₁ d₂ → ℕ) :
    ∏ k, factorV P₁ P₂ k (γ k) = C (weight P₁ P₂ γ) * X ^ verticalTotal γ := by
  simp only [factorV]
  rw [prod_ite, filter_step_eq_D, filter_step_ne_D, prod_mul_distrib, prod_pow_eq_pow_sum,
    weight_eq_prod, map_mul, map_prod, map_prod, verticalTotal_eq]
  ring

private theorem prod_factorH (γ : Edge d₁ d₂ → ℕ) :
    ∏ k, factorH P₁ P₂ k (γ k) = C (weight P₁ P₂ γ) * X ^ horizontalTotal γ := by
  simp only [factorH]
  rw [prod_ite, filter_step_eq_D, filter_step_ne_D, prod_mul_distrib, prod_pow_eq_pow_sum,
    weight_eq_prod, map_mul, map_prod, map_prod, horizontalTotal_eq]
  ring

/-- Grading the edges of `O` freely and the others as `γ'` multiplies the generating function
of `γ'` by one copy of the full local sum per edge of `O`. -/
private theorem sum_piFinset_factor (f : Edge d₁ d₂ → ℕ → S[X]) (O : Finset (Edge d₁ d₂))
    (t : ℕ) (Q : S[X]) (hQ : ∀ k ∈ O, ∑ j ∈ range (t + 1), f k j = Q)
    (γ' : Edge d₁ d₂ → ℕ) (h₀ : ∀ k ∈ O, f k (γ' k) = 1) :
    ∑ γ ∈ Fintype.piFinset (fun k ↦ if k ∈ O then range (t + 1) else {γ' k}), ∏ k, f k (γ k) =
      (∏ k, f k (γ' k)) * Q ^ #O := by
  rw [← prod_univ_sum]
  have h₁ : ∀ k, ∑ j ∈ (if k ∈ O then range (t + 1) else {γ' k}), f k j =
      if k ∈ O then Q * f k (γ' k) else f k (γ' k) := by
    intro k
    split_ifs with hk
    · rw [hQ k hk, h₀ k hk, mul_one]
    · rw [sum_singleton]
  rw [prod_congr rfl fun k _ ↦ h₁ k, prod_ite, prod_mul_distrib, ← prod_mul_prod_compl
    (univ.filter (· ∈ O)), compl_filter]
  rw [prod_congr rfl fun k hk ↦ h₀ k (mem_filter.mp hk).2, prod_const_one, one_mul,
    prod_const, filter_mem_eq_inter, univ_inter]
  ring

/-- Zero the vertical grades outside the total horizontal shadow. -/
private def truncV (γ : Edge d₁ d₂ → ℕ) : Edge d₁ d₂ → ℕ := fun k ↦
  if k ∈ verticalEdges d₁ d₂ \ totalHorizontalShadow γ then 0 else γ k

/-- Zero the horizontal grades outside the total vertical shadow. -/
private def truncH (γ : Edge d₁ d₂ → ℕ) : Edge d₁ d₂ → ℕ := fun k ↦
  if k ∈ horizontalEdges d₁ d₂ \ totalVerticalShadow γ then 0 else γ k

private theorem truncV_eq_of_notMem {γ : Edge d₁ d₂ → ℕ} {k : Edge d₁ d₂}
    (hk : k ∉ verticalEdges d₁ d₂ \ totalHorizontalShadow γ) : truncV γ k = γ k := by
  simp [truncV, hk]

private theorem truncH_eq_of_notMem {γ : Edge d₁ d₂ → ℕ} {k : Edge d₁ d₂}
    (hk : k ∉ horizontalEdges d₁ d₂ \ totalVerticalShadow γ) : truncH γ k = γ k := by
  simp [truncH, hk]

private theorem truncV_horizontal (γ : Edge d₁ d₂ → ℕ) :
    ∀ k ∈ horizontalEdges d₁ d₂, truncV γ k = γ k := fun _ hk ↦
  truncV_eq_of_notMem fun hmem ↦ notMem_verticalEdges_of_mem hk (mem_sdiff.mp hmem).1

private theorem truncH_vertical (γ : Edge d₁ d₂ → ℕ) :
    ∀ k ∈ verticalEdges d₁ d₂, truncH γ k = γ k := fun _ hk ↦
  truncH_eq_of_notMem fun hmem ↦ notMem_horizontalEdges_of_mem hk (mem_sdiff.mp hmem).1

private theorem totalHorizontalShadow_truncV (γ : Edge d₁ d₂ → ℕ) :
    totalHorizontalShadow (truncV γ) = totalHorizontalShadow γ :=
  totalHorizontalShadow_congr (truncV_horizontal γ)

private theorem totalVerticalShadow_truncH (γ : Edge d₁ d₂ → ℕ) :
    totalVerticalShadow (truncH γ) = totalVerticalShadow γ :=
  totalVerticalShadow_congr (truncH_vertical γ)

private theorem compatible_truncV (γ : Edge d₁ d₂ → ℕ) : Compatible (truncV γ) ↔ Compatible γ :=
  compatible_congr_of_horizontal (truncV_horizontal γ) fun k hk ↦ truncV_eq_of_notMem
    fun hmem ↦ (mem_sdiff.mp hmem).2 (by rwa [totalHorizontalShadow_truncV] at hk)

private theorem compatible_truncH (γ : Edge d₁ d₂ → ℕ) : Compatible (truncH γ) ↔ Compatible γ :=
  compatible_congr_of_vertical (truncH_vertical γ) fun k hk ↦ truncH_eq_of_notMem
    fun hmem ↦ (mem_sdiff.mp hmem).2 (by rwa [totalVerticalShadow_truncH] at hk)

private theorem horizontalTotal_truncV (γ : Edge d₁ d₂ → ℕ) :
    horizontalTotal (truncV γ) = horizontalTotal γ := by
  rw [horizontalTotal_eq, horizontalTotal_eq, sum_congr rfl (truncV_horizontal γ)]

private theorem verticalTotal_truncH (γ : Edge d₁ d₂ → ℕ) :
    verticalTotal (truncH γ) = verticalTotal γ := by
  rw [verticalTotal_eq, verticalTotal_eq, sum_congr rfl (truncH_vertical γ)]

private theorem truncV_le (γ : Edge d₁ d₂ → ℕ) (k : Edge d₁ d₂) : truncV γ k ≤ γ k := by
  unfold truncV
  split_ifs <;> omega

private theorem truncH_le (γ : Edge d₁ d₂ → ℕ) (k : Edge d₁ d₂) : truncH γ k ≤ γ k := by
  unfold truncH
  split_ifs <;> omega

private theorem verticalSupport_truncV (γ : Edge d₁ d₂ → ℕ) :
    verticalSupport (truncV γ) ⊆ totalHorizontalShadow (truncV γ) := by
  intro k hk
  rw [mem_verticalSupport] at hk
  rw [totalHorizontalShadow_truncV]
  by_contra hsh
  exact hk.2 (by simp [truncV, hk.1, hsh])

private theorem horizontalSupport_truncH (γ : Edge d₁ d₂ → ℕ) :
    horizontalSupport (truncH γ) ⊆ totalVerticalShadow (truncH γ) := by
  intro k hk
  rw [mem_horizontalSupport] at hk
  rw [totalVerticalShadow_truncH]
  by_contra hsh
  exact hk.2 (by simp [truncH, hk.1, hsh])

private theorem truncV_eq_self {γ : Edge d₁ d₂ → ℕ}
    (hs : verticalSupport γ ⊆ totalHorizontalShadow γ) : truncV γ = γ := by
  funext k
  unfold truncV
  split_ifs with hk
  · rw [mem_sdiff] at hk
    by_contra hγ
    exact hk.2 (hs ((mem_verticalSupport γ).mpr ⟨hk.1, Ne.symm hγ⟩))
  · rfl

private theorem truncH_eq_self {γ : Edge d₁ d₂ → ℕ}
    (hs : horizontalSupport γ ⊆ totalVerticalShadow γ) : truncH γ = γ := by
  funext k
  unfold truncH
  split_ifs with hk
  · rw [mem_sdiff] at hk
    by_contra hγ
    exact hk.2 (hs ((mem_horizontalSupport γ).mpr ⟨hk.1, Ne.symm hγ⟩))
  · rfl

/-- The fibre of the vertical truncation over a truncated grading `γ'`. -/
private theorem filter_truncV_eq {γ' : Edge d₁ d₂ → ℕ}
    (hγ' : γ' ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree) (hfix : truncV γ' = γ') :
    (gradings d₁ d₂ P₁.natDegree P₂.natDegree).filter (truncV · = γ') =
      Fintype.piFinset fun k ↦ if k ∈ verticalEdges d₁ d₂ \ totalHorizontalShadow γ' then
        range (P₁.natDegree + 1) else {γ' k} := by
  ext γ
  rw [mem_gradings] at hγ'
  simp only [mem_filter, mem_gradings, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hb, rfl⟩ k
    rw [totalHorizontalShadow_truncV]
    split_ifs with hk
    · have := hb k
      simp only [mem_verticalEdges.mp (mem_sdiff.mp hk).1, ↓reduceIte] at this
      exact mem_range.mpr (by omega)
    · exact mem_singleton.mpr (truncV_eq_of_notMem hk).symm
  · intro hT
    have hH : ∀ k ∈ horizontalEdges d₁ d₂, γ k = γ' k := fun k hk ↦ by
      have hk' : k ∉ verticalEdges d₁ d₂ \ totalHorizontalShadow γ' :=
        fun hmem ↦ notMem_verticalEdges_of_mem hk (mem_sdiff.mp hmem).1
      have := hT k
      simpa only [hk', ↓reduceIte, mem_singleton] using this
    have hsh : totalHorizontalShadow γ = totalHorizontalShadow γ' := totalHorizontalShadow_congr hH
    refine ⟨fun k ↦ ?_, funext fun k ↦ ?_⟩
    · have := hT k
      split_ifs at this with hk
      · simp only [mem_verticalEdges.mp (mem_sdiff.mp hk).1, ↓reduceIte]
        exact Nat.lt_succ_iff.mp (mem_range.mp this)
      · rw [mem_singleton.mp this]
        exact hγ' k
    · have := hT k
      unfold truncV
      rw [hsh]
      split_ifs at this ⊢ with hk
      · rw [← hfix]
        simp [truncV, hk]
      · exact mem_singleton.mp this

/-- The fibre of the horizontal truncation over a truncated grading `γ'`. -/
private theorem filter_truncH_eq {γ' : Edge d₁ d₂ → ℕ}
    (hγ' : γ' ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree) (hfix : truncH γ' = γ') :
    (gradings d₁ d₂ P₁.natDegree P₂.natDegree).filter (truncH · = γ') =
      Fintype.piFinset fun k ↦ if k ∈ horizontalEdges d₁ d₂ \ totalVerticalShadow γ' then
        range (P₂.natDegree + 1) else {γ' k} := by
  ext γ
  rw [mem_gradings] at hγ'
  simp only [mem_filter, mem_gradings, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hb, rfl⟩ k
    rw [totalVerticalShadow_truncH]
    split_ifs with hk
    · have := hb k
      simp only [mem_horizontalEdges.mp (mem_sdiff.mp hk).1, reduceCtorEq, ↓reduceIte] at this
      exact mem_range.mpr (by omega)
    · exact mem_singleton.mpr (truncH_eq_of_notMem hk).symm
  · intro hT
    have hV : ∀ k ∈ verticalEdges d₁ d₂, γ k = γ' k := fun k hk ↦ by
      have hk' : k ∉ horizontalEdges d₁ d₂ \ totalVerticalShadow γ' :=
        fun hmem ↦ notMem_horizontalEdges_of_mem hk (mem_sdiff.mp hmem).1
      have := hT k
      simpa only [hk', ↓reduceIte, mem_singleton] using this
    have hsh : totalVerticalShadow γ = totalVerticalShadow γ' := totalVerticalShadow_congr hV
    refine ⟨fun k ↦ ?_, funext fun k ↦ ?_⟩
    · have := hT k
      split_ifs at this with hk
      · simp only [mem_horizontalEdges.mp (mem_sdiff.mp hk).1, reduceCtorEq, ↓reduceIte]
        exact Nat.lt_succ_iff.mp (mem_range.mp this)
      · rw [mem_singleton.mp this]
        exact hγ' k
    · have := hT k
      unfold truncH
      rw [hsh]
      split_ifs at this ⊢ with hk
      · rw [← hfix]
        simp [truncH, hk]
      · exact mem_singleton.mp this

/-- The generating function of a fibre of the vertical truncation. -/
private theorem sum_fiber_truncV (hP₁ : P₁.coeff 0 = 1) {γ' : Edge d₁ d₂ → ℕ}
    (hγ' : γ' ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree) (hfix : truncV γ' = γ') :
    ∑ γ ∈ (gradings d₁ d₂ P₁.natDegree P₂.natDegree).filter (truncV · = γ'),
        C (weight P₁ P₂ γ) * X ^ verticalTotal γ =
      C (weight P₁ P₂ γ') * X ^ verticalTotal γ' * P₁ ^ (d₂ - min d₂ (horizontalTotal γ')) := by
  rw [filter_truncV_eq P₁ P₂ hγ' hfix]
  simp_rw [← prod_factorV P₁ P₂]
  rw [sum_piFinset_factor (factorV P₁ P₂) _ P₁.natDegree P₁ ?_ γ' ?_,
    card_sdiff_of_subset (totalHorizontalShadow_subset γ'), card_verticalEdges,
    card_totalHorizontalShadow]
  · intro k hk
    simp only [factorV, mem_verticalEdges.mp (mem_sdiff.mp hk).1, ↓reduceIte]
    exact (as_sum_range_C_mul_X_pow P₁).symm
  · intro k hk
    have h₀ : γ' k = 0 := by
      rw [← hfix]
      simp [truncV, hk]
    simp [factorV, mem_verticalEdges.mp (mem_sdiff.mp hk).1, h₀, hP₁]

/-- Summing over the fibres of the vertical truncation: the generating function by `p` of the
compatible gradings with `q` fixed is that of the gradings counted by `C₊`, times
`P₁ ^ (d₂ - min d₂ q)`. -/
private theorem sum_compatible_genV (hP₁ : P₁.coeff 0 = 1) (q : ℕ) :
    ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Compatible γ ∧ horizontalTotal γ = q,
        C (weight P₁ P₂ γ) * X ^ verticalTotal γ =
      (∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Compatible γ ∧
          horizontalTotal γ = q ∧ verticalSupport γ ⊆ totalHorizontalShadow γ,
          C (weight P₁ P₂ γ) * X ^ verticalTotal γ) * P₁ ^ (d₂ - min d₂ q) := by
  rw [← sum_fiberwise_of_maps_to (g := truncV) ?_, sum_mul]
  · refine sum_congr rfl fun γ' hγ' ↦ ?_
    obtain ⟨hγ'g, hc', hq', hs'⟩ := mem_filter.mp hγ'
    have hfix := truncV_eq_self hs'
    rw [← hq', ← sum_fiber_truncV P₁ P₂ hP₁ hγ'g hfix, filter_filter]
    congr 1
    refine filter_congr fun γ _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨⟨?_, ?_⟩, h⟩⟩
    · rw [← compatible_truncV, h]
      exact hc'
    · rw [← horizontalTotal_truncV, h]
  · intro γ hγ
    obtain ⟨hγg, hc, hq⟩ := mem_filter.mp hγ
    refine mem_filter.mpr ⟨?_, (compatible_truncV γ).mpr hc, by rw [horizontalTotal_truncV, hq],
      verticalSupport_truncV γ⟩
    rw [mem_gradings] at hγg ⊢
    exact fun k ↦ (truncV_le γ k).trans (hγg k)

/-- Extracting the coefficient of `X ^ p` from `X ^ a * Q`, summed over the splittings
`p = a + s`. -/
private theorem sum_range_ite_eq (p a : ℕ) (f : ℕ → S) (w : S) :
    ∑ s ∈ range (p + 1), (if a = p - s then f s * w else 0) =
      w * if a ≤ p then f (p - a) else 0 := by
  by_cases ha : a ≤ p
  · rw [sum_eq_single (p - a)]
    · split_ifs <;> first | exact mul_comm _ _ | (exfalso; omega)
    · intro s hs hne
      exact ite_eq_right_iff.mpr fun h ↦ absurd (by have := mem_range.mp hs; omega) hne
    · exact fun h ↦ absurd (mem_range.mpr (by omega)) h
  · rw [sum_eq_zero fun s hs ↦ ite_eq_right_iff.mpr fun h ↦ absurd h (by omega)]
    simp [ha]

/-- **The `C₊` side of (R).** When `P₁` has constant coefficient `1`,
`∑_{s ≤ p} [x^s] P₁^{d₂ - min(d₂, q)} C₊(p - s, q)` is the weight sum of all compatible
gradings with totals `(p, q)`. -/
theorem sum_coeff_mul_cplus (hP₁ : P₁.coeff 0 = 1) (p q : ℕ) :
    ∑ s ∈ range (p + 1), (P₁ ^ (d₂ - min d₂ q)).coeff s * cplus d₁ d₂ P₁ P₂ (p - s) q =
      compatibleSum d₁ d₂ P₁ P₂ p q := by
  have key := congrArg (coeff · p) (sum_compatible_genV (d₁ := d₁) (d₂ := d₂) P₁ P₂ hP₁ q)
  simp only [finsetSum_coeff, sum_mul, mul_assoc, coeff_C_mul, coeff_X_pow_mul'] at key
  rw [sum_filter, sum_filter] at key
  have h₁ (a : Edge d₁ d₂ → ℕ) :
      (if Compatible a ∧ verticalTotal a = p ∧ horizontalTotal a = q then weight P₁ P₂ a else 0) =
        if Compatible a ∧ horizontalTotal a = q then weight P₁ P₂ a * (X ^ verticalTotal a).coeff p
        else 0 := by
    rw [coeff_X_pow]
    by_cases hv : verticalTotal a = p
    · simp [hv]
    · have hv' : ¬p = verticalTotal a := fun h ↦ hv h.symm
      simp [hv, hv']
  have h₂ (y : Edge d₁ d₂ → ℕ) :
      ∑ x ∈ range (p + 1), (P₁ ^ (d₂ - min d₂ q)).coeff x *
          (if Compatible y ∧ verticalTotal y = p - x ∧ horizontalTotal y = q ∧
            verticalSupport y ⊆ totalHorizontalShadow y then weight P₁ P₂ y else 0) =
        if Compatible y ∧ horizontalTotal y = q ∧ verticalSupport y ⊆ totalHorizontalShadow y then
          weight P₁ P₂ y * if verticalTotal y ≤ p then
            (P₁ ^ (d₂ - min d₂ q)).coeff (p - verticalTotal y) else 0
        else 0 := by
    by_cases hA : Compatible y ∧ horizontalTotal y = q ∧
        verticalSupport y ⊆ totalHorizontalShadow y
    · rw [ite_eq_left_iff.mpr fun h ↦ absurd hA h, ← sum_range_ite_eq]
      refine sum_congr rfl fun x _ ↦ ?_
      by_cases hx : verticalTotal y = p - x <;> simp [hA, hx]
    · rw [ite_eq_right_iff.mpr fun h ↦ absurd h hA]
      exact sum_eq_zero fun x _ ↦ by
        rw [ite_eq_right_iff.mpr fun h ↦ absurd ⟨h.1, h.2.2⟩ hA, mul_zero]
  rw [compatibleSum_def, sum_filter]
  simp only [cplus_def, mul_sum, sum_filter]
  rw [sum_comm, sum_congr rfl fun y _ ↦ h₂ y, ← key]
  exact sum_congr rfl fun a _ ↦ (h₁ a).symm

/-- The generating function of a fibre of the horizontal truncation. -/
private theorem sum_fiber_truncH (hP₂ : P₂.coeff 0 = 1) {γ' : Edge d₁ d₂ → ℕ}
    (hγ' : γ' ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree) (hfix : truncH γ' = γ') :
    ∑ γ ∈ (gradings d₁ d₂ P₁.natDegree P₂.natDegree).filter (truncH · = γ'),
        C (weight P₁ P₂ γ) * X ^ horizontalTotal γ =
      C (weight P₁ P₂ γ') * X ^ horizontalTotal γ' * P₂ ^ (d₁ - min d₁ (verticalTotal γ')) := by
  rw [filter_truncH_eq P₁ P₂ hγ' hfix]
  simp_rw [← prod_factorH P₁ P₂]
  rw [sum_piFinset_factor (factorH P₁ P₂) _ P₂.natDegree P₂ ?_ γ' ?_,
    card_sdiff_of_subset (totalVerticalShadow_subset γ'), card_horizontalEdges,
    card_totalVerticalShadow]
  · intro k hk
    simp only [factorH, mem_horizontalEdges.mp (mem_sdiff.mp hk).1, reduceCtorEq, ↓reduceIte]
    exact (as_sum_range_C_mul_X_pow P₂).symm
  · intro k hk
    have h₀ : γ' k = 0 := by
      rw [← hfix]
      simp [truncH, hk]
    simp [factorH, mem_horizontalEdges.mp (mem_sdiff.mp hk).1, h₀, hP₂]

/-- Summing over the fibres of the horizontal truncation: the generating function by `q` of the
compatible gradings with `p` fixed is that of the gradings counted by `C₋`, times
`P₂ ^ (d₁ - min d₁ p)`. -/
private theorem sum_compatible_genH (hP₂ : P₂.coeff 0 = 1) (p : ℕ) :
    ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Compatible γ ∧ verticalTotal γ = p,
        C (weight P₁ P₂ γ) * X ^ horizontalTotal γ =
      (∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Compatible γ ∧
          verticalTotal γ = p ∧ horizontalSupport γ ⊆ totalVerticalShadow γ,
          C (weight P₁ P₂ γ) * X ^ horizontalTotal γ) * P₂ ^ (d₁ - min d₁ p) := by
  rw [← sum_fiberwise_of_maps_to (g := truncH) ?_, sum_mul]
  · refine sum_congr rfl fun γ' hγ' ↦ ?_
    obtain ⟨hγ'g, hc', hp', hs'⟩ := mem_filter.mp hγ'
    have hfix := truncH_eq_self hs'
    rw [← hp', ← sum_fiber_truncH P₁ P₂ hP₂ hγ'g hfix, filter_filter]
    congr 1
    refine filter_congr fun γ _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨⟨?_, ?_⟩, h⟩⟩
    · rw [← compatible_truncH, h]
      exact hc'
    · rw [← verticalTotal_truncH, h]
  · intro γ hγ
    obtain ⟨hγg, hc, hp⟩ := mem_filter.mp hγ
    refine mem_filter.mpr ⟨?_, (compatible_truncH γ).mpr hc, by rw [verticalTotal_truncH, hp],
      horizontalSupport_truncH γ⟩
    rw [mem_gradings] at hγg ⊢
    exact fun k ↦ (truncH_le γ k).trans (hγg k)

/-- **The `C₋` side of (R).** When `P₂` has constant coefficient `1`,
`∑_{s ≤ q} [y^s] P₂^{d₁ - min(d₁, p)} C₋(p, q - s)` is the weight sum of all compatible
gradings with totals `(p, q)`. -/
theorem sum_coeff_mul_cminus (hP₂ : P₂.coeff 0 = 1) (p q : ℕ) :
    ∑ s ∈ range (q + 1), (P₂ ^ (d₁ - min d₁ p)).coeff s * cminus d₁ d₂ P₁ P₂ p (q - s) =
      compatibleSum d₁ d₂ P₁ P₂ p q := by
  have key := congrArg (coeff · q) (sum_compatible_genH (d₁ := d₁) (d₂ := d₂) P₁ P₂ hP₂ p)
  simp only [finsetSum_coeff, sum_mul, mul_assoc, coeff_C_mul, coeff_X_pow_mul'] at key
  rw [sum_filter, sum_filter] at key
  have h₁ (a : Edge d₁ d₂ → ℕ) :
      (if Compatible a ∧ verticalTotal a = p ∧ horizontalTotal a = q then weight P₁ P₂ a else 0) =
        if Compatible a ∧ verticalTotal a = p then
          weight P₁ P₂ a * (X ^ horizontalTotal a).coeff q
        else 0 := by
    rw [coeff_X_pow]
    by_cases hv : horizontalTotal a = q
    · simp [hv]
    · have hv' : ¬q = horizontalTotal a := fun h ↦ hv h.symm
      simp [hv, hv']
  have h₂ (y : Edge d₁ d₂ → ℕ) :
      ∑ x ∈ range (q + 1), (P₂ ^ (d₁ - min d₁ p)).coeff x *
          (if Compatible y ∧ verticalTotal y = p ∧ horizontalTotal y = q - x ∧
            horizontalSupport y ⊆ totalVerticalShadow y then weight P₁ P₂ y else 0) =
        if Compatible y ∧ verticalTotal y = p ∧ horizontalSupport y ⊆ totalVerticalShadow y then
          weight P₁ P₂ y * if horizontalTotal y ≤ q then
            (P₂ ^ (d₁ - min d₁ p)).coeff (q - horizontalTotal y) else 0
        else 0 := by
    by_cases hA : Compatible y ∧ verticalTotal y = p ∧
        horizontalSupport y ⊆ totalVerticalShadow y
    · rw [ite_eq_left_iff.mpr fun h ↦ absurd hA h, ← sum_range_ite_eq]
      refine sum_congr rfl fun x _ ↦ ?_
      by_cases hx : horizontalTotal y = q - x <;> simp [hA, hx]
    · rw [ite_eq_right_iff.mpr fun h ↦ absurd h hA]
      exact sum_eq_zero fun x _ ↦ by
        rw [ite_eq_right_iff.mpr fun h ↦ absurd ⟨h.1, h.2.1, h.2.2.2⟩ hA, mul_zero]
  rw [compatibleSum_def, sum_filter]
  simp only [cminus_def, mul_sum, sum_filter]
  rw [sum_comm, sum_congr rfl fun y _ ↦ h₂ y, ← key]
  exact sum_congr rfl fun a _ ↦ (h₁ a).symm

/-- **The recursion (R).** When `P₁` and `P₂` have constant coefficient `1`,
`∑_{s ≤ p} [x^s] P₁^{d₂ - min(d₂, q)} C₊(p - s, q)` equals
`∑_{s ≤ q} [y^s] P₂^{d₁ - min(d₁, p)} C₋(p, q - s)`: both are the weight sum of the compatible
gradings with totals `(p, q)`. -/
theorem sum_coeff_mul_cplus_eq_sum_coeff_mul_cminus (hP₁ : P₁.coeff 0 = 1)
    (hP₂ : P₂.coeff 0 = 1) (p q : ℕ) :
    ∑ s ∈ range (p + 1), (P₁ ^ (d₂ - min d₂ q)).coeff s * cplus d₁ d₂ P₁ P₂ (p - s) q =
      ∑ s ∈ range (q + 1), (P₂ ^ (d₁ - min d₁ p)).coeff s * cminus d₁ d₂ P₁ P₂ p (q - s) := by
  rw [sum_coeff_mul_cplus P₁ P₂ hP₁, sum_coeff_mul_cminus P₁ P₂ hP₂]

end Recursion

end Mei.MaximalDyckPath
