/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Combinatorics.Enumerative.Dyck.Shadow
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mei.Algebra.BigOperators.Ring.Finset
public import Mei.Algebra.Polynomial.Coeff

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

## References

The two coefficient identities and the resulting recursion formalize Lemma 5.27 of
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*.
-/

public section

open DyckStep Finset Polynomial Mei.CyclicMatching

namespace Mei.MaximalDyckPath

variable {d₁ d₂ : ℕ}



section Recursion

variable {S : Type*} [CommSemiring S] (P₁ P₂ : S[X])

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
    weight_def, map_mul, map_prod, map_prod, verticalTotal_eq]
  ring

private theorem prod_factorH (γ : Edge d₁ d₂ → ℕ) :
    ∏ k, factorH P₁ P₂ k (γ k) = C (weight P₁ P₂ γ) * X ^ horizontalTotal γ := by
  simp only [factorH]
  rw [prod_ite, filter_step_eq_D, filter_step_ne_D, prod_mul_distrib, prod_pow_eq_pow_sum,
    weight_def, map_mul, map_prod, map_prod, horizontalTotal_eq]
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
  rw [sum_piFinset_factor (factorV P₁ P₂) _ (range (P₁.natDegree + 1)) P₁ ?_ γ' ?_,
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

/-- **The `C₊` side of (R).** When `P₁` has constant coefficient `1`,
`∑_{s ≤ p} [x^s] P₁^{d₂ - min(d₂, q)} C₊(p - s, q)` is the weight sum of all compatible
gradings with totals `(p, q)`. -/
theorem sum_coeff_mul_cplus (hP₁ : P₁.coeff 0 = 1) (p q : ℕ) :
    ∑ s ∈ range (p + 1), (P₁ ^ (d₂ - min d₂ q)).coeff s * cplus d₁ d₂ P₁ P₂ (p - s) q =
      compatibleSum d₁ d₂ P₁ P₂ p q := by
  have key := congrArg (coeff · p) (sum_compatible_genV (d₁ := d₁) (d₂ := d₂) P₁ P₂ hP₁ q)
  conv_rhs at key => rw [mul_comm]
  simp only [coeff_sum_C_mul_X_pow, coeff_mul_sum_C_mul_X_pow] at key
  simpa only [cplus_def, compatibleSum_def, and_assoc, and_left_comm, and_comm] using key.symm

/-- The generating function of a fibre of the horizontal truncation. -/
private theorem sum_fiber_truncH (hP₂ : P₂.coeff 0 = 1) {γ' : Edge d₁ d₂ → ℕ}
    (hγ' : γ' ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree) (hfix : truncH γ' = γ') :
    ∑ γ ∈ (gradings d₁ d₂ P₁.natDegree P₂.natDegree).filter (truncH · = γ'),
        C (weight P₁ P₂ γ) * X ^ horizontalTotal γ =
      C (weight P₁ P₂ γ') * X ^ horizontalTotal γ' * P₂ ^ (d₁ - min d₁ (verticalTotal γ')) := by
  rw [filter_truncH_eq P₁ P₂ hγ' hfix]
  simp_rw [← prod_factorH P₁ P₂]
  rw [sum_piFinset_factor (factorH P₁ P₂) _ (range (P₂.natDegree + 1)) P₂ ?_ γ' ?_,
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
  conv_rhs at key => rw [mul_comm]
  simp only [coeff_sum_C_mul_X_pow, coeff_mul_sum_C_mul_X_pow] at key
  simpa only [cminus_def, compatibleSum_def, and_assoc, and_left_comm, and_comm] using key.symm

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
