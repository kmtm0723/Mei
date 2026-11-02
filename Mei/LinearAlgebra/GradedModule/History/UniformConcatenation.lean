/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Uniform
public import Mei.LinearAlgebra.GradedModule.History.Concatenation

/-!
# Concatenating uniform finite history supports

A finite uniform support for the right block and a finite uniform support for the
left block on each whole intermediate linear map give a uniform finite support
for the concatenation. The sets are independent of incoming inputs, with no
finite-generation hypothesis. Zero maps and cancellations are retained.

Selected sums over the joined set are exactly iterated sums over the two blocks.
This is the linear-map counterpart of the input-dependent support equivalence in
`History/Concatenation.lean`; the right block acts first.
-/

public noncomputable section

namespace Mei

variable {ι : Type*} [DecidableEq ι] {n m : ℕ}

/-- Join finite degree-history sets, retaining the right history as part of each
concatenated label. Left supports may depend on that complete right history. -/
def appendHistorySupport (S : Finset (Fin m → ι))
    (F : (Fin m → ι) → Finset (Fin n → ι)) : Finset (Fin (n + m) → ι) :=
  S.biUnion fun q => (F q).image fun p => Fin.append p q

/-- A joined label records exactly one right history and one left history. -/
@[simp]
theorem mem_appendHistorySupport (S : Finset (Fin m → ι))
    (F : (Fin m → ι) → Finset (Fin n → ι)) (r : Fin (n + m) → ι) :
    r ∈ appendHistorySupport S F ↔
      (fun j => r (Fin.natAdd n j)) ∈ S ∧
        (fun j => r (Fin.castAdd m j)) ∈ F (fun j => r (Fin.natAdd n j)) := by
  simp only [appendHistorySupport, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, p, hp, rfl⟩
    simpa only [Fin.append_right, Fin.append_left] using And.intro hq hp
  · rintro ⟨hq, hp⟩
    exact ⟨_, hq, _, hp, Fin.append_castAdd_natAdd⟩

variable {R M E : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid E] [Module R E] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
  (T : Fin n → Module.End R M) (U : Fin m → Module.End R M) (a : E →ₗ[R] M)

/-- Uniform supports compose when each left support controls the entire
intermediate input map. The resulting support is valid for every input at once. -/
theorem homogeneousHistory_comp_eq_zero_of_notMem_appendHistorySupport
    (S : Finset (Fin m → ι)) (F : (Fin m → ι) → Finset (Fin n → ι))
    (hS : ∀ q ∉ S, (homogeneousHistory ℳ U q).comp a = 0)
    (hF : ∀ q ∈ S, ∀ p ∉ F q,
      (homogeneousHistory ℳ T p).comp ((homogeneousHistory ℳ U q).comp a) = 0)
    (r : Fin (n + m) → ι) (hr : r ∉ appendHistorySupport S F) :
    (homogeneousHistory ℳ (Fin.append T U) r).comp a = 0 := by
  apply LinearMap.ext
  intro x
  by_contra hx
  let p := fun j => r (Fin.castAdd m j)
  let q := fun j => r (Fin.natAdd n j)
  have he : Fin.append p q = r := Fin.append_castAdd_natAdd
  have hne : homogeneousHistory ℳ (Fin.append T U) (Fin.append p q) (a x) ≠ 0 := by
    simpa only [he, LinearMap.comp_apply, LinearMap.zero_apply] using hx
  have hq : q ∈ S := by
    by_contra hq
    have hz := LinearMap.congr_fun (hS q hq) x
    exact (homogeneousHistory_right_ne_zero ℳ T U p q hne)
      (by simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hz)
  have hp : p ∈ F q := by
    by_contra hp
    have hz := LinearMap.congr_fun (hF q hq p hp) x
    exact hne (by simpa only [homogeneousHistory_append, LinearMap.comp_apply,
      LinearMap.zero_apply] using hz)
  exact hr ((mem_appendHistorySupport S F r).mpr ⟨hq, hp⟩)

open Classical in
/-- Selecting joined histories by any condition commutes with their nested
finite sum, as an identity of linear maps. Distinct labels remain distinct even
when their maps agree, vanish, or cancel in the sum. -/
theorem sum_ite_homogeneousHistory_comp_appendHistorySupport
    (S : Finset (Fin m → ι)) (F : (Fin m → ι) → Finset (Fin n → ι))
    (P : (Fin (n + m) → ι) → Prop) :
    (∑ r ∈ appendHistorySupport S F,
      if P r then (homogeneousHistory ℳ (Fin.append T U) r).comp a else 0) =
      ∑ q ∈ S, ∑ p ∈ F q,
        if P (Fin.append p q) then
          (homogeneousHistory ℳ T p).comp ((homogeneousHistory ℳ U q).comp a) else 0 := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑S)
      (fun q => (F q).image fun p => Fin.append p q) := by
    intro q _ q' _ hqq'
    apply Finset.disjoint_left.mpr
    intro r hr hr'
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨p', _, he⟩ := Finset.mem_image.mp hr'
    exact hqq' (funext fun j => by simpa only [Fin.append_right] using
      (congrFun he (Fin.natAdd n j)).symm)
  rw [appendHistorySupport, Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_image (fun p _ p' _ he => funext fun j => by
    simpa only [Fin.append_left] using congrFun he (Fin.castAdd m j))]
  simp only [homogeneousHistory_append, LinearMap.comp_assoc]

/-- Summing over the joined uniform support recovers the composite of the two
blocks on the entire input module. No individual branch nonvanishing is assumed. -/
theorem sum_homogeneousHistory_comp_appendHistorySupport
    (S : Finset (Fin m → ι)) (F : (Fin m → ι) → Finset (Fin n → ι))
    (hS : ∀ q ∉ S, (homogeneousHistory ℳ U q).comp a = 0)
    (hF : ∀ q ∈ S, ∀ p ∉ F q,
      (homogeneousHistory ℳ T p).comp ((homogeneousHistory ℳ U q).comp a) = 0) :
    ∑ r ∈ appendHistorySupport S F, (homogeneousHistory ℳ (Fin.append T U) r).comp a =
      ((List.ofFn T).prod).comp (((List.ofFn U).prod).comp a) := by
  have he := sum_homogeneousHistory_comp_eq ℳ (Fin.append T U) a _
    (homogeneousHistory_comp_eq_zero_of_notMem_appendHistorySupport ℳ T U a S F hS hF)
  simpa only [List.ofFn_fin_append, List.prod_append, Module.End.mul_eq_comp,
    LinearMap.comp_assoc] using he

end Mei
