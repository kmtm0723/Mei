/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Uniform
import Mathlib.Data.Fintype.BigOperators

/-!
# Uniform finite expansions of homogeneous histories

When all nonzero homogeneous pieces lie in a fixed finite set, a composite of
linear maps is the sum of its whole-component history maps over that set.
Unlike the support of a single input, this finite index set works simultaneously
for every coefficient, without a finite generation assumption on the modules.
Thus the expansion is an identity of linear maps, suitable for coefficient
identities with a variable incoming parameter.

`sum_homogeneousHistory_comp_eq` in `History/Uniform.lean` gives the version
for a uniform support on the range of an input map, which also covers
infinitely supported gradings.
-/

public noncomputable section

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- A history using a degree outside the finite support of the grading is the
zero linear map, independently of its input. -/
theorem homogeneousHistory_eq_zero_of_notMem_piFinset (S : Finset ι)
    (hS : ∀ i, i ∉ S → ℳ i = ⊥) {n : ℕ} (T : Fin n → Module.End R M)
    (p : Fin n → ι) (hp : p ∉ Fintype.piFinset (fun _ => S)) :
    homogeneousHistory ℳ T p = 0 := by
  apply LinearMap.ext
  intro x
  by_contra hx
  apply hp
  apply Fintype.mem_piFinset.mpr
  intro j
  by_contra hj
  have hstage := homogeneousHistoryStage_mem ℳ T p x j
  rw [hS _ hj, Submodule.mem_bot] at hstage
  exact homogeneousHistoryStage_ne_zero ℳ T p hx j.castSucc hstage

/-- If the grading is supported on a finite set, summing all history maps over
that set recovers the composite as a linear map. The same index set works for
every input; zero component maps contribute zero. -/
theorem sum_homogeneousHistory_eq_prod (S : Finset ι)
    (hS : ∀ i, i ∉ S → ℳ i = ⊥) {n : ℕ} (T : Fin n → Module.End R M) :
    ∑ p : Fin n → S, homogeneousHistory ℳ T (fun j => (p j).val) =
      (List.ofFn T).prod := by
  classical
  let embed : (Fin n → S) → (Fin n → ι) := fun p j => (p j).val
  have hinj : Function.Injective embed := by
    intro p q hpq
    funext j
    exact Subtype.ext (congrFun hpq j)
  have hzero (p : Fin n → ι) (hp : p ∉ Finset.univ.image embed) :
      (homogeneousHistory ℳ T p).comp LinearMap.id = 0 := by
    have hp' : p ∉ Fintype.piFinset (fun _ => S) := by
      intro hmem
      exact hp (Finset.mem_image.mpr
        ⟨fun j => ⟨p j, (Fintype.mem_piFinset.mp hmem) j⟩, Finset.mem_univ _, rfl⟩)
    rw [homogeneousHistory_eq_zero_of_notMem_piFinset ℳ S hS T p hp', LinearMap.zero_comp]
  have he := sum_homogeneousHistory_comp_eq ℳ T LinearMap.id
    (Finset.univ.image embed) hzero
  rw [Finset.sum_image (fun p _ q _ hpq => hinj hpq)] at he
  simpa only [LinearMap.comp_id] using he

end Mei
