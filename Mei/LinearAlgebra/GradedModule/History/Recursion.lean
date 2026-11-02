/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.End.Recursion
public import Mei.LinearAlgebra.GradedModule.History.Uniform

/-!
# Homogeneous histories of finite recursion solutions

The finite geometric solution operator of `Module.End.finiteRecursion` expands
as the finite sum of homogeneous histories of every length below its bound.
For a nilpotent endomorphism, every solution of `x = a + U x` equals this sum.
Only the histories of each actual input are needed; the grading may be infinite.

Uniform finite support on an input range gives the corresponding identity of
linear maps, including after any final linear output map. Finite generation of
that range supplies such supports through `exists_uniform_homogeneousHistory_support`.
The proofs reuse the existing finite recursion and finite component expansions,
and retain their semiring hypotheses without additive cancellation.
-/

public noncomputable section

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
  (U : Module.End R M)

/-- The finite recursion operator is the sum of all contributing histories
of every length below its bound, without a finite ambient grading. -/
theorem sum_sum_homogeneousHistory_eq_finiteRecursion (r : ℕ) (a : M) :
    (∑ j ∈ Finset.range r,
      ∑ p ∈ homogeneousHistorySupport ℳ (fun _ : Fin j => U) a,
        homogeneousHistory ℳ (fun _ : Fin j => U) p a) = U.finiteRecursion r a := by
  simp only [sum_homogeneousHistory, List.ofFn_const, List.prod_replicate,
    Module.End.finiteRecursion_apply]

/-- Every solution of a nilpotent recursion equals its finite homogeneous
history expansion. The uniqueness argument needs no subtraction. -/
theorem eq_sum_sum_homogeneousHistory_of_eq_add {r : ℕ} (hU : U ^ r = 0)
    {a x : M} (hx : x = a + U x) :
    x = ∑ j ∈ Finset.range r,
      ∑ p ∈ homogeneousHistorySupport ℳ (fun _ : Fin j => U) a,
        homogeneousHistory ℳ (fun _ : Fin j => U) p a := by
  rw [sum_sum_homogeneousHistory_eq_finiteRecursion]
  exact U.eq_finiteRecursion_of_eq_add hU hx

/-- Uniform finite history supports give the finite recursion as a linear-map
identity on the input range, also after any final projection or linear output map. -/
theorem sum_sum_comp_homogeneousHistory_eq_finiteRecursion
    {E N : Type*} [AddCommMonoid E] [Module R E] [AddCommMonoid N] [Module R N]
    (a : E →ₗ[R] M) (b : M →ₗ[R] N) (r : ℕ)
    (S : (j : ℕ) → Finset (Fin j → ι))
    (hS : ∀ j < r, ∀ p ∉ S j, (homogeneousHistory ℳ (fun _ : Fin j => U) p).comp a = 0) :
    (∑ j ∈ Finset.range r,
      ∑ p ∈ S j, b.comp ((homogeneousHistory ℳ (fun _ : Fin j => U) p).comp a)) =
      b.comp ((U.finiteRecursion r).comp a) := by
  calc
    _ = ∑ j ∈ Finset.range r, b.comp (((List.ofFn fun _ : Fin j => U).prod).comp a) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_comp_homogeneousHistory_comp_eq ℳ (fun _ : Fin j => U) a b (S j)
        (hS j (Finset.mem_range.mp hj))
    _ = _ := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, List.ofFn_const,
        List.prod_replicate, Module.End.finiteRecursion_apply, map_sum]

end Mei
