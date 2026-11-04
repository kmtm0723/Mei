/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.End.Recursion
public import Mathlib.LinearAlgebra.Pi

/-!
# Finite triangular systems of coefficient recursions

A strict lower triangular family of linear maps between finitely many semimodules defines a
nilpotent endomorphism of their product. Consequently a finite triangular coefficient system
has a unique solution, given by the existing finite geometric recursion operator.

After `k` applications the first `k` components vanish. Thus the nilpotence bound is the number
of components and does not depend on freeness, dimensions, coefficients, or additive cancellation.
The components may be different semimodules over an arbitrary semiring. Componentwise
coefficient maps intertwining the entries also intertwine the unique solution operators,
without injectivity or surjectivity.
-/

public section

namespace Module.End

variable {R : Type*} [Semiring R] {n : ℕ} {M : Fin n → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The strict lower triangular endomorphism whose `i`-th component is the sum of the
maps from components with smaller index. Entries on or above the diagonal are ignored. -/
def strictLowerTriangular (T : (i j : Fin n) → M j →ₗ[R] M i) :
    Module.End R (∀ i, M i) :=
  LinearMap.pi fun i =>
    ∑ j ∈ Finset.univ.filter (fun j => j < i), (T i j).comp (LinearMap.proj j)

/-- Applying a strict lower triangular system uses precisely the smaller input components. -/
@[simp]
theorem strictLowerTriangular_apply (T : (i j : Fin n) → M j →ₗ[R] M i)
    (x : ∀ i, M i) (i : Fin n) :
    strictLowerTriangular T x i = ∑ j ∈ Finset.univ.filter (fun j => j < i), T i j (x j) := by
  simp only [strictLowerTriangular, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

/-- After `k` applications, the first `k` components of a triangular system vanish. -/
theorem strictLowerTriangular_pow_apply_eq_zero (T : (i j : Fin n) → M j →ₗ[R] M i)
    (k : ℕ) (x : ∀ i, M i) (i : Fin n) (hi : i.val < k) :
    (strictLowerTriangular T ^ k) x i = 0 := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, strictLowerTriangular_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j < i := (Finset.mem_filter.mp hj).2
    have hjk : j.val < k := by omega
    rw [ih j hjk, map_zero]

/-- A strict lower triangular system on `n` components is nilpotent with exponent `n`. -/
@[simp]
theorem strictLowerTriangular_pow_eq_zero (T : (i j : Fin n) → M j →ₗ[R] M i) :
    strictLowerTriangular T ^ n = 0 := by
  apply LinearMap.ext
  intro x
  funext i
  exact strictLowerTriangular_pow_apply_eq_zero T n x i i.isLt

/-- The linear solution operator of a finite triangular system. -/
def lowerTriangularRecursion (T : (i j : Fin n) → M j →ₗ[R] M i) :
    Module.End R (∀ i, M i) :=
  (strictLowerTriangular T).finiteRecursion n

/-- The finite geometric solution satisfies every component of the triangular recursion. -/
theorem lowerTriangularRecursion_eq (T : (i j : Fin n) → M j →ₗ[R] M i)
    (a : ∀ i, M i) (i : Fin n) :
    lowerTriangularRecursion T a i =
      a i + ∑ j ∈ Finset.univ.filter (fun j => j < i),
        T i j (lowerTriangularRecursion T a j) := by
  have h := (strictLowerTriangular T).finiteRecursion_eq_add
    (strictLowerTriangular_pow_eq_zero T) a
  simpa only [lowerTriangularRecursion, Pi.add_apply, strictLowerTriangular_apply]
    using congrFun h i

/-- A family satisfying a finite triangular recursion equals its finite geometric solution. -/
theorem eq_lowerTriangularRecursion_of_forall (T : (i j : Fin n) → M j →ₗ[R] M i)
    {a x : ∀ i, M i}
    (hx : ∀ i, x i = a i + ∑ j ∈ Finset.univ.filter (fun j => j < i), T i j (x j)) :
    x = lowerTriangularRecursion T a := by
  apply (strictLowerTriangular T).eq_finiteRecursion_of_eq_add
    (strictLowerTriangular_pow_eq_zero T)
  funext i
  exact (hx i).trans (by rw [Pi.add_apply, strictLowerTriangular_apply])

/-- Every finite triangular coefficient system has exactly one solution over semimodules. -/
theorem existsUnique_lowerTriangularRecursion (T : (i j : Fin n) → M j →ₗ[R] M i)
    (a : ∀ i, M i) :
    ∃! x : ∀ i, M i,
      ∀ i, x i = a i + ∑ j ∈ Finset.univ.filter (fun j => j < i), T i j (x j) :=
  ⟨lowerTriangularRecursion T a, lowerTriangularRecursion_eq T a,
    fun _ hx => eq_lowerTriangularRecursion_of_forall T hx⟩

section Naturality

variable {N : Fin n → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- Component maps intertwining every lower triangular entry intertwine the assembled
systems. No injectivity or surjectivity of the component maps is required. -/
theorem piMap_comp_strictLowerTriangular
    (T : (i j : Fin n) → M j →ₗ[R] M i) (U : (i j : Fin n) → N j →ₗ[R] N i)
    (f : ∀ i, M i →ₗ[R] N i)
    (hf : ∀ i j, j < i → (f i).comp (T i j) = (U i j).comp (f j)) :
    (LinearMap.piMap f).comp (strictLowerTriangular T) =
      (strictLowerTriangular U).comp (LinearMap.piMap f) := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [LinearMap.comp_apply, LinearMap.coe_piMap, Pi.map_apply,
    strictLowerTriangular_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact LinearMap.congr_fun (hf i j (Finset.mem_filter.mp hj).2) (x j)

/-- Componentwise coefficient intertwiners preserve the unique finite triangular solution.
This follows from the common nilpotent recursion comparison theorem. -/
theorem piMap_comp_lowerTriangularRecursion
    (T : (i j : Fin n) → M j →ₗ[R] M i) (U : (i j : Fin n) → N j →ₗ[R] N i)
    (f : ∀ i, M i →ₗ[R] N i)
    (hf : ∀ i j, j < i → (f i).comp (T i j) = (U i j).comp (f j)) :
    (LinearMap.piMap f).comp (lowerTriangularRecursion T) =
      (lowerTriangularRecursion U).comp (LinearMap.piMap f) :=
  comp_finiteRecursion (strictLowerTriangular T) (strictLowerTriangular U)
    (LinearMap.piMap f) (piMap_comp_strictLowerTriangular T U f hf)
    (strictLowerTriangular_pow_eq_zero T) (strictLowerTriangular_pow_eq_zero U)

end Naturality

end Module.End
