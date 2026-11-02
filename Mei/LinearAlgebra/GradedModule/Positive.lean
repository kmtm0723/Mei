/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.DirectSum.Internal
public import Mei.LinearAlgebra.End.Recursion

/-!
# Componentwise positive graded modules

A family of additive positive monoids on homogeneous pieces determines an
additive submonoid of the whole module. Componentwise positivity of an
endomorphism on homogeneous inputs makes this submonoid invariant. The generic
finite-recursion preservation theorem then gives positivity of finite sums and
of every solution of a nilpotent recursion, including mixed-degree inputs.
The coefficient semiring needs no order or additive cancellation.
-/

public noncomputable section

namespace Mei

variable {R M Γ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (Pos : Γ → AddSubmonoid M)

/-- Elements whose homogeneous components belong to the chosen positive monoids. -/
def componentwisePositive : AddSubmonoid M where
  carrier := {x | ∀ q, (DirectSum.decompose ℳ x q : M) ∈ Pos q}
  zero_mem' := by
    intro q
    simpa only [DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
      using (Pos q).zero_mem
  add_mem' := by
    intro x y hx hy q
    simpa only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      using (Pos q).add_mem (hx q) (hy q)

@[simp]
theorem mem_componentwisePositive (x : M) :
    x ∈ componentwisePositive ℳ Pos ↔
      ∀ q, (DirectSum.decompose ℳ x q : M) ∈ Pos q := Iff.rfl

/-- Homogeneous componentwise positivity implies preservation of the whole positive monoid. -/
theorem map_mem_componentwisePositive (U : Module.End R M)
    (hU : ∀ i q x, x ∈ ℳ i → x ∈ Pos i →
      (DirectSum.decompose ℳ (U x) q : M) ∈ Pos q)
    {a : M} (ha : a ∈ componentwisePositive ℳ Pos) :
    U a ∈ componentwisePositive ℳ Pos := by
  classical
  rw [mem_componentwisePositive] at ha ⊢
  intro q
  rw [← DirectSum.sum_support_decompose ℳ a]
  simp only [map_sum, DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  exact (Pos q).sum_mem (fun i _ => hU i q _ (DirectSum.decompose ℳ a i).property (ha i))


variable (U : Module.End R M)

/-- Finite recursion preserves componentwise positive inputs if every homogeneous
component of the endomorphism preserves the chosen additive positive monoids. -/
theorem finiteRecursion_component_mem_addSubmonoid (Pos : Γ → AddSubmonoid M)
    (hU : ∀ i q x, x ∈ ℳ i → x ∈ Pos i →
      (DirectSum.decompose ℳ (U x) q : M) ∈ Pos q)
    (r : ℕ) (a : M) (ha : ∀ i, (DirectSum.decompose ℳ a i : M) ∈ Pos i) (q : Γ) :
    (DirectSum.decompose ℳ (U.finiteRecursion r a) q : M) ∈ Pos q := by
  have h := U.finiteRecursion_mem (componentwisePositive ℳ Pos)
    (fun _ hx => map_mem_componentwisePositive ℳ Pos U hU hx) r
    ((mem_componentwisePositive ℳ Pos a).mpr ha)
  exact (mem_componentwisePositive ℳ Pos _).mp h q

/-- Every solution of a nilpotent recursion has positive components when its input
does and every component of `U` maps `ℳ i ∩ Pos i` into `Pos q`.
The endomorphism need not preserve homogeneous degrees. -/
theorem component_mem_addSubmonoid_of_eq_add (Pos : Γ → AddSubmonoid M)
    (hU : ∀ i q x, x ∈ ℳ i → x ∈ Pos i →
      (DirectSum.decompose ℳ (U x) q : M) ∈ Pos q)
    {r : ℕ} (hnil : U ^ r = 0) {a x : M}
    (ha : ∀ i, (DirectSum.decompose ℳ a i : M) ∈ Pos i)
    (hx : x = a + U x) (q : Γ) : (DirectSum.decompose ℳ x q : M) ∈ Pos q := by
  have h := U.mem_of_eq_add_of_pow_eq_zero (componentwisePositive ℳ Pos)
    (fun _ hx => map_mem_componentwisePositive ℳ Pos U hU hx) hnil
    ((mem_componentwisePositive ℳ Pos a).mpr ha) hx
  exact (mem_componentwisePositive ℳ Pos _).mp h q


end Mei
