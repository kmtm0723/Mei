/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.Stratification

/-!
# Common closed polyhedral partitions for weighted semilinear families

One finite collection of closed rational-normal polyhedra has disjoint relative
interiors covering the whole space and deciding all memberships in a finite
semilinear family. Lower-dimensional strata are retained. Consequently finitely
many weighted semilinear sums are constant simultaneously on each stratum, with
weights in any additive commutative monoid.

The common arrangement is supplied by `exists_common_signCell`. Taking closures
of its nonempty sign cells retains exactly those cells as relative interiors.
-/

public noncomputable section

namespace Mei

variable {N V J : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Finite J] {S : J → Set V}

/-- A finite semilinear family has a common partition into the disjoint relative
interiors of closed rational-normal polyhedra. The interiors are nonempty, cover
all points, and determine membership in every original domain. -/
theorem IsRationalSemilinear.exists_common_intrinsicInteriors
    (hS : ∀ j, IsRationalSemilinear h (S j)) :
    ∃ (κ : Type) (_ : Finite κ) (C : κ → Set V),
      (∀ a, (C a).Nonempty ∧ IsRationalNormalPolyhedron h (C a) ∧
        (intrinsicInterior ℝ (C a)).Nonempty) ∧
      (Pairwise fun a b => Disjoint (intrinsicInterior ℝ (C a))
        (intrinsicInterior ℝ (C b))) ∧ (⋃ a, intrinsicInterior ℝ (C a)) = Set.univ ∧
      ∀ a x, x ∈ intrinsicInterior ℝ (C a) → ∀ y,
        y ∈ intrinsicInterior ℝ (C a) → ∀ j, (x ∈ S j ↔ y ∈ S j) := by
  obtain ⟨ι, _, g, hg, hmem⟩ := IsRationalSemilinear.exists_common_signCell hS
  let κ := {σ : ι → SignType // (Convex.signCell g σ).Nonempty}
  refine ⟨κ, inferInstance, fun σ => closure (Convex.signCell g σ), ?_, ?_, ?_, ?_⟩
  · intro σ
    refine ⟨σ.property.mono subset_closure,
      (isLocallyClosedPolyhedron_signCell g hg σ).isRationalNormalPolyhedron_closure, ?_⟩
    rw [Convex.intrinsicInterior_closure_signCell]
    exact σ.property
  · intro σ τ hστ
    simp only [Convex.intrinsicInterior_closure_signCell]
    exact Convex.signCell_disjoint (Subtype.coe_injective.ne hστ)
  · simp only [Convex.intrinsicInterior_closure_signCell]
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨⟨_, x, Convex.mem_signCell_sign g x⟩,
      Convex.mem_signCell_sign g x⟩
  · intro σ x hx y hy
    rw [Convex.intrinsicInterior_closure_signCell] at hx hy
    exact hmem σ x y hx hy

open Classical in
/-- Finitely many finite weighted semilinear sums share one closed polyhedral
partition. Each weight function is constant on every stratum, including boundary
strata. The summand index types may differ between the weighted sums. -/
theorem IsRationalSemilinear.exists_common_weighted_polyhedralPartition
    {K β : Type*} [Finite K] [AddCommMonoid β] (J : K → Type*) [∀ k, Fintype (J k)]
    (A : ∀ k, J k → Set V) (hA : ∀ k j, IsRationalSemilinear h (A k j))
    (L : ∀ k, J k → β) :
    ∃ (n : ℕ) (C : Fin n → Set V) (W : Fin n → K → β),
      (∀ a, (C a).Nonempty ∧ IsRationalNormalPolyhedron h (C a) ∧
        (intrinsicInterior ℝ (C a)).Nonempty) ∧
      (Pairwise fun a b => Disjoint (intrinsicInterior ℝ (C a))
        (intrinsicInterior ℝ (C b))) ∧ (⋃ a, intrinsicInterior ℝ (C a)) = Set.univ ∧
      ∀ a k x, x ∈ intrinsicInterior ℝ (C a) →
        (∑ j, if x ∈ A k j then L k j else 0) = W a k := by
  classical
  obtain ⟨κ, _, C, hC, hdisj, hcover, hmem⟩ :=
    IsRationalSemilinear.exists_common_intrinsicInteriors
      (S := fun p : Σ k, J k => A p.1 p.2) (fun p => hA p.1 p.2)
  let x a := (hC a).2.2.choose
  have hx a : x a ∈ intrinsicInterior ℝ (C a) := (hC a).2.2.choose_spec
  let W a k := ∑ j, if x a ∈ A k j then L k j else 0
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  refine ⟨n, fun a => C (e.symm a), fun a => W (e.symm a),
    fun a => hC (e.symm a), ?_, ?_, ?_⟩
  · intro a b hab
    exact hdisj (e.symm.injective.ne hab)
  · rw [← hcover]
    exact e.symm.surjective.iUnion_comp (fun a => intrinsicInterior ℝ (C a))
  · intro a k y hy
    apply Finset.sum_congr rfl
    intro j _
    simp only [hmem (e.symm a) y hy (x (e.symm a)) (hx _) ⟨k, j⟩]

end Mei
