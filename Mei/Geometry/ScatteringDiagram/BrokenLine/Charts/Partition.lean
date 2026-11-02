/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Linear
public import Mei.Geometry.Convex.Polyhedron.Rational.Partition

/-!
# Common polyhedral strata for bounded cutoff operators

For every finite range of cutoffs, the actual decorated-ray evaluation operators
are constant on one common finite closed-polyhedral partition. Its disjoint
relative interiors cover every endpoint, including all lower-dimensional boundary
strata. The same operator weights apply to every incoming coefficient at once.
The finite histories retain their original incoming tails. No boundary-ray
realization or local-resolution identity is asserted.
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M Γ V J K Λ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P W : J → Set V) (S : K → Set V) (C : Set V)
  [AddCommGroup Λ] {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (w : Γ → Λ) [Finite J] [Finite K]
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

include hf hP hW hS hC in
/-- All actual cutoff operators through `k` share a finite closed rational-normal
partition, simultaneously for every input. Relative interiors are nonempty,
pairwise disjoint, cover the whole endpoint space, and carry fixed linear maps. -/
theorem exists_cutoffDecoratedEvaluationLinearMap_commonPartition (k : ℕ) :
    ∃ (n : ℕ) (A : Fin n → Set V) (L : Fin n → Fin (k + 1) → ℳ 0 →ₗ[R] M),
      (∀ j, (A j).Nonempty ∧ IsRationalNormalPolyhedron h (A j) ∧
        (intrinsicInterior ℝ (A j)).Nonempty) ∧
      (Pairwise fun a b => Disjoint (intrinsicInterior ℝ (A a))
        (intrinsicInterior ℝ (A b))) ∧ (⋃ j, intrinsicInterior ℝ (A j)) = Set.univ ∧
      ∀ j q Q, Q ∈ intrinsicInterior ℝ (A j) →
        cutoffDecoratedEvaluationLinearMap d ℳ T (fun p => i (w p))
          f c ε P W S C q.val Q = L j q := by
  classical
  choose n A L hA hsum using fun q : Fin (k + 1) =>
    exists_cutoffDecoratedEvaluationLinearMap_semilinearPresentation
      d ℳ T f c ε P W S C h w hf hP hW hS hC q.val
  obtain ⟨m, B, W, hB, hdisj, hcover, hW⟩ :=
    IsRationalSemilinear.exists_common_weighted_polyhedralPartition
      (fun q => Fin (n q)) A hA L
  exact ⟨m, B, W, hB, hdisj, hcover,
    fun j q Q hQ => (hsum q Q).trans (hW j q Q hQ)⟩

end Mei
