/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Linear
public import Mei.Geometry.Convex.Polyhedron.Rational.Stratification
public import Mei.Geometry.Affine.Generic

/-!
# Input-independent polyhedral operator charts for cutoff rays

The entire actual cutoff-ray evaluation has a finite presentation by closed
rational-normal polyhedra carrying fixed linear maps. A chart contributes on its
relative interior. The same charts and maps apply simultaneously to every incoming
coefficient, even when addition or scalar multiplication kills individual histories.
A single common partition works for every cutoff in a bounded finite range,
including all lower-dimensional strata. The one-cutoff presentation uses the
corresponding single-family weighted
presentation, derived from the same partition theorem.
Countably many such operators, including systems with different coefficient
modules and cutoffs, have a dense Gδ common generic locus. At each point of this
locus every operator is locally constant, with a neighborhood for each system.

This is a presentation of the actual evaluation operator, with the original
incoming tails and endpoint admission. Boundary points of a closed chart are
limits; no valid boundary ray or local resolution identity is asserted.
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
/-- All actual cutoff operators through `k` share a finite family of closed
rational-normal polyhedra whose relative interiors partition the endpoint space.
Those interiors are nonempty and carry fixed linear maps for every input. -/
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

include hf hP hW hS hC in
open Classical in
/-- A single finite list of nonempty closed rational-normal polyhedra with fixed
linear weights computes the actual cutoff-ray operator on their relative interiors,
simultaneously for every incoming coefficient. Distinct charts may have coincident images. -/
theorem exists_cutoffDecoratedEvaluationLinearMap_polyhedralCharts (k : ℕ) :
    ∃ (n : ℕ) (A : Fin n → Set V) (L : Fin n → ℳ 0 →ₗ[R] M),
      (∀ j, (A j).Nonempty ∧ IsRationalNormalPolyhedron h (A j)) ∧
        ∀ Q, cutoffDecoratedEvaluationLinearMap d ℳ T (fun q => i (w q))
          f c ε P W S C k Q = ∑ j, if Q ∈ intrinsicInterior ℝ (A j) then L j else 0 := by
  classical
  obtain ⟨n, D, L, hD, hL⟩ :=
    exists_cutoffDecoratedEvaluationLinearMap_semilinearPresentation
      d ℳ T f c ε P W S C h w hf hP hW hS hC k
  obtain ⟨m, B, L', hB, hsum⟩ :=
    IsRationalSemilinear.exists_weighted_polyhedralCharts D hD L
  exact ⟨m, B, L', hB, fun Q => (hL Q).trans (hsum Q)⟩

section Countable

variable {τ : Type*} [Countable τ] [FiniteDimensional ℝ V]
  (M' : τ → Type*) [∀ t, AddCommMonoid (M' t)] [∀ t, Module R (M' t)]
  (𝓜 : ∀ t, Γ → Submodule R (M' t)) [∀ t, DirectSum.Decomposition (𝓜 t)]
  (actions : ∀ t, J → Module.End R (M' t)) (cutoff : τ → ℕ)
  (sources : τ → Set V) (hsources : ∀ t, IsRationalNormalPolyhedron h (sources t))

include hf hP hW hS hsources in
/-- A countable collection of actual cutoff-ray operators has a dense Gδ common
generic locus. Coefficient modules, actions, cutoffs and source domains may vary.
At each generic endpoint, the neighborhood for one operator works for all its
inputs; different operators may require different neighborhoods. -/
theorem exists_cutoffDecoratedEvaluationLinearMap_dense_commonGeneric :
    ∃ E : τ → ExceptionalArrangement V,
      Dense {Q | ∀ t, (E t).IsGeneric Q} ∧ IsGδ {Q | ∀ t, (E t).IsGeneric Q} ∧
        ∀ t Q, (E t).IsGeneric Q → ∀ᶠ Q' in nhds Q,
          cutoffDecoratedEvaluationLinearMap d (𝓜 t) (actions t) (fun q => i (w q))
            f c ε P W S (sources t) (cutoff t) Q' =
          cutoffDecoratedEvaluationLinearMap d (𝓜 t) (actions t) (fun q => i (w q))
            f c ε P W S (sources t) (cutoff t) Q := by
  classical
  choose E hE using fun t =>
    exists_cutoffDecoratedEvaluationLinearMap_eventually_eq
      d (𝓜 t) (actions t) f c ε P W S (sources t)
      h w hf hP hW hS (hsources t) (cutoff t)
  exact ⟨E, ExceptionalArrangement.dense_iInter_isGeneric E,
    ExceptionalArrangement.isGδ_iInter_isGeneric E, hE⟩

end Countable

end Mei
