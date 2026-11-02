/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Linear

/-!
# Input-independent polyhedral operator charts for cutoff rays

The entire actual cutoff-ray evaluation has a finite presentation by closed
rational-normal polyhedra carrying fixed linear maps. A chart contributes on its
relative interior. The same charts and maps apply simultaneously to every incoming
coefficient, even when addition or scalar multiplication kills individual histories.
Coincident chart images contribute separately to the sum.

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

end Mei
