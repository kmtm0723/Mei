/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Linear
public import Mei.Geometry.Affine.Generic.Line
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Cutoff evaluation between finitely many line events

For rational polyhedral data, choose the exceptional arrangement for the full
cutoff evaluation linear map. A line starting at a generic point has finitely
many exceptional parameter values. On every preconnected parameter set avoiding
those values, the actual evaluation operator is constant, simultaneously for all
incoming coefficients. The event set can contain times at which no jump occurs.
This result supplies intervalwise operator constancy, without asserting a local
resolution identity at an event or extending admissible rays to their boundaries.
-/

public noncomputable section

namespace Mei

open Mei.Convex

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M)
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P W : J → Set V) (S : K → Set V) (C : Set V)
  {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : Γ → Λ) [Finite J] [Finite K]
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

include hf hP hW hS hC

/-- Along any line starting at a generic point, finitely many parameter values
contain all possible changes of the actual cutoff evaluation operator. On every
preconnected set avoiding them, equality holds as linear maps, hence for every
incoming coefficient at once. The other endpoint need not be generic. -/
theorem exists_cutoffDecoratedEvaluationLinearMap_lineEvents (k : ℕ) :
    ∃ E : ExceptionalArrangement V, ∀ x, E.IsGeneric x → ∀ y,
      ∃ A : Finset ℝ,
        (∀ t, t ∈ A ↔ ¬ E.IsGeneric (AffineMap.lineMap x y t)) ∧
        ∀ B : Set ℝ, IsPreconnected B → (∀ t ∈ B, t ∉ A) →
          ∀ s ∈ B, ∀ t ∈ B,
            cutoffDecoratedEvaluationLinearMap d ℳ T (fun q => i (w q)) f c ε P W S C k
                (AffineMap.lineMap x y s) =
              cutoffDecoratedEvaluationLinearMap d ℳ T (fun q => i (w q)) f c ε P W S C k
                (AffineMap.lineMap x y t) := by
  classical
  obtain ⟨E, hstable⟩ := exists_cutoffDecoratedEvaluationLinearMap_eventually_eq
    d ℳ T f c ε P W S C h w hf hP hW hS hC k
  refine ⟨E, fun x hx y => ?_⟩
  let hfinite := E.finite_nonGeneric_lineMap hx y
  refine ⟨hfinite.toFinset, fun t => hfinite.mem_toFinset, ?_⟩
  intro B hB havoid s hs t ht
  let : PreconnectedSpace B := isPreconnected_iff_preconnectedSpace.mp hB
  let L (b : B) := cutoffDecoratedEvaluationLinearMap d ℳ T (fun q => i (w q))
    f c ε P W S C k (AffineMap.lineMap x y (b : ℝ))
  have hc : Continuous (fun b : B => AffineMap.lineMap x y (b : ℝ)) := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    exact (continuous_subtype_val.smul continuous_const).add continuous_const
  have hlocal : IsLocallyConstant L := by
    apply (IsLocallyConstant.iff_eventually_eq L).mpr
    intro b
    have hgeneric : E.IsGeneric (AffineMap.lineMap x y (b : ℝ)) := by
      by_contra hn
      exact havoid b b.property (hfinite.mem_toFinset.mpr hn)
    exact hc.continuousAt.tendsto.eventually (hstable _ hgeneric)
  exact hlocal.apply_eq_of_preconnectedSpace ⟨s, hs⟩ ⟨t, ht⟩

end Mei
