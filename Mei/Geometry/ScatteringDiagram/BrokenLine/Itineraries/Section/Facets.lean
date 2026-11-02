/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Section
public import Mei.Topology.Sheaves.DenseBasisTransport.Linear.FacetDescent

/-!
# Extending actual cutoff-ray sections across facets

The actual cutoff decorated-ray sum defines a coefficient-section map on a dense
open of generic endpoints. Local linear section maps agreeing with that sum on
incident generic endpoints supply its facet extensions. The existing facet descent
then extends the whole sum uniquely past those facets and a countable union of
codimension-at-least-two affine obstacles. Individual ray summands need not extend.

The theorem assumes the local resolution identities in the form of coefficient
value equations; it does not construct exhaustive local resolutions or their
certificates. The histories in the sum retain their original incoming tails and
are not restricted to the chosen endpoint domains.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite Topology Set TopCat Mei.Convex

universe u m r

namespace Mei.FiniteWallDiagram

variable {N G Γ J K : Type*} {V : Type u} {M : Type m} {R : Type r} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {i : N →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i} {C : FinitePolyhedralComplex h}
  [Group G] (D : FiniteWallDiagram C G) [Semiring R] [AddCommMonoid M]
  [DistribMulAction G M] [Module R M] [SMulCommClass G R M]
  [AddCommGroup Γ] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (T : J → Module.End R M) (w : Γ → N) [Finite J] [Finite K]
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P W : J → Set V) (S : K → Set V) (A : Set V)
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hA : IsRationalNormalPolyhedron h A)


variable (H : SemimoduleCat.{max u m} R)

include hf hP hW hS hA in
/-- One exceptional arrangement supplies unique linear extensions of the actual
cutoff-ray totals. `B ≤ O ≤ U` are endpoint opens: `B` is off-wall and generic,
dense in `O`; `U \ O` lies in countably many affine subspaces of codimension at
least two. At each point of `O \ B`, a local linear section map must agree with
the ray total on `N ⊓ B`. This is a condition on the total, not on its summands. -/
theorem exists_cutoffDecoratedEvaluation_extension_of_facets (k : ℕ) :
    ∃ 𝒜 : ExceptionalArrangement V, ∀ (B O U : Opens C.regularSpace)
      (_ : (B : Set C.regularSpace) ⊆ C.coefficientPoints)
      (_ : ∀ x ∈ B, 𝒜.IsGeneric x.val)
      (hBO : B ≤ O) (hOU : O ≤ U)
      (_ : (O : Set C.regularSpace) ⊆ closure (B : Set C.regularSpace))
      {κ : Type*} [Countable κ] (Z : κ → AffineSubspace ℝ V)
      (_ : ∀ j, Module.finrank ℝ (Z j).direction + 1 < Module.finrank ℝ V)
      (_ : ∀ x ∈ U, x ∉ O → ∃ j, (x : V) ∈ Z j)
      (α : H →ₗ[R] ℳ 0),
      (∀ x ∈ O, x ∉ B → ∃ (N : Opens C.regularSpace)
        (t : H →ₗ[R] (D.coefficientLocalSystem M).presheaf.obj (op N)), x ∈ N ∧
        ∀ a (y : C.coefficientPoints) (hyN : y.val ∈ N) (_ : y.val ∈ B),
          (D.coefficientTransport M).value (t a) y hyN =
            cutoffDecoratedEvaluation d ℳ T (α a) (fun q => i (w q))
              f c ε P W S A k y.val.val) →
      ∃! t : H →ₗ[R] (D.coefficientLocalSystem M).presheaf.obj (op U),
        ∀ a (y : C.coefficientPoints) (hyB : y.val ∈ B),
          (D.coefficientTransport M).value (t a) y ((hBO.trans hOU) hyB) =
            cutoffDecoratedEvaluation d ℳ T (α a) (fun q => i (w q))
              f c ε P W S A k y.val.val := by
  have := h.finiteDimensional
  obtain ⟨𝒜, h𝒜⟩ := D.exists_cutoffDecoratedEvaluation_sections
    (E := H) d ℳ T w f c ε P W S A hf hP hW hS hA k
  refine ⟨𝒜, ?_⟩
  intro B O U hoff hgen hBO hOU hdense κ hκ Z hZ hsing α hfacet
  obtain ⟨s, hs, -⟩ := h𝒜 B hoff hgen α
  obtain ⟨t, ht, huniq⟩ := (D.coefficientTransport M).existsUnique_linearMap_extension_of_facets
    R C.isOpen_regularLocus Z hZ hBO hOU hdense hsing H s (by
      intro x hx hxn
      obtain ⟨N, t, hxN, ht⟩ := hfacet x hx hxn
      exact ⟨N, t, hxN, fun a y hyN hyB => (ht a y hyN hyB).trans (hs a y hyB).symm⟩)
  refine ⟨t, fun a y hyB => (ht a y hyB).trans (hs a y hyB), fun t' ht' => ?_⟩
  exact huniq t' (fun a y hyB => (ht' a y hyB).trans (hs a y hyB).symm)

end Mei.FiniteWallDiagram
