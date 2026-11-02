/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Section
public import Mei.Topology.Sheaves.LocallyConstant.FacetDescent.Hom
public import Mei.Topology.Sheaves.DenseBasisTransport.Linear.Comparison

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
  let F := D.coefficientSemimoduleLocalSystem M R
  let Q := D.coefficientTransport M
  let e (W : Opens C.regularSpace) := Q.semimoduleSheafSectionsIso R W
  have hres {W W' : Opens C.regularSpace} (hWW' : W' ≤ W) :
      F.obj.map (homOfLE hWW').op = (e W).hom ≫
        SemimoduleCat.ofHom (Q.restrictionLinearMap R hWW') ≫ (e W').inv :=
    Q.semimoduleSheaf_map R hWW'
  obtain ⟨s, hs, -⟩ := h𝒜 B hoff hgen α
  have hF := Q.exists_isIso_restrictions_semimoduleSheaf R
  have hlocal : ∀ x ∈ O, x ∉ B → ∃ (N : Opens C.regularSpace)
      (t : H ⟶ F.obj.obj (op N)), x ∈ N ∧
        t ≫ F.obj.map (homOfLE (inf_le_left : N ⊓ B ≤ N)).op =
          (SemimoduleCat.ofHom s ≫ (e B).inv) ≫
            F.obj.map (homOfLE (inf_le_right : N ⊓ B ≤ B)).op := by
    intro x hx hxn
    obtain ⟨N, t, hxN, ht⟩ := hfacet x hx hxn
    refine ⟨N, SemimoduleCat.ofHom t ≫ (e N).inv, hxN, ?_⟩
    rw [hres, hres]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, ← Category.assoc]
    apply congrArg (fun q => q ≫ (e (N ⊓ B)).inv)
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Q.section_ext
    intro y hy
    -- Composition with a linear restriction evaluates the original section map.
    change Q.value (Q.restrictionLinearMap R inf_le_left (t a)) y hy =
      Q.value (Q.restrictionLinearMap R inf_le_right (s a)) y hy
    rw [Q.value_restrictionLinearMap, Q.value_restrictionLinearMap]
    exact (ht a y hy.1 hy.2).trans (hs a y hy.2).symm
  obtain ⟨t, ht, huniq⟩ := F.existsUnique_hom_extension_of_facets hF
    C.isOpen_regularLocus Z hZ hBO hOU hdense hsing H
      (SemimoduleCat.ofHom s ≫ (e B).inv) hlocal
  let result := (t ≫ (e U).hom).hom
  have hr : (Q.restrictionLinearMap R (hBO.trans hOU)).comp result = s := by
    have he := congrArg (fun z => z ≫ (e B).hom) ht
    rw [hres] at he
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at he
    exact congrArg SemimoduleCat.Hom.hom he
  have hvalues (a : H) (y : C.coefficientPoints) (hyB : y.val ∈ B) :
      Q.value (result a) y ((hBO.trans hOU) hyB) =
        cutoffDecoratedEvaluation d ℳ T (α a) (fun q => i (w q))
          f c ε P W S A k y.val.val := by
    have he := LinearMap.congr_fun hr a
    exact (Q.value_restrictionLinearMap R _ (result a) y hyB).symm.trans
      ((congrArg (fun z => Q.value z y hyB) he).trans (hs a y hyB))
  refine ⟨result, hvalues, fun t' ht' => ?_⟩
  have he : (Q.restrictionLinearMap R (hBO.trans hOU)).comp t' = s := by
    apply LinearMap.ext
    intro a
    apply Q.section_ext
    intro y hyB
    exact (Q.value_restrictionLinearMap R _ (t' a) y hyB).trans
      ((ht' a y hyB).trans (hs a y hyB).symm)
  have hm : (SemimoduleCat.ofHom t' ≫ (e U).inv) ≫
      F.obj.map (homOfLE (hBO.trans hOU)).op =
        SemimoduleCat.ofHom s ≫ (e B).inv := by
    rw [hres]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc]
    apply congrArg (fun z => z ≫ (e B).inv)
    apply SemimoduleCat.hom_ext
    exact he
  have hu := congrArg (fun z => z ≫ (e U).hom) (huniq _ hm)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hu
  exact congrArg SemimoduleCat.Hom.hom hu

end Mei.FiniteWallDiagram
