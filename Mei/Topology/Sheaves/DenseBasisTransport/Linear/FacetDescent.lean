/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.DenseBasisTransport.Linear.Comparison
public import Mei.Topology.Sheaves.LocallyConstant.FacetDescent.Hom

/-!
# Extending linear transport-section maps across facets

A linear family of transport sections on a dense open extends uniquely when
local linear families agree with its coefficient values across every facet.
The larger domain may also contain countably many affine obstacles of
codimension at least two. Only the total family needs these local extensions.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite Topology Set TopCat

universe u v r

namespace Mei.DenseBasisTransport

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {S : Set V} {A : Set (TopCat.of S)} {M : Type v}
  (T : DenseBasisTransport A M) (R : Type r) [Semiring R]
  [AddCommMonoid M] [Module R M] [T.IsAdditive] [T.PreservesSMul R]

-- Pin the transport datum when inferring algebra on its opaque section carrier.
/-- Addition on the section carrier for the specified transport datum. -/
local instance sectionAddCommMonoid (W : Opens (TopCat.of S)) :
    AddCommMonoid (T.sheaf.presheaf.obj (op W)) :=
  T.instAddCommMonoidSections W
/-- Scalars on the section carrier for the specified transport datum. -/
local instance sectionModule (W : Opens (TopCat.of S)) :
    Module R (T.sheaf.presheaf.obj (op W)) :=
  T.instModuleSections R W

/-- A linear family on a dense open has a unique extension characterized by
its coefficient values when those values extend locally across facets.
The complement of the facet domain may lie in countably many affine subspaces
of codimension at least two. -/
theorem existsUnique_linearMap_extension_of_facets
    [T.sheaf.HasLocallyBijectivePreconnectedRestrictions]
    (hS : IsOpen S) {κ : Type*} [Countable κ] (Z : κ → AffineSubspace ℝ V)
    (hZ : ∀ j, Module.finrank ℝ (Z j).direction + 1 < Module.finrank ℝ V)
    {B O U : Opens (TopCat.of S)} (hBO : B ≤ O) (hOU : O ≤ U)
    (hdense : (O : Set (TopCat.of S)) ⊆ closure (B : Set (TopCat.of S)))
    (hsing : ∀ x ∈ U, x ∉ O → ∃ j, (x : V) ∈ Z j)
    (H : SemimoduleCat.{max u v} R) (s : H →ₗ[R] T.sheaf.presheaf.obj (op B))
    (hfacet : ∀ x ∈ O, x ∉ B → ∃ (N : Opens (TopCat.of S))
      (t : H →ₗ[R] T.sheaf.presheaf.obj (op N)), x ∈ N ∧
        ∀ a (y : A) (hyN : y.val ∈ N) (hyB : y.val ∈ B),
          T.value (t a) y hyN = T.value (s a) y hyB) :
    ∃! t : H →ₗ[R] T.sheaf.presheaf.obj (op U),
      ∀ a (y : A) (hyB : y.val ∈ B),
        T.value (t a) y ((hBO.trans hOU) hyB) = T.value (s a) y hyB := by
  let e := T.semimoduleSheafObjIso R
  -- Convert local value equations into morphism equations on the overlap.
  have hlocal : ∀ x ∈ O, x ∉ B → ∃ (N : Opens (TopCat.of S))
      (t : H ⟶ (T.semimoduleSheaf R).obj.obj (op N)), x ∈ N ∧
        t ≫ (T.semimoduleSheaf R).obj.map
          (homOfLE (inf_le_left : N ⊓ B ≤ N)).op =
        (SemimoduleCat.ofHom s ≫ (e B).inv) ≫ (T.semimoduleSheaf R).obj.map
          (homOfLE (inf_le_right : N ⊓ B ≤ B)).op := by
    intro x hx hxn
    obtain ⟨N, t, hxN, ht⟩ := hfacet x hx hxn
    let q := (T.restrictionLinearMap R (inf_le_right : N ⊓ B ≤ B)).comp s
    have hq : (SemimoduleCat.ofHom s ≫ (e B).inv) ≫
        (T.semimoduleSheaf R).obj.map (homOfLE inf_le_right).op =
          SemimoduleCat.ofHom q ≫ (e (N ⊓ B)).inv :=
      (T.ofHom_restrict_eq_iff R H inf_le_right s q).mpr rfl
    refine ⟨N, SemimoduleCat.ofHom t ≫ (e N).inv, hxN, ?_⟩
    rw [hq]
    apply (T.ofHom_restrict_eq_iff R H inf_le_left t q).mpr
    apply LinearMap.ext
    intro a
    apply T.section_ext
    intro y hy
    simp only [q, LinearMap.comp_apply, T.value_restrictionLinearMap]
    exact ht a y hy.1 hy.2
  -- Existing Hom-sheaf facet descent supplies existence and uniqueness.
  obtain ⟨t, ht, huniq⟩ := (T.semimoduleSheaf R).existsUnique_hom_extension_of_facets
    (T.exists_isIso_restrictions_semimoduleSheaf R) hS Z hZ hBO hOU hdense hsing H
      (SemimoduleCat.ofHom s ≫ (e B).inv) hlocal
  let result := (t ≫ (e U).hom).hom
  have ht' : SemimoduleCat.ofHom result ≫ (e U).inv = t := by
    simp only [result, SemimoduleCat.ofHom_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hr : (T.restrictionLinearMap R (hBO.trans hOU)).comp result = s :=
    (T.ofHom_restrict_eq_iff R H _ _ _).mp (by rw [ht']; exact ht)
  -- Section extensionality translates the result back to coefficient values.
  refine ⟨result, ?_, fun t' ht' => ?_⟩
  · intro a y hyB
    exact (T.value_restrictionLinearMap R _ (result a) y hyB).symm.trans
      (congrArg (fun z => T.value z y hyB) (LinearMap.congr_fun hr a))
  · have he : (T.restrictionLinearMap R (hBO.trans hOU)).comp t' = s := by
      apply LinearMap.ext
      intro a
      apply T.section_ext
      intro y hyB
      exact (T.value_restrictionLinearMap R _ (t' a) y hyB).trans (ht' a y hyB)
    have hu := congrArg (fun z => z ≫ (e U).hom)
      (huniq (SemimoduleCat.ofHom t' ≫ (e U).inv)
        ((T.ofHom_restrict_eq_iff R H _ _ _).mpr he))
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hu
    exact congrArg SemimoduleCat.Hom.hom hu

end Mei.DenseBasisTransport
