/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Multispan.Basic
public import Mei.CategoryTheory.Limits.Multispan.Subdivision
public import Mathlib.Logic.Relation

/-!
# Matching families under subdivisions with identity faces

A subdivision copies chambers and faces and adds identity faces between chamber
copies. Provided every chamber and face has at least one copy and the identity
faces connect each chamber's copies, compatible chamber families descend uniquely.
If the original face spans are jointly injective, this gives an equivalence of
matching sections. Individual incidence maps need not be injective and the index
sets may be infinite.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.MultispanShape.Subdivision

universe r m

variable {J : MultispanShape} (D : Subdivision J)
  {R : Type r} [Semiring R] (I : MultispanIndex J (SemimoduleCat.{m} R))

/-- A compatible chamber family pulls back by giving every copy the old value. -/
def compatibleMap : I.compatibleFamilies →ₗ[R] (D.index I).compatibleFamilies :=
  (D.index I).piCompatibleFamilies
    (fun j => LinearMap.proj j.1 ∘ₗ I.compatibleFamilies.subtype) (by
      intro x b
      rcases b with (⟨b, a⟩ | ⟨j, e⟩)
      · exact I.mem_compatibleFamilies_iff_forall_mem_range.mp x.property b
      · refine ⟨x.val j, ?_⟩
        simp only [SemimoduleCat.hom_id, LinearMap.prod_apply, Function.prod_apply,
          LinearMap.id_apply, LinearMap.comp_apply, LinearMap.proj_apply,
          Submodule.subtype_apply])

/-- Pullback reads the original value at every chamber copy. -/
@[simp]
theorem compatibleMap_apply (x : I.compatibleFamilies) (j : J.R) (a : D.chambers j) :
    (D.compatibleMap I x).val ⟨j, a⟩ = x.val j := by
  -- The copied coefficient objects agree definitionally across the generic index.
  dsimp only [compatibleMap]
  erw [MultispanIndex.piCompatibleFamilies_apply]
  rfl

/-- Compatibility at identity faces makes values constant along their equivalence closure. -/
theorem eq_of_eqvGen_edgeRel (x : (D.index I).compatibleFamilies) (j : J.R)
    {a b : D.chambers j} (hab : Relation.EqvGen (D.edgeRel j) a b) :
    x.val ⟨j, a⟩ = x.val ⟨j, b⟩ := by
  let f : D.chambers j → I.right j := fun c => x.val ⟨j, c⟩
  have h' : Relation.EqvGen (InvImage Eq f) a b := by
    apply Relation.EqvGen.mono (fun a b h => ?_) a b hab
    simp only [edgeRel] at h
    obtain ⟨e, rfl, rfl⟩ := h
    obtain ⟨z, hs, ht⟩ := (D.index I).mem_compatibleFamilies.mp x.property (.inr ⟨j, e⟩)
    simp only [SemimoduleCat.hom_id, LinearMap.id_apply] at hs ht
    exact hs.symm.trans ht
  exact (InvImage.equivalence Eq f eq_equivalence).eqvGen_iff.mp h'

/-- Restrict an original matching section to the copied objects and identity faces. -/
def sectionsPullback : SemimoduleCat.sectionsSubmodule I.multispan →ₗ[R]
    SemimoduleCat.sectionsSubmodule (D.index I).multispan where
  toFun s := ⟨fun j => match j with
    | .left (.inl ⟨b, _⟩) => s.val (.left b)
    | .left (.inr ⟨j, _⟩) => s.val (.right j)
    | .right ⟨j, _⟩ => s.val (.right j), by
      apply (D.index I).mem_sectionsSubmodule_multispan.mpr
      constructor <;> rintro (⟨b, c⟩ | ⟨j, e⟩)
      · exact (SemimoduleCat.mem_sectionsSubmodule.mp s.property) (.fst b)
      · rfl
      · exact (SemimoduleCat.mem_sectionsSubmodule.mp s.property) (.snd b)
      · rfl⟩
  map_add' _ _ := by ext j; cases j with
    | left b => cases b <;> rfl
    | right j => rfl
  map_smul' _ _ := by ext j; cases j with
    | left b => cases b <;> rfl
    | right j => rfl

/-- Restriction preserves the value at every chamber copy. -/
@[simp]
theorem sectionsPullback_apply_right (s : SemimoduleCat.sectionsSubmodule I.multispan)
    (j : J.R) (a : D.chambers j) :
    (D.sectionsPullback I s).val (.right ⟨j, a⟩) = s.val (.right j) := (rfl)

/-- Restriction preserves each copied original face value. -/
@[simp]
theorem sectionsPullback_apply_copy (s : SemimoduleCat.sectionsSubmodule I.multispan)
    (b : J.L) (a : D.faces b) :
    (D.sectionsPullback I s).val (.left (.inl ⟨b, a⟩)) = s.val (.left b) := (rfl)

/-- An identity face receives the old chamber value. -/
@[simp]
theorem sectionsPullback_apply_edge (s : SemimoduleCat.sectionsSubmodule I.multispan)
    (j : J.R) (e : D.edges j) :
    (D.sectionsPullback I s).val (.left (.inr ⟨j, e⟩)) = s.val (.right j) := (rfl)

variable [∀ j, Nonempty (D.chambers j)]

/-- Pullback is injective if every original chamber has at least one copy. -/
theorem compatibleMap_injective : Function.Injective (D.compatibleMap I) := by
  classical
  intro x y h
  apply Subtype.ext
  funext j
  have he := congrArg (fun z => z.val ⟨j, Classical.choice inferInstance⟩) h
  erw [compatibleMap_apply, compatibleMap_apply] at he
  exact he

/-- If every original chamber and face has a copy and each chamber's identity-face graph is
connected, every compatible refined family descends to a compatible original family. -/
theorem compatibleMap_surjective [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b) :
    Function.Surjective (D.compatibleMap I) := by
  classical
  intro y
  let a (j : J.R) : D.chambers j := Classical.choice inferInstance
  have hconst (j : J.R) (b : D.chambers j) : y.val ⟨j, b⟩ = y.val ⟨j, a j⟩ :=
    D.eq_of_eqvGen_edgeRel I y j (hc j b (a j))
  let x : I.compatibleFamilies := ⟨fun j => y.val ⟨j, a j⟩, by
    apply I.mem_compatibleFamilies.mpr
    intro b
    let c : D.faces b := Classical.choice inferInstance
    obtain ⟨z, hs, ht⟩ := (D.index I).mem_compatibleFamilies.mp y.property (.inl ⟨b, c⟩)
    exact ⟨z, hs.trans (hconst _ _), ht.trans (hconst _ _)⟩⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext ⟨j, b⟩
  erw [compatibleMap_apply]
  exact (hconst j b).symm

/-- If every chamber and face has a copy and each chamber's identity-face graph is
connected, compatible chamber families are linearly equivalent before and after subdivision. -/
noncomputable def compatibleEquiv [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b) :
    I.compatibleFamilies ≃ₗ[R] (D.index I).compatibleFamilies :=
  LinearEquiv.ofBijective (D.compatibleMap I)
    ⟨D.compatibleMap_injective I, D.compatibleMap_surjective I hc⟩

/-- The comparison equivalence is the canonical chamber pullback. -/
@[simp]
theorem compatibleEquiv_apply [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b) (x : I.compatibleFamilies) :
    D.compatibleEquiv I hc x = D.compatibleMap I x := (rfl)

/-- Descending a refined family recovers its value at every copy of each chamber. -/
theorem compatibleEquiv_symm_apply [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (y : (D.index I).compatibleFamilies) (j : J.R) (a : D.chambers j) :
    ((D.compatibleEquiv I hc).symm y).val j = y.val ⟨j, a⟩ := by
  have he := congrArg (fun z : (D.index I).compatibleFamilies => z.val ⟨j, a⟩)
    ((D.compatibleEquiv I hc).apply_symm_apply y)
  erw [compatibleEquiv_apply, compatibleMap_apply] at he
  exact he

omit [∀ j, Nonempty (D.chambers j)] in
/-- Copied face spans and identity face spans remain jointly injective. -/
theorem index_jointly_injective
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    ∀ b, Function.Injective (((D.index I).fst b).hom.prod ((D.index I).snd b).hom) := by
  rintro (⟨b, c⟩ | ⟨j, e⟩)
  · exact hinj b
  · intro x y h
    simpa only [index_fst_edge, SemimoduleCat.hom_id, LinearMap.prod_apply, Function.prod_apply,
      LinearMap.id_apply] using congrArg _root_.Prod.fst h

/-- Pullback is injective if every chamber has a copy and the old face spans are
jointly injective. -/
theorem sectionsPullback_injective
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    Function.Injective (D.sectionsPullback I) := by
  classical
  intro s t h
  apply I.restrictSections_injective hinj
  ext j
  simpa only [MultispanIndex.multispan_obj_right, index_right,
    MultispanIndex.restrictSections_apply, sectionsPullback_apply_right] using
    congrArg (fun z : SemimoduleCat.sectionsSubmodule (D.index I).multispan =>
      z.val (.right ⟨j, Classical.choice inferInstance⟩)) h

/-- If every chamber and face has a copy, the identity graphs are connected and old face
spans are jointly injective, every refined matching section descends. -/
theorem sectionsPullback_surjective [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    Function.Surjective (D.sectionsPullback I) := by
  intro y
  obtain ⟨x, hx⟩ := D.compatibleMap_surjective I hc ((D.index I).restrictSections y)
  obtain ⟨s, hs⟩ := I.restrictSections_surjective x
  refine ⟨s, ?_⟩
  apply (D.index I).restrictSections_injective (D.index_jointly_injective I hinj)
  ext ⟨j, a⟩
  have hx' : x.val j = y.val (.right ⟨j, a⟩) := by
    have he := congrArg (fun z : (D.index I).compatibleFamilies => z.val ⟨j, a⟩) hx
    erw [compatibleMap_apply, MultispanIndex.restrictSections_apply] at he
    exact he
  erw [MultispanIndex.restrictSections_apply, sectionsPullback_apply_right,
    MultispanIndex.restrictSections_apply]
  have hs' := congrArg (fun z : I.compatibleFamilies => z.val j) hs
  erw [MultispanIndex.restrictSections_apply] at hs'
  exact hs'.trans hx'

/-- If every chamber and face has a copy, each chamber's identity-face graph is connected
and the original face spans are jointly injective, pullback of matching sections is a
linear equivalence. -/
noncomputable def sectionsEquiv [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    SemimoduleCat.sectionsSubmodule I.multispan ≃ₗ[R]
      SemimoduleCat.sectionsSubmodule (D.index I).multispan :=
  LinearEquiv.ofBijective (D.sectionsPullback I)
    ⟨D.sectionsPullback_injective I hinj, D.sectionsPullback_surjective I hc hinj⟩

/-- The section comparison is the actual pullback along the incidence projection. -/
@[simp]
theorem sectionsEquiv_apply [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule I.multispan) :
    D.sectionsEquiv I hc hinj s = D.sectionsPullback I s := (rfl)

/-- Descent recovers each old chamber value from any of its refined copies. -/
theorem sectionsEquiv_symm_apply_right [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule (D.index I).multispan) (j : J.R)
    (a : D.chambers j) :
    ((D.sectionsEquiv I hc hinj).symm s).val (.right j) = s.val (.right ⟨j, a⟩) := by
  simpa only [MultispanIndex.multispan_obj_right, index_right,
    sectionsEquiv_apply, sectionsPullback_apply_right] using
    congrArg (fun z : SemimoduleCat.sectionsSubmodule (D.index I).multispan =>
      z.val (.right ⟨j, a⟩)) ((D.sectionsEquiv I hc hinj).apply_symm_apply s)

end CategoryTheory.Limits.MultispanShape.Subdivision
