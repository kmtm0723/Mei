/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Multispan
public import Mathlib.Logic.Relation

/-!
# Matching families under subdivisions with identity faces

A subdivision copies the chambers and faces of an incidence diagram and adds
identity faces between chamber copies. If those identity faces connect the copies
of each chamber, matching families descend uniquely. Joint injectivity of the
original face spans determines all copied face values. Individual incidence maps
need not be injective, and the index sets may be infinite.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.MultispanShape

universe w

/-- Copies of chambers and faces, with additional identity faces inside each chamber. -/
structure Subdivision (J : MultispanShape) where
  /-- Copies of each original chamber. -/
  chambers : J.R → Type w
  /-- Copies of each original face. -/
  faces : J.L → Type w
  /-- The source chamber copy incident to a copied original face. -/
  source : ∀ b, faces b → chambers (J.fst b)
  /-- The target chamber copy incident to a copied original face. -/
  target : ∀ b, faces b → chambers (J.snd b)
  /-- The new identity faces inside each original chamber. -/
  edges : J.R → Type w
  /-- Source of an identity face. -/
  edgeSource : ∀ j, edges j → chambers j
  /-- Target of an identity face. -/
  edgeTarget : ∀ j, edges j → chambers j

namespace Subdivision

variable {J : MultispanShape} (D : Subdivision J)

/-- The refined incidence shape, retaining copied faces and added identity faces. -/
abbrev shape : MultispanShape where
  L := (Σ b, D.faces b) ⊕ (Σ j, D.edges j)
  R := Σ j, D.chambers j
  fst
    | .inl ⟨b, c⟩ => ⟨J.fst b, D.source b c⟩
    | .inr ⟨j, e⟩ => ⟨j, D.edgeSource j e⟩
  snd
    | .inl ⟨b, c⟩ => ⟨J.snd b, D.target b c⟩
    | .inr ⟨j, e⟩ => ⟨j, D.edgeTarget j e⟩

/-- Forget the copied indices and send each identity face to its old chamber. -/
def projection : WalkingMultispan D.shape ⥤ WalkingMultispan J where
  obj
    | .left (.inl ⟨b, _⟩) => .left b
    | .left (.inr ⟨j, _⟩) => .right j
    | .right ⟨j, _⟩ => .right j
  map {x y} f := by
    cases f with
    | id x => exact 𝟙 _
    | fst b =>
      rcases b with (⟨b, c⟩ | ⟨j, e⟩)
      · exact WalkingMultispan.Hom.fst b
      · exact 𝟙 _
    | snd b =>
      rcases b with (⟨b, c⟩ | ⟨j, e⟩)
      · exact WalkingMultispan.Hom.snd b
      · exact 𝟙 _
  map_id := by rintro (_ | _) <;> rfl
  map_comp := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) <;> cat_disch

/-- Two copies joined by an identity face, with the displayed orientation. -/
def edgeRel (j : J.R) (a b : D.chambers j) : Prop :=
  ∃ e, D.edgeSource j e = a ∧ D.edgeTarget j e = b

/-- The generating relation consists precisely of the displayed identity-face endpoints. -/
theorem edgeRel_iff (j : J.R) (a b : D.chambers j) :
    D.edgeRel j a b ↔ ∃ e, D.edgeSource j e = a ∧ D.edgeTarget j e = b := Iff.rfl

variable {R : Type*} [Semiring R] (I : MultispanIndex J (SemimoduleCat R))

/-- The refined coefficient diagram copies original spans and uses identity spans
at the new internal faces. -/
@[expose]
def index : MultispanIndex D.shape (SemimoduleCat R) where
  left
    | .inl ⟨b, _⟩ => I.left b
    | .inr ⟨j, _⟩ => I.right j
  right j := I.right j.1
  fst
    | .inl ⟨b, _⟩ => I.fst b
    | .inr ⟨_, _⟩ => 𝟙 _
  snd
    | .inl ⟨b, _⟩ => I.snd b
    | .inr ⟨_, _⟩ => 𝟙 _

/-- The refined coefficient diagram is the pullback along the incidence projection. -/
def multispanIso : (D.index I).multispan ≅ D.projection ⋙ I.multispan :=
  WalkingMultispan.functorExt
    (fun b => by rcases b with (⟨b, c⟩ | ⟨j, e⟩) <;> exact Iso.refl _)
    (fun j => Iso.refl _)
    (by rintro (⟨b, c⟩ | ⟨j, e⟩) <;> rfl)
    (by rintro (⟨b, c⟩ | ⟨j, e⟩) <;> rfl)

/-- Copied chamber coefficients are unchanged. -/
@[simp]
theorem index_right (j : J.R) (a : D.chambers j) :
    (D.index I).right ⟨j, a⟩ = I.right j := (rfl)

/-- A copied face has the original source incidence. -/
@[simp]
theorem index_fst_copy (b : J.L) (a : D.faces b) :
    (D.index I).fst (.inl ⟨b, a⟩) = I.fst b := (rfl)

/-- A copied face has the original target incidence. -/
@[simp]
theorem index_snd_copy (b : J.L) (a : D.faces b) :
    (D.index I).snd (.inl ⟨b, a⟩) = I.snd b := (rfl)

/-- An internal identity face has identity source incidence. -/
@[simp]
theorem index_fst_edge (j : J.R) (e : D.edges j) :
    (D.index I).fst (.inr ⟨j, e⟩) = 𝟙 (I.right j) := (rfl)

/-- An internal identity face has identity target incidence. -/
@[simp]
theorem index_snd_edge (j : J.R) (e : D.edges j) :
    (D.index I).snd (.inr ⟨j, e⟩) = 𝟙 (I.right j) := (rfl)

/-- A compatible chamber family pulls back by giving every copy the old value. -/
def compatibleMap : I.compatibleFamilies →ₗ[R] (D.index I).compatibleFamilies where
  toFun x := ⟨fun j => x.val j.1, by
    apply (D.index I).mem_compatibleFamilies.mpr
    rintro (⟨b, c⟩ | ⟨j, e⟩)
    · exact I.mem_compatibleFamilies.mp x.property b
    · exact ⟨x.val j, rfl, rfl⟩⟩
  map_add' _ _ := by ext j; rfl
  map_smul' _ _ := by ext j; rfl

/-- Pullback reads the original value at every chamber copy. -/
@[simp]
theorem compatibleMap_apply (x : I.compatibleFamilies) (j : J.R) (a : D.chambers j) :
    (D.compatibleMap I x).val ⟨j, a⟩ = x.val j := (rfl)

/-- Compatibility at identity faces makes values constant along their equivalence closure. -/
theorem eq_of_eqvGen_edgeRel (x : (D.index I).compatibleFamilies) (j : J.R)
    {a b : D.chambers j} (hab : Relation.EqvGen (D.edgeRel j) a b) :
    x.val ⟨j, a⟩ = x.val ⟨j, b⟩ := by
  induction hab with
  | rel a b h =>
    obtain ⟨e, rfl, rfl⟩ := h
    obtain ⟨z, hs, ht⟩ := (D.index I).mem_compatibleFamilies.mp x.property (.inr ⟨j, e⟩)
    exact hs.symm.trans ht
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hab hbc => exact hab.trans hbc

/-- Restrict an original matching section to the copied objects and identity faces. -/
def restrictSections : SemimoduleCat.sectionsSubmodule I.multispan →ₗ[R]
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
theorem restrictSections_apply_right (s : SemimoduleCat.sectionsSubmodule I.multispan)
    (j : J.R) (a : D.chambers j) :
    (D.restrictSections I s).val (.right ⟨j, a⟩) = s.val (.right j) := (rfl)

/-- Restriction preserves each copied original face value. -/
@[simp]
theorem restrictSections_apply_copy (s : SemimoduleCat.sectionsSubmodule I.multispan)
    (b : J.L) (a : D.faces b) :
    (D.restrictSections I s).val (.left (.inl ⟨b, a⟩)) = s.val (.left b) := (rfl)

/-- An identity face receives the old chamber value. -/
@[simp]
theorem restrictSections_apply_edge (s : SemimoduleCat.sectionsSubmodule I.multispan)
    (j : J.R) (e : D.edges j) :
    (D.restrictSections I s).val (.left (.inr ⟨j, e⟩)) = s.val (.right j) := (rfl)

variable [∀ j, Nonempty (D.chambers j)]

/-- Pullback is injective if every original chamber has at least one copy. -/
theorem compatibleMap_injective : Function.Injective (D.compatibleMap I) := by
  classical
  intro x y h
  apply Subtype.ext
  funext j
  exact congrArg (fun z => z.val ⟨j, Classical.choice inferInstance⟩) h

/-- If every original face has a copy and each chamber's identity-face graph is
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
  exact (hconst j b).symm

/-- Connected subdivisions preserve compatible chamber families as semimodules. -/
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

omit [∀ j, Nonempty (D.chambers j)] in
/-- Copied face spans and identity face spans remain jointly injective. -/
theorem index_jointly_injective
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    ∀ b, Function.Injective (((D.index I).fst b).hom.prod ((D.index I).snd b).hom) := by
  rintro (⟨b, c⟩ | ⟨j, e⟩)
  · exact hinj b
  · intro x y h
    exact congrArg _root_.Prod.fst h

/-- Matching sections are unchanged by connected subdivisions with identity faces. -/
noncomputable def sectionsEquiv [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    SemimoduleCat.sectionsSubmodule I.multispan ≃ₗ[R]
      SemimoduleCat.sectionsSubmodule (D.index I).multispan :=
  (I.matchingFamilyEquiv hinj).trans
    ((D.compatibleEquiv I hc).trans
      ((D.index I).matchingFamilyEquiv (D.index_jointly_injective I hinj)).symm)

/-- The section comparison restricts to pullback of the chamber values. -/
@[simp]
theorem sectionsEquiv_apply_right [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule I.multispan) (j : J.R) (a : D.chambers j) :
    (D.sectionsEquiv I hc hinj s).val (.right ⟨j, a⟩) = s.val (.right j) := by
  simp only [sectionsEquiv, LinearEquiv.trans_apply]
  rw [MultispanIndex.matchingFamilyEquiv_symm_apply_right]
  rw [compatibleEquiv_apply, compatibleMap_apply]
  exact (congrArg (fun x : I.compatibleFamilies => x.val j)
    (I.matchingFamilyEquiv_apply hinj s)).trans (I.restrictSections_apply s j)

/-- The subdivision equivalence is the actual restriction map on matching families. -/
theorem sectionsEquiv_toLinearMap [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    (D.sectionsEquiv I hc hinj).toLinearMap = D.restrictSections I := by
  ext s : 1
  apply (D.index I).restrictSections_injective (D.index_jointly_injective I hinj)
  ext ⟨j, a⟩
  rw [MultispanIndex.restrictSections_apply, MultispanIndex.restrictSections_apply]
  exact (D.sectionsEquiv_apply_right I hc hinj s j a).trans
    (D.restrictSections_apply_right I s j a).symm

/-- Subdivision preserves the original value at each copied face. -/
@[simp]
theorem sectionsEquiv_apply_copy [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule I.multispan) (b : J.L) (a : D.faces b) :
    (D.sectionsEquiv I hc hinj s).val (.left (.inl ⟨b, a⟩)) = s.val (.left b) := by
  have he := LinearMap.congr_fun (D.sectionsEquiv_toLinearMap I hc hinj) s
  exact (congrArg (fun t => t.val (.left (.inl ⟨b, a⟩))) he).trans
    (D.restrictSections_apply_copy I s b a)

/-- Each new identity face receives the original chamber coefficient. -/
@[simp]
theorem sectionsEquiv_apply_edge [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule I.multispan) (j : J.R) (e : D.edges j) :
    (D.sectionsEquiv I hc hinj s).val (.left (.inr ⟨j, e⟩)) = s.val (.right j) := by
  have he := LinearMap.congr_fun (D.sectionsEquiv_toLinearMap I hc hinj) s
  exact (congrArg (fun t => t.val (.left (.inr ⟨j, e⟩))) he).trans
    (D.restrictSections_apply_edge I s j e)

/-- The inverse comparison reconstructs the unique old matching section. -/
@[simp]
theorem restrictSections_sectionsEquiv_symm [∀ b, Nonempty (D.faces b)]
    (hc : ∀ j a b, Relation.EqvGen (D.edgeRel j) a b)
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule (D.index I).multispan) :
    D.restrictSections I ((D.sectionsEquiv I hc hinj).symm s) = s := by
  rw [← sectionsEquiv_toLinearMap D I hc hinj]
  exact (D.sectionsEquiv I hc hinj).apply_symm_apply s

end Subdivision
end CategoryTheory.Limits.MultispanShape
