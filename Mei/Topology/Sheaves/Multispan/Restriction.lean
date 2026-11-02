/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.Multispan.Morphism

/-!
# Endpoint restriction of multispan matching families

The original sheaf restrictions give a transformation between the evaluated
incidence diagrams. Applying the existing linear map on sections restricts all
face and chamber values together. These restrictions preserve identities and
composition, commute with coefficient transformations, and preserve coefficient
descent equations for linear matching families.
-/

public section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r w t

namespace CategoryTheory.Limits.MultispanIndex

variable {X : TopCat.{u}} {J : MultispanShape}

section Category

variable {C : Type w} [Category.{t} C] (I : MultispanIndex J (X.Sheaf C))

/-- Restrict every original sheaf object in the incidence diagram. Naturality
is exactly the naturality of the original two face-leg morphisms. -/
noncomputable def sectionsRestriction {U V : Opens X} (hVU : V ≤ U) :
    (I.sectionsIndex U).multispan ⟶ (I.sectionsIndex V).multispan where
  app j := match j with
    | .left b => (I.left b).obj.map (homOfLE hVU).op
    | .right j => (I.right j).obj.map (homOfLE hVU).op
  naturality j k f := by
    cases f with
    | id j => simp only [WalkingMultispan.Hom.id_eq_id, Functor.map_id,
        Category.id_comp, Category.comp_id]
    | fst b => exact ((I.fst b).hom.naturality (homOfLE hVU).op).symm
    | snd b => exact ((I.snd b).hom.naturality (homOfLE hVU).op).symm

/-- The face component is the original face-sheaf restriction. -/
@[simp]
theorem sectionsRestriction_app_left {U V : Opens X} (hVU : V ≤ U) (b : J.L) :
    (I.sectionsRestriction hVU).app (.left b) = (I.left b).obj.map (homOfLE hVU).op := by rfl

/-- The chamber component is the original chamber-sheaf restriction. -/
@[simp]
theorem sectionsRestriction_app_right {U V : Opens X} (hVU : V ≤ U) (j : J.R) :
    (I.sectionsRestriction hVU).app (.right j) = (I.right j).obj.map (homOfLE hVU).op := by rfl

/-- Identity endpoint restriction fixes the evaluated incidence diagram. -/
@[simp]
theorem sectionsRestriction_refl (U : Opens X) :
    I.sectionsRestriction (le_refl U) = 𝟙 (I.sectionsIndex U).multispan := by
  apply NatTrans.ext
  funext j
  cases j <;> simp only [sectionsRestriction_app_left, sectionsRestriction_app_right,
    homOfLE_refl, op_id, Functor.map_id, NatTrans.id_app] <;> rfl

/-- Successive endpoint restrictions give the composite inclusion. -/
@[simp]
theorem sectionsRestriction_comp {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V) :
    I.sectionsRestriction hVU ≫ I.sectionsRestriction hWV =
      I.sectionsRestriction (hWV.trans hVU) := by
  symm
  apply NatTrans.ext
  funext j
  cases j with
  | left b =>
    rw [NatTrans.comp_app, sectionsRestriction_app_left, sectionsRestriction_app_left,
      sectionsRestriction_app_left]
    -- Restate the dependent mapped-index carrier as the original face section object.
    change (I.left b).obj.map (homOfLE (hWV.trans hVU)).op =
      (I.left b).obj.map (homOfLE hVU).op ≫ (I.left b).obj.map (homOfLE hWV).op
    rw [← Functor.map_comp, ← op_comp, homOfLE_comp]
  | right j =>
    rw [NatTrans.comp_app, sectionsRestriction_app_right, sectionsRestriction_app_right,
      sectionsRestriction_app_right]
    -- The same normalization identifies the original chamber section object.
    change (I.right j).obj.map (homOfLE (hWV.trans hVU)).op =
      (I.right j).obj.map (homOfLE hVU).op ≫ (I.right j).obj.map (homOfLE hWV).op
    rw [← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- Restriction commutes with every coefficient transformation of sheaf multispans. -/
theorem sectionsRestriction_naturality {I' : MultispanIndex J (X.Sheaf C)}
    (η : I.multispan ⟶ I'.multispan) {U V : Opens X} (hVU : V ≤ U) :
    I.sectionsRestriction hVU ≫ η.sectionsMultispan V =
      η.sectionsMultispan U ≫ I'.sectionsRestriction hVU := by
  apply NatTrans.ext
  funext j
  cases j with
  | left b =>
    rw [NatTrans.comp_app, NatTrans.comp_app, sectionsRestriction_app_left,
      sectionsRestriction_app_left, NatTrans.sectionsMultispan_app_left,
      NatTrans.sectionsMultispan_app_left]
    exact (η.app (.left b)).hom.naturality (homOfLE hVU).op
  | right j =>
    rw [NatTrans.comp_app, NatTrans.comp_app, sectionsRestriction_app_right,
      sectionsRestriction_app_right, NatTrans.sectionsMultispan_app_right,
      NatTrans.sectionsMultispan_app_right]
    exact (η.app (.right j)).hom.naturality (homOfLE hVU).op

end Category

variable {R : Type r} [Semiring R]
  (I : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R)))

/-- Restrict actual matching sections through the existing linear section map. -/
noncomputable def sectionsRestrict {U V : Opens X} (hVU : V ≤ U) :
    SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan →ₗ[R]
      SemimoduleCat.sectionsSubmodule (I.sectionsIndex V).multispan :=
  SemimoduleCat.sectionsMap (I.sectionsRestriction hVU)

/-- Restricting a matching family restricts its original face value. -/
@[simp]
theorem sectionsRestrict_apply_left {U V : Opens X} (hVU : V ≤ U)
    (s : SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan) (b : J.L) :
    (I.sectionsRestrict hVU s).val (.left b) =
      (I.left b).obj.map (homOfLE hVU).op (s.val (.left b)) := by
  rw [sectionsRestrict, SemimoduleCat.sectionsMap_apply, sectionsRestriction_app_left]
  rfl

/-- Restricting a matching family restricts its original chamber value. -/
@[simp]
theorem sectionsRestrict_apply_right {U V : Opens X} (hVU : V ≤ U)
    (s : SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan) (j : J.R) :
    (I.sectionsRestrict hVU s).val (.right j) =
      (I.right j).obj.map (homOfLE hVU).op (s.val (.right j)) := by
  rw [sectionsRestrict, SemimoduleCat.sectionsMap_apply, sectionsRestriction_app_right]
  rfl

/-- Identity restriction fixes every matching family. -/
@[simp]
theorem sectionsRestrict_refl (U : Opens X) :
    I.sectionsRestrict (le_refl U) = LinearMap.id := by
  rw [sectionsRestrict, sectionsRestriction_refl, SemimoduleCat.sectionsMap_id]

/-- Linear restrictions compose along endpoint inclusions. -/
@[simp]
theorem sectionsRestrict_comp {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V) :
    (I.sectionsRestrict hWV).comp (I.sectionsRestrict hVU) =
      I.sectionsRestrict (hWV.trans hVU) := by
  unfold sectionsRestrict
  rw [← SemimoduleCat.sectionsMap_comp, I.sectionsRestriction_comp hVU hWV]

/-- Coefficient transport and endpoint restriction commute on actual matching families. -/
theorem sectionsRestrict_naturality
    {I' : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R))}
    (η : I.multispan ⟶ I'.multispan) {U V : Opens X} (hVU : V ≤ U) :
    (SemimoduleCat.sectionsMap (η.sectionsMultispan V)).comp (I.sectionsRestrict hVU) =
      (I'.sectionsRestrict hVU).comp
        (SemimoduleCat.sectionsMap (η.sectionsMultispan U)) := by
  simp only [sectionsRestrict, ← SemimoduleCat.sectionsMap_comp, sectionsRestriction_naturality]

/-- A linear coefficient descent remains a descent on every smaller endpoint open. -/
theorem sections_descent_restrict
    {I' : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R))}
    (η : I.multispan ⟶ I'.multispan) {E : Type*} [AddCommMonoid E] [Module R E]
    {U V : Opens X} (hVU : V ≤ U)
    (ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan)
    (m : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I'.sectionsIndex U).multispan)
    (hℓ : (SemimoduleCat.sectionsMap (η.sectionsMultispan U)).comp ℓ = m) :
    (SemimoduleCat.sectionsMap (η.sectionsMultispan V)).comp
        ((I.sectionsRestrict hVU).comp ℓ) =
      (I'.sectionsRestrict hVU).comp m := by
  rw [← LinearMap.comp_assoc, sectionsRestrict_naturality, LinearMap.comp_assoc, hℓ]

end CategoryTheory.Limits.MultispanIndex
