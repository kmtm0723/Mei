/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.CategoryTheory.Grothendieck.TransportSection
public import Mei.CategoryTheory.Grothendieck.Pullback
public import Mathlib.CategoryTheory.Equivalence

/-!
# Transport presentations of sections

The transport presentation of a section is equivalent to the category of actual
sections of the Grothendieck projection. The comparison works for arbitrary
category-valued diagrams, including noninvertible transport arrows.

`ofSection` extracts transport data using `Grothendieck.liftFunctor` over the
identity base. `fromSectionHom` extracts vertical components, and its two
reconstruction equations identify the original comparison as fully faithful.
Together with object reconstruction this yields `sectionEquivalence` through
Mathlib's existing equivalence constructor.

For groupoid fibers, `sectionAutEquiv` transfers the existing compatible-family
description of transport automorphisms to automorphisms of actual sections.
-/

public section

open CategoryTheory

universe v u w z

namespace Mei.GrothendieckSection

variable {D : Type u} [Category.{v} D] {L : D ⥤ Cat.{w, z}}

/-- Normalize the base components of an actual section using the existing base lift. -/
abbrev normalized (s : CategoryTheory.Grothendieck.Section L) : D ⥤ Grothendieck L :=
  Grothendieck.liftFunctor (𝟭 D) s.toFunctor s.toFunctor_comp_forget

/-- Transport data extracted from an actual section. -/
def ofSection (s : CategoryTheory.Grothendieck.Section L) : GrothendieckSection L where
  obj d := (normalized s).obj d |>.fiber
  map f := Grothendieck.fiberHom ((normalized s).map f) f
    (Grothendieck.liftHom_base _ _ _ _ _ _)
  map_id d := by
    have h := (Grothendieck.mk_fiberHom ((normalized s).map (𝟙 d)) (𝟙 d)
      (Grothendieck.liftHom_base _ _ _ _ _ _)).trans ((normalized s).map_id d)
    have hf := Grothendieck.congr h
    erw [Grothendieck.id_fiber, eqToHom_trans] at hf
    exact hf
  map_comp f g := by
    have h := (Grothendieck.mk_fiberHom ((normalized s).map (f ≫ g)) (f ≫ g)
      (Grothendieck.liftHom_base _ _ _ _ _ _)).trans ((normalized s).map_comp f g)
    rw [← Grothendieck.mk_fiberHom ((normalized s).map f) f
      (Grothendieck.liftHom_base _ _ _ _ _ _),
      ← Grothendieck.mk_fiberHom ((normalized s).map g) g
        (Grothendieck.liftHom_base _ _ _ _ _ _)] at h
    have hf := Grothendieck.congr h
    erw [Grothendieck.comp_fiber, eqToHom_trans_assoc] at hf
    exact hf

/-- The extracted transport functor is the normalized original functor. -/
@[simp]
theorem ofSection_toFunctor (s : CategoryTheory.Grothendieck.Section L) :
    (ofSection s).toFunctor = normalized s := by
  refine _root_.CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro d e f
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact Grothendieck.mk_fiberHom ((normalized s).map f) f
    (Grothendieck.liftHom_base _ _ _ _ _ _)

/-- Normalizing an actual section preserves its underlying total functor. -/
@[simp]
theorem normalized_eq (s : CategoryTheory.Grothendieck.Section L) :
    normalized s = s.toFunctor := by
  have h := Grothendieck.liftFunctor_comp_pre (𝟭 D) s.toFunctor s.toFunctor_comp_forget
  simpa only [Grothendieck.pre_id, Functor.comp_id] using h

/-- Reassembling the extracted transport data recovers the actual section. -/
@[simp]
theorem ofSection_toSection (s : CategoryTheory.Grothendieck.Section L) :
    (ofSection s).toSection = s := by
  apply CategoryTheory.Functor.Fiber.fiberInclusion_obj_inj
  exact (ofSection_toFunctor s).trans (normalized_eq s)

/-- The underlying transformation of a composite of section morphisms is their composite. -/
theorem sectionHom_comp {s t r : CategoryTheory.Grothendieck.Section L}
    (α : s ⟶ t) (β : t ⟶ r) :
    CategoryTheory.Grothendieck.Section.hom (α ≫ β) =
      CategoryTheory.Grothendieck.Section.hom α ≫
        CategoryTheory.Grothendieck.Section.hom β := (rfl)

/-- A transformation between transport sections has identity base components. -/
theorem sectionHom_base {s t : GrothendieckSection L} (α : s.toSection ⟶ t.toSection) (d : D) :
    ((CategoryTheory.Grothendieck.Section.hom α).app d).base = 𝟙 d := by
  have h := CategoryTheory.Grothendieck.Section.hom_over α
  erw [eqToHom_refl (C := D ⥤ D), Category.id_comp] at h
  exact NatTrans.congr_app h d

/-- The actual section constructed from transport data has the specified total functor. -/
@[simp]
theorem toSection_toFunctor (s : GrothendieckSection L) :
    s.toSection.toFunctor = s.toFunctor := (rfl)

/-- The actual section and its transport presentation have the same arrow components. -/
theorem toSection_toFunctor_map (s : GrothendieckSection L) {d e : D} (f : d ⟶ e) :
    s.toSection.toFunctor.map f = s.toFunctor.map f := (rfl)

/-- An arrow of the total transport functor has its prescribed base and fiber components. -/
theorem toFunctor_map (s : GrothendieckSection L) {d e : D} (f : d ⟶ e) :
    s.toFunctor.map f = ⟨f, s.map f⟩ := (rfl)

/-- The transport arrow factors through the fiber inclusion in the target category. -/
theorem toFunctor_map_factor (s : GrothendieckSection L) {d e : D} (f : d ⟶ e) :
    s.toFunctor.map f =
      (Grothendieck.ιNatTrans f).app (s.obj d) ≫ (Grothendieck.ι L e).map (s.map f) := by
  rw [toFunctor_map]
  exact (Grothendieck.ιNatTrans_app_comp_ι_map
    (⟨f, s.map f⟩ : s.toFunctor.obj d ⟶ s.toFunctor.obj e)).symm

/-- A component of a vertical section morphism, regarded in the actual fiber. -/
def sectionHomComponent {s t : GrothendieckSection L} (α : s.toSection ⟶ t.toSection)
    (d : D) : s.obj d ⟶ t.obj d :=
  Grothendieck.verticalFiber ((CategoryTheory.Grothendieck.Section.hom α).app d)
    (sectionHom_base α d)

/-- Including the extracted component recovers the component of the section morphism. -/
@[simp↓]
theorem ι_map_sectionHomComponent {s t : GrothendieckSection L}
    (α : s.toSection ⟶ t.toSection) (d : D) :
    (Grothendieck.ι L d).map (sectionHomComponent α d) =
      (CategoryTheory.Grothendieck.Section.hom α).app d :=
  Grothendieck.ι_map_verticalFiber _ (sectionHom_base α d)

/-- Naturality of a vertical label after factoring both transport arrows through
the target fiber inclusion. All endpoints are displayed as fiber objects. -/
theorem sectionHom_factorized_naturality {s t : GrothendieckSection L}
    (α : s.toSection ⟶ t.toSection) {d e : D} (f : d ⟶ e) :
    ((Grothendieck.ιNatTrans f).app (s.obj d) ≫ (Grothendieck.ι L e).map (s.map f)) ≫
        (Grothendieck.ι L e).map (sectionHomComponent α e) =
      (Grothendieck.ι L d).map (sectionHomComponent α d) ≫
        (Grothendieck.ιNatTrans f).app (t.obj d) ≫ (Grothendieck.ι L e).map (t.map f) := by
  have h := (CategoryTheory.Grothendieck.Section.hom α).naturality f
  rw [toSection_toFunctor_map, toSection_toFunctor_map,
    ← ι_map_sectionHomComponent α d, ← ι_map_sectionHomComponent α e,
    toFunctor_map_factor, toFunctor_map_factor] at h
  -- The component equations identify the arrows. `Section.hom` still stores
  -- their endpoints through the fiber inclusion; default transparency identifies
  -- these with the explicit Grothendieck object constructors in the statement.
  exact h

/-- The fiber components of a vertical transformation between transport sections. -/
def fromSectionHom {s t : GrothendieckSection L} (α : s.toSection ⟶ t.toSection) : s ⟶ t where
  app := sectionHomComponent α
  naturality {d e} f := by
    have h := sectionHom_factorized_naturality α f
    rw [Category.assoc, (Grothendieck.ιNatTrans f).naturality_assoc (sectionHomComponent α d),
      Functor.comp_map,
      ← Functor.map_comp, ← Functor.map_comp] at h
    rw [Grothendieck.ιNatTrans_app_comp_ι_map
      (⟨f, s.map f ≫ sectionHomComponent α e⟩ : s.toFunctor.obj d ⟶ t.toFunctor.obj e),
      Grothendieck.ιNatTrans_app_comp_ι_map
        (⟨f, (L.map f).toFunctor.map (sectionHomComponent α d) ≫ t.map f⟩ :
          s.toFunctor.obj d ⟶ t.toFunctor.obj e)] at h
    have hf := Grothendieck.congr h
    erw [eqToHom_refl, Category.id_comp] at hf
    exact hf.symm

/-- Extraction is computed by the vertical component in the fiber. -/
@[simp]
theorem fromSectionHom_app {s t : GrothendieckSection L}
    (α : s.toSection ⟶ t.toSection) (d : D) :
    (fromSectionHom α).app d = sectionHomComponent α d := (rfl)

/-- Reassembling the fiber components of a vertical transformation recovers it. -/
@[simp]
theorem toSectionHom_fromSectionHom {s t : GrothendieckSection L}
    (α : s.toSection ⟶ t.toSection) : toSectionHom (fromSectionHom α) = α := by
  apply CategoryTheory.Grothendieck.Section.hom_ext
  intro d
  rw [hom_toSectionHom, toNatTrans_app]
  exact Grothendieck.ι_map_verticalFiber _ (sectionHom_base α d)

instance : (sectionFunctor (L := L)).Faithful where
  map_injective {s t} α β h := by
    apply Hom.ext
    funext d
    apply (Grothendieck.ι L d).map_injective
    have hd := congrArg (fun γ => (CategoryTheory.Grothendieck.Section.hom γ).app d) h
    rw [sectionFunctor_map, sectionFunctor_map, hom_toSectionHom, hom_toSectionHom,
      toNatTrans_app, toNatTrans_app] at hd
    exact hd

instance : (sectionFunctor (L := L)).Full where
  map_surjective α := ⟨fromSectionHom α, toSectionHom_fromSectionHom α⟩

/-- Extracting the components of a transport morphism recovers that morphism. -/
@[simp]
theorem fromSectionHom_toSectionHom {s t : GrothendieckSection L} (α : s ⟶ t) :
    fromSectionHom (toSectionHom α) = α := by
  apply (sectionFunctor (L := L)).map_injective
  exact toSectionHom_fromSectionHom (toSectionHom α)

instance : (sectionFunctor (L := L)).EssSurj :=
  _root_.CategoryTheory.Functor.essSurj_of_surj (fun s => ⟨ofSection s, ofSection_toSection s⟩)

instance : (sectionFunctor (L := L)).IsEquivalence where

/-- Fiberwise transport data and actual sections of the Grothendieck projection
are equivalent categories, without an invertibility hypothesis on transport. -/
noncomputable def sectionEquivalence :
    GrothendieckSection L ≌ CategoryTheory.Grothendieck.Section L :=
  sectionFunctor.asEquivalence

/-- The comparison equivalence uses the original transport-to-section functor. -/
@[simp]
theorem sectionEquivalence_functor : (sectionEquivalence (L := L)).functor = sectionFunctor := (rfl)

/-- The fully faithful comparison extracts the vertical components of a section morphism. -/
@[simp]
theorem sectionFunctor_preimage {s t : GrothendieckSection L}
    (α : s.toSection ⟶ t.toSection) :
    (sectionFunctor (L := L)).preimage α = fromSectionHom α := by
  apply (sectionFunctor (L := L)).map_injective
  rw [Functor.map_preimage, sectionFunctor_map, toSectionHom_fromSectionHom]

/-- Automorphisms of an actual section are compatible families of fiber
automorphisms, with conjugation by the extracted transport maps. -/
noncomputable def sectionAutEquiv [∀ d, IsGroupoid (L.obj d)]
    (s : CategoryTheory.Grothendieck.Section L) :
    Aut s ≃* GrpCat.sectionsSubgroup (ofSection s).automorphismDiagram :=
  (Aut.autMulEquivOfIso (eqToIso (ofSection_toSection s).symm)).trans
    ((_root_.CategoryTheory.Functor.FullyFaithful.autMulEquivOfFullyFaithful
      (.ofFullyFaithful sectionFunctor) (ofSection s)).symm.trans
        (autEquivSections (ofSection s)))

/-- The compatible-family component is the vertical part of the original section
morphism, transported along object reconstruction. -/
@[simp]
theorem sectionAutEquiv_apply_hom [∀ d, IsGroupoid (L.obj d)]
    (s : CategoryTheory.Grothendieck.Section L) (a : Aut s) (d : D) :
    ((sectionAutEquiv s a).val d).asIso.hom =
      (fromSectionHom (eqToHom (ofSection_toSection s) ≫ a.asIso.hom ≫
        eqToHom (ofSection_toSection s).symm)).app d := by
  have heval (b : Aut (ofSection s)) :
      ((evaluation d).mapAut _ b).asIso.hom = b.asIso.hom.app d := (rfl)
  simp only [sectionAutEquiv, MulEquiv.trans_apply, autEquivSections_apply, heval]
  -- The comparison functors store their object endpoints through fiber inclusions.
  -- Default transparency aligns those endpoints for Mathlib's component formula.
  erw [_root_.CategoryTheory.Functor.FullyFaithful.autMulEquivOfFullyFaithful_symm_apply_asIso_hom]
  simp [_root_.CategoryTheory.Functor.FullyFaithful.ofFullyFaithful]

/-- Including a compatible-family component recovers the original total component
under the canonical reconstruction of its section. -/
@[simp↓]
theorem ι_map_sectionAutEquiv_apply_hom [∀ d, IsGroupoid (L.obj d)]
    (s : CategoryTheory.Grothendieck.Section L) (a : Aut s) (d : D) :
    (Grothendieck.ι L d).map (((sectionAutEquiv s a).val d).asIso.hom) =
      (CategoryTheory.Grothendieck.Section.hom
        (eqToHom (ofSection_toSection s) ≫ a.asIso.hom ≫
          eqToHom (ofSection_toSection s).symm)).app d := by
  rw [sectionAutEquiv_apply_hom, fromSectionHom_app, ι_map_sectionHomComponent]

/-- The inverse comparison includes the chosen family component, transported
back from the extracted section along object reconstruction. -/
@[simp]
theorem sectionAutEquiv_symm_apply_hom [∀ d, IsGroupoid (L.obj d)]
    (s : CategoryTheory.Grothendieck.Section L)
    (a : GrpCat.sectionsSubgroup (ofSection s).automorphismDiagram) (d : D) :
    (CategoryTheory.Grothendieck.Section.hom
      (((sectionAutEquiv s).symm a).asIso.hom)).app d =
      (CategoryTheory.Grothendieck.Section.hom
        (eqToHom (ofSection_toSection s).symm)).app d ≫
      (Grothendieck.ι L d).map ((a.val d).asIso.hom) ≫
      (CategoryTheory.Grothendieck.Section.hom
        (eqToHom (ofSection_toSection s))).app d := by
  have hconj (b : Aut (ofSection s).toSection) :
      ((Aut.autMulEquivOfIso (eqToIso (ofSection_toSection s).symm)).symm b).asIso.hom =
        (eqToHom (ofSection_toSection s).symm ≫ b.asIso.hom) ≫
          eqToHom (ofSection_toSection s) := by
    simp [Aut.autMulEquivOfIso, Category.assoc]
  simp only [sectionAutEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  rw [hconj]
  -- Object reconstruction identifies endpoints through the section fiber inclusion;
  -- default transparency aligns these endpoints before applying the public formula.
  erw [_root_.CategoryTheory.Functor.FullyFaithful.autMulEquivOfFullyFaithful_apply_asIso_hom]
  simp only [sectionHom_comp, NatTrans.comp_app]
  erw [hom_toSectionHom, toNatTrans_app,
    autEquivSections_symm_apply_hom, Category.assoc]
  rfl

end Mei.GrothendieckSection
