/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.Multispan

/-!
# Evaluating morphisms of sheaf multispans

A natural transformation of sheaf incidence diagrams induces a natural
transformation of their original section diagrams on every open.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w

namespace CategoryTheory.NatTrans

variable {X : TopCat.{u}} {C : Type w} [Category.{v} C] {J : MultispanShape}
  {I I' : MultispanIndex J (X.Sheaf C)} (η : I.multispan ⟶ I'.multispan) (U : Opens X)

/-- Evaluate a coefficient change on an endpoint open, using the canonical
comparison between a mapped multispan and its functor composition. -/
noncomputable def sectionsMultispan :
    (I.sectionsIndex U).multispan ⟶ (I'.sectionsIndex U).multispan :=
  (I.multispanMapIso ((sheafSections (Opens.grothendieckTopology X) C).obj (op U))).hom ≫
    Functor.whiskerRight η ((sheafSections (Opens.grothendieckTopology X) C).obj (op U)) ≫
      (I'.multispanMapIso ((sheafSections (Opens.grothendieckTopology X) C).obj (op U))).inv

/-- The face component is the original coefficient morphism evaluated on the open. -/
@[simp]
theorem sectionsMultispan_app_left (b : J.L) :
    (η.sectionsMultispan U).app (.left b) = (η.app (.left b)).hom.app (op U) := by
  simp only [sectionsMultispan, NatTrans.comp_app]
  rw [I.multispanMapIso_hom_app
      ((sheafSections (Opens.grothendieckTopology X) C).obj (op U)) (.left b),
    I'.multispanMapIso_inv_app
      ((sheafSections (Opens.grothendieckTopology X) C).obj (op U)) (.left b)]
  simp only [Iso.refl_hom, Iso.refl_inv]
  -- The canonical comparison components are identities; evaluation is the
  -- original presheaf component, so only the two identity compositions remain.
  change 𝟙 _ ≫ (η.app (.left b)).hom.app (op U) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- The chamber component is the original coefficient morphism evaluated on the open. -/
@[simp]
theorem sectionsMultispan_app_right (j : J.R) :
    (η.sectionsMultispan U).app (.right j) = (η.app (.right j)).hom.app (op U) := by
  simp only [sectionsMultispan, NatTrans.comp_app]
  rw [I.multispanMapIso_hom_app
      ((sheafSections (Opens.grothendieckTopology X) C).obj (op U)) (.right j),
    I'.multispanMapIso_inv_app
      ((sheafSections (Opens.grothendieckTopology X) C).obj (op U)) (.right j)]
  simp only [Iso.refl_hom, Iso.refl_inv]
  -- As for the face component, evaluation retains the original chamber map.
  change 𝟙 _ ≫ (η.app (.right j)).hom.app (op U) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

end CategoryTheory.NatTrans
