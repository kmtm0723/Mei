/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Semi
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Limits.Final.Type
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Matching sections of semimodule diagrams

The matching families of a diagram of semimodules form a submodule of the product of its
objects. This supplies linear operations on matching families without an additive-inverse
hypothesis. The construction follows Mathlib's `ModuleCat.sectionsSubmodule`, using the
same `CategoryTheory.Functor.sections` carrier for semirings and semimodules.
Natural transformations induce linear maps on these matching families, respecting
identity and composition. Their underlying maps are Mathlib section maps.
Index functors restrict sections linearly through Mathlib's `Functor.sectionsPrecomp`.
-/

public section

open CategoryTheory

namespace SemimoduleCat

variable {R : Type*} [Semiring R] {J : Type*} [Category* J]

/-- The submodule of families compatible with every arrow of a semimodule diagram. -/
def sectionsSubmodule (F : J ⥤ SemimoduleCat R) : Submodule R (∀ j, F.obj j) where
  carrier := (F ⋙ forget (SemimoduleCat R)).sections
  zero_mem' := by intro j j' f; exact map_zero (F.map f).hom
  add_mem' := by
    intro x y hx hy j j' f
    exact (map_add (F.map f).hom _ _).trans (congrArg₂ (· + ·) (hx f) (hy f))
  smul_mem' := by
    intro r x hx j j' f
    exact (map_smul (F.map f).hom r _).trans (congrArg (r • ·) (hx f))

section

variable (F : J ⥤ SemimoduleCat R)

/-- The matching-family carrier agrees with Mathlib's sections of the underlying diagram. -/
def sectionsEquivTypes : sectionsSubmodule F ≃ (F ⋙ forget (SemimoduleCat R)).sections :=
  Equiv.refl _

/-- The carrier comparison preserves each component. -/
@[simp]
theorem sectionsEquivTypes_apply (s : sectionsSubmodule F) (j : J) :
    (sectionsEquivTypes F s).val j = s.val j := (rfl)

/-- Evaluate a matching family at one object, independently of the index universe. -/
def sectionsEval (j : J) : sectionsSubmodule F →ₗ[R] F.obj j :=
  (LinearMap.proj j).domRestrict (sectionsSubmodule F)

/-- Linear evaluation reads the specified component. -/
@[simp]
theorem sectionsEval_apply (j : J) (s : sectionsSubmodule F) :
    sectionsEval F j s = s.val j := (rfl)

end

/-- Membership means compatibility along all arrows. -/
@[simp]
theorem mem_sectionsSubmodule {F : J ⥤ SemimoduleCat R} {s : ∀ j, F.obj j} :
    s ∈ sectionsSubmodule F ↔ ∀ {j j'} (f : j ⟶ j'), F.map f (s j) = s j' := Iff.rfl

/-- Restrict matching sections along a functor of index categories, using Mathlib's
section precomposition on the underlying type-valued diagrams. -/
def sectionsPrecomp {K : Type*} [Category* K] (p : K ⥤ J) (F : J ⥤ SemimoduleCat R) :
    sectionsSubmodule F →ₗ[R] sectionsSubmodule (p ⋙ F) where
  toFun := p.sectionsPrecomp (P := F ⋙ forget (SemimoduleCat R))
  map_add' _ _ := by ext j; rfl
  map_smul' _ _ := by ext j; rfl

/-- Restricting a matching section reads its component at the image index. -/
@[simp]
theorem sectionsPrecomp_apply {K : Type*} [Category* K] (p : K ⥤ J)
    (F : J ⥤ SemimoduleCat R) (s : sectionsSubmodule F) (k : K) :
    (sectionsPrecomp p F s).val k = s.val (p.obj k) := (rfl)

section Maps

variable {F G H : J ⥤ SemimoduleCat R}

/-- Apply a natural transformation of semimodule diagrams to every section component. -/
def sectionsMap (α : F ⟶ G) : sectionsSubmodule F →ₗ[R] sectionsSubmodule G where
  toFun := (Functor.sectionsFunctor J).map (Functor.whiskerRight α (forget _))
  map_add' x y := by ext j; exact map_add (α.app j).hom _ _
  map_smul' r x := by ext j; exact map_smul (α.app j).hom r _

/-- Section transport evaluates by the corresponding coefficient map. -/
@[simp]
theorem sectionsMap_apply (α : F ⟶ G) (x : sectionsSubmodule F) (j : J) :
    (sectionsMap α x).val j = (α.app j).hom (x.val j) := (rfl)

/-- Identity coefficient maps fix matching sections. -/
@[simp]
theorem sectionsMap_id : sectionsMap (𝟙 F) = LinearMap.id := by
  ext x j
  rfl

/-- Successive coefficient changes compose on matching sections. -/
@[simp]
theorem sectionsMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    sectionsMap (α ≫ β) = (sectionsMap β).comp (sectionsMap α) := by
  ext x j
  rfl

end Maps

end SemimoduleCat
