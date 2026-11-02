/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.Diagram.Gluing

/-!
# Coefficient maps, restrictions and gluing of matching families

A transformation of diagrams of semimodule-valued sheaves acts linearly on their
actual matching families. This action commutes with endpoint restriction, so
compatible families remain compatible on overlaps. Applying the transformation
to a glued family gives a glued family of the transformed local maps.

No finiteness, injectivity or surjectivity is imposed on the coefficient maps,
the incidence category or the endpoint cover. Face values are retained along
with chamber values.
-/

public section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r w t

namespace CategoryTheory.NatTrans

variable {X : TopCat.{u}} {R : Type r} [Semiring R]
  {J : Type w} [Category.{t} J]
  {D D' D'' : J ⥤ X.Sheaf (SemimoduleCat.{v} R)}

/-- Apply the coefficient transformation on every component of a matching
family, using the existing linear map on diagram sections. -/
noncomputable def matchingSectionsMap (η : D ⟶ D') (U : Opens X) :
    SemimoduleCat.sectionsSubmodule (D.sectionsOver U) →ₗ[R]
      SemimoduleCat.sectionsSubmodule (D'.sectionsOver U) :=
  SemimoduleCat.sectionsMap (Functor.whiskerRight η
    (((TopCat.Sheaf.forget (SemimoduleCat.{v} R) X).flip).obj (op U)))

/-- Evaluation uses the original coefficient sheaf morphism on this open. -/
@[simp]
theorem matchingSectionsMap_apply (η : D ⟶ D') (U : Opens X)
    (s : SemimoduleCat.sectionsSubmodule (D.sectionsOver U)) (j : J) :
    (η.matchingSectionsMap U s).val j = (η.app j).hom.app (op U) (s.val j) :=
  SemimoduleCat.sectionsMap_apply _ s j

/-- Identity coefficient transport fixes all matching-family components. -/
@[simp]
theorem matchingSectionsMap_id (U : Opens X) :
    (𝟙 D : D ⟶ D).matchingSectionsMap U = LinearMap.id := by
  unfold matchingSectionsMap
  rw [Functor.whiskerRight_id']
  exact SemimoduleCat.sectionsMap_id

/-- Successive coefficient transformations act by composition on matching families. -/
@[simp]
theorem matchingSectionsMap_comp (η : D ⟶ D') (θ : D' ⟶ D'') (U : Opens X) :
    (η ≫ θ).matchingSectionsMap U =
      (θ.matchingSectionsMap U).comp (η.matchingSectionsMap U) := by
  unfold matchingSectionsMap
  rw [Functor.whiskerRight_comp, SemimoduleCat.sectionsMap_comp]

/-- Coefficient transport commutes with restriction of the endpoint open. -/
theorem matchingSectionsMap_restrict (η : D ⟶ D') {U V : Opens X} (hVU : V ≤ U) :
    (D'.sectionsRestrict hVU).comp (η.matchingSectionsMap U) =
      (η.matchingSectionsMap V).comp (D.sectionsRestrict hVU) := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext j
  simp only [LinearMap.comp_apply, Functor.sectionsRestrict_apply, matchingSectionsMap_apply]
  exact (ConcreteCategory.congr_hom ((η.app j).hom.naturality (homOfLE hVU).op) (s.val j)).symm

/-- Applying a coefficient map to a glued linear family glues the transformed
local families, on the same endpoint cover. -/
theorem matchingSectionsMap_gluing (η : D ⟶ D') (E : SemimoduleCat.{v} R)
    {ι : Type*} (U : ι → Opens X)
    (ℓ : ∀ i, E →ₗ[R] SemimoduleCat.sectionsSubmodule (D.sectionsOver (U i)))
    (L : E →ₗ[R] SemimoduleCat.sectionsSubmodule (D.sectionsOver (iSup U)))
    (hL : ∀ i, (D.sectionsRestrict (le_iSup U i)).comp L = ℓ i) :
    ∀ i, (D'.sectionsRestrict (le_iSup U i)).comp
        ((η.matchingSectionsMap (iSup U)).comp L) =
      (η.matchingSectionsMap (U i)).comp (ℓ i) := by
  intro i
  rw [← LinearMap.comp_assoc, matchingSectionsMap_restrict, LinearMap.comp_assoc, hL]

/-- Compatible local matching families remain compatible after any coefficient
transformation, and therefore still have a unique glued linear map. -/
theorem existsUnique_matchingSectionsMap_gluing (η : D ⟶ D') (E : SemimoduleCat.{v} R)
    {ι : Type*} (U : ι → Opens X)
    (ℓ : ∀ i, E →ₗ[R] SemimoduleCat.sectionsSubmodule (D.sectionsOver (U i)))
    (hcompat : ∀ i k,
      (D.sectionsRestrict (inf_le_left : U i ⊓ U k ≤ U i)).comp (ℓ i) =
        (D.sectionsRestrict (inf_le_right : U i ⊓ U k ≤ U k)).comp (ℓ k)) :
    ∃! L : E →ₗ[R] SemimoduleCat.sectionsSubmodule (D'.sectionsOver (iSup U)),
      ∀ i, (D'.sectionsRestrict (le_iSup U i)).comp L =
        (η.matchingSectionsMap (U i)).comp (ℓ i) := by
  apply D'.existsUnique_sections_gluing E U
  intro i k
  rw [← LinearMap.comp_assoc, matchingSectionsMap_restrict, LinearMap.comp_assoc, hcompat,
    ← LinearMap.comp_assoc, ← matchingSectionsMap_restrict, LinearMap.comp_assoc]

end CategoryTheory.NatTrans
