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
the incidence category or the endpoint cover. The map acts on every component `j : J`. When `J` is a
chamber-and-face
incidence category, this includes its face components.
-/

public section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r w t

namespace CategoryTheory.NatTrans

variable {X : TopCat.{u}} {R : Type r} [Semiring R]
  {J : Type w} [Category.{t} J]
  {D D' D'' : J ⥤ X.Sheaf (SemimoduleCat.{v} R)}

/-- The `R`-linear map on matching families over `U` induced by `η`, sending
each component section `s j` to its image under the coefficient morphism `η.app j`. -/
noncomputable def sectionsMap (η : D ⟶ D') (U : Opens X) :
    SemimoduleCat.sectionsSubmodule (D.sectionsOver U) →ₗ[R]
      SemimoduleCat.sectionsSubmodule (D'.sectionsOver U) :=
  SemimoduleCat.sectionsMap (Functor.whiskerRight η
    (((TopCat.Sheaf.forget (SemimoduleCat.{v} R) X).flip).obj (op U)))

/-- Evaluation uses the original coefficient sheaf morphism on this open. -/
@[simp]
theorem sectionsMap_apply (η : D ⟶ D') (U : Opens X)
    (s : SemimoduleCat.sectionsSubmodule (D.sectionsOver U)) (j : J) :
    (η.sectionsMap U s).val j = (η.app j).hom.app (op U) (s.val j) :=
  SemimoduleCat.sectionsMap_apply _ s j

/-- Identity coefficient transport fixes all matching-family components. -/
@[simp]
theorem sectionsMap_id (U : Opens X) :
    (𝟙 D : D ⟶ D).sectionsMap U = LinearMap.id := by
  unfold sectionsMap
  rw [Functor.whiskerRight_id']
  exact SemimoduleCat.sectionsMap_id

/-- Successive coefficient transformations act by composition on matching families. -/
@[simp]
theorem sectionsMap_comp (η : D ⟶ D') (θ : D' ⟶ D'') (U : Opens X) :
    (η ≫ θ).sectionsMap U =
      (θ.sectionsMap U).comp (η.sectionsMap U) := by
  unfold sectionsMap
  rw [Functor.whiskerRight_comp, SemimoduleCat.sectionsMap_comp]

/-- Coefficient transport commutes with restriction of the endpoint open. -/
theorem sectionsMap_restrict (η : D ⟶ D') {U V : Opens X} (hVU : V ≤ U) :
    (D'.sectionsRestrict hVU).comp (η.sectionsMap U) =
      (η.sectionsMap V).comp (D.sectionsRestrict hVU) := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext j
  simp only [LinearMap.comp_apply, Functor.sectionsRestrict_apply, sectionsMap_apply]
  exact (ConcreteCategory.congr_hom ((η.app j).hom.naturality (homOfLE hVU).op) (s.val j)).symm

/-- Compatible local matching families remain compatible after any coefficient
transformation, and therefore still have a unique glued linear map. -/
theorem existsUnique_sectionsMap_gluing (η : D ⟶ D') (E : SemimoduleCat.{v} R)
    {ι : Type*} (U : ι → Opens X)
    (ℓ : ∀ i, E →ₗ[R] SemimoduleCat.sectionsSubmodule (D.sectionsOver (U i)))
    (hcompat : ∀ i k,
      (D.sectionsRestrict (inf_le_left : U i ⊓ U k ≤ U i)).comp (ℓ i) =
        (D.sectionsRestrict (inf_le_right : U i ⊓ U k ≤ U k)).comp (ℓ k)) :
    ∃! L : E →ₗ[R] SemimoduleCat.sectionsSubmodule (D'.sectionsOver (iSup U)),
      ∀ i, (D'.sectionsRestrict (le_iSup U i)).comp L =
        (η.sectionsMap (U i)).comp (ℓ i) := by
  apply D'.existsUnique_sections_gluing E U
  intro i k
  rw [← LinearMap.comp_assoc, sectionsMap_restrict, LinearMap.comp_assoc, hcompat,
    ← LinearMap.comp_assoc, ← sectionsMap_restrict, LinearMap.comp_assoc]

end CategoryTheory.NatTrans
