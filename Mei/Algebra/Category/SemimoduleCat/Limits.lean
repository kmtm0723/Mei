/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Sections
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Algebra.Module.Shrink

/-!
# Limits of semimodules over semirings

Matching families give small limits of semimodule diagrams over arbitrary
semirings. The limit projections are linear evaluations, and the forgetful
functor preserves these limits. No additive inverses are required.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace SemimoduleCat

universe r v w t v' t'

variable {R : Type r} [Semiring R] {J : Type v} [Category.{t} J]
  (F : J ⥤ SemimoduleCat.{w} R)

/-- A cone induces a linear map into matching families by its compatible projections. -/
def sectionsLift (c : Cone F) : c.pt →ₗ[R] sectionsSubmodule F :=
  (LinearMap.pi fun j => (c.π.app j).hom).codRestrict (sectionsSubmodule F) (by
    intro x
    apply mem_sectionsSubmodule.mpr
    intro j j' f
    simpa only [LinearMap.pi_apply, SemimoduleCat.comp_apply] using
      ConcreteCategory.congr_hom (c.w f) x)

/-- A cone's section lift evaluates to its original projections. -/
@[simp]
theorem sectionsLift_apply (c : Cone F) (x : c.pt) (j : J) :
    (sectionsLift F c x).val j = c.π.app j x := (rfl)

section SmallSections

variable [Small.{w} (sectionsSubmodule F)]

/-- The matching-family cone, shrinking its carrier into the coefficient universe.
Only the section carrier needs to be small; the index category may be larger. -/
@[expose]
noncomputable def sectionsCone : Cone F where
  pt := SemimoduleCat.of R (Shrink.{w} (sectionsSubmodule F))
  π :=
    { app j := SemimoduleCat.ofHom
        ((sectionsEval F j).comp (Shrink.linearEquiv R (sectionsSubmodule F)).toLinearMap)
      naturality j j' f := by
        -- Default transparency identifies the transported Shrink module in the
        -- bundled constant object and in the evaluation morphism.
        erw [Functor.const_obj_map, Category.id_comp]
        apply SemimoduleCat.hom_ext
        ext x
        simpa only [SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom,
          LinearMap.comp_apply, LinearEquiv.coe_coe, sectionsEval_apply] using
          (mem_sectionsSubmodule.mp
            ((Shrink.linearEquiv R (sectionsSubmodule F) x).property) f).symm }

/-- The cone projections are evaluation after the linear shrinking equivalence. -/
@[simp]
theorem sectionsCone_π_app (j : J) :
    (sectionsCone F).π.app j = SemimoduleCat.ofHom
      ((sectionsEval F j).comp (Shrink.linearEquiv R (sectionsSubmodule F)).toLinearMap) := (rfl)

/-- Cone projections read the corresponding component of the unshrunk section. -/
theorem sectionsCone_π_apply (j : J) (x : (sectionsCone F).pt) :
    (sectionsCone F).π.app j x =
      (Shrink.linearEquiv R (sectionsSubmodule F) x).val j := by
  -- Rewriting uses the public equations at default transparency to identify the
  -- bundled Shrink carrier with the domain of its linear equivalence.
  erw [sectionsCone_π_app, SemimoduleCat.ofHom_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, sectionsEval_apply]

/-- The matching-family cone satisfies the limit universal property. -/
noncomputable def sectionsConeIsLimit : IsLimit (sectionsCone F) where
  lift c := SemimoduleCat.ofHom
    ((Shrink.linearEquiv R (sectionsSubmodule F)).symm.toLinearMap.comp (sectionsLift F c))
  fac c j := by
    apply SemimoduleCat.hom_ext
    ext x
    erw [SemimoduleCat.hom_comp, sectionsCone_π_app, SemimoduleCat.hom_ofHom,
      SemimoduleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, sectionsEval_apply,
      LinearEquiv.apply_symm_apply, sectionsLift_apply]
  uniq c m hm := by
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (Shrink.linearEquiv R (sectionsSubmodule F)).injective
    apply Subtype.ext
    funext j
    have he := ConcreteCategory.congr_hom (hm j) x
    erw [SemimoduleCat.comp_apply, sectionsCone_π_apply] at he
    erw [SemimoduleCat.hom_ofHom, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, sectionsLift_apply]
    exact he

/-- The type-valued section map of the forgotten cone is the canonical carrier comparison.
This equality follows componentwise from the public cone projection equation. -/
theorem sectionOfCone_forget_sectionsCone :
    Types.sectionOfCone ((forget (SemimoduleCat R)).mapCone (sectionsCone F)) =
      fun x => sectionsEquivTypes F (Shrink.linearEquiv R (sectionsSubmodule F) x) := by
  funext x
  apply Subtype.ext
  funext j
  simp only [Types.sectionOfCone, Functor.mapCone_π_app, sectionsEquivTypes_apply]
  exact sectionsCone_π_apply F j x

/-- The underlying cone is a limit of the underlying diagram of types. -/
noncomputable def forgetSectionsConeIsLimit :
    IsLimit ((forget (SemimoduleCat R)).mapCone (sectionsCone F)) :=
  Classical.choice <| (Types.isLimit_iff_bijective_sectionOfCone _).mpr <| by
    rw [sectionOfCone_forget_sectionsCone]
    exact (sectionsEquivTypes F).bijective.comp
      (Shrink.linearEquiv R (sectionsSubmodule F)).bijective

/-- A semimodule diagram has a limit whenever its matching-family carrier is small. -/
instance hasLimit : HasLimit F :=
  HasLimit.mk ⟨sectionsCone F, sectionsConeIsLimit F⟩

/-- Forgetting semimodule structure preserves limits with small matching-family carriers. -/
instance forget_preservesLimit : PreservesLimit F (forget (SemimoduleCat.{w} R)) :=
  preservesLimit_of_preserves_limit_cone (sectionsConeIsLimit F)
    (forgetSectionsConeIsLimit F)

variable [HasLimit F]

/-- The categorical limit is linearly identified with the unshrunk matching families. -/
noncomputable def limitLinearEquivSections :
    (limit F : SemimoduleCat R) ≃ₗ[R] sectionsSubmodule F :=
  (limit.isoLimitCone ⟨sectionsCone F, sectionsConeIsLimit F⟩).toLinearEquivₛ.trans
    (Shrink.linearEquiv R (sectionsSubmodule F))

/-- Reading a component after identifying the limit with sections is a limit projection. -/
@[simp]
theorem limitLinearEquivSections_apply (x : (limit F : SemimoduleCat R)) (j : J) :
    (limitLinearEquivSections F x).val j = limit.π F j x := by
  have he := ConcreteCategory.congr_hom (limit.isoLimitCone_hom_π
    ⟨sectionsCone F, sectionsConeIsLimit F⟩ j) x
  erw [SemimoduleCat.comp_apply, sectionsCone_π_apply] at he
  exact he

/-- The inverse comparison has the prescribed value under every limit projection. -/
@[simp]
theorem limit_π_limitLinearEquivSections_symm (s : sectionsSubmodule F) (j : J) :
    limit.π F j ((limitLinearEquivSections F).symm s) = s.val j := by
  rw [← limitLinearEquivSections_apply, LinearEquiv.apply_symm_apply]

/-- The section of a categorical cone lift is the linear lift of its projections. -/
@[simp]
theorem limitLinearEquivSections_limit_lift (c : Cone F) (x : c.pt) :
    limitLinearEquivSections F (limit.lift F c x) = sectionsLift F c x := by
  apply Subtype.ext
  funext j
  rw [limitLinearEquivSections_apply, sectionsLift_apply]
  exact ConcreteCategory.congr_hom (limit.lift_π c j) x

/-- The map of categorical limits is componentwise coefficient change on sections. -/
theorem limitLinearEquivSections_limMap_apply {G : J ⥤ SemimoduleCat.{w} R}
    [Small.{w} (sectionsSubmodule G)] [HasLimit G]
    (α : F ⟶ G) (x : (limit F : SemimoduleCat R)) (j : J) :
    (limitLinearEquivSections G (limMap α x)).val j =
      (α.app j).hom ((limitLinearEquivSections F x).val j) := by
  rw [limitLinearEquivSections_apply, limitLinearEquivSections_apply]
  exact ConcreteCategory.congr_hom (limMap_π α j) x

/-- Restricting categorical limits restricts matching families along any index functor. -/
@[simp↓]
theorem limitLinearEquivSections_pre_apply {K : Type v'} [Category.{t'} K] (p : K ⥤ J)
    [Small.{w} (sectionsSubmodule (p ⋙ F))] [HasLimit (p ⋙ F)]
    (x : (limit F : SemimoduleCat R)) (k : K) :
    (limitLinearEquivSections (p ⋙ F) (limit.pre F p x)).val k =
      (limitLinearEquivSections F x).val (p.obj k) := by
  rw [limitLinearEquivSections_apply, limitLinearEquivSections_apply]
  exact ConcreteCategory.congr_hom (limit.pre_π F p k) x

end SmallSections

/-- A small index type supplies limits of its shape, independently of morphism universe. -/
instance hasLimitsOfShape [Small.{w} J] : HasLimitsOfShape J (SemimoduleCat.{w} R) where
  has_limit := inferInstance

/-- Semimodules have limits of every size fitting in their carrier universe. -/
instance hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (SemimoduleCat.{w} R) where
  has_limits_of_shape _ := inferInstance

/-- The forgetful functor preserves limits of every size fitting in the carrier universe. -/
instance forget_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget (SemimoduleCat.{w} R)) where
  preservesLimitsOfShape := { preservesLimit := inferInstance }

end SemimoduleCat
