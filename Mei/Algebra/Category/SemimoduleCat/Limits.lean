/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Sections
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Limits of semimodules over semirings

Matching families give small limits of semimodule diagrams over arbitrary
semirings. The limit projections are linear evaluations, and the forgetful
functor preserves these limits. No additive inverses are required.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace SemimoduleCat

universe u v w

variable {R : Type u} [Semiring R] {J : Type v} [Category.{w} J]
  (F : J ⥤ SemimoduleCat.{v} R)

/-- The matching-family carrier agrees with Mathlib's sections of the underlying diagram. -/
def sectionsEquivTypes : sectionsSubmodule F ≃ (F ⋙ forget (SemimoduleCat R)).sections where
  toFun s := ⟨s.val, (mem_sectionsSubmodule.mp s.property)⟩
  invFun s := ⟨s.val, mem_sectionsSubmodule.mpr s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The carrier comparison preserves each component. -/
@[simp]
theorem sectionsEquivTypes_apply (s : sectionsSubmodule F) (j : J) :
    (sectionsEquivTypes F s).val j = s.val j := (rfl)

/-- Evaluate a matching family at one object of its diagram. -/
def sectionsEval (j : J) : sectionsSubmodule F →ₗ[R] F.obj j where
  toFun s := s.val j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear evaluation reads the specified component. -/
@[simp]
theorem sectionsEval_apply (j : J) (s : sectionsSubmodule F) :
    sectionsEval F j s = s.val j := (rfl)

/-- The cone whose point is the semimodule of matching families. -/
@[expose]
def sectionsCone : Cone F where
  pt := SemimoduleCat.of R (sectionsSubmodule F)
  π :=
    { app j := SemimoduleCat.ofHom (sectionsEval F j)
      naturality j j' f := by
        ext s
        exact (mem_sectionsSubmodule.mp s.property f).symm }

/-- The cone projections are the bundled linear evaluation maps. -/
@[simp]
theorem sectionsCone_π_app (j : J) :
    (sectionsCone F).π.app j = SemimoduleCat.ofHom (sectionsEval F j) := (rfl)

/-- The cone projections read the matching-family components. -/
theorem sectionsCone_π_apply (j : J) (s : sectionsSubmodule F) :
    (sectionsCone F).π.app j s = s.val j := (rfl)

/-- A cone induces a linear map into matching families by its compatible projections. -/
def sectionsLift (c : Cone F) : c.pt →ₗ[R] sectionsSubmodule F where
  toFun x := ⟨fun j => c.π.app j x, mem_sectionsSubmodule.mpr fun f =>
    ConcreteCategory.congr_hom (c.w f) x⟩
  map_add' x y := by ext j; exact map_add (c.π.app j).hom x y
  map_smul' r x := by ext j; exact map_smul (c.π.app j).hom r x

/-- A cone's section lift evaluates to the original cone projections. -/
@[simp]
theorem sectionsLift_apply (c : Cone F) (x : c.pt) (j : J) :
    (sectionsLift F c x).val j = c.π.app j x := (rfl)

/-- The matching-family cone satisfies the limit universal property. -/
def sectionsConeIsLimit : IsLimit (sectionsCone F) where
  lift c := SemimoduleCat.ofHom (sectionsLift F c)
  fac c j := by ext x; rfl
  uniq c m hm := by
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext j
    exact ConcreteCategory.congr_hom (hm j) x

/-- The underlying cone is a limit of the underlying diagram of types. -/
noncomputable def forgetSectionsConeIsLimit :
    IsLimit ((forget (SemimoduleCat R)).mapCone (sectionsCone F)) :=
  Classical.choice <| (Types.isLimit_iff_bijective_sectionOfCone _).mpr <| by
    change Function.Bijective (sectionsEquivTypes F)
    exact (sectionsEquivTypes F).bijective

/-- Small diagrams of semimodules over a semiring have limits. -/
instance hasLimit : HasLimit F :=
  HasLimit.mk ⟨sectionsCone F, sectionsConeIsLimit F⟩

/-- Semimodules have limits of every shape whose objects fit in the carrier universe. -/
instance hasLimitsOfShape : HasLimitsOfShape J (SemimoduleCat.{v} R) where
  has_limit := inferInstance

/-- The category of semimodules has all small limits. -/
instance hasLimitsOfSize : HasLimitsOfSize.{w, v} (SemimoduleCat.{v} R) where
  has_limits_of_shape _ := inferInstance

/-- Forgetting the semimodule structure preserves limits of semimodule diagrams. -/
instance forget_preservesLimit : PreservesLimit F (forget (SemimoduleCat.{v} R)) :=
  preservesLimit_of_preserves_limit_cone (sectionsConeIsLimit F)
    (forgetSectionsConeIsLimit F)

/-- The forgetful functor preserves all small limits. -/
instance forget_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (forget (SemimoduleCat.{v} R)) where
  preservesLimitsOfShape := { preservesLimit := inferInstance }

variable [HasLimit F]

/-- The categorical limit is linearly identified with matching families. -/
noncomputable def limitLinearEquivSections :
    (limit F : SemimoduleCat R) ≃ₗ[R] sectionsSubmodule F :=
  (limit.isoLimitCone ⟨sectionsCone F, sectionsConeIsLimit F⟩).toLinearEquivₛ

/-- Reading a component after identifying the limit with sections is a limit projection. -/
@[simp]
theorem limitLinearEquivSections_apply (x : (limit F : SemimoduleCat R)) (j : J) :
    (limitLinearEquivSections F x).val j = limit.π F j x := by
  exact ConcreteCategory.congr_hom (limit.isoLimitCone_hom_π
    ⟨sectionsCone F, sectionsConeIsLimit F⟩ j) x

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

/-- The map of categorical limits is the componentwise coefficient change on sections. -/
theorem limitLinearEquivSections_limMap_apply {G : J ⥤ SemimoduleCat.{v} R}
    [HasLimit G] (α : F ⟶ G) (x : (limit F : SemimoduleCat R)) (j : J) :
    (limitLinearEquivSections G (limMap α x)).val j =
      (α.app j).hom ((limitLinearEquivSections F x).val j) := by
  rw [limitLinearEquivSections_apply, limitLinearEquivSections_apply]
  exact ConcreteCategory.congr_hom (limMap_π α j) x

/-- Restriction of categorical limits restricts the matching family along the index functor. -/
theorem limitLinearEquivSections_pre_apply {K : Type v} [Category* K] (p : K ⥤ J)
    [HasLimit (p ⋙ F)] (x : (limit F : SemimoduleCat R)) (k : K) :
    (limitLinearEquivSections (p ⋙ F) (limit.pre F p x)).val k =
      (limitLinearEquivSections F x).val (p.obj k) := by
  rw [limitLinearEquivSections_apply, limitLinearEquivSections_apply]
  exact ConcreteCategory.congr_hom (limit.pre_π F p k) x

end SemimoduleCat
