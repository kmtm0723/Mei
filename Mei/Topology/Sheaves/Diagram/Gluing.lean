/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Sections
public import Mei.Topology.Sheaves.Section

/-!
# Gluing linear matching families on endpoint covers

A diagram of semimodule-valued sheaves has linear restriction maps on its actual
matching families. Compatible linear families on an arbitrary open cover glue
uniquely. No joint injectivity or finiteness of the incidence diagram is needed:
all face values are retained, and compatibility includes them.

For a chamber-and-face diagram this glues local resolution certificates on
endpoint covers after their matching families agree on overlaps. Gluing takes
place in the existing Hom sheaves, so the incoming module and coefficient ring
need not be finite or admit additive inverses.
-/

public section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r w t

namespace CategoryTheory.Functor

variable {X : TopCat.{u}} {R : Type r} [Semiring R]
  {J : Type w} [Category.{t} J] (D : J ⥤ X.Sheaf (SemimoduleCat.{v} R))

/-- The coefficient diagram evaluated on one endpoint open. -/
noncomputable abbrev sectionsOver (U : Opens X) : J ⥤ SemimoduleCat.{v} R :=
  D ⋙ (sheafSections (Opens.grothendieckTopology X) (SemimoduleCat.{v} R)).obj (op U)

/-- Evaluation retains the original component section carrier. -/
@[simp]
theorem sectionsOver_obj (U : Opens X) (j : J) :
    (D.sectionsOver U).obj j = (D.obj j).obj.obj (op U) := (rfl)

/-- An arrow of the evaluated diagram is its sheaf morphism on this open. -/
@[simp]
theorem sectionsOver_map (U : Opens X) {j k : J} (f : j ⟶ k) :
    (D.sectionsOver U).map f = (D.map f).hom.app (op U) := (rfl)

/-- Restrict every component of a matching family to a smaller endpoint open. -/
noncomputable def sectionsRestrict {U V : Opens X} (hVU : V ≤ U) :
    SemimoduleCat.sectionsSubmodule (D.sectionsOver U) →ₗ[R]
      SemimoduleCat.sectionsSubmodule (D.sectionsOver V) where
  toFun s := ⟨fun j => (D.obj j).obj.map (homOfLE hVU).op (s.val j), by
    apply SemimoduleCat.mem_sectionsSubmodule.mpr
    intro j k f
    have hn := ConcreteCategory.congr_hom ((D.map f).hom.naturality (homOfLE hVU).op)
      (s.val j)
    exact hn.trans (congrArg ((D.obj k).obj.map (homOfLE hVU).op)
      ((SemimoduleCat.mem_sectionsSubmodule.mp s.property) f))⟩
  map_add' s t := by
    apply Subtype.ext
    funext j
    exact map_add ((D.obj j).obj.map (homOfLE hVU).op).hom _ _
  map_smul' r s := by
    apply Subtype.ext
    funext j
    exact map_smul ((D.obj j).obj.map (homOfLE hVU).op).hom _ _

/-- A matching-family restriction evaluates by the original sheaf restriction. -/
@[simp]
theorem sectionsRestrict_apply {U V : Opens X} (hVU : V ≤ U)
    (s : SemimoduleCat.sectionsSubmodule (D.sectionsOver U)) (j : J) :
    (D.sectionsRestrict hVU s).val j = (D.obj j).obj.map (homOfLE hVU).op (s.val j) := (rfl)

/-- Restriction along an identity inclusion fixes every matching family. -/
@[simp]
theorem sectionsRestrict_refl (U : Opens X) :
    D.sectionsRestrict (le_refl U) = LinearMap.id := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext j
  simp only [sectionsRestrict_apply, homOfLE_refl, op_id, Functor.map_id,
    SemimoduleCat.id_apply, LinearMap.id_apply]

/-- Successive restrictions are restriction along the composite inclusion. -/
@[simp]
theorem sectionsRestrict_comp {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V) :
    (D.sectionsRestrict hWV).comp (D.sectionsRestrict hVU) =
      D.sectionsRestrict (hWV.trans hVU) := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext j
  simp only [LinearMap.comp_apply, sectionsRestrict_apply]
  simpa only [← op_comp, homOfLE_comp, SemimoduleCat.comp_apply] using
    (ConcreteCategory.congr_hom
      ((D.obj j).obj.map_comp (homOfLE hVU).op (homOfLE hWV).op) (s.val j)).symm

/-- Compatible linear maps to matching families glue uniquely over any endpoint
cover. Compatibility is equality of the restricted linear maps on every overlap;
the cover and the coefficient diagram may both be infinite. -/
theorem existsUnique_sections_gluing (E : SemimoduleCat.{v} R)
    {ι : Type*} (U : ι → Opens X)
    (ℓ : ∀ i, E →ₗ[R] SemimoduleCat.sectionsSubmodule (D.sectionsOver (U i)))
    (hcompat : ∀ i k,
      (D.sectionsRestrict (inf_le_left : U i ⊓ U k ≤ U i)).comp (ℓ i) =
        (D.sectionsRestrict (inf_le_right : U i ⊓ U k ≤ U k)).comp (ℓ k)) :
    ∃! L : E →ₗ[R] SemimoduleCat.sectionsSubmodule (D.sectionsOver (iSup U)),
      ∀ i, (D.sectionsRestrict (le_iSup U i)).comp L = ℓ i := by
  let H (j : J) : X.Sheaf (Type v) := sheafOver (D.obj j) E
  let a (j : J) (i : ι) : E ⟶ (D.obj j).obj.obj (op (U i)) :=
    SemimoduleCat.ofHom ((SemimoduleCat.sectionsEval (D.sectionsOver (U i)) j).comp (ℓ i))
  have hc (j : J) : TopCat.Presheaf.IsCompatible (H j).obj U (a j) := by
    intro i k
    -- Restriction in the Hom sheaf is postcomposition in the coefficient category.
    change a j i ≫ (D.obj j).obj.map (homOfLE inf_le_left).op =
      a j k ≫ (D.obj j).obj.map (homOfLE inf_le_right).op
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro x
    simpa only [a, SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom,
      LinearMap.comp_apply, SemimoduleCat.sectionsEval_apply, sectionsRestrict_apply] using
      congrArg (fun q => (q x).val j) (hcompat i k)
  have hglue (j : J) : ∃! b : E ⟶ (D.obj j).obj.obj (op (iSup U)),
      ∀ i, b ≫ (D.obj j).obj.map (homOfLE (le_iSup U i)).op = a j i := by
    exact TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types (H j).property (a j) (hc j)
  choose b hb using fun j => (hglue j).exists
  have hn {j k : J} (f : j ⟶ k) :
      b j ≫ (D.map f).hom.app (op (iSup U)) = b k := by
    apply TopCat.Sheaf.section_ext (sheafOver (D.obj k) E)
    intro x hx
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
    refine ⟨U i, le_iSup U i, hxi, ?_⟩
    -- The Hom-sheaf restriction again is postcomposition; naturality moves it past f.
    change (b j ≫ (D.map f).hom.app (op (iSup U))) ≫
      (D.obj k).obj.map (homOfLE (le_iSup U i)).op =
        b k ≫ (D.obj k).obj.map (homOfLE (le_iSup U i)).op
    rw [Category.assoc, ← (D.map f).hom.naturality, ← Category.assoc, hb j i, hb k i]
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro y
    simpa only [a, SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom,
      LinearMap.comp_apply, SemimoduleCat.sectionsEval_apply, sectionsOver_map] using
        (SemimoduleCat.mem_sectionsSubmodule.mp (ℓ i y).property) f
  let L : E →ₗ[R] SemimoduleCat.sectionsSubmodule (D.sectionsOver (iSup U)) :=
    { toFun x := ⟨fun j => b j x, by
        apply SemimoduleCat.mem_sectionsSubmodule.mpr
        intro j k f
        exact ConcreteCategory.congr_hom (hn f) x⟩
      map_add' x y := by
        apply Subtype.ext
        funext j
        exact map_add (b j).hom x y
      map_smul' r x := by
        apply Subtype.ext
        funext j
        exact map_smul (b j).hom r x }
  have hL (x : E) (j : J) : (L x).val j = (b j).hom x := by rfl
  refine ⟨L, ?_, ?_⟩
  · intro i
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext j
    rw [LinearMap.comp_apply, sectionsRestrict_apply, hL]
    simpa only [a, SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom,
      LinearMap.comp_apply, SemimoduleCat.sectionsEval_apply] using
        ConcreteCategory.congr_hom (hb j i) x
  · intro m hm
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext j
    let δ : E ⟶ (D.obj j).obj.obj (op (iSup U)) :=
      SemimoduleCat.ofHom ((SemimoduleCat.sectionsEval (D.sectionsOver (iSup U)) j).comp m)
    have hδ (i : ι) : δ ≫ (D.obj j).obj.map (homOfLE (le_iSup U i)).op = a j i := by
      apply SemimoduleCat.hom_ext
      apply LinearMap.ext
      intro y
      simpa only [δ, a, SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom,
        LinearMap.comp_apply, SemimoduleCat.sectionsEval_apply, sectionsRestrict_apply] using
        congrArg (fun q => (q y).val j) (hm i)
    have he := ConcreteCategory.congr_hom ((hglue j).unique hδ (hb j)) x
    rw [hL]
    simpa only [δ, SemimoduleCat.hom_ofHom, LinearMap.comp_apply,
      SemimoduleCat.sectionsEval_apply] using he

end CategoryTheory.Functor
