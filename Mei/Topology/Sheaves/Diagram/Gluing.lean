/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Limits
public import Mei.Topology.Sheaves.Section

/-!
# Gluing linear matching families on endpoint covers

A diagram of semimodule-valued sheaves has linear restriction maps on its actual
matching families. Compatible linear families on an arbitrary open cover glue
uniquely. No joint injectivity or finiteness of the incidence diagram is needed:
all face values are retained, and compatibility includes them.

For a chamber-and-face diagram, matching-section maps supplied by local
resolution certificates glue on endpoint covers when they agree on overlaps. Gluing takes
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
  D ⋙ ((TopCat.Sheaf.forget (SemimoduleCat.{v} R) X).flip).obj (op U)

/-- Evaluation retains the original component section carrier. -/
theorem sectionsOver_obj (U : Opens X) (j : J) :
    (D.sectionsOver U).obj j = (D.obj j).obj.obj (op U) := (rfl)

/-- An arrow of the evaluated diagram is its sheaf morphism on this open. -/
theorem sectionsOver_map (U : Opens X) {j k : J} (f : j ⟶ k) :
    (D.sectionsOver U).map f = (D.map f).hom.app (op U) := (rfl)

/-- Restrict every component of a matching family to a smaller endpoint open. -/
noncomputable def sectionsRestrict {U V : Opens X} (hVU : V ≤ U) :
    SemimoduleCat.sectionsSubmodule (D.sectionsOver U) →ₗ[R]
      SemimoduleCat.sectionsSubmodule (D.sectionsOver V) :=
  SemimoduleCat.sectionsMap (whiskerLeft D
    (((TopCat.Sheaf.forget (SemimoduleCat.{v} R) X).flip).map
      (homOfLE hVU).op))

/-- A matching-family restriction evaluates by the original sheaf restriction. -/
@[simp]
theorem sectionsRestrict_apply {U V : Opens X} (hVU : V ≤ U)
    (s : SemimoduleCat.sectionsSubmodule (D.sectionsOver U)) (j : J) :
    (D.sectionsRestrict hVU s).val j = (D.obj j).obj.map (homOfLE hVU).op (s.val j) :=
  SemimoduleCat.sectionsMap_apply _ s j

/-- Restriction along an identity inclusion fixes every matching family. -/
@[simp]
theorem sectionsRestrict_refl (U : Opens X) :
    D.sectionsRestrict (le_refl U) = LinearMap.id := by
  unfold sectionsRestrict
  have hi : ((TopCat.Sheaf.forget (SemimoduleCat.{v} R) X).flip).map
      (homOfLE (le_refl U)).op =
        𝟙 (((TopCat.Sheaf.forget (SemimoduleCat.{v} R) X).flip).obj (op U)) :=
    ((TopCat.Sheaf.forget (SemimoduleCat.{v} R) X).flip).map_id (op U)
  rw [hi, whiskerLeft_id']
  exact SemimoduleCat.sectionsMap_id

/-- Successive restrictions are restriction along the composite inclusion. -/
@[simp]
theorem sectionsRestrict_comp {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V) :
    (D.sectionsRestrict hWV).comp (D.sectionsRestrict hVU) =
      D.sectionsRestrict (hWV.trans hVU) := by
  unfold sectionsRestrict
  rw [← SemimoduleCat.sectionsMap_comp, ← whiskerLeft_comp, ← Functor.map_comp,
    ← op_comp, homOfLE_comp]

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
  have ha (j : J) (i : ι) (x : E) : (a j i).hom x = (ℓ i x).val j :=
    SemimoduleCat.sectionsEval_apply (D.sectionsOver (U i)) j (ℓ i x)
  have hc (j : J) : TopCat.Presheaf.IsCompatible (H j).obj U (a j) := by
    intro i k
    -- Restriction in the Hom sheaf is postcomposition in the coefficient category.
    change a j i ≫ (D.obj j).obj.map (homOfLE inf_le_left).op =
      a j k ≫ (D.obj j).obj.map (homOfLE inf_le_right).op
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro x
    have he := congrArg (fun q => (q x).val j) (hcompat i k)
    have hr : (D.obj j).obj.map (homOfLE inf_le_left).op ((ℓ i x).val j) =
        (D.obj j).obj.map (homOfLE inf_le_right).op ((ℓ k x).val j) :=
      (D.sectionsRestrict_apply inf_le_left (ℓ i x) j).symm.trans
        (he.trans (D.sectionsRestrict_apply inf_le_right (ℓ k x) j))
    -- Read the component morphisms on this input using their public values.
    change (D.obj j).obj.map (homOfLE inf_le_left).op ((a j i).hom x) =
      (D.obj j).obj.map (homOfLE inf_le_right).op ((a j k).hom x)
    exact (congrArg ((D.obj j).obj.map (homOfLE inf_le_left).op) (ha j i x)).trans
      (hr.trans (congrArg ((D.obj j).obj.map (homOfLE inf_le_right).op) (ha j k x).symm))
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
    have hf : (D.map f).hom.app (op (U i)) ((ℓ i y).val j) = (ℓ i y).val k :=
      (SemimoduleCat.mem_sectionsSubmodule.mp (ℓ i y).property) f
    -- Composition in the value category evaluates to the component values above.
    change (D.map f).hom.app (op (U i)) ((a j i).hom y) = (a k i).hom y
    exact (congrArg ((D.map f).hom.app (op (U i))) (ha j i y)).trans
      (hf.trans (ha k i y).symm)
  let c : Limits.Cone (D.sectionsOver (iSup U)) :=
    { pt := E
      π :=
        { app := b
          naturality := by
            intro j k f
            exact (Category.id_comp (b k)).trans (hn f).symm } }
  let L := SemimoduleCat.sectionsLift (D.sectionsOver (iSup U)) c
  have hL (x : E) (j : J) : (L x).val j = (b j).hom x :=
    SemimoduleCat.sectionsLift_apply _ c x j
  refine ⟨L, ?_, ?_⟩
  · intro i
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext j
    rw [LinearMap.comp_apply, sectionsRestrict_apply, hL]
    have he : (D.obj j).obj.map (homOfLE (le_iSup U i)).op ((b j).hom x) = (a j i).hom x :=
      ConcreteCategory.congr_hom (hb j i) x
    exact he.trans (ha j i x)
  · intro m hm
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext j
    let δ : E ⟶ (D.obj j).obj.obj (op (iSup U)) :=
      SemimoduleCat.ofHom ((SemimoduleCat.sectionsEval (D.sectionsOver (iSup U)) j).comp m)
    have hδval (y : E) : δ.hom y = (m y).val j :=
      SemimoduleCat.sectionsEval_apply (D.sectionsOver (iSup U)) j (m y)
    have hδ (i : ι) : δ ≫ (D.obj j).obj.map (homOfLE (le_iSup U i)).op = a j i := by
      apply SemimoduleCat.hom_ext
      apply LinearMap.ext
      intro y
      have he := congrArg (fun q => (q y).val j) (hm i)
      have hr : (D.obj j).obj.map (homOfLE (le_iSup U i)).op ((m y).val j) = (ℓ i y).val j :=
        (D.sectionsRestrict_apply (le_iSup U i) (m y) j).symm.trans he
      -- Again compare the original section values, without unfolding sectionsEval.
      change (D.obj j).obj.map (homOfLE (le_iSup U i)).op (δ.hom y) = (a j i).hom y
      exact (congrArg ((D.obj j).obj.map (homOfLE (le_iSup U i)).op) (hδval y)).trans
        (hr.trans (ha j i y).symm)
    have he : δ.hom x = (b j).hom x :=
      ConcreteCategory.congr_hom ((hglue j).unique hδ (hb j)) x
    rw [hL]
    exact (hδval x).symm.trans he

end CategoryTheory.Functor
