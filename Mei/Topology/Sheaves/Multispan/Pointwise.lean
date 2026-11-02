/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.Multispan
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Matching families from inputwise local face lifts

Local face lifts may be supplied separately for each incoming coefficient. Their
neighborhoods and lifts need not vary linearly or be uniform in that coefficient.
Joint injectivity makes the resulting matching family unique, and linearity then
follows from the prescribed linear chamber maps. In particular, testing local
resolution certificates on finite lists of inputs suffices: singleton lists already
supply the local existence used here.

The proof applies local linear gluing to scalar multiples of each input and then
uses the characterization of linear matching-family lifts by incident span images.
No finiteness or finite generation of the incoming module is assumed.
-/

public section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v

namespace CategoryTheory.Limits.MultispanIndex

variable {X : TopCat.{u}} {R : Type v} [Semiring R] {J : MultispanShape}
  (I : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R)))

/-- Linear chamber maps admit a unique linear matching family when each individual
input has common face lifts near every point. The local neighborhoods can depend
on both the input and the face, and either individual face leg may have a kernel. -/
theorem existsUnique_sections_lift_of_pointwise_local (E : SemimoduleCat.{v} R)
    (U : Opens X) (α : ∀ j, E ⟶ (I.right j).obj.obj (op U))
    (hinj : ∀ (W : Opens X), W ≤ U → ∀ b,
      Function.Injective (((I.sectionsIndex W).fst b).hom.prod
        ((I.sectionsIndex W).snd b).hom))
    (hloc : ∀ (a : E) b x, x ∈ U → ∃ (N : Opens X) (hNU : N ≤ U)
      (t : (I.left b).obj.obj (op N)), x ∈ N ∧
        (I.fst b).hom.app (op N) t =
          (I.right (J.fst b)).obj.map (homOfLE hNU).op ((α (J.fst b)).hom a) ∧
        (I.snd b).hom.app (op N) t =
          (I.right (J.snd b)).obj.map (homOfLE hNU).op ((α (J.snd b)).hom a)) :
    ∃! ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan,
      ∀ a j, (ℓ a).val (.right j) = (α j).hom a := by
  apply ((I.sectionsIndex U).existsUnique_sections_lift_iff
    (fun j => (α j).hom) (hinj U le_rfl)).mpr
  intro a b
  let β (j : J.R) : SemimoduleCat.of R R ⟶ (I.right j).obj.obj (op U) :=
    SemimoduleCat.ofHom (LinearMap.toSpanSingleton R _ ((α j).hom a))
  obtain ⟨ℓ, hℓ, -⟩ := I.existsUnique_sections_lift_of_local (SemimoduleCat.of R R) U β
    hinj (by
      intro c x hx
      obtain ⟨N, hNU, t, hxN, hf, hg⟩ := hloc a c x hx
      refine ⟨N, hNU, SemimoduleCat.ofHom (LinearMap.toSpanSingleton R _ t), hxN, ?_, ?_⟩
      · apply SemimoduleCat.hom_ext
        apply LinearMap.ext
        intro r
        simpa only [β, SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom,
          LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, map_smul] using
          congrArg (r • ·) hf
      · apply SemimoduleCat.hom_ext
        apply LinearMap.ext
        intro r
        simpa only [β, SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom,
          LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, map_smul] using
          congrArg (r • ·) hg)
  have hright (j : J.R) : (ℓ 1).val (.right j) = (α j).hom a := by
    simpa only [β, SemimoduleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one] using hℓ 1 j
  have hface := (I.sectionsIndex U).mem_sectionsSubmodule_multispan.mp (ℓ 1).property
  exact ⟨(ℓ 1).val (.left b), Prod.ext ((hface.1 b).trans (hright _))
    ((hface.2 b).trans (hright _))⟩

end CategoryTheory.Limits.MultispanIndex
