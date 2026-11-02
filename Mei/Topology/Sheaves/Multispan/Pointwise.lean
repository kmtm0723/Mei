/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.Multispan

/-!
# Matching families from inputwise local face lifts

Local face lifts may be supplied separately for each incoming coefficient. Their
neighborhoods and lifts need not vary linearly or be uniform in that coefficient.
Joint injectivity makes the resulting matching family unique, and linearity then
follows from the prescribed linear chamber maps. In particular, testing local
resolution certificates on finite lists of inputs suffices: singleton lists already
supply the local existence used here.

No finiteness or finite generation of the incoming module is assumed.
-/

public section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r

namespace CategoryTheory.Limits.MultispanIndex

variable {X : TopCat.{u}} {R : Type r} [Semiring R] {J : MultispanShape}
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
  -- Glue on the cyclic submodule of each input. It fits in the section universe
  -- even when the scalar semiring does not; span closure supplies all local lifts.
  let P : Submodule R E := Submodule.span R {a}
  let β (j : J.R) : SemimoduleCat.of R P ⟶ (I.right j).obj.obj (op U) :=
    SemimoduleCat.ofHom ((α j).hom.comp P.subtype)
  obtain ⟨ℓ, hℓ, -⟩ := I.existsUnique_sections_lift_of_local (SemimoduleCat.of R P) U β
    hinj (by
      intro c x hx
      obtain ⟨N, hNU, t, hxN, hf, hg⟩ := hloc a c x hx
      let f := ((I.sectionsIndex N).fst c).hom.prod ((I.sectionsIndex N).snd c).hom
      let g :=
        (((I.right (J.fst c)).obj.map (homOfLE hNU).op).hom.comp (α (J.fst c)).hom).prod
        (((I.right (J.snd c)).obj.map (homOfLE hNU).op).hom.comp (α (J.snd c)).hom)
      have hPg : P ≤ f.range.comap g := by
        apply Submodule.span_le.mpr
        intro z hz
        obtain rfl := Set.mem_singleton_iff.mp hz
        exact ⟨t, Prod.ext hf hg⟩
      let ψ : P →ₗ[R] (I.left c).obj.obj (op N) :=
        (LinearEquiv.ofInjective f (hinj N hNU c)).symm.toLinearMap.comp
          (g.restrict (fun z hz => hPg hz))
      have hψ (z : P) : f (ψ z) = g z :=
        LinearEquiv.ofInjective_symm_apply f (h := hinj N hNU c)
          (g.restrict (fun z hz => hPg hz) z)
      refine ⟨N, hNU, SemimoduleCat.ofHom ψ, hxN, ?_, ?_⟩
      · apply SemimoduleCat.hom_ext
        apply LinearMap.ext
        intro z
        have hz := congrArg _root_.Prod.fst (hψ z)
        change (I.fst c).hom.app (op N) (ψ z) =
          (I.right (J.fst c)).obj.map (homOfLE hNU).op ((α (J.fst c)).hom z.val) at hz
        simpa only [β, SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom,
          LinearMap.comp_apply, Submodule.subtype_apply] using hz
      · apply SemimoduleCat.hom_ext
        apply LinearMap.ext
        intro z
        have hz := congrArg _root_.Prod.snd (hψ z)
        change (I.snd c).hom.app (op N) (ψ z) =
          (I.right (J.snd c)).obj.map (homOfLE hNU).op ((α (J.snd c)).hom z.val) at hz
        simpa only [β, SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom,
          LinearMap.comp_apply, Submodule.subtype_apply] using hz)
  let aP : P := ⟨a, Submodule.mem_span_singleton_self a⟩
  have hright (j : J.R) : (ℓ aP).val (.right j) = (α j).hom a := by
    simpa only [β, SemimoduleCat.hom_ofHom, LinearMap.comp_apply,
      Submodule.subtype_apply] using hℓ aP j
  have hface := (I.sectionsIndex U).mem_sectionsSubmodule_multispan.mp (ℓ aP).property
  exact ⟨(ℓ aP).val (.left b), Prod.ext ((hface.1 b).trans (hright _))
    ((hface.2 b).trans (hright _))⟩

end CategoryTheory.Limits.MultispanIndex
