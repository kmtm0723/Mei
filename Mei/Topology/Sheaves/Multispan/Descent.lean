/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Multispan.Descent
public import Mei.Topology.Sheaves.Multispan.Morphism

/-!
# Local descent of matching families through coefficient embeddings

A linear matching family in the target of a coefficient embedding descends
uniquely if its chamber values have prescribed source preimages and its face maps
have linear source preimages locally on the endpoint domain. The source face legs
need only be jointly injective; the target face legs need not be jointly injective.
Local source preimages can vary with the endpoint neighborhood. No finite cover,
finite incidence diagram, finite generation, or additive inverses are required.
-/

public section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r

namespace CategoryTheory.Limits.MultispanIndex

variable {X : TopCat.{u}} {R : Type r} [Semiring R] {J : MultispanShape}

/-- A matching family descends uniquely when its prescribed chamber preimages
are compatible with the coefficient change and its face maps have linear local
preimages. Joint injectivity and chamber embeddings are only needed on subopens
of the chosen domain. -/
theorem existsUnique_sections_descent_of_local
    (I : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R)))
    {I' : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R))}
    (η : I.multispan ⟶ I'.multispan) (E : SemimoduleCat.{v} R) (U : Opens X)
    (m : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I'.sectionsIndex U).multispan)
    (α : ∀ j, E ⟶ (I.right j).obj.obj (op U))
    (hinj : ∀ (W : Opens X), W ≤ U → ∀ b,
      Function.Injective (((I.sectionsIndex W).fst b).hom.prod
        ((I.sectionsIndex W).snd b).hom))
    (hemb : ∀ (W : Opens X), W ≤ U → ∀ j,
      Function.Injective ((η.app (.right j)).hom.app (op W)).hom)
    (hα : ∀ a j, ((η.app (.right j)).hom.app (op U)).hom ((α j).hom a) =
      (m a).val (.right j))
    (hloc : ∀ b x, x ∈ U → ∃ (N : Opens X) (hNU : N ≤ U)
      (t : E ⟶ (I.left b).obj.obj (op N)), x ∈ N ∧
        t ≫ (η.app (.left b)).hom.app (op N) =
          SemimoduleCat.ofHom
            ((SemimoduleCat.sectionsEval (I'.sectionsIndex U).multispan (.left b)).comp m) ≫
              (I'.left b).obj.map (homOfLE hNU).op) :
    ∃! ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan,
      (SemimoduleCat.sectionsMap (η.sectionsMultispan U)).comp ℓ = m ∧
        ∀ a j, (ℓ a).val (.right j) = (α j).hom a := by
  let ηW (W : Opens X) := η.sectionsMultispan W
  have hembW (W : Opens X) (hWU : W ≤ U) (j : J.R) :
      Function.Injective ((ηW W).app (.right j)).hom := by
    rw [show (ηW W).app (.right j) = (η.app (.right j)).hom.app (op W) from
      η.sectionsMultispan_app_right W j]
    exact hemb W hWU j
  have hfaceinj (W : Opens X) (hWU : W ≤ U) (b : J.L) :
      Function.Injective ((ηW W).app (.left b)).hom := by
    intro s t hst
    apply hinj W hWU b
    apply Prod.ext
    · apply hembW W hWU (J.fst b)
      have hs := ConcreteCategory.congr_hom ((ηW W).naturality (WalkingMultispan.Hom.fst b)) s
      have ht := ConcreteCategory.congr_hom ((ηW W).naturality (WalkingMultispan.Hom.fst b)) t
      exact hs.trans ((congrArg ((I'.sectionsIndex W).fst b) hst).trans ht.symm)
    · apply hembW W hWU (J.snd b)
      have hs := ConcreteCategory.congr_hom ((ηW W).naturality (WalkingMultispan.Hom.snd b)) s
      have ht := ConcreteCategory.congr_hom ((ηW W).naturality (WalkingMultispan.Hom.snd b)) t
      exact hs.trans ((congrArg ((I'.sectionsIndex W).snd b) hst).trans ht.symm)
  have hαW (a : E) (j : J.R) : ((ηW U).app (.right j)).hom ((α j).hom a) =
      (m a).val (.right j) := by
    rw [show (ηW U).app (.right j) = (η.app (.right j)).hom.app (op U) from
      η.sectionsMultispan_app_right U j]
    exact hα a j
  apply (existsUnique_sections_descent_iff (ηW U) (hinj U le_rfl) (hembW U le_rfl)
    m (fun j => (α j).hom) hαW).mpr
  intro a b
  let β : E ⟶ (I'.left b).obj.obj (op U) := SemimoduleCat.ofHom
    ((SemimoduleCat.sectionsEval (I'.sectionsIndex U).multispan (.left b)).comp m)
  have hinjHom (W : Opens X) (hWU : W ≤ U) : Function.Injective
      (fun t : E ⟶ (I.left b).obj.obj (op W) =>
        (t ≫ (η.app (.left b)).hom.app (op W),
          t ≫ (η.app (.left b)).hom.app (op W))) := by
    intro s t hst
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply hfaceinj W hWU b
    rw [show (ηW W).app (.left b) = (η.app (.left b)).hom.app (op W) from
      η.sectionsMultispan_app_left W b]
    exact ConcreteCategory.congr_hom (congrArg _root_.Prod.fst hst) z
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_hom_lift_of_local
    (I.left b) (I'.left b) (I'.left b) (η.app (.left b)) (η.app (.left b)) E U
    hinjHom β β (by
      intro x hx
      obtain ⟨N, hNU, t, hxN, ht⟩ := hloc b x hx
      exact ⟨N, hNU, t, hxN, ht, ht⟩)
  refine ⟨t.hom a, ?_⟩
  rw [show (ηW U).app (.left b) = (η.app (.left b)).hom.app (op U) from
    η.sectionsMultispan_app_left U b]
  have he : ((η.app (.left b)).hom.app (op U)).hom (t.hom a) = β.hom a :=
    ConcreteCategory.congr_hom ht.1 a
  exact he.trans
    (SemimoduleCat.sectionsEval_apply (I'.sectionsIndex U).multispan (.left b) (m a))

end CategoryTheory.Limits.MultispanIndex
