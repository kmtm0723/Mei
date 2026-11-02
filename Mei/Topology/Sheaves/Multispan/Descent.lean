/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Multispan.Descent
public import Mei.Topology.Sheaves.Multispan.Morphism
public import Mei.LinearAlgebra.CommonLift

/-!
# Local descent of matching families through coefficient embeddings

A linear matching family in the target of a coefficient embedding descends
uniquely if its chamber values have prescribed source preimages and each face value
has a source preimage locally on the endpoint domain, separately for each input.
The source face legs
need only be jointly injective; the target face legs need not be jointly injective.
Local source preimages and their neighborhoods can vary with both input and endpoint.
No finite cover,
finite incidence diagram, finite generation, or additive inverses are required.
-/

public section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r

namespace CategoryTheory.Limits.MultispanIndex

variable {X : TopCat.{u}} {R : Type r} [Semiring R] {J : MultispanShape}

/-- A matching family descends uniquely when its prescribed chamber preimages
are compatible with the coefficient change and its face values have pointwise local
preimages. The preimages need not vary linearly and neighborhoods may depend on
the input. Joint injectivity and chamber embeddings are only needed on subopens
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
    (hloc : ∀ a b x, x ∈ U → ∃ (N : Opens X) (hNU : N ≤ U)
      (s : (I.left b).obj.obj (op N)), x ∈ N ∧
        (η.app (.left b)).hom.app (op N) s =
          (I'.left b).obj.map (homOfLE hNU).op ((m a).val (.left b))) :
    ∃! ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan,
      (SemimoduleCat.sectionsMap (η.sectionsMultispan U)).comp ℓ = m ∧
        ∀ a j, (ℓ a).val (.right j) = (α j).hom a := by
  let ηW (W : Opens X) := η.sectionsMultispan W
  have hembW (W : Opens X) (hWU : W ≤ U) (j : J.R) :
      Function.Injective ((ηW W).app (.right j)).hom := by
    -- The mapped index and evaluated diagram have different dependent object types;
    -- rewriting the public component equality aligns their carriers before using hemb.
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
    -- Align the dependent chamber carrier as above; simp alone leaves the two object types.
    rw [show (ηW U).app (.right j) = (η.app (.right j)).hom.app (op U) from
      η.sectionsMultispan_app_right U j]
    exact hα a j
  apply (existsUnique_sections_descent_iff (ηW U) (hinj U le_rfl) (hembW U le_rfl)
    m (fun j => (α j).hom) hαW).mpr
  intro a b
  -- Work on the cyclic submodule of this target face value. It lies in the
  -- section universe even when R does not; span closure supplies linear local
  -- lifts without imposing linearity or uniform neighborhoods on hloc.
  let z := (m a).val (.left b)
  let P : Submodule R ((I'.left b).obj.obj (op U)) := Submodule.span R {z}
  let β : SemimoduleCat.of R P ⟶ (I'.left b).obj.obj (op U) :=
    SemimoduleCat.ofHom P.subtype
  have hraw (W : Opens X) (hWU : W ≤ U) :
      Function.Injective ((η.app (.left b)).hom.app (op W)).hom := by
    have hi := hfaceinj W hWU b
    -- Rewrite the public face equation to move injectivity to the original section carrier.
    rw [show (ηW W).app (.left b) = (η.app (.left b)).hom.app (op W) from
      η.sectionsMultispan_app_left W b] at hi
    exact hi
  have hinjHom (W : Opens X) (hWU : W ≤ U) : Function.Injective
      (fun t : SemimoduleCat.of R P ⟶ (I.left b).obj.obj (op W) =>
        (t ≫ (η.app (.left b)).hom.app (op W),
          t ≫ (η.app (.left b)).hom.app (op W))) := by
    intro s t hst
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro p
    exact hraw W hWU (ConcreteCategory.congr_hom (congrArg _root_.Prod.fst hst) p)
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_hom_lift_of_local
    (I.left b) (I'.left b) (I'.left b) (η.app (.left b)) (η.app (.left b))
    (SemimoduleCat.of R P) U hinjHom β β (by
      intro x hx
      obtain ⟨N, hNU, s, hxN, hs⟩ := hloc a b x hx
      let f := ((η.app (.left b)).hom.app (op N)).hom
      let r := ((I'.left b).obj.map (homOfLE hNU).op).hom
      have hPr : P ≤ f.range.comap r := by
        apply Submodule.span_le.mpr
        intro q hq
        obtain rfl := Set.mem_singleton_iff.mp hq
        exact ⟨s, hs⟩
      have hrange : LinearMap.range (r.comp P.subtype) ≤ f.range := by
        rintro q ⟨p, rfl⟩
        exact hPr p.property
      obtain ⟨ψ, hψ⟩ := (LinearMap.exists_comp_eq_iff_range_le (hraw N hNU)).mpr hrange
      have hψ' : SemimoduleCat.ofHom ψ ≫ (η.app (.left b)).hom.app (op N) =
          β ≫ (I'.left b).obj.map (homOfLE hNU).op := by
        apply SemimoduleCat.hom_ext
        -- The Hom-sheaf equation is exactly the canonical linear factorization.
        change f.comp ψ = r.comp P.subtype
        exact hψ
      exact ⟨N, hNU, SemimoduleCat.ofHom ψ, hxN, hψ', hψ'⟩)
  let p : P := ⟨z, Submodule.mem_span_singleton_self z⟩
  refine ⟨t.hom p, ?_⟩
  have he : ((η.app (.left b)).hom.app (op U)).hom (t.hom p) = z :=
    ConcreteCategory.congr_hom ht.1 p
  -- Match the dependent face carrier in the algebraic range criterion to the original one.
  rw [show (ηW U).app (.left b) = (η.app (.left b)).hom.app (op U) from
    η.sectionsMultispan_app_left U b]
  exact he

end CategoryTheory.Limits.MultispanIndex
