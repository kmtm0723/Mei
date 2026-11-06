/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.FiniteInput
public import Mei.Topology.Sheaves.Multispan

/-!
# Matching families from finite input certificates

Chamber evaluations need not be supplied as linear maps. For each finite set of
incoming vectors, a linear chamber expansion on its span and local linear common
face lifts suffice. The expansion agrees with the evaluations only at the tested
vectors. Different tests may use different expansions and neighborhoods, with no
compatibility assumed between them. Finite interpolation proves global linearity;
local common face lifts then produce the unique matching family.
-/

public section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r

namespace CategoryTheory.Limits.MultispanIndex

variable {X : TopCat.{u}} {R : Type r} [Semiring R] {J : MultispanShape}

/-- Finite-input linear expansions with local common face lifts determine a
unique global linear matching family. No global linearity of the chamber
evaluations and no compatibility between finite-input certificates are assumed.
Face legs need only be jointly injective, and the incoming semimodule and the
incidence diagram need not be finite. -/
theorem existsUnique_sections_lift_of_finite_inputs
    (I : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R)))
    (E : SemimoduleCat.{v} R) (U : Opens X)
    (f : ∀ j, E → (I.right j).obj.obj (op U))
    (hinj : ∀ (W : Opens X), W ≤ U → ∀ b,
      Function.Injective (((I.sectionsIndex W).fst b).hom.prod
        ((I.sectionsIndex W).snd b).hom))
    (hfin : ∀ s : Finset E, ∃ β : ∀ j,
      SemimoduleCat.of R (Submodule.span R (s : Set E)) ⟶ (I.right j).obj.obj (op U),
      (∀ j a (ha : a ∈ s), (β j).hom ⟨a, Submodule.subset_span ha⟩ = f j a) ∧
      ∀ b x, x ∈ U → ∃ (N : Opens X) (hNU : N ≤ U)
        (t : SemimoduleCat.of R (Submodule.span R (s : Set E)) ⟶
          (I.left b).obj.obj (op N)), x ∈ N ∧
          t ≫ (I.fst b).hom.app (op N) =
            β (J.fst b) ≫ (I.right (J.fst b)).obj.map (homOfLE hNU).op ∧
          t ≫ (I.snd b).hom.app (op N) =
            β (J.snd b) ≫ (I.right (J.snd b)).obj.map (homOfLE hNU).op) :
    ∃! ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan,
      ∀ a j, (ℓ a).val (.right j) = f j a := by
  classical
  have hex j := LinearMap.existsUnique_of_finite_span_interpolation (f j) (by
    intro s
    obtain ⟨β, hβ, -⟩ := hfin s
    exact ⟨(β j).hom, hβ j⟩)
  choose α hα hαuniq using hex
  obtain ⟨ℓ, hℓ, huniq⟩ := I.existsUnique_sections_lift_of_local E U
    (fun j => SemimoduleCat.ofHom (α j)) hinj (by
      intro a b x hx
      obtain ⟨β, hβ, hloc⟩ := hfin {a}
      obtain ⟨N, hNU, t, hxN, hf, hg⟩ := hloc b x hx
      let aP : Submodule.span R (({a} : Finset E) : Set E) :=
        ⟨a, Submodule.subset_span (Finset.mem_singleton_self a)⟩
      refine ⟨N, hNU, t aP, hxN, ?_, ?_⟩
      · have he : (I.fst b).hom.app (op N) (t aP) =
          (I.right (J.fst b)).obj.map (homOfLE hNU).op ((β (J.fst b)).hom aP) :=
          ConcreteCategory.congr_hom hf aP
        rw [hβ _ a (Finset.mem_singleton_self a)] at he
        simpa only [SemimoduleCat.hom_ofHom, hα] using he
      · have he : (I.snd b).hom.app (op N) (t aP) =
          (I.right (J.snd b)).obj.map (homOfLE hNU).op ((β (J.snd b)).hom aP) :=
          ConcreteCategory.congr_hom hg aP
        rw [hβ _ a (Finset.mem_singleton_self a)] at he
        simpa only [SemimoduleCat.hom_ofHom, hα] using he)
  refine ⟨ℓ, fun a j => (hℓ a j).trans (hα j a), ?_⟩
  intro q hq
  exact huniq q (fun a j => (hq a j).trans (hα j a).symm)

end CategoryTheory.Limits.MultispanIndex
