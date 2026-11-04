/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Multispan.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Testing common face lifts on finite lists of inputs

For jointly injective face spans, linear chamber maps extend uniquely to a
matching family if their restrictions along every map from a finite free
semimodule have a common total lift at every face. The lift is required only
for the two total chamber maps; individual summands need not lift.

The input semimodule, chamber set and face set may all be infinite. The proof
uses the existing matching-family reconstruction. In particular it does not
choose separate lifts for the terms of a local resolution. This is the
finite-input test for terminal resolutions in
[Scattering Diagrams §5.4](https://github.com/yuma-mizuno/TauCetiRoadmap/blob/mei/TauCetiRoadmap/ScatteringDiagrams/README.md#54-local-resolutions-and-gluing-of-sections).
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.MultispanIndex

variable {R : Type*} [Semiring R] {J : MultispanShape}
  (I : MultispanIndex J (SemimoduleCat R))
  {E : Type*} [AddCommMonoid E] [Module R E]
  (α : ∀ j, E →ₗ[R] I.right j)

/-- Matching families for an arbitrary incoming semimodule are characterized by
common total face lifts after testing every finite list of inputs. Joint
injectivity supplies uniqueness; neither individual face leg need be injective. -/
theorem existsUnique_sections_lift_iff_finiteInput
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    (∃! ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule I.multispan,
      ∀ x j, (ℓ x).val (.right j) = α j x) ↔
      ∀ n (a : (Fin n → R) →ₗ[R] E) b,
        ∃ l : (Fin n → R) →ₗ[R] I.left b,
          (I.fst b).hom.comp l = (α (J.fst b)).comp a ∧
          (I.snd b).hom.comp l = (α (J.snd b)).comp a := by
  constructor
  · rintro ⟨ℓ, hℓ, -⟩ n a b
    refine ⟨((SemimoduleCat.sectionsEval I.multispan (.left b)).comp ℓ).comp a,
      ?_, ?_⟩
    · apply LinearMap.ext
      intro x
      change (I.fst b).hom (SemimoduleCat.sectionsEval I.multispan (.left b)
        (ℓ (a x))) = α (J.fst b) (a x)
      rw [SemimoduleCat.sectionsEval_apply]
      exact ((I.mem_sectionsSubmodule_multispan.mp (ℓ (a x)).property).1 b).trans
        (hℓ (a x) (J.fst b))
    · apply LinearMap.ext
      intro x
      change (I.snd b).hom (SemimoduleCat.sectionsEval I.multispan (.left b)
        (ℓ (a x))) = α (J.snd b) (a x)
      rw [SemimoduleCat.sectionsEval_apply]
      exact ((I.mem_sectionsSubmodule_multispan.mp (ℓ (a x)).property).2 b).trans
        (hℓ (a x) (J.snd b))
  · intro h
    apply (I.existsUnique_sections_lift_iff α hinj).mpr
    intro x b
    let a : (Fin 1 → R) →ₗ[R] E :=
      (LinearMap.toSpanSingleton R E x).comp (LinearMap.proj 0)
    obtain ⟨l, hl, hr⟩ := h 1 a b
    refine ⟨l (fun _ => 1), ?_⟩
    exact Prod.ext
      (by simpa [a] using LinearMap.congr_fun hl (fun _ => 1))
      (by simpa [a] using LinearMap.congr_fun hr (fun _ => 1))

end CategoryTheory.Limits.MultispanIndex
