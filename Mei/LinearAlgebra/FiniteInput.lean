/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Linearity from finite input tests

A function is linear if every finite set of inputs admits a linear interpolation
on its span. The interpolations need only agree with the function on the tested
vectors, and no compatibility between different interpolations is assumed.
This permits different finite expansions or refinements for each input test.
-/

public section

namespace LinearMap

variable {R E F : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
  [AddCommMonoid F] [Module R F]

/-- Finite linear interpolation forces a function to be linear, even when the
incoming module is not finitely generated. Only the tested vectors, not their
whole span, must agree with the chosen interpolation. -/
theorem existsUnique_of_finite_span_interpolation (f : E → F)
    (hfin : ∀ s : Finset E, ∃ g : Submodule.span R (s : Set E) →ₗ[R] F,
      ∀ a (ha : a ∈ s), g ⟨a, Submodule.subset_span ha⟩ = f a) :
    ∃! g : E →ₗ[R] F, ∀ a, g a = f a := by
  classical
  have hadd (a b : E) : f (a + b) = f a + f b := by
    let s : Finset E := {a, b, a + b}
    obtain ⟨g, hg⟩ := hfin s
    have ha : a ∈ s := by simp [s]
    have hb : b ∈ s := by simp [s]
    have hab : a + b ∈ s := by simp [s]
    rw [← hg (a + b) hab, ← hg a ha, ← hg b hb]
    exact g.map_add ⟨a, Submodule.subset_span ha⟩ ⟨b, Submodule.subset_span hb⟩
  have hsmul (r : R) (a : E) : f (r • a) = r • f a := by
    let s : Finset E := {a, r • a}
    obtain ⟨g, hg⟩ := hfin s
    have ha : a ∈ s := by simp [s]
    have hra : r • a ∈ s := by simp [s]
    rw [← hg (r • a) hra, ← hg a ha]
    exact g.map_smul r ⟨a, Submodule.subset_span ha⟩
  refine ⟨{ toFun := f, map_add' := hadd, map_smul' := hsmul }, fun _ => rfl, ?_⟩
  intro g hg
  exact LinearMap.ext hg

end LinearMap
