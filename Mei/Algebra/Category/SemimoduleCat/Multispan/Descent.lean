/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Multispan.Basic

/-!
# Descent of matching families through coefficient embeddings

Suppose the chamber maps of a coefficient change are injective, and chamber
values in the target have prescribed preimages. A linear matching family descends
uniquely precisely when each target face value also has a source preimage.
The source spans need only be jointly injective; no joint injectivity is imposed
on the target spans. Neither surjectivity of coefficient maps nor finite
generation of the incoming module is assumed.

This is the common-face-lift descent criterion for coefficient embeddings:
chamber identities reflect through injective maps, while face lifts require the
additional preimage condition. All matching-family carriers and coefficient maps
are the existing semimodule sections, with no replacement carrier.
-/

public section

open CategoryTheory

namespace CategoryTheory.Limits.MultispanIndex

variable {R : Type*} [Semiring R] {J : MultispanShape}
  {I I' : MultispanIndex J (SemimoduleCat R)}
  (η : I.multispan ⟶ I'.multispan)
  (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
  (hemb : ∀ j, Function.Injective (η.app (.right j)).hom)
  {E : Type*} [AddCommMonoid E] [Module R E]
  (m : E →ₗ[R] SemimoduleCat.sectionsSubmodule I'.multispan)
  (α : ∀ j, E →ₗ[R] I.right j)
  (hα : ∀ a j, (η.app (.right j)).hom (α j a) = (m a).val (.right j))

include hinj hemb hα in
/-- Prescribed chamber preimages assemble to a unique linear descent exactly
when the target face values have source preimages. In particular a terminal
common lift descends only when its face coefficient lies in the source image. -/
theorem existsUnique_sections_descent_iff :
    (∃! ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule I.multispan,
      (SemimoduleCat.sectionsMap η).comp ℓ = m ∧
        ∀ a j, (ℓ a).val (.right j) = α j a) ↔
      ∀ a b, (m a).val (.left b) ∈ LinearMap.range (η.app (.left b)).hom := by
  constructor
  · rintro ⟨ℓ, ⟨hℓ, -⟩, -⟩ a b
    refine ⟨(ℓ a).val (.left b), ?_⟩
    simpa only [LinearMap.comp_apply, SemimoduleCat.sectionsMap_apply] using
      congrArg (fun s => s.val (.left b)) (LinearMap.congr_fun hℓ a)
  · intro hface
    have hlift (a : E) (b : J.L) : ∃ x : I.left b,
        (η.app (.left b)).hom x = (m a).val (.left b) ∧
        I.fst b x = α (J.fst b) a ∧ I.snd b x = α (J.snd b) a := by
      obtain ⟨x, hx⟩ := hface a b
      have hm := I'.mem_sectionsSubmodule_multispan.mp (m a).property
      refine ⟨x, hx, ?_, ?_⟩
      · apply hemb (J.fst b)
        have hn : (η.app (.right (J.fst b))).hom (I.fst b x) =
            I'.fst b ((η.app (.left b)).hom x) :=
          ConcreteCategory.congr_hom (η.naturality (WalkingMultispan.Hom.fst b)) x
        exact hn.trans ((congrArg (I'.fst b) hx).trans ((hm.1 b).trans (hα a _).symm))
      · apply hemb (J.snd b)
        have hn : (η.app (.right (J.snd b))).hom (I.snd b x) =
            I'.snd b ((η.app (.left b)).hom x) :=
          ConcreteCategory.congr_hom (η.naturality (WalkingMultispan.Hom.snd b)) x
        exact hn.trans ((congrArg (I'.snd b) hx).trans ((hm.2 b).trans (hα a _).symm))
    obtain ⟨ℓ, hℓ, huniq⟩ := (I.existsUnique_sections_lift_iff α hinj).mpr (by
      intro a b
      obtain ⟨x, -, hf, hg⟩ := hlift a b
      exact ⟨x, Prod.ext hf hg⟩)
    refine ⟨ℓ, ⟨?_, hℓ⟩, fun q hq => huniq q hq.2⟩
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext j
    simp only [LinearMap.comp_apply, SemimoduleCat.sectionsMap_apply]
    cases j with
    | right j => rw [hℓ]; exact hα a j
    | left b =>
      obtain ⟨x, hx, hf, hg⟩ := hlift a b
      have hs := I.mem_sectionsSubmodule_multispan.mp (ℓ a).property
      have he : (ℓ a).val (.left b) = x := hinj b (Prod.ext
        ((hs.1 b).trans ((hℓ a _).trans hf.symm))
        ((hs.2 b).trans ((hℓ a _).trans hg.symm)))
      rw [he]
      exact hx

end CategoryTheory.Limits.MultispanIndex
