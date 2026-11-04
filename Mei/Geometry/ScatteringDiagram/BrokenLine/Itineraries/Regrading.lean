/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Coefficient.Embedding

/-!
# Regrading all cutoff encounter itineraries

An injective additive degree map identifies surviving coefficient histories over
all finite encounter words. Only membership in the two chosen cutoffs and in the
positive monoids must agree on the degree map's image. The target grading may
have other degrees; every actual target history still lifts by coefficient
naturality. No finite ambient grading or assumed encounter bound is used.

The comparison retains the complete path, incoming tail, encounter parameters
and every whole-component segment decoration. Weighted cutoff evaluations commute
with the coefficient map, even when some source decorations vanish.
-/

public noncomputable section

namespace Mei

open Mei.Convex

variable {R M N Γ Δ V J K : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommGroup Γ] [DecidableEq Γ] [AddCommGroup Δ] [DecidableEq Δ]
  (d : PositiveDegrees Γ) (e : PositiveDegrees Δ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (𝓝 : Δ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (σ : Γ →+ Δ) (hσ : Function.Injective σ)
  (hr : ∀ p x, x ∈ ℳ p → r x ∈ 𝓝 (σ p))
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (U : J → Module.End R N)
  (hT : ∀ j, r.comp (T j) = (U j).comp r)
  (a : ℳ 0) (v : Γ → V) (w : Δ → V) (hv : ∀ p, v p = w (σ p))
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P W : J → Set V) (S : K → Set V) (C : Set V)
  (k l : ℕ) (hcut : ∀ p, p ∈ d.cutoff k ↔ σ p ∈ e.cutoff l)
  (hpos : ∀ p, p ∈ d.monoid ↔ σ p ∈ e.monoid) (Q : V)

local notation "a'" => (Subtype.mk (r a)
  (Eq.mp (congrArg (fun q => r a ∈ 𝓝 q) (map_zero σ)) (hr 0 a a.property)) : 𝓝 0)
local notation "Source" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
local notation "Target" => CutoffDecoratedRay e 𝓝 U a' w f c ε P W S C l Q

private def wordIncomingEquiv (word : List J) (p q : Δ) (b : 𝓝 p) (b' : 𝓝 q)
    (h : p = q) (hb : (b : N) = b') :
    DecoratedAdmissibleRay 𝓝 (fun j => U (word.get j)) p b w
      (fun j => f (word.get j)) (fun j => c (word.get j))
      (fun j => ε (word.get j)) (fun j => P (word.get j)) W S C Q ≃
    DecoratedAdmissibleRay 𝓝 (fun j => U (word.get j)) q b' w
      (fun j => f (word.get j)) (fun j => c (word.get j))
      (fun j => ε (word.get j)) (fun j => P (word.get j)) W S C Q := by
  subst q
  have he : b = b' := Subtype.ext hb
  subst b'
  exact Equiv.refl _

omit [AddCommGroup Δ] in
private theorem wordIncomingEquiv_properties (word : List J) (p q : Δ)
    (b : 𝓝 p) (b' : 𝓝 q) (h : p = q) (hb : (b : N) = b') (β) :
    let γ := wordIncomingEquiv 𝓝 U w f c ε P W S C Q word p q b b' h hb β
    γ.1.val = β.1.val ∧ γ.2.ray = β.2.ray ∧ γ.2.parameter = β.2.parameter ∧
      γ.decoration = β.decoration := by
  subst q
  have he : b = b' := Subtype.ext hb
  subst b'
  exact ⟨rfl, rfl, rfl, rfl⟩

include hσ hT hv in
private def wordCoefficientEquiv (word : List J) :
    {β : DecoratedAdmissibleRay ℳ (fun j => T (word.get j)) 0 a v
      (fun j => f (word.get j)) (fun j => c (word.get j))
      (fun j => ε (word.get j)) (fun j => P (word.get j)) W S C Q //
      r (β.decoration 0) ≠ 0} ≃
    DecoratedAdmissibleRay 𝓝 (fun j => U (word.get j)) 0 a' w
      (fun j => f (word.get j)) (fun j => c (word.get j))
      (fun j => ε (word.get j)) (fun j => P (word.get j)) W S C Q :=
  (decoratedRayCoefficientEquiv ℳ 𝓝 r σ hr hσ (fun j => T (word.get j))
    (fun j => U (word.get j)) (fun j => hT (word.get j)) 0 a v w hv
    (fun j => f (word.get j)) (fun j => c (word.get j))
    (fun j => ε (word.get j)) (fun j => P (word.get j)) W S C Q).trans
      (wordIncomingEquiv 𝓝 U w f c ε P W S C Q word (σ 0) 0
        ⟨r a, hr 0 a a.property⟩ a' σ.map_zero rfl)

private theorem wordCoefficientEquiv_history (word : List J) (β) :
    (wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv f c ε P W S C Q word β).1.val =
      σ ∘ β.val.1.val := by
  rw [wordCoefficientEquiv, Equiv.trans_apply,
    (wordIncomingEquiv_properties ..).1]
  exact decoratedRayCoefficientEquiv_history ..

private theorem wordCoefficientEquiv_ray (word : List J) (β) :
    (wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv f c ε P W S C Q word β).2.ray =
      β.val.2.ray := by
  rw [wordCoefficientEquiv, Equiv.trans_apply,
    (wordIncomingEquiv_properties ..).2.1]
  exact decoratedRayCoefficientEquiv_ray ..

private theorem wordCoefficientEquiv_parameter (word : List J) (β) :
    (wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv f c ε P W S C Q word β).2.parameter =
      β.val.2.parameter := by
  rw [wordCoefficientEquiv, Equiv.trans_apply,
    (wordIncomingEquiv_properties ..).2.2.1]
  exact decoratedRayCoefficientEquiv_parameter ..

private theorem wordCoefficientEquiv_decoration (word : List J) (β) (j) :
    (wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv f c ε P W S C Q word β).decoration j =
      r (β.val.decoration j) := by
  rw [wordCoefficientEquiv, Equiv.trans_apply,
    congrFun (wordIncomingEquiv_properties ..).2.2.2 j]
  exact decoratedRayCoefficientEquiv_decoration ..

/-- Over all encounter words, regrading identifies exactly the source rays whose
final coefficient survives with the target cutoff ray family. -/
def cutoffDecoratedRayRegradingEquiv : {β : Source // r β.decoration ≠ 0} ≃ Target := by
  let F : {β : Source // r β.decoration ≠ 0} → Target := fun β => by
    let E := wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv f c ε P W S C Q
      β.val.itinerary
    let γ := E ⟨β.val.realization, by
      simpa only [CutoffDecoratedRay.decoration_eq, DecoratedAdmissibleRay.decoration_zero]
        using β.property⟩
    have hh : γ.1.val = σ ∘ β.val.realization.1.val := by
      exact wordCoefficientEquiv_history ..
    exact ⟨β.val.itinerary, γ,
      fun j => by rw [hh]; exact (hcut _).mp (β.val.degree_mem j),
      fun i j hij => by
        rw [hh]
        simpa only [Function.comp_apply, ← map_sub] using
          (hpos _).mp (β.val.degree_sub_mem i j hij)⟩
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · rintro ⟨⟨word, β, hβ, hmβ⟩, hb⟩ ⟨⟨word', γ, hγ, hmγ⟩, hc⟩ h
    have hw := congrArg CutoffDecoratedRay.itinerary h
    change word = word' at hw
    subst word'
    apply Subtype.ext
    apply CutoffDecoratedRay.ext
    · rfl
    have hg := congrArg (fun z : Target => z.degreeItinerary) h
    simp only [CutoffDecoratedRay.degreeItinerary_eq, F, wordCoefficientEquiv_history] at hg
    have hh : σ ∘ β.1.val = σ ∘ γ.1.val := by
      have he := List.ofFn_injective hg
      exact funext fun j => congrArg Prod.fst (congrFun he j)
    exact heq_of_eq (DecoratedAdmissibleRay.ext_history
      (funext fun j => hσ (congrFun hh j)))
  · intro β
    let E := wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv f c ε P W S C Q β.itinerary
    let α := E.symm β.realization
    have hh : σ ∘ α.val.1.val = β.realization.1.val := by
      have he := wordCoefficientEquiv_history ℳ 𝓝 r σ hσ hr T U hT a v w hv
        f c ε P W S C Q β.itinerary α
      change (E α).1.val = _ at he
      rw [Equiv.apply_symm_apply] at he
      exact he.symm
    let γ : Source := ⟨β.itinerary, α.val,
      fun j => (hcut _).mpr
        ((congrArg (fun q => q ∈ e.cutoff l) (congrFun hh j)).mpr (β.degree_mem j)),
      fun i j hij => (hpos _).mpr (by
        have hs : σ (α.val.1.val i - α.val.1.val j) =
            β.realization.1.val i - β.realization.1.val j :=
          (map_sub σ _ _).trans (congrArg₂ (· - ·) (congrFun hh i) (congrFun hh j))
        exact (congrArg (fun q => q ∈ e.monoid) hs).mpr (β.degree_sub_mem i j hij))⟩
    refine ⟨⟨γ, by
      simpa only [CutoffDecoratedRay.decoration_eq, DecoratedAdmissibleRay.decoration_zero]
        using α.property⟩, ?_⟩
    apply CutoffDecoratedRay.ext
    · rfl
    exact heq_of_eq (E.apply_symm_apply β.realization)

/-- Every recorded encounter, including unchanged-degree encounters, is retained. -/
@[simp]
theorem cutoffDecoratedRayRegradingEquiv_itinerary
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv f c ε P W S C
      k l hcut hpos Q β).itinerary = β.val.itinerary := (rfl)

/-- Every segment degree is regraded, retaining shifts of zero spatial direction. -/
@[simp]
theorem cutoffDecoratedRayRegradingEquiv_history
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).realization.1.val (σ ∘ β.val.realization.1.val) :=
  heq_of_eq (wordCoefficientEquiv_history ..)

/-- The entire degree-labelled encounter word is reindexed without omitting encounters. -/
@[simp]
theorem cutoffDecoratedRayRegradingEquiv_degreeItinerary
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).degreeItinerary =
      β.val.degreeItinerary.map (Prod.map σ id) := by
  simp only [CutoffDecoratedRay.degreeItinerary_eq, List.map_ofFn]
  rw [eq_of_heq (cutoffDecoratedRayRegradingEquiv_history d e ℳ 𝓝 r σ hσ hr
    T U hT a v w hv f c ε P W S C k l hcut hpos Q β)]
  rfl

/-- Regrading preserves the entire affine path, including the incoming tail. -/
@[simp]
theorem cutoffDecoratedRayRegradingEquiv_ray
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).realization.2.ray = β.val.realization.2.ray :=
  wordCoefficientEquiv_ray ..

/-- Every encounter parameter is preserved across the full cutoff family. -/
@[simp]
theorem cutoffDecoratedRayRegradingEquiv_parameter
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).realization.2.parameter β.val.realization.2.parameter :=
  heq_of_eq (wordCoefficientEquiv_parameter ..)

/-- The whole coefficient on every segment specializes by the coefficient map. -/
@[simp↓]
theorem cutoffDecoratedRayRegradingEquiv_segmentDecorations
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).realization.decoration
      (fun j => r (β.val.realization.decoration j)) :=
  heq_of_eq (funext (fun _j => wordCoefficientEquiv_decoration ..))

/-- The final whole decoration specializes without discarding retained encounters. -/
@[simp↓]
theorem cutoffDecoratedRayRegradingEquiv_decoration
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).decoration = r β.val.decoration := by
  have hh := eq_of_heq
    (cutoffDecoratedRayRegradingEquiv_history d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β)
  rw [CutoffDecoratedRay.decoration_eq, CutoffDecoratedRay.decoration_eq, hh]
  exact (map_homogeneousHistory_of_injective ℳ 𝓝 r σ hr hσ
    (fun j => T (β.val.itinerary.get j)) (fun j => U (β.val.itinerary.get j))
    (fun j => hT (β.val.itinerary.get j)) β.val.realization.1.val a).symm

/-- An injective coefficient map preserves every source ray at corresponding
cutoffs, including all unchanged-degree and zero-direction encounters. -/
def cutoffDecoratedRayRegradingEmbeddingEquiv (hinj : Function.Injective r) : Source ≃ Target :=
  (Equiv.subtypeUnivEquiv fun β => fun hz => β.decoration_ne_zero
    (hinj (by simpa only [map_zero] using hz))).symm.trans
      (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
        f c ε P W S C k l hcut hpos Q)

/-- With injective coefficients the full degree-labelled encounter word is retained. -/
@[simp]
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_degreeItinerary
    (hinj : Function.Injective r) (β : Source) :
    (cutoffDecoratedRayRegradingEmbeddingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q hinj β).degreeItinerary =
      β.degreeItinerary.map (Prod.map σ id) :=
  cutoffDecoratedRayRegradingEquiv_degreeItinerary d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q _

/-- Injective coefficient transport preserves the complete ray and incoming tail. -/
@[simp]
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_ray
    (hinj : Function.Injective r) (β : Source) :
    (cutoffDecoratedRayRegradingEmbeddingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q hinj β).realization.2.ray = β.realization.2.ray :=
  cutoffDecoratedRayRegradingEquiv_ray d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q _

/-- Injective coefficient transport preserves every encounter parameter. -/
@[simp]
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_parameter
    (hinj : Function.Injective r) (β : Source) :
    HEq (cutoffDecoratedRayRegradingEmbeddingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q hinj β).realization.2.parameter β.realization.2.parameter :=
  cutoffDecoratedRayRegradingEquiv_parameter d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q _

/-- Injective coefficient transport maps all whole-component segment decorations. -/
@[simp↓]
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_segmentDecorations
    (hinj : Function.Injective r) (β : Source) :
    HEq (cutoffDecoratedRayRegradingEmbeddingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q hinj β).realization.decoration
      (fun j => r (β.realization.decoration j)) :=
  cutoffDecoratedRayRegradingEquiv_segmentDecorations d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q _

include hσ hT hv hcut hpos in
/-- Weighted evaluation across all finite encounter words commutes with
regrading and coefficient change. Source coefficients which vanish contribute zero. -/
theorem map_cutoffDecoratedEvaluation_regrading [Finite J] :
    r (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) =
      cutoffDecoratedEvaluation e 𝓝 U a' w f c ε P W S C l Q := by
  classical
  let := Fintype.ofFinite Source
  let := Fintype.ofFinite Target
  let E := cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q
  simp only [cutoffDecoratedEvaluation_def, map_sum]
  refine Finset.sum_bij_ne_zero (fun β _ hβ => E ⟨β, hβ⟩) (by simp) ?_ ?_ ?_
  · intro β _ hβ γ _ hγ he
    exact congrArg Subtype.val (E.injective he)
  · intro β _ _
    exact ⟨(E.symm β).val, Finset.mem_univ _, (E.symm β).property, E.apply_symm_apply β⟩
  · intro β _ hβ
    exact (cutoffDecoratedRayRegradingEquiv_decoration d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q ⟨β, hβ⟩).symm

end Mei
