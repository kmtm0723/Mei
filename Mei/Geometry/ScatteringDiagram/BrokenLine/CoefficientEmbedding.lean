/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.CoefficientMap

/-!
# Coefficient embeddings of decorated ray fibers

An intertwining coefficient map and an injective map of degree sets identify the
surviving source rays with the target rays for a fixed signed encounter itinerary.
The comparison keeps the complete path, incoming tail, encounter parameters and
all whole-component segment decorations. An injective coefficient map loses no
source rays. Unchanged degrees and degree changes of zero spatial direction are
not removed, and the empty itinerary includes stationary incoming sections.

This is the fixed-itinerary coefficient-embedding comparison for the common
decorated ray construction. Whole-component decorations follow
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Definitions 3.1–3.3 (arXiv:1411.1394v2).
-/

public noncomputable section

namespace Mei

open Mei.Convex

variable {R M N Γ Δ V J K : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [DecidableEq Γ] [DecidableEq Δ]
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (𝓝 : Δ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (σ : Γ → Δ)
  (hr : ∀ p x, x ∈ ℳ p → r x ∈ 𝓝 (σ p))
  (hσ : Function.Injective σ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (T : Fin n → Module.End R M) (U : Fin n → Module.End R N)
  (hT : ∀ j, r.comp (T j) = (U j).comp r)
  (p₀ : Γ) (a : ℳ p₀) (v : Γ → V) (w : Δ → V)
  (hv : ∀ p, v p = w (σ p))
  (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (ε : Fin n → SignType)
  (P : Fin n → Set V) (W : J → Set V) (S : K → Set V) (C : Set V) (Q : V)

local notation "a'" => (Subtype.mk (r a) (hr p₀ a a.property) : 𝓝 (σ p₀))
local notation "Source" => DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q
local notation "Target" => DecoratedAdmissibleRay 𝓝 U (σ p₀) a' w f c ε P W S C Q

omit [DecidableEq Γ] [DecidableEq Δ] [NormedAddCommGroup V] [NormedSpace ℝ V] in
include hv in
private theorem regrade_velocity (p : Fin n → Γ) (j : Fin (n + 1)) :
    v (Fin.snoc (α := fun _ => Γ) p p₀ j) =
      w (Fin.snoc (α := fun _ => Δ) (σ ∘ p) (σ p₀) j) := by
  rw [hv, ← Function.comp_apply (f := σ), Fin.comp_snoc]

/-- At a fixed endpoint and itinerary, the degree history determines the entire
admissible decorated ray, including its encounter parameters and incoming tail. -/
theorem DecoratedAdmissibleRay.ext_history {β γ : Source} (h : β.1.val = γ.1.val) : β = γ := by
  obtain ⟨p, β⟩ := β
  obtain ⟨q, γ⟩ := γ
  have hpq : p = q := Subtype.ext h
  subst q
  exact congrArg (Sigma.mk p) (Subsingleton.elim β γ)

/-- An injective regrading identifies the rays whose final coefficient
survives with all target rays. The geometric source and obstacle data are fixed. -/
def decoratedRayCoefficientEquiv : {β : Source // r (β.decoration 0) ≠ 0} ≃ Target := by
  let F : {β : Source // r (β.decoration 0) ≠ 0} → Target := fun β => by
    have he := map_homogeneousHistory_of_injective ℳ 𝓝 r σ hr hσ
      T U hT β.val.1.val a
    have hnormal := (mem_decoratedHistorySupport ..).mp β.val.1.property |>.2
    refine ⟨⟨σ ∘ β.val.1.val, ?_⟩, β.val.2.congrVelocity ?_⟩
    · rw [mem_decoratedHistorySupport]
      refine ⟨?_, fun j => ?_⟩
      · rw [← he]
        simpa only [DecoratedAdmissibleRay.decoration_zero] using β.property
      · constructor
        · change f j (w (σ (β.val.1.val j))) = _
          rw [← hv, ← regrade_velocity σ p₀ v w hv β.val.1.val j.succ]
          exact (hnormal j).1
        · change SignType.sign (f j (w (σ (β.val.1.val j)))) = ε j
          rw [← hv]
          exact (hnormal j).2
    · exact funext (regrade_velocity σ p₀ v w hv β.val.1.val)
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro β γ h
    apply Subtype.ext
    apply DecoratedAdmissibleRay.ext_history
    have he : σ ∘ β.val.1.val = σ ∘ γ.val.1.val := congrArg (fun δ : Target => δ.1.val) h
    exact funext fun j => hσ (congrFun he j)
  · intro β
    obtain ⟨α, hp, hn, -, -⟩ :=
      DecoratedAdmissibleRay.exists_coefficient_refinement ℳ 𝓝 r σ hr T U hT
        p₀ a v w hv f c ε P W S C Q β
    refine ⟨⟨α, hn⟩, ?_⟩
    apply DecoratedAdmissibleRay.ext_history
    exact funext hp

/-- The coefficient comparison reindexes the full history and retains every
encounter, rather than forgetting unchanged-degree or zero-direction changes. -/
@[simp]
theorem decoratedRayCoefficientEquiv_history
    (β : {β : Source // r (β.decoration 0) ≠ 0}) :
    (decoratedRayCoefficientEquiv ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv f c ε P W S C Q β).1.val =
      σ ∘ β.val.1.val := (rfl)

/-- The entire affine path, including the incoming tail, is preserved. -/
@[simp]
theorem decoratedRayCoefficientEquiv_ray
    (β : {β : Source // r (β.decoration 0) ≠ 0}) :
    (decoratedRayCoefficientEquiv ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv f c ε P W S C Q β).2.ray =
      β.val.2.ray := by
  exact AdmissibleRayRealization.ray_congrVelocity ..

/-- All encounter parameters, including the endpoint parameter, are preserved. -/
@[simp]
theorem decoratedRayCoefficientEquiv_parameter
    (β : {β : Source // r (β.decoration 0) ≠ 0}) :
    (decoratedRayCoefficientEquiv ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv f c ε P W S C Q β).2.parameter =
      β.val.2.parameter := by
  exact AdmissibleRayRealization.parameter_congrVelocity ..

/-- The whole coefficient on every segment is the image of its source coefficient. -/
@[simp↓]
theorem decoratedRayCoefficientEquiv_decoration
    (β : {β : Source // r (β.decoration 0) ≠ 0}) (j : Fin (n + 1)) :
    (decoratedRayCoefficientEquiv ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv f c ε P W S C Q β).decoration j =
      r (β.val.decoration j) := by
  simp only [DecoratedAdmissibleRay.decoration_def, decoratedRayCoefficientEquiv_history]
  exact (map_homogeneousHistoryStage_of_injective ℳ 𝓝 r σ hr hσ T U hT
    β.val.1.val a j).symm

/-- An injective coefficient map preserves every source decoration, so no source
ray is discarded by the coefficient comparison. -/
def decoratedRayCoefficientEmbeddingEquiv (hinj : Function.Injective r) : Source ≃ Target :=
  (Equiv.subtypeUnivEquiv fun β => fun hz => β.decoration_ne_zero 0
    (hinj (by simpa only [map_zero] using hz))).symm.trans
      (decoratedRayCoefficientEquiv ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv f c ε P W S C Q)

/-- An injective coefficient comparison reindexes every selected degree. -/
@[simp]
theorem decoratedRayCoefficientEmbeddingEquiv_history (hinj : Function.Injective r)
    (β : Source) :
    (decoratedRayCoefficientEmbeddingEquiv ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv
      f c ε P W S C Q hinj β).1.val = σ ∘ β.1.val := (rfl)

/-- An injective coefficient comparison preserves the complete affine path. -/
@[simp]
theorem decoratedRayCoefficientEmbeddingEquiv_ray (hinj : Function.Injective r)
    (β : Source) :
    (decoratedRayCoefficientEmbeddingEquiv ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv
      f c ε P W S C Q hinj β).2.ray = β.2.ray := by
  exact decoratedRayCoefficientEquiv_ray ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv
    f c ε P W S C Q _

/-- An injective coefficient comparison preserves every encounter parameter. -/
@[simp]
theorem decoratedRayCoefficientEmbeddingEquiv_parameter (hinj : Function.Injective r)
    (β : Source) :
    (decoratedRayCoefficientEmbeddingEquiv ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv
      f c ε P W S C Q hinj β).2.parameter = β.2.parameter := by
  exact decoratedRayCoefficientEquiv_parameter ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv
    f c ε P W S C Q _

/-- An injective coefficient comparison maps each whole segment decoration. -/
@[simp↓]
theorem decoratedRayCoefficientEmbeddingEquiv_decoration (hinj : Function.Injective r)
    (β : Source) (j : Fin (n + 1)) :
    (decoratedRayCoefficientEmbeddingEquiv ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv
      f c ε P W S C Q hinj β).decoration j = r (β.decoration j) := by
  exact decoratedRayCoefficientEquiv_decoration ℳ 𝓝 r σ hr hσ T U hT p₀ a v w hv
    f c ε P W S C Q _ j

end Mei
