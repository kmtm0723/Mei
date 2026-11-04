/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Regrading

/-!
# Coefficient change across all cutoff encounter itineraries

A degree-preserving coefficient map intertwining the signed propagation maps
commutes with the weighted evaluation of the entire cutoff ray family. Rays
whose final decoration vanishes are discarded. The surviving source rays are
in bijection with target rays, preserving the encounter word, degree history,
geometric path and encounter times. No injectivity of the coefficient map or
endpoint genericity is required.

The construction uses `CutoffDecoratedRay` and its finite all-itinerary
inventory and the injective-degree comparison in `Itineraries.Regrading`. Since the
degrees are fixed, no histories merge, and linear propagation ensures that a
vanished intermediate decoration cannot contribute later. This is the
coefficient-specialization comparison for whole-component broken lines of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Definitions 3.1–3.3 (arXiv:1411.1394v2), and Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Definition 2.10 and
Proposition 2.13 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei

open Mei.Convex

variable {R M N Γ V J K : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (𝓝 : Γ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (hr : ∀ p x, x ∈ ℳ p → r x ∈ 𝓝 p)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (U : J → Module.End R N)
  (hT : ∀ j, r.comp (T j) = (U j).comp r)
  (a : ℳ 0) (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ)
  (ε : J → SignType) (P W : J → Set V) (S : K → Set V) (C : Set V)
  (k : ℕ) (Q : V)

local notation "a'" => (Subtype.mk (r a) (hr 0 a a.property) : 𝓝 0)
local notation "Source" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
local notation "Target" => CutoffDecoratedRay d 𝓝 U a' v f c ε P W S C k Q

/-- Specialization identifies precisely the source rays whose whole final
coefficient survives with the target rays, over every encounter itinerary. -/
def cutoffDecoratedRayCoefficientEquiv : {β : Source // r β.decoration ≠ 0} ≃ Target :=
  cutoffDecoratedRayRegradingEquiv d d ℳ 𝓝 r (AddMonoidHom.id Γ) Function.injective_id
    hr T U hT a v v (fun _ => rfl) f c ε P W S C k k (fun _ => Iff.rfl) (fun _ => Iff.rfl) Q

/-- Specialization retains every recorded encounter, including identity
components and nonzero degree changes with zero spatial projection. -/
@[simp]
theorem cutoffDecoratedRayCoefficientEquiv_itinerary
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayCoefficientEquiv d ℳ 𝓝 r hr T U hT a v f c ε P W S C k Q β).itinerary =
      β.val.itinerary :=
  cutoffDecoratedRayRegradingEquiv_itinerary d d ℳ 𝓝 r (AddMonoidHom.id Γ)
    Function.injective_id hr T U hT a v v (fun _ => rfl) f c ε P W S C
    k k (fun _ => Iff.rfl) (fun _ => Iff.rfl) Q β

/-- The selected degrees of every segment are unchanged by specialization. -/
@[simp]
theorem cutoffDecoratedRayCoefficientEquiv_history
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (cutoffDecoratedRayCoefficientEquiv d ℳ 𝓝 r hr T U hT a
      v f c ε P W S C k Q β).realization.1.val
      β.val.realization.1.val := by
  simpa only [cutoffDecoratedRayCoefficientEquiv, AddMonoidHom.coe_id, Function.id_comp] using
    cutoffDecoratedRayRegradingEquiv_history d d ℳ 𝓝 r (AddMonoidHom.id Γ)
      Function.injective_id hr T U hT a v v (fun _ => rfl) f c ε P W S C
      k k (fun _ => Iff.rfl) (fun _ => Iff.rfl) Q β

/-- Specialization preserves the entire geometric ray, including its incoming tail. -/
@[simp]
theorem cutoffDecoratedRayCoefficientEquiv_ray
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayCoefficientEquiv d ℳ 𝓝 r hr T U hT a
      v f c ε P W S C k Q β).realization.2.ray =
      β.val.realization.2.ray :=
  cutoffDecoratedRayRegradingEquiv_ray d d ℳ 𝓝 r (AddMonoidHom.id Γ)
    Function.injective_id hr T U hT a v v (fun _ => rfl) f c ε P W S C
    k k (fun _ => Iff.rfl) (fun _ => Iff.rfl) Q β

/-- All encounter times are preserved, including unchanged-direction encounters. -/
@[simp]
theorem cutoffDecoratedRayCoefficientEquiv_parameter
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (cutoffDecoratedRayCoefficientEquiv d ℳ 𝓝 r hr T U hT a
      v f c ε P W S C k Q β).realization.2.parameter
      β.val.realization.2.parameter :=
  cutoffDecoratedRayRegradingEquiv_parameter d d ℳ 𝓝 r (AddMonoidHom.id Γ)
    Function.injective_id hr T U hT a v v (fun _ => rfl) f c ε P W S C
    k k (fun _ => Iff.rfl) (fun _ => Iff.rfl) Q β

/-- The final whole decoration specializes by the given coefficient map. -/
@[simp↓]
theorem cutoffDecoratedRayCoefficientEquiv_decoration
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayCoefficientEquiv d ℳ 𝓝 r hr T U hT a v f c ε P W S C k Q β).decoration =
      r β.val.decoration :=
  cutoffDecoratedRayRegradingEquiv_decoration d d ℳ 𝓝 r (AddMonoidHom.id Γ)
    Function.injective_id hr T U hT a v v (fun _ => rfl) f c ε P W S C
    k k (fun _ => Iff.rfl) (fun _ => Iff.rfl) Q β

include hT

/-- Weighted evaluation across all cutoff itineraries commutes with a
coefficient specialization. Vanished decorations are discarded automatically. -/
theorem map_cutoffDecoratedEvaluation [Finite J] :
    r (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) =
      cutoffDecoratedEvaluation d 𝓝 U a' v f c ε P W S C k Q :=
  map_cutoffDecoratedEvaluation_regrading d d ℳ 𝓝 r (AddMonoidHom.id Γ)
    Function.injective_id hr T U hT a v v (fun _ => rfl) f c ε P W S C
    k k (fun _ => Iff.rfl) (fun _ => Iff.rfl) Q

end Mei
