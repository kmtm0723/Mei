/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Continuation

/-!
# Coherent local transport of actual decorated rays

Where the admitted complete types agree, a ray has a unique continuation to a
new endpoint with exactly the same type. These continuations preserve the whole
decoration and obey identity, inverse and composition laws. On a neighborhood
with constant admitted types they trivialize the actual ray family by a fixed
fiber, and each transported path varies continuously in compact-open topology.

The canonical continuation theorem supplies such open neighborhoods from a
common membership arrangement for rational semilinear type domains. Distinct
complete types remain separate even when their
geometric paths or decorations coincide. The family equivalence is an equivalence
of actual rays; no topology on the dependent ray fibers is asserted.

The endpoint-family interpretation follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedRay

variable {R M Γ V J K O : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ}
  (c : J → ℝ) (P : J → Set V) (W : O → Set V) (S : K → Set V) (C : Set V)

local notation "Types" => CutoffDecoratedType d ℳ T a v f ε k
local notation "Rays(" Q ")" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
local notation "domain(" t ")" => CutoffDecoratedType.domain c P W S C t
local notation "fiber(" Q ")" => cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q

/-- A neighborhood with constant admitted types is a product of its endpoints
and one actual ray fiber. All actual rays over the neighborhood are retained. -/
def familyTrivialization {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) :
    U × Rays(Q₀) ≃ Σ Q : U, Rays(Q.val) :=
  (Equiv.sigmaEquivProdOfEquiv
    (fun Q : U => (endpointEquiv c P W S C (hU Q Q.property)).symm)).symm

/-- The forward chart map keeps the endpoint and continues the reference ray. -/
@[simp]
theorem familyTrivialization_apply {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) (z : U × Rays(Q₀)) :
    familyTrivialization c P W S C hU z =
      ⟨z.1, endpointEquiv c P W S C (hU z.1 z.1.property) z.2⟩ := (rfl)

/-- The inverse chart map returns the ray to the reference fiber. -/
@[simp]
theorem familyTrivialization_symm_apply {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) (z : Σ Q : U, Rays(Q.val)) :
    (familyTrivialization c P W S C hU).symm z =
      ⟨z.1, (endpointEquiv c P W S C (hU z.1 z.1.property)).symm z.2⟩ := (rfl)

/-- The trivialization leaves the endpoint coordinate unchanged. -/
theorem familyTrivialization_endpoint {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) (z : U × Rays(Q₀)) :
    (familyTrivialization c P W S C hU z).1 = z.1 := (rfl)

/-- The inverse trivialization also leaves the endpoint coordinate unchanged. -/
theorem familyTrivialization_symm_endpoint {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) (z : Σ Q : U, Rays(Q.val)) :
    ((familyTrivialization c P W S C hU).symm z).1 = z.1 := (rfl)

/-- Every product branch retains its exact complete decorated type. -/
@[simp↓]
theorem familyTrivialization_type {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) (z : U × Rays(Q₀)) :
    (fiber((familyTrivialization c P W S C hU z).1.val)
      (familyTrivialization c P W S C hU z).2).val = (fiber(Q₀) z.2).val :=
  endpointEquiv_type c P W S C (hU z.1 z.1.property) z.2

/-- The whole coefficient, not just its homogeneous degree, is preserved. -/
@[simp↓]
theorem familyTrivialization_decoration {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) (z : U × Rays(Q₀)) :
    (familyTrivialization c P W S C hU z).2.decoration = z.2.decoration :=
  endpointEquiv_decoration c P W S C (hU z.1 z.1.property) z.2

/-- Returning a chart ray to the reference fiber preserves its whole coefficient. -/
@[simp↓]
theorem familyTrivialization_symm_decoration {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t))
    (z : Σ Q : U, Rays(Q.val)) :
    ((familyTrivialization c P W S C hU).symm z).2.decoration = z.2.decoration := by
  rw [familyTrivialization_symm_apply, endpointEquiv_symm_decoration]

/-- Changing the reference fiber gives a constant transition on an overlap:
first transport the fixed reference ray, then use the second product chart. -/
theorem familyTrivialization_change_base {U : Set V} {Q₀ Q₁ : V}
    (h₀ : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t))
    (h₁ : ∀ Q ∈ U, ∀ t : Types, Q₁ ∈ domain(t) ↔ Q ∈ domain(t))
    (h₀₁ : ∀ t : Types, Q₀ ∈ domain(t) ↔ Q₁ ∈ domain(t))
    (Q : U) (r : Rays(Q₀)) :
    familyTrivialization c P W S C h₁ (Q, endpointEquiv c P W S C h₀₁ r) =
      familyTrivialization c P W S C h₀ (Q, r) := by
  rw [familyTrivialization_apply, familyTrivialization_apply]
  congr 1
  exact endpointEquiv_trans c P W S C h₀₁ (h₁ Q Q.property) r

/-- The path of a product branch is the continuous extension of its reference
ray's complete type, evaluated at the new endpoint. -/
theorem familyTrivialization_path {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) (z : U × Rays(Q₀)) :
    (familyTrivialization c P W S C hU z).2.realization.2.ray.toContinuousMap =
      (fiber(Q₀) z.2).val.path c z.1.val := by
  rw [familyTrivialization_apply, toContinuousMap_eq_typePath c P W S C, endpointEquiv_type]

/-- Each actual product branch varies continuously in compact-open path space.
The path includes its entire incoming half-line. -/
theorem continuous_familyTrivialization_path {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) (r : Rays(Q₀)) :
    Continuous (fun Q : U =>
      (familyTrivialization c P W S C hU (Q, r)).2.realization.2.ray.toContinuousMap) := by
  apply continuous_of_type_eq c P W S C
    (fun Q : U => (familyTrivialization c P W S C hU (Q, r)).2)
    (fiber(Q₀) r).val
  · simpa only [familyTrivialization_endpoint] using
      (continuous_subtype_val : Continuous (fun Q : U => Q.val))
  · intro Q
    exact familyTrivialization_type c P W S C hU (Q, r)

end Mei.CutoffDecoratedRay
