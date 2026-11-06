/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration

/-!
# Coherent local transport of actual decorated rays

Where the admitted complete types agree, a ray has a unique continuation to a
new endpoint with exactly the same type. These continuations preserve the whole
decoration and obey identity, inverse and composition laws. On a neighborhood
with constant admitted types they trivialize the actual ray family by a fixed
fiber, and each transported path varies continuously in compact-open topology.

A common membership arrangement supplies such open neighborhoods for rational
semilinear type domains. Distinct complete types remain separate even when their
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

/-- Canonical continuation between endpoints admitting exactly the same complete
types. The geometric ray is reconstructed at the new endpoint. -/
def endpointEquiv {Q Q' : V} (h : ∀ t : Types, Q ∈ domain(t) ↔ Q' ∈ domain(t)) :
    Rays(Q) ≃ Rays(Q') :=
  (fiber(Q)).trans ((Equiv.subtypeEquivRight h).trans (fiber(Q')).symm)

/-- Canonical endpoint continuation preserves the entire decorated type. -/
theorem endpointEquiv_type {Q Q' : V}
    (h : ∀ t : Types, Q ∈ domain(t) ↔ Q' ∈ domain(t)) (r : Rays(Q)) :
    (fiber(Q') (endpointEquiv c P W S C h r)).val = (fiber(Q) r).val := by
  simp only [endpointEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- A ray at the new endpoint with the same complete type is the canonical
continuation. No equality of geometric paths is substituted for equality of types. -/
theorem endpointEquiv_eq_of_type_eq {Q Q' : V}
    (h : ∀ t : Types, Q ∈ domain(t) ↔ Q' ∈ domain(t)) (r : Rays(Q)) (r' : Rays(Q'))
    (ht : (fiber(Q') r').val = (fiber(Q) r).val) :
    endpointEquiv c P W S C h r = r' := by
  apply (fiber(Q')).injective
  apply Subtype.ext
  exact (endpointEquiv_type c P W S C h r).trans ht.symm

/-- Continuing a ray to its own endpoint is the identity. -/
@[simp]
theorem endpointEquiv_self {Q : V}
    (h : ∀ t : Types, Q ∈ domain(t) ↔ Q ∈ domain(t)) (r : Rays(Q)) :
    endpointEquiv c P W S C h r = r :=
  endpointEquiv_eq_of_type_eq c P W S C h r r rfl

/-- Endpoint continuation is coherent under composition. -/
theorem endpointEquiv_trans {Q₀ Q₁ Q₂ : V}
    (h₀₁ : ∀ t : Types, Q₀ ∈ domain(t) ↔ Q₁ ∈ domain(t))
    (h₁₂ : ∀ t : Types, Q₁ ∈ domain(t) ↔ Q₂ ∈ domain(t)) (r : Rays(Q₀)) :
    endpointEquiv c P W S C h₁₂ (endpointEquiv c P W S C h₀₁ r) =
      endpointEquiv c P W S C (fun t => (h₀₁ t).trans (h₁₂ t)) r := by
  apply (fiber(Q₂)).injective
  apply Subtype.ext
  simp only [endpointEquiv_type]

/-- Reversing the endpoint comparison gives the inverse continuation. -/
theorem endpointEquiv_symm {Q Q' : V}
    (h : ∀ t : Types, Q ∈ domain(t) ↔ Q' ∈ domain(t)) :
    (endpointEquiv c P W S C h).symm = endpointEquiv c P W S C (fun t => (h t).symm) := by
  apply Equiv.ext
  intro r'
  apply (endpointEquiv c P W S C h).injective
  rw [Equiv.apply_symm_apply, endpointEquiv_trans, endpointEquiv_self]

/-- The whole decoration is constant along canonical endpoint continuation. -/
theorem endpointEquiv_decoration {Q Q' : V}
    (h : ∀ t : Types, Q ∈ domain(t) ↔ Q' ∈ domain(t)) (r : Rays(Q)) :
    (endpointEquiv c P W S C h r).decoration = r.decoration := by
  rw [← cutoffDecoratedRayFiberEquiv_decoration d ℳ T a v f c ε P W S C,
    endpointEquiv_type, cutoffDecoratedRayFiberEquiv_decoration]

/-- A neighborhood with constant admitted types is a product of its endpoints
and one actual ray fiber. All actual rays over the neighborhood are retained.
The endpoint projection is exposed so the dependent target fiber reduces to the
specified endpoint without inserting casts. -/
@[expose] def familyTrivialization {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) :
    U × Rays(Q₀) ≃ Σ Q : U, Rays(Q.val) where
  toFun z := ⟨z.1, endpointEquiv c P W S C (hU z.1 z.1.property) z.2⟩
  invFun z := ⟨z.1, (endpointEquiv c P W S C (hU z.1 z.1.property)).symm z.2⟩
  left_inv z := by simp
  right_inv z := by simp

/-- The trivialization leaves the endpoint coordinate unchanged. -/
@[simp]
theorem familyTrivialization_endpoint {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) (z : U × Rays(Q₀)) :
    (familyTrivialization c P W S C hU z).1 = z.1 := by rfl

/-- Every product branch retains its exact complete decorated type. -/
@[simp]
theorem familyTrivialization_type {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) (z : U × Rays(Q₀)) :
    (fiber(z.1.val) (familyTrivialization c P W S C hU z).2).val = (fiber(Q₀) z.2).val :=
  endpointEquiv_type c P W S C (hU z.1 z.1.property) z.2

/-- The whole coefficient, not just its homogeneous degree, is preserved. -/
theorem familyTrivialization_decoration {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) (z : U × Rays(Q₀)) :
    (familyTrivialization c P W S C hU z).2.decoration = z.2.decoration :=
  endpointEquiv_decoration c P W S C (hU z.1 z.1.property) z.2

/-- Changing the reference fiber gives a constant transition on an overlap:
first transport the fixed reference ray, then use the second product chart. -/
theorem familyTrivialization_change_base {U : Set V} {Q₀ Q₁ : V}
    (h₀ : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t))
    (h₁ : ∀ Q ∈ U, ∀ t : Types, Q₁ ∈ domain(t) ↔ Q ∈ domain(t))
    (h₀₁ : ∀ t : Types, Q₀ ∈ domain(t) ↔ Q₁ ∈ domain(t))
    (Q : U) (r : Rays(Q₀)) :
    (familyTrivialization c P W S C h₁
      (Q, endpointEquiv c P W S C h₀₁ r)).2 =
        (familyTrivialization c P W S C h₀ (Q, r)).2 := by
  -- Expand only the forward maps of the two product charts.
  change endpointEquiv c P W S C (h₁ Q Q.property)
    (endpointEquiv c P W S C h₀₁ r) = endpointEquiv c P W S C (h₀ Q Q.property) r
  apply (fiber(Q.val)).injective
  apply Subtype.ext
  simp only [endpointEquiv_type]

/-- The path of a product branch is the continuous extension of its reference
ray's complete type, evaluated at the new endpoint. -/
theorem familyTrivialization_path {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) (z : U × Rays(Q₀)) :
    (familyTrivialization c P W S C hU z).2.realization.2.ray.toContinuousMap =
      (fiber(Q₀) z.2).val.path c z.1.val := by
  -- Expand the product chart's forward map, leaving endpoint continuation abstract.
  change (endpointEquiv c P W S C (hU z.1 z.1.property) z.2).realization.2.ray.toContinuousMap = _
  rw [toContinuousMap_eq_typePath c P W S C, endpointEquiv_type]

/-- Each actual product branch varies continuously in compact-open path space.
The path includes its entire incoming half-line. -/
theorem continuous_familyTrivialization_path {U : Set V} {Q₀ : V}
    (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)) (r : Rays(Q₀)) :
    Continuous (fun Q : U =>
      (familyTrivialization c P W S C hU (Q, r)).2.realization.2.ray.toContinuousMap) := by
  have he : (fun Q : U =>
      (familyTrivialization c P W S C hU (Q, r)).2.realization.2.ray.toContinuousMap) =
      fun Q : U => (fiber(Q₀) r).val.path c Q.val := by
    funext Q
    exact familyTrivialization_path c P W S C hU (Q, r)
  rw [he]
  exact ((fiber(Q₀) r).val.path c).continuous.comp continuous_subtype_val

/-- A single exceptional arrangement supplies genuine local product charts of
actual rays, with continuous path branches and constant complete types and weights.
The charts also admit the canonical identity and composition laws above. -/
theorem exists_localFamilyTrivialization
    {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
    {h : TauCeti.Toric.IsIntegralLattice i}
    (hdom : ∀ t : Types, IsRationalSemilinear h (domain(t))) :
    ∃ E : ExceptionalArrangement V,
      (∀ t : Types, frontier (domain(t)) ⊆ {Q | ¬ E.IsGeneric Q}) ∧
      ∀ Q₀, E.IsGeneric Q₀ →
        ∃ (U : Set V) (_ : IsOpen U) (_ : Q₀ ∈ U)
          (hU : ∀ Q ∈ U, ∀ t : Types, Q₀ ∈ domain(t) ↔ Q ∈ domain(t)),
          let e := familyTrivialization c P W S C hU
          (∀ z, (e z).1 = z.1) ∧
          (∀ z, (fiber(z.1.val) (e z).2).val = (fiber(Q₀) z.2).val) ∧
          (∀ z, (e z).2.decoration = z.2.decoration) ∧
          ∀ r : Rays(Q₀), Continuous
            (fun Q : U => (e (Q, r)).2.realization.2.ray.toContinuousMap) := by
  obtain ⟨E, hfrontier, hstable⟩ := IsRationalSemilinear.exists_membershipArrangement hdom
  refine ⟨E, hfrontier, fun Q₀ hQ₀ => ?_⟩
  obtain ⟨U, hUsub, hUopen, hQ₀U⟩ := mem_nhds_iff.mp (hstable Q₀ hQ₀)
  let hU (Q : V) (hQ : Q ∈ U) (t : Types) := (hUsub hQ t).symm
  refine ⟨U, hUopen, hQ₀U, hU, ?_, ?_, ?_, ?_⟩
  · exact familyTrivialization_endpoint c P W S C hU
  · exact familyTrivialization_type c P W S C hU
  · exact familyTrivialization_decoration c P W S C hU
  · exact continuous_familyTrivialization_path c P W S C hU

end Mei.CutoffDecoratedRay
