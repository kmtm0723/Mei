/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Component
public import Mei.LinearAlgebra.GradedModule.Shifted.Map

/-!
# Degree-preserving maps of global shifted coefficients

A linear map preserving every homogeneous piece acts on the existing shifted
completions. These maps commute with support inclusions, hence descend through
Mathlib's module direct limit. The resulting map preserves each ambient
component, and is functorial without injectivity or a spanning hypothesis.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M N P : Type*} [AddCommGroup Γ] [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (𝓝 : Γ → Submodule R N)
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  (f : M →ₗ[R] N) (hf : ∀ u, ℳ u ≤ (𝓝 u).comap f)

omit [DirectSum.Decomposition 𝓝] in
/-- The fixed-degree coefficient map is the canonical filtered map with identity cutoff. -/
theorem completionCoefficientMap_eq_completionMap (p : Γ) :
    d.completionCoefficientMap ℳ 𝓝 p f hf =
      (d.shiftedFiltration ℳ p).completionMap (d.shiftedFiltration 𝓝 p)
        (d.shiftedCoefficientMap ℳ 𝓝 p f hf) id monotone_id
        (fun k _ ha => d.shiftedCoefficientMap_mem_filtration ℳ 𝓝 p f hf k ha) := by
  apply LinearMap.ext
  intro x
  apply (d.shiftedFiltration 𝓝 p).completion_ext
  intro k
  rw [projection_completionCoefficientMap, ModuleFiltration.projection_completionMap,
    quotientCoefficientMap_def]
  -- Both quotient maps use the identity cutoff and the same induced map.
  rfl

/-- A fixed-degree completed map applies the original linear map to each ambient component. -/
@[simp]
theorem coe_shiftedHomogeneousComponent_completionCoefficientMap (p u : Γ)
    (x : d.ShiftedCoefficients ℳ p) :
    (d.shiftedHomogeneousComponent 𝓝 p u (d.completionCoefficientMap ℳ 𝓝 p f hf x) : N) =
      f (d.shiftedHomogeneousComponent ℳ p u x) := by
  let k := (d.degree (u - p)).toNat
  have hk : d.degree (u - p) ≤ k := Int.self_le_toNat _
  obtain ⟨a, ha⟩ := ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ_surjective
    ((d.shiftedFiltration ℳ p).projection k x)
  rw [d.shiftedHomogeneousComponent_eq 𝓝 p u k hk,
    projection_completionCoefficientMap, ← ha, Submodule.mkQ_apply,
    quotientCoefficientMap_mk, shiftedQuotientComponent_mk,
    d.shiftedHomogeneousComponent_eq ℳ p u k hk, ← ha,
    Submodule.mkQ_apply, shiftedQuotientComponent_mk, coe_shiftedCoefficientMap]
  exact (DirectSum.map_decompose_shift ℳ 𝓝 f.toAddMonoidHom id
    Function.injective_id (fun i a ha => hf i ha) u a).symm

omit [DirectSum.Decomposition 𝓝] in
/-- Completing a degree-preserving map agrees with its map on ordinary shifted coefficients. -/
@[simp]
theorem completionCoefficientMap_of (p : Γ) (a : shiftedSubmodule ℳ d.monoid p) :
    d.completionCoefficientMap ℳ 𝓝 p f hf ((d.shiftedFiltration ℳ p).of a) =
      (d.shiftedFiltration 𝓝 p).of (d.shiftedCoefficientMap ℳ 𝓝 p f hf a) := by
  rw [completionCoefficientMap_eq_completionMap]
  exact (d.shiftedFiltration ℳ p).completionMap_of (d.shiftedFiltration 𝓝 p)
    (d.shiftedCoefficientMap ℳ 𝓝 p f hf) id monotone_id
    (fun k _ ha => d.shiftedCoefficientMap_mem_filtration ℳ 𝓝 p f hf k ha) a

/-- Degree-preserving completed maps commute with enlarging a support translate. -/
theorem completionCoefficientMap_inclusion (p q : Γ) (hpq : p - q ∈ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) :
    d.completionCoefficientMap ℳ 𝓝 q f hf (d.shiftedCompletedInclusion ℳ p q hpq x) =
      d.shiftedCompletedInclusion 𝓝 p q hpq (d.completionCoefficientMap ℳ 𝓝 p f hf x) := by
  apply d.shiftedCoefficients_ext 𝓝 q
  intro u
  apply Subtype.ext
  simp only [coe_shiftedHomogeneousComponent_completionCoefficientMap,
    shiftedHomogeneousComponent_inclusion]

/-- The map of global coefficients induced by a degree-preserving linear map. -/
def shiftedDirectLimitMap : d.ShiftedDirectLimit ℳ →ₗ[R] d.ShiftedDirectLimit 𝓝 :=
  Module.DirectLimit.lift R (Multiset d.monoid)
    (fun s => d.ShiftedCoefficients ℳ (d.coefficientOrigin s))
    (fun s t h => d.coefficientInclusion ℳ s t h)
    (fun s => (d.toShiftedDirectLimit 𝓝 s).comp
      (d.completionCoefficientMap ℳ 𝓝 (d.coefficientOrigin s) f hf))
    (by
      intro s t h x
      simp only [LinearMap.comp_apply, coefficientInclusion_eq,
        completionCoefficientMap_inclusion]
      simpa only [coefficientInclusion_eq] using d.toShiftedDirectLimit_inclusion 𝓝 h
        (d.completionCoefficientMap ℳ 𝓝 (d.coefficientOrigin s) f hf x))

/-- The global map restricts to the original completion map in every canonical chart. -/
@[simp]
theorem shiftedDirectLimitMap_toShiftedDirectLimit (s : Multiset d.monoid)
    (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    d.shiftedDirectLimitMap ℳ 𝓝 f hf (d.toShiftedDirectLimit ℳ s x) =
      d.toShiftedDirectLimit 𝓝 s
        (d.completionCoefficientMap ℳ 𝓝 (d.coefficientOrigin s) f hf x) := by
  simp only [shiftedDirectLimitMap, toShiftedDirectLimit_apply,
    Module.DirectLimit.lift_of, LinearMap.comp_apply]

/-- The global map acts componentwise by its original linear map. -/
@[simp]
theorem coe_shiftedDirectLimitComponents_map (x : d.ShiftedDirectLimit ℳ) (u : Γ) :
    (d.shiftedDirectLimitComponents 𝓝 (d.shiftedDirectLimitMap ℳ 𝓝 f hf x) u : N) =
      f (d.shiftedDirectLimitComponents ℳ x u) := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit ℳ x
  simp only [shiftedDirectLimitMap_toShiftedDirectLimit,
    shiftedDirectLimitComponents_toShiftedDirectLimit,
    coe_shiftedHomogeneousComponent_completionCoefficientMap]

/-- Mapping commutes with any chosen containing chart, not only a canonical origin. -/
@[simp]
theorem shiftedDirectLimitMap_toShiftedDirectLimitOfChart (p : Γ)
    (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedDirectLimitMap ℳ 𝓝 f hf (d.toShiftedDirectLimitOfChart ℳ p s hp x) =
      d.toShiftedDirectLimitOfChart 𝓝 p s hp (d.completionCoefficientMap ℳ 𝓝 p f hf x) := by
  rw [toShiftedDirectLimitOfChart_apply, shiftedDirectLimitMap_toShiftedDirectLimit,
    completionCoefficientMap_inclusion, ← toShiftedDirectLimitOfChart_apply]

/-- The identity linear map induces the identity on global coefficients. -/
@[simp]
theorem shiftedDirectLimitMap_id (x : d.ShiftedDirectLimit ℳ) :
    d.shiftedDirectLimitMap ℳ ℳ LinearMap.id (fun _ => le_rfl) x = x := by
  apply d.shiftedDirectLimitComponents_injective ℳ
  funext u
  apply Subtype.ext
  simp only [coe_shiftedDirectLimitComponents_map, LinearMap.id_apply]

/-- Global coefficient maps preserve composition of degree-preserving linear maps. -/
theorem shiftedDirectLimitMap_comp (ℒ : Γ → Submodule R P) [DirectSum.Decomposition ℒ]
    (g : N →ₗ[R] P) (hg : ∀ u, 𝓝 u ≤ (ℒ u).comap g) (x : d.ShiftedDirectLimit ℳ) :
    d.shiftedDirectLimitMap 𝓝 ℒ g hg (d.shiftedDirectLimitMap ℳ 𝓝 f hf x) =
      d.shiftedDirectLimitMap ℳ ℒ (g.comp f) (fun u _ ha => hg u (hf u ha)) x := by
  apply d.shiftedDirectLimitComponents_injective ℒ
  funext u
  apply Subtype.ext
  simp only [coe_shiftedDirectLimitComponents_map, LinearMap.comp_apply]

end Mei.PositiveDegrees
