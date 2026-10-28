/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Inner.Basic
public import Mei.Algebra.Lie.UniversalEnveloping.BCH.Completion
public import Mei.Algebra.Lie.Filtered.Inner.Completed

/-!
# Completed inner BCH actions are conjugation

Every completed BCH label acts on the degree-completed enveloping algebra by
conjugation with its canonical group-like unit. Thus the coefficient representation
and the homomorphism into enveloping units agree on arbitrary compatible families,
including Lie series with infinitely many nonzero homogeneous components.

The finite comparison uses the commutator action from
`UniversalEnvelopingAlgebra.InnerAction` and
the general filtered inner-action conjugation theorems. Linear-map comparisons
identify their canonical inner images with the existing enveloping Lie maps.
The completed comparison uses the existing
finite projection laws for `completedBCHAction` and `completedBCHToGroupLike`.
No freeness, PBW, or injectivity assumption on the canonical Lie map is required.
-/

public section

open scoped UniversalEnvelopingAlgebra.InnerAction

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Mei.UniversalEnvelopingAlgebra

open Mei

variable {N R L : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "F" => degreeFiltration ℒ d.degree
  (fun n hn => d.eq_bot_of_degree_nonpos ℒ n (le_of_lt hn))

local notation "j" => ((_root_.UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ U) : L →ₗ[R] U)

/-- The general truncated inner coefficient map at the canonical Lie map is the
existing finite enveloping Lie map, independently of its filtration witness. -/
@[simp]
theorem truncatedInnerMap_eq_truncatedLieToU
    (hj : ∀ k, d.degreeSubmodule ℒ k ≤
      (((F).ideal (k + 1)).restrictScalars R).comap j) (k : ℕ) :
    (F).truncatedInnerMap d ℒ j hj k = (truncatedLieToU d ℒ k).toLinearMap := by
  ext x
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  simp only [LieIdeal.mkQ_apply, Mei.AlgFiltration.truncatedInnerMap_mk,
    LieHom.coe_toLinearMap, truncatedLieToU_mk]

/-- The general completed inner coefficient map at the canonical Lie map is the
existing completed enveloping Lie map, as a linear map. -/
@[simp]
theorem completedInnerMap_eq_completedLieToU
    (hj : ∀ k, d.degreeSubmodule ℒ k ≤
      (((F).ideal (k + 1)).restrictScalars R).comap j) :
    (F).completedInnerMap d ℒ j hj = (completedLieToU d ℒ).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (F).completion_ext
  intro k
  simp only [Mei.AlgFiltration.projection_completedInnerMap,
    truncatedInnerMap_eq_truncatedLieToU, LieHom.coe_toLinearMap,
    projection_completedLieToU]

end Mei.UniversalEnvelopingAlgebra

namespace UniversalEnvelopingAlgebra.InnerAction

open Mei Mei.UniversalEnvelopingAlgebra

variable {N R L : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "F" => degreeFiltration ℒ d.degree
  (fun n hn => d.eq_bot_of_degree_nonpos ℒ n (le_of_lt hn))

local notation "j" => ((ι R : L →ₗ⁅R⁆ U) : L →ₗ[R] U)

variable [Algebra ℚ R]

/-- Rational scalars on the enveloping algebra are induced from the coefficient ring. -/
local instance rationalCompletedInnerAlgebra : Algebra ℚ U :=
  Algebra.compHom _ (algebraMap ℚ R)

/-- At every cutoff, the inner exponential of a truncated Lie element is
conjugation by the finite exponential of its canonical enveloping image. -/
@[simp]
theorem truncatedExpLieAction_apply (k : ℕ) (x : d.truncatedLie ℒ k)
    (a : U ⧸ (F).ideal (k + 1)) :
    (F).truncatedExpLieAction d ℒ k x a =
      IsNilpotent.exp (truncatedLieToU d ℒ k x) * a *
        IsNilpotent.exp (-truncatedLieToU d ℒ k x) := by
  have hj : ∀ k, d.degreeSubmodule ℒ k ≤
      (((F).ideal (k + 1)).restrictScalars R).comap j := by
    intro k y hy
    apply ι_mem_degreeFiltration_of_mem_degreeIdeal d ℒ
    have hy' : y ∈ (d.degreeIdeal ℒ k).toSubmodule := by
      simpa only [d.degreeIdeal_toSubmodule ℒ k] using hy
    exact hy'
  simpa only [truncatedInnerMap_eq_truncatedLieToU, LieHom.coe_toLinearMap] using
    (F).truncatedExpLieAction_eq_inner d ℒ j
      hj lie_eq k x a

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- The finite inner BCH action is conjugation by the canonical enveloping unit. -/
theorem truncatedBCHAction_apply (k : ℕ) (g : BCHGroup (d.truncatedLie ℒ k))
    (a : U ⧸ (F).ideal (k + 1)) :
    (F).truncatedBCHAction d ℒ k g a =
      (truncatedBCHToUnits d ℒ k g : U ⧸ (F).ideal (k + 1)) * a *
        (truncatedBCHToUnits d ℒ k g⁻¹ : U ⧸ (F).ideal (k + 1)) := by
  simp only [Mei.AlgFiltration.truncatedBCHAction_apply,
    truncatedExpLieAction_apply, coe_truncatedBCHToUnits, BCHGroup.log_inv, map_neg]

/-- The inner representation of every completed BCH label is conjugation by its
canonical completed group-like unit. -/
@[simp]
theorem completedBCHAction_apply (g : d.completedBCHGroup ℒ) (a : (F).completion) :
    (F).completedBCHAction d ℒ g a =
      ((completedBCHToGroupLike d ℒ g).val : (F).completion) * a *
        ((completedBCHToGroupLike d ℒ g⁻¹).val : (F).completion) := by
  apply (F).completion_ext
  intro k
  rw [Mei.AlgFiltration.projection_completedBCHAction, map_mul, map_mul,
    projection_completedBCHToGroupLike, projection_completedBCHToGroupLike]
  have h := truncatedBCHAction_apply d ℒ k
    (CompletedGroup.projection k g) ((F).projection k a)
  rw [(F).truncatedBCHAction_apply d ℒ k (CompletedGroup.projection k g)] at h
  simp only [map_inv] at h ⊢
  -- The categorical tower object and its concrete BCH group carry the same operations.
  convert h using 1
  rfl

/-- In completed Lie coordinates, the inner action is conjugation by the completed
exponential of the canonical Lie image, with inverse given by its negative. -/
theorem completedBCHAction_exp_apply (x : d.completedLie ℒ) (a : (F).completion) :
    (F).completedBCHAction d ℒ (d.completedBCHExp ℒ x) a =
      (F).completedExp ⟨completedLieToU d ℒ x,
        completedLieToU_mem_completionIdeal_one d ℒ x⟩ * a *
      (F).completedExp (-⟨completedLieToU d ℒ x,
        completedLieToU_mem_completionIdeal_one d ℒ x⟩) := by
  have hj : ∀ k, d.degreeSubmodule ℒ k ≤
      (((F).ideal (k + 1)).restrictScalars R).comap j := by
    intro k y hy
    apply ι_mem_degreeFiltration_of_mem_degreeIdeal d ℒ
    have hy' : y ∈ (d.degreeIdeal ℒ k).toSubmodule := by
      simpa only [d.degreeIdeal_toSubmodule ℒ k] using hy
    exact hy'
  have he : (F).completedInnerElement d ℒ j
      hj x =
      ⟨completedLieToU d ℒ x, completedLieToU_mem_completionIdeal_one d ℒ x⟩ := by
    apply Subtype.ext
    simp only [Mei.AlgFiltration.coe_completedInnerElement,
      completedInnerMap_eq_completedLieToU, LieHom.coe_toLinearMap]
  simpa only [he] using
    (F).completedBCHAction_exp_eq_inner d ℒ j
      hj lie_eq x a

end UniversalEnvelopingAlgebra.InnerAction
