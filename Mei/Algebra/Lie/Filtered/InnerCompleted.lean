/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Inner
public import Mei.Algebra.Lie.Filtered.BCH

/-!
# Completed inner actions as conjugations

A linear map from a positively graded Lie algebra into a filtered associative
algebra extends to completions when it carries every degree cutoff into the
corresponding ideal. Positivity puts its completed image in the first completion
ideal. If the original Lie action is the commutator with this map, every completed
BCH group element acts by conjugation with the completed exponential of its
completed logarithmic image.

The extension reuses `ModuleFiltration.completionMap` and the quotient scalar
restriction equivalence. The conjugation formula reduces, by projection and a
representative in each Lie quotient, to
`AlgFiltration.quotientExpLieAction_apply_eq_exp_mul_exp_neg`. No faithfulness,
separatedness, finite rank, or injectivity hypothesis is required.
-/

public section

noncomputable section

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (F : AlgFiltration A)

private theorem quotientScalarEquiv_transition {k l : ℕ} (h : k ≤ l)
    (a : (F.toModuleFiltration R).quotient l) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
        (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (l + 1)) a) =
      Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
        ((F.toModuleFiltration R).transition h a) := by
  obtain ⟨a, rfl⟩ := ((F.toModuleFiltration R).submodule (l + 1)).mkQ_surjective a
  simp

private def moduleCompletionToAlgebra : (F.toModuleFiltration R).completion →ₗ[R]
    F.completion where
  toFun x := ⟨fun k => Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k.unop + 1))
    ((F.toModuleFiltration R).projection k.unop x),
    (F.mem_completion_iff _).mpr (by
      intro k l h
      rw [F.quotientScalarEquiv_transition h,
        (F.toModuleFiltration R).transition_projection h x])⟩
  map_add' x y := by
    apply F.completion_ext
    intro k
    simp only [map_add, projection_apply]
  map_smul' r x := by
    apply F.completion_ext
    intro k
    have hs (z : F.completion) : F.projection k (r • z) = r • F.projection k z := by
      simpa only [projectionₐ_apply] using map_smul (F.projectionₐ (R := R) k) r z
    rw [RingHom.id_apply, hs]
    simp only [projection_apply]
    exact map_smul
      ((Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).toLinearMap.comp
        ((F.toModuleFiltration R).projection k)) r x

private theorem projection_moduleCompletionToAlgebra (k : ℕ)
    (x : (F.toModuleFiltration R).completion) :
    F.projection k (F.moduleCompletionToAlgebra x) =
      Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
        ((F.toModuleFiltration R).projection k x) := by
  rw [projection_apply]
  rfl

variable {N L : Type*} [AddCommMonoid N] [LieRing L] [LieAlgebra R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (j : L →ₗ[R] A)
  (hj : ∀ k, d.degreeSubmodule ℒ k ≤ ((F.ideal (k + 1)).restrictScalars R).comap j)

local notation "G" => LieIdeal.completionFiltration
  (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

include hj in
private theorem innerMap_filtered (k : ℕ) :
    (G).submodule (k + 1) ≤ ((F.toModuleFiltration R).submodule (k + 1)).comap j := by
  simpa only [LieIdeal.completionFiltration_succ, PositiveDegrees.degreeIdeal_toSubmodule,
    toModuleFiltration_submodule] using hj k

/-- The coefficient map induced on the matching Lie and algebra quotients. -/
def truncatedInnerMap (k : ℕ) : d.truncatedLie ℒ k →ₗ[R] A ⧸ F.ideal (k + 1) :=
  (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).toLinearMap.comp
    (((G).submodule (k + 1)).mapQ ((F.toModuleFiltration R).submodule (k + 1)) j
      (F.innerMap_filtered d ℒ j hj k))

/-- The truncated coefficient map sends the class of a Lie element to its coefficient class. -/
@[simp]
theorem truncatedInnerMap_mk (k : ℕ) (x : L) :
    F.truncatedInnerMap d ℒ j hj k (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk (F.ideal (k + 1)) (j x) := by
  rfl

/-- Extend the inner coefficient map to the completed Lie algebra. -/
def completedInnerMap : d.completedLie ℒ →ₗ[R] F.completion :=
  F.moduleCompletionToAlgebra.comp
    ((G).completionMap (F.toModuleFiltration R) j id monotone_id
      (F.innerMap_filtered d ℒ j hj))

/-- Every projection of the completed coefficient map is its finite quotient map. -/
@[simp]
theorem projection_completedInnerMap (k : ℕ) (x : d.completedLie ℒ) :
    F.projection k (F.completedInnerMap d ℒ j hj x) =
      F.truncatedInnerMap d ℒ j hj k
        (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k x) := by
  simp only [completedInnerMap, LinearMap.comp_apply, projection_moduleCompletionToAlgebra,
    ModuleFiltration.projection_completionMap, id_eq, truncatedInnerMap,
    LinearEquiv.coe_coe, LieIdeal.completionProjection_apply]

/-- The completed extension agrees with the original coefficient map on Lie elements. -/
@[simp]
theorem completedInnerMap_toCompletion (x : L) :
    F.completedInnerMap d ℒ j hj
        (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x) =
      F.toCompletion (j x) := by
  apply F.completion_ext
  intro k
  simp

include hj in
/-- Strict positivity puts every original coefficient image in the first ideal. -/
theorem innerMap_mem_one (x : L) : j x ∈ F.ideal 1 := by
  have hx : x ∈ d.degreeSubmodule ℒ 0 := by simp
  exact hj 0 hx

/-- Strict positivity puts every completed coefficient image in the first completion ideal. -/
theorem completedInnerMap_mem_one (x : d.completedLie ℒ) :
    F.completedInnerMap d ℒ j hj x ∈ F.completionIdeal 1 := by
  rw [completionIdeal_succ, RingHom.mem_ker, projection_completedInnerMap]
  rw [Subsingleton.elim
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) 0 x) 0,
    map_zero]

/-- The completed inner image with the positive-order membership needed for exponentiation. -/
def completedInnerElement (x : d.completedLie ℒ) : F.completionIdeal 1 :=
  ⟨F.completedInnerMap d ℒ j hj x, F.completedInnerMap_mem_one d ℒ j hj x⟩

/-- Forgetting positivity returns the completed coefficient map. -/
@[simp]
theorem coe_completedInnerElement (x : d.completedLie ℒ) :
    (F.completedInnerElement d ℒ j hj x : F.completion) =
      F.completedInnerMap d ℒ j hj x := (rfl)

variable [LieRingModule L A] [LieModule R L A]
  [IsFiltrationRaising d ℒ (F.toModuleFiltration R)] [IsDerivationAction L A]
  [Algebra ℚ A]
  (hinner : ∀ x a, ⁅x, a⁆ = j x * a - a * j x)

include hinner in
/-- At each order, a truncated inner action is conjugation by the exponential of its image. -/
theorem truncatedExpLieAction_eq_inner (k : ℕ) (x : d.truncatedLie ℒ k)
    (a : A ⧸ F.ideal (k + 1)) :
    F.truncatedExpLieAction d ℒ k x a =
      IsNilpotent.exp (F.truncatedInnerMap d ℒ j hj k x) * a *
        IsNilpotent.exp (-F.truncatedInnerMap d ℒ j hj k x) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  rw [LieIdeal.mkQ_apply, truncatedExpLieAction_mk]
  simpa only [LieIdeal.mkQ_apply, truncatedInnerMap_mk] using
    F.quotientExpLieAction_apply_eq_exp_mul_exp_neg d ℒ k (hinner x)
      (F.innerMap_mem_one d ℒ j hj x) a

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

include hinner in
/-- Arbitrary completed Lie elements act by conjugation on arbitrary completed coefficients. -/
theorem completedBCHAction_exp_eq_inner (x : d.completedLie ℒ) (a : F.completion) :
    F.completedBCHAction d ℒ (d.completedBCHExp ℒ x) a =
      F.completedExp (F.completedInnerElement d ℒ j hj x) * a *
        F.completedExp (-F.completedInnerElement d ℒ j hj x) := by
  apply F.completion_ext
  intro k
  simp only [projection_completedBCHAction, PositiveDegrees.projection_completedBCHExp,
    BCHGroup.log_exp, map_mul, projection_completedExp, Submodule.coe_neg,
    coe_completedInnerElement, map_neg, projection_completedInnerMap]
  exact F.truncatedExpLieAction_eq_inner d ℒ j hj hinner k _ _

include hinner in
/-- Every completed BCH label acts by the exponential of its completed logarithmic image. -/
theorem completedBCHAction_eq_inner (g : d.completedBCHGroup ℒ) (a : F.completion) :
    F.completedBCHAction d ℒ g a =
      F.completedExp (F.completedInnerElement d ℒ j hj ((d.completedBCHExp ℒ).symm g)) *
        a * F.completedExp
          (-F.completedInnerElement d ℒ j hj ((d.completedBCHExp ℒ).symm g)) := by
  simpa only [Equiv.apply_symm_apply] using
    F.completedBCHAction_exp_eq_inner d ℒ j hj hinner ((d.completedBCHExp ℒ).symm g) a

end Mei.AlgFiltration
