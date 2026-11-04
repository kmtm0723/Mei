/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Terminal.FiniteInput
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Comparison.Basic
public import Mei.LinearAlgebra.CommonLift

/-!
# Reflecting terminal slab lifts to the truncated coefficient diagram

The face component of the faithful chamber Laurent comparison is the inverse
slab algebra dictionary. Every total nodal terminal lift therefore has an
explicit preimage in the original truncated slab. If its two chamber values
are the images of specified chamber maps, their common lift reflects uniquely.
We apply this to the actual finite weighted terminal evaluations.

Only the total chamber maps require a common face lift. No preimages of separate
binomial branches are needed. We use the existing common-lift reflection theorem
and correspondence comparison, retaining the original coefficient scalar action.
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial
open scoped Mei.NodeAlgebra

variable (K : Type*) [CommRing K] (k : ℕ)

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "A" => slabAlgebra (C τ) (1 + T 1) k

local instance : IsScalarTower K S (SlabNode τ) :=
  IsScalarTower.to₁₂₄ K S S[ℤ] _

/-- Every target face coefficient has its specified preimage under the inverse
slab dictionary. This is the terminal-lift preimage condition for reflection. -/
theorem chamberLaurentComparison_middle_preimage (z : SlabNode τ) :
    (chamberLaurentComparison K k).middle
      (algebraEquiv τ k (AdjoinRoot.root_X_pow_pow (k + 1)) z) = z := by
  simp only [chamberLaurentComparison_middle, LinearMap.restrictScalars_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]

variable {H : Type*} [AddCommMonoid H] [Module K H]

set_option maxHeartbeats 600000 in
-- Scalar restriction through the two Laurent coefficient towers makes elaboration expensive.
/-- Total chamber maps whose Laurent images have the prescribed nodal common
lift reflect uniquely to the actual truncated slab. The resulting face map is
also required to be the specified preimage of that target lift. -/
theorem existsUnique_chamberCommonLift_of_laurent
    (l : H →ₗ[K] SlabNode τ)
    (βL : H →ₗ[K] TruncatedExponentChamber K k 1)
    (βR : H →ₗ[K] TruncatedExponentChamber K k 0)
    (hL : ((exponentLeftMap (C τ * (1 + T 1))).toLinearMap.restrictScalars K).comp l =
      (leftChamberExponentMap K k).toLinearMap.comp βL)
    (hR : ((exponentRightMap (C τ * (1 + T 1))).toLinearMap.restrictScalars K).comp l =
      (rightChamberExponentMap K k).toLinearMap.comp βR) :
    ∃! L : H →ₗ[K] A,
      (chamberCorrespondence K k).left.comp L = βL ∧
      (chamberCorrespondence K k).right.comp L = βR ∧
      (chamberLaurentComparison K k).middle.comp L = l := by
  let f := chamberLaurentComparison K k
  have hmid : Function.Injective f.middle := by
    intro x y h
    apply (algebraEquiv τ k (AdjoinRoot.root_X_pow_pow (k + 1))).symm.injective
    simpa only [f, chamberLaurentComparison_middle, LinearMap.restrictScalars_apply,
      AlgEquiv.toLinearMap_apply] using h
  have hleft : Function.Injective f.left := by
    intro x y h
    apply leftChamberExponentMap_injective K k
    simpa only [f, chamberLaurentComparison_left, AlgHom.toLinearMap_apply] using h
  have hright : Function.Injective f.right := by
    intro x y h
    apply rightChamberExponentMap_injective K k
    simpa only [f, chamberLaurentComparison_right, AlgHom.toLinearMap_apply] using h
  have hL' : (((exponentCorrespondence (C τ * (1 + T 1))).restrictScalars K).left).comp l =
      f.left.comp βL := by
    simpa only [f, GradedCorrespondence.restrictScalars_left, exponentCorrespondence_left,
      chamberLaurentComparison_left] using hL
  have hR' : (((exponentCorrespondence (C τ * (1 + T 1))).restrictScalars K).right).comp l =
      f.right.comp βR := by
    simpa only [f, GradedCorrespondence.restrictScalars_right, exponentCorrespondence_right,
      chamberLaurentComparison_right] using hR
  obtain ⟨L, hLL, hLR, hLm⟩ :=
    LinearMap.exists_comp_eq_and_comp_eq_and_comp_eq_of_forall_mem_range
      f.middle f.left f.right f.left_comm.symm f.right_comm.symm
      hleft hright hmid l hL' hR' (fun a =>
        ⟨algebraEquiv τ k (AdjoinRoot.root_X_pow_pow (k + 1)) (l a),
          chamberLaurentComparison_middle_preimage K k (l a)⟩)
  refine ⟨L, ⟨hLL, hLR, hLm⟩, ?_⟩
  intro L' hL'
  apply LinearMap.ext
  intro a
  apply hmid
  exact (LinearMap.congr_fun hL'.2.2 a).trans (LinearMap.congr_fun hLm a).symm

section FiniteInput

variable {ι : Type*}
  [Module (AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)) H]
  [IsScalarTower K (AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)) H]
  (s : Finset ι) (n b : ι → ℤ)
  (α : ι → H →ₗ[AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)]
    AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K))

/-- The actual mixed finite terminal evaluations reflect to one common lift in
the original chamber coefficient diagram whenever the total evaluations are
the Laurent images of the given chamber maps. Its face preimage is specified
by the existing slab dictionary, including tangential and constant records. -/
theorem existsUnique_slabTerminalFinite_chamberLift
    {v : ℝ} {L U : ℝ × ℝ}
    (hL : L ∈ slabTerminalFiniteDomain s n b v)
    (hU : U ∈ slabTerminalFiniteDomain s n b v) (hLs : L.1 < 0) (hUs : 0 < U.1)
    (βL : H →ₗ[K] TruncatedExponentChamber K k 1)
    (βR : H →ₗ[K] TruncatedExponentChamber K k 0)
    (hβL : ∀ a, leftChamberExponentMap K k (βL a) =
      ∑ i ∈ s, slabThetaEvaluation τ (α i a) (n i) (b i) L)
    (hβR : ∀ a, rightChamberExponentMap K k (βR a) =
      ∑ i ∈ s, slabThetaEvaluation τ (α i a) (n i) (b i) U) :
    ∃! l : H →ₗ[K] A,
      (chamberCorrespondence K k).left.comp l = βL ∧
      (chamberCorrespondence K k).right.comp l = βR ∧
      (chamberLaurentComparison K k).middle.comp l =
        (slabTerminalFiniteLift s n b τ α).restrictScalars K := by
  apply existsUnique_chamberCommonLift_of_laurent K k
  · apply LinearMap.ext
    intro a
    exact (exponentLeftMap_slabTerminalFiniteLift s n b τ α hL hLs a).trans (hβL a).symm
  · apply LinearMap.ext
    intro a
    exact (exponentRightMap_slabTerminalFiniteLift s n b τ α hU hUs a).trans (hβR a).symm

end FiniteInput

end Mei.FocusFocus
