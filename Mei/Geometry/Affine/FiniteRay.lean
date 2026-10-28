/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Algebra.ContinuousAffineMap
public import Mei.Topology.Maps.Proper
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Module
import Mathlib.Tactic.FunProp

/-!
# Incoming rays with finitely many affine bends

A finite affine ray has an endpoint at time zero, a final direction, and a
finitely supported family of direction changes at negative times. Hinge
functions give its continuous realization without choices of interval charts.
Before all bends it agrees with one affine line.

These are the geometric paths underlying affine broken lines. Coefficient
decorations and wall-encounter conditions are additional data. The sign
convention is that the spatial velocity is the negative of the direction.
-/

public section

open Set Filter

namespace Mei

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

/-- Finite direction changes at negative times, with a specified endpoint. -/
@[ext]
structure FiniteAffineRay where
  /-- Position at time zero. -/
  endpoint : V
  /-- Negative of the velocity after the final bend. -/
  direction : V
  /-- Direction increments when moving backwards across the bend times. -/
  bends : ℝ →₀ V
  /-- Every actual bend precedes the endpoint. -/
  bend_neg : ∀ t ∈ bends.support, t < 0

namespace FiniteAffineRay

variable {V}

/-- Realization of the finite ray, extended affinely past its endpoint. -/
def eval (β : FiniteAffineRay V) (t : ℝ) : V :=
  β.endpoint - t • β.direction + β.bends.sum (fun b v => max (b - t) 0 • v)

instance : CoeFun (FiniteAffineRay V) (fun _ => ℝ → V) := ⟨eval⟩

/-- The endpoint parameter reads the specified endpoint. -/
@[simp]
theorem eval_zero (β : FiniteAffineRay V) : β 0 = β.endpoint := by
  classical
  simp only [eval, zero_smul, sub_zero, Finsupp.sum]
  have h : ∑ b ∈ β.bends.support, max (b - 0) 0 • β.bends b = (0 : V) := by
    apply Finset.sum_eq_zero
    intro b hb
    rw [sub_zero, max_eq_right (β.bend_neg b hb).le, zero_smul]
  simpa only [sub_zero, add_zero] using congrArg (β.endpoint + ·) h

/-- The incoming direction is the final direction plus all direction increments. -/
def incomingDirection (β : FiniteAffineRay V) : V :=
  β.direction + β.bends.sum (fun _ v => v)

/-- Reference position at zero of the incoming affine representative. -/
def incomingReference (β : FiniteAffineRay V) : V :=
  β.endpoint + β.bends.sum (fun b v => b • v)

/-- A ray without bends, with its given endpoint and direction. -/
def straight (Q v : V) : FiniteAffineRay V where
  endpoint := Q
  direction := v
  bends := 0
  bend_neg := by simp

omit [Module ℝ V] in
/-- An unbent ray has no direction increments. -/
@[simp]
theorem bends_straight (Q v : V) : (straight Q v).bends = 0 := (rfl)

/-- The unbent ray is the affine half-line with negative velocity. -/
@[simp]
theorem straight_apply (Q v : V) (t : ℝ) : straight Q v t = Q - t • v := by
  simp [eval, straight]

omit [Module ℝ V] in
/-- An unbent ray retains its specified incoming direction. -/
@[simp]
theorem incomingDirection_straight (Q v : V) : (straight Q v).incomingDirection = v := by
  simp [incomingDirection, straight]

/-- The affine reference position of an unbent ray is its endpoint. -/
@[simp]
theorem incomingReference_straight (Q v : V) : (straight Q v).incomingReference = Q := by
  simp [incomingReference, straight]

/-- Add a direction increment at a negative time. Zero increments give artificial
subdivisions; increments at the same time combine in the existing finitely supported family. -/
noncomputable def insert (β : FiniteAffineRay V) (b : ℝ) (δ : V) (hb : b < 0) :
    FiniteAffineRay V := by
  classical
  refine ⟨β.endpoint, β.direction, β.bends + Finsupp.single b δ, ?_⟩
  intro t ht
  rcases Finset.mem_union.mp (Finsupp.support_add ht) with h | h
  · exact β.bend_neg t h
  · have htb : t = b := Finset.mem_singleton.mp (Finsupp.support_single_subset h)
    exact htb ▸ hb

omit [Module ℝ V] in
/-- Insertion adds the increment to the finitely supported bend data. -/
@[simp]
theorem bends_insert (β : FiniteAffineRay V) (b : ℝ) (δ : V) (hb : b < 0) :
    (β.insert b δ hb).bends = β.bends + Finsupp.single b δ := (rfl)

/-- A newly inserted bend contributes its hinge function to realization. -/
theorem insert_apply (β : FiniteAffineRay V) (b : ℝ) (δ : V) (hb : b < 0) (t : ℝ) :
    β.insert b δ hb t = β t + max (b - t) 0 • δ := by
  classical
  dsimp [eval, insert]
  rw [Finsupp.sum_add_index' (fun b => smul_zero (max (b - t) 0))
    (fun b v w => smul_add (max (b - t) 0) v w),
    Finsupp.sum_single_index (h := fun b v => max (b - t) 0 • v)
      (smul_zero (max (b - t) 0))]
  abel

omit [Module ℝ V] in
/-- An artificial subdivision with unchanged velocity preserves the ray itself. -/
@[simp]
theorem insert_zero (β : FiniteAffineRay V) (b : ℝ) (hb : b < 0) :
    β.insert b 0 hb = β := by
  ext <;> simp [insert]

omit [Module ℝ V] in
/-- Inserting a direction change adds it to the incoming direction. -/
@[simp]
theorem incomingDirection_insert (β : FiniteAffineRay V) (b : ℝ) (δ : V) (hb : b < 0) :
    (β.insert b δ hb).incomingDirection = β.incomingDirection + δ := by
  classical
  simp [incomingDirection, insert, Finsupp.sum_add_index', add_assoc]

/-- A bend at time `b` shifts the incoming affine reference position by `b • δ`. -/
@[simp]
theorem incomingReference_insert (β : FiniteAffineRay V) (b : ℝ) (δ : V) (hb : b < 0) :
    (β.insert b δ hb).incomingReference = β.incomingReference + b • δ := by
  classical
  simp [incomingReference, insert, Finsupp.sum_add_index', smul_add, add_assoc]

omit [Module ℝ V] in
/-- Direction increments at the same time combine into a single bend. -/
theorem insert_insert_same (β : FiniteAffineRay V) (b : ℝ) (δ ε : V) (hb : b < 0) :
    (β.insert b δ hb).insert b ε hb = β.insert b (δ + ε) hb := by
  ext <;> simp [insert, Finsupp.single_add, add_assoc]

/-- Direction on an interval ending at `t`, including bends at its right endpoint. -/
noncomputable def directionAt (β : FiniteAffineRay V) (t : ℝ) : V :=
  β.direction + β.bends.sum (fun b v => if t ≤ b then v else 0)

omit [Module ℝ V] in
/-- An unbent ray has the same direction on every interval. -/
@[simp]
theorem directionAt_straight (Q v : V) (t : ℝ) : (straight Q v).directionAt t = v := by
  simp [directionAt, straight]

omit [Module ℝ V] in
/-- A bend contributes to the direction on its incoming side, including at the bend. -/
@[simp]
theorem directionAt_insert (β : FiniteAffineRay V) (b : ℝ) (δ : V) (hb : b < 0) (t : ℝ) :
    (β.insert b δ hb).directionAt t = β.directionAt t + if t ≤ b then δ else 0 := by
  classical
  dsimp [directionAt, insert]
  rw [Finsupp.sum_add_index' (fun _ => by split <;> rfl)
      (fun _ v w => by split <;> simp),
    Finsupp.sum_single_index (h := fun b v => if t ≤ b then v else 0) (by split <;> rfl)]
  abel

/-- On any interval without an interior bend, realization has the stated constant velocity. -/
theorem eval_sub_eval (β : FiniteAffineRay V) {s t : ℝ} (hst : s ≤ t)
    (hb : ∀ b ∈ β.bends.support, b ≤ s ∨ t ≤ b) :
    β t - β s = (s - t) • β.directionAt t := by
  classical
  have h : β.bends.sum (fun b v => max (b - t) 0 • v) -
      β.bends.sum (fun b v => max (b - s) 0 • v) =
        (s - t) • β.bends.sum (fun b v => if t ≤ b then v else 0) := by
    simp only [Finsupp.sum]
    rw [← Finset.sum_sub_distrib, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b hmem
    rcases hb b hmem with hbs | htb
    · by_cases htb : t ≤ b
      · have hst' : s = t := le_antisymm hst (htb.trans hbs)
        subst t
        simp
      · rw [max_eq_right (sub_nonpos.mpr (hbs.trans hst)),
          max_eq_right (sub_nonpos.mpr hbs), ite_eq_right htb]
        simp
    · rw [max_eq_left (sub_nonneg.mpr htb),
        max_eq_left (sub_nonneg.mpr (hst.trans htb)), ite_eq_left htb, ← sub_smul]
      congr 1
      abel
  calc
    β t - β s = (s - t) • β.direction +
        (β.bends.sum (fun b v => max (b - t) 0 • v) -
          β.bends.sum (fun b v => max (b - s) 0 • v)) := by
      simp only [eval, sub_smul]
      module
    _ = (s - t) • β.directionAt t := by rw [h, directionAt, smul_add]

/-- Before all bends, realization is the incoming affine formula. -/
theorem eval_of_le_bends (β : FiniteAffineRay V) (t : ℝ)
    (ht : ∀ b ∈ β.bends.support, t ≤ b) :
    β t = β.incomingReference - t • β.incomingDirection := by
  classical
  have h : β.bends.sum (fun b v => max (b - t) 0 • v) =
      β.bends.sum (fun b v => b • v) - t • β.bends.sum (fun _ v => v) := by
    simp only [Finsupp.sum]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [max_eq_left (sub_nonneg.mpr (ht b hb)), sub_smul]
  rw [eval, h, incomingReference, incomingDirection, smul_add]
  module

section Topology

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

/-- The hinge realization is continuous, including at every bend time. -/
theorem continuous (β : FiniteAffineRay V) : Continuous β := by
  classical
  unfold eval
  simp only [Finsupp.sum]
  fun_prop

/-- The affine line representing the incoming germ of the bent ray. -/
def incomingLine (β : FiniteAffineRay V) : ℝ →ᴬ[ℝ] V :=
  ContinuousAffineMap.lineMap β.incomingReference (β.incomingReference - β.incomingDirection)

/-- Evaluation of the canonical incoming line. -/
@[simp]
theorem incomingLine_apply (β : FiniteAffineRay V) (t : ℝ) :
    β.incomingLine t = β.incomingReference - t • β.incomingDirection := by
  simp only [incomingLine, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_module']
  module

/-- The finite realization agrees with its incoming affine line near negative infinity. -/
theorem eventuallyEq_incomingLine (β : FiniteAffineRay V) :
    (β : ℝ → V) =ᶠ[atBot] β.incomingLine := by
  filter_upwards [(β.bends.support.eventually_all).mpr
    (fun b _ => eventually_le_atBot b)] with t ht
  exact (β.eval_of_le_bends t ht).trans (β.incomingLine_apply t).symm

/-- The incoming affine line has the prescribed negative velocity. -/
@[simp]
theorem incomingLine_velocity (β : FiniteAffineRay V) :
    β.incomingLine.linear 1 = -β.incomingDirection := by
  simp [incomingLine, ContinuousAffineMap.lineMap_toAffineMap, AffineMap.lineMap_linear]

variable [T2Space V]

/-- Every closed incoming half-line is proper when the incoming direction is nonzero.
Finitely many bends may include zero-velocity segments without affecting properness. -/
theorem isProperMap_restrict_Iic (β : FiniteAffineRay V) (hv : β.incomingDirection ≠ 0)
    (b : ℝ) : IsProperMap (fun t : Iic b => β t) := by
  obtain ⟨a, ha⟩ := eventually_atBot.mp β.eventuallyEq_incomingLine
  have hv' : β.incomingLine.contLinear 1 ≠ 0 := by
    simpa only [ContinuousAffineMap.coe_contLinear, incomingLine_velocity, ne_eq,
      neg_eq_zero] using hv
  refine (β.incomingLine.isProperMap_restrict_Iic hv' b).of_eqOn_compl_isCompact
    (K := Subtype.val ⁻¹' Icc a b)
    (β.continuous.comp continuous_subtype_val)
    (isClosed_Iic.isClosedEmbedding_subtypeVal.isCompact_preimage isCompact_Icc) ?_
  intro t ht
  apply ha t.val
  have hn : ¬ a ≤ t.val := by
    intro hat
    exact ht ⟨hat, t.property⟩
  exact (lt_of_not_ge hn).le

end Topology

end FiniteAffineRay
end Mei
