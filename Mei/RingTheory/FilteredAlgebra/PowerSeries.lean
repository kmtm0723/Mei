/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.Algebra
public import Mei.RingTheory.PowerSeries.Nilpotent
import TauCeti.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Evaluating power series in a completed filtered algebra

An element of the first completed ideal is nilpotent at every finite order. Evaluate scalar
power series at these projections and use the existing inverse-limit algebra lift to obtain
an algebra homomorphism into the completion. Its finite projections are finite sums.

The scalar ring is any commutative ring, and the filtered algebra can be noncommutative.
No topology or separatedness assumption is needed.
-/

public section

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (F : AlgFiltration A)

/-- Evaluate scalar power series at an element of the first completed ideal. -/
noncomputable def completedAeval (x : F.completionIdeal 1) :
    PowerSeries R →ₐ[R] F.completion :=
  F.liftₐ (fun k => PowerSeries.nilpotentAeval (F.isNilpotent_projection x.property k))
    (fun {k l} h => by
      ext f
      rw [AlgHom.comp_apply]
      rw [PowerSeries.map_nilpotentAeval]
      congr 2
      exact F.factor_projection h x)

/-- At finite order, completed evaluation is evaluation at the nilpotent projection. -/
@[simp]
theorem projection_completedAeval (x : F.completionIdeal 1) (k : ℕ) (f : PowerSeries R) :
    F.projection k (F.completedAeval x f) =
      PowerSeries.nilpotentAeval (F.isNilpotent_projection x.property k) f := by
  simp [completedAeval]

/-- At order `k`, only the first `k + 1` scalar coefficients contribute. -/
theorem projection_completedAeval_eq_sum (x : F.completionIdeal 1) (k : ℕ)
    (f : PowerSeries R) :
    F.projection k (F.completedAeval x f) =
      ∑ i ∈ Finset.range (k + 1), PowerSeries.coeff i f • F.projection k x ^ i := by
  rw [F.projection_completedAeval]
  exact PowerSeries.nilpotentAeval_eq_sum _ (F.projection_pow_eq_zero x.property k) f

/-- Constants evaluate to their scalar images in the completion. -/
@[simp]
theorem completedAeval_C (x : F.completionIdeal 1) (r : R) :
    F.completedAeval x (PowerSeries.C r) = algebraMap R F.completion r :=
  (F.completedAeval x).commutes r

/-- The variable evaluates to the chosen completed element. -/
@[simp]
theorem completedAeval_X (x : F.completionIdeal 1) :
    F.completedAeval (R := R) x PowerSeries.X = x := by
  apply F.completion_ext
  intro k
  simp

/-- On polynomials, completed evaluation is ordinary polynomial algebra evaluation. -/
@[simp]
theorem completedAeval_coe (x : F.completionIdeal 1) (p : Polynomial R) :
    F.completedAeval x (p : PowerSeries R) = Polynomial.aeval (x : F.completion) p := by
  rw [PowerSeries.algHom_coe_eq_aeval, F.completedAeval_X]

/-- A series with zero constant coefficient evaluates into the first completed ideal. -/
theorem completedAeval_mem_first (x : F.completionIdeal 1) {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) :
    F.completedAeval x f ∈ F.completionIdeal 1 := by
  rw [F.completionIdeal_succ 0, RingHom.mem_ker,
    F.projection_completedAeval_eq_sum]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]

/-- A series with invertible constant coefficient evaluates to a unit. -/
theorem isUnit_completedAeval (x : F.completionIdeal 1) {f : PowerSeries R}
    (hf : IsUnit (PowerSeries.constantCoeff f)) : IsUnit (F.completedAeval x f) :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr hf).map (F.completedAeval x)

end Mei.AlgFiltration
