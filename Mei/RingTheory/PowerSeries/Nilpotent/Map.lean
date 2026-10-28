/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.PowerSeries.Nilpotent.Basic

/-!
# Scalar-change naturality of nilpotent power-series evaluation

A compatible pair of ring maps on scalars and coefficients commutes with finite
nilpotent evaluation. Both maps may have kernels, and the coefficient rings need
not be commutative. The proof reuses the finite-sum formula for evaluation.
-/

public section

namespace PowerSeries

variable {R S A B : Type*} [CommRing R] [CommRing S] [Ring A] [Ring B]
  [Algebra R A] [Algebra S B]

/-- Changing scalars and coefficients commutes with nilpotent evaluation. -/
theorem map_nilpotentAeval_map (φ : R →+* S) (ψ : A →+* B)
    (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap S B (φ r))
    {x : A} (hx : IsNilpotent x) (f : R⟦X⟧) :
    ψ (nilpotentAeval hx f) = nilpotentAeval (hx.map ψ) (map φ f) := by
  let n := hx.choose
  have hn : x ^ n = 0 := hx.choose_spec
  have hψn : ψ x ^ n = 0 := by rw [← map_pow, hn, map_zero]
  rw [nilpotentAeval_eq_sum _ hn, nilpotentAeval_eq_sum _ hψn]
  simp only [map_sum, Algebra.smul_def, map_mul, map_pow, hψ, coeff_map]

end PowerSeries
