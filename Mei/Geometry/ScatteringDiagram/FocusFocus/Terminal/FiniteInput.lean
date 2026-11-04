/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Terminal

/-!
# Uniform terminal lifts for finite focus-focus inputs

A finite collection of incoming exponents has one open terminal neighborhood
controlling every binomial index of every input. It is independent of incoming
coefficients and incoming parameter values, and still contains endpoints in both
chambers. Thus mixed incoming directions, tangential records and stationary
sections admit one common linear lift for their total weighted evaluations.

The indexing set may retain entire incoming histories: equal exponents are not
identified, and coefficients that vanish after specialization are not removed
from the uniform geometric test. This extends the one-exponent terminal theorem;
it does not assert a singular-origin certificate or global theta gluing.
-/

public noncomputable section

namespace Mei.FocusFocus

open Set Mei.NodeAlgebra _root_.LaurentPolynomial

variable {ι : Type*} (s : Finset ι) (n b : ι → ℤ)

/-- One coefficient-independent terminal neighborhood for all incoming records
in a finite input list, including every candidate binomial branch. -/
def slabTerminalFiniteDomain (v : ℝ) : Set (ℝ × ℝ) :=
  ⋂ i ∈ s, slabTerminalDomain (n i) (b i) v

/-- The uniform neighborhood imposes the original terminal test on every record. -/
theorem mem_slabTerminalFiniteDomain (v : ℝ) (Q : ℝ × ℝ) :
    Q ∈ slabTerminalFiniteDomain s n b v ↔
      ∀ i ∈ s, Q ∈ slabTerminalDomain (n i) (b i) v := by
  simp [slabTerminalFiniteDomain]

/-- The common terminal domain is open, without a bound on the exponents. -/
theorem isOpen_slabTerminalFiniteDomain (v : ℝ) :
    IsOpen (slabTerminalFiniteDomain s n b v) :=
  isOpen_biInter_finset fun i _ => isOpen_slabTerminalDomain (n i) (b i) v

/-- Every regular slab point belongs to the common terminal neighborhood. -/
theorem slabPoint_mem_slabTerminalFiniteDomain {v : ℝ} (hv : v ≠ 0) :
    (0, v) ∈ slabTerminalFiniteDomain s n b v := by
  rw [mem_slabTerminalFiniteDomain]
  intro i _
  simpa using hv

/-- The uniform domain contains endpoints in both chambers, including when the
finite incoming list is empty or contains only tangential inputs. -/
theorem slabTerminalFiniteDomain_meets_chambers {v : ℝ} (hv : v ≠ 0) :
    ∃ L U : ℝ × ℝ, L ∈ slabTerminalFiniteDomain s n b v ∧
      U ∈ slabTerminalFiniteDomain s n b v ∧ L.1 < 0 ∧ 0 < U.1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_slabTerminalFiniteDomain s n b v) (0, v)
    (slabPoint_mem_slabTerminalFiniteDomain s n b hv)
  refine ⟨(-ε / 2, v), (ε / 2, v), hball ?_, hball ?_, by linarith, by linarith⟩
  all_goals
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, sub_self, abs_zero]
    rw [max_lt_iff]
    constructor
    · rw [abs_lt]
      constructor <;> linarith
    · exact hε

section Coefficients

variable {R H : Type*} [CommRing R] [AddCommMonoid H] [Module R H]
  (t : R) (α : ι → H →ₗ[R] R)

/-- The common lift of a finite family of complete incoming records. -/
def slabTerminalFiniteLift :
    H →ₗ[R] TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1)) :=
  ∑ i ∈ s, (LinearMap.toSpanSingleton R _ (theta t (n i) (b i))).comp (α i)

/-- The negative chamber value of the total lift is the total actual weighted
evaluation throughout the uniform terminal neighborhood. -/
theorem exponentLeftMap_slabTerminalFiniteLift {v : ℝ} {Q : ℝ × ℝ}
    (hQ : Q ∈ slabTerminalFiniteDomain s n b v) (hside : Q.1 < 0) (a : H) :
    exponentLeftMap (C t * (1 + T 1)) (slabTerminalFiniteLift s n b t α a) =
      ∑ i ∈ s, slabThetaEvaluation t (α i a) (n i) (b i) Q := by
  simp only [slabTerminalFiniteLift, LinearMap.sum_apply, map_sum,
    LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact (slabThetaEvaluation_eq_exponentLeftMap t (α i a) (n i) (b i) Q hside
    (fun _ j _ => slabTerminalDomain_crossingHeight_ne_zero
      ((mem_slabTerminalFiniteDomain s n b v Q).mp hQ i hi) j)).symm

/-- The positive chamber value uses the same total lift and the same uniform
neighborhood, even for mixed normal signs or coefficients that vanish. -/
theorem exponentRightMap_slabTerminalFiniteLift {v : ℝ} {Q : ℝ × ℝ}
    (hQ : Q ∈ slabTerminalFiniteDomain s n b v) (hside : 0 < Q.1) (a : H) :
    exponentRightMap (C t * (1 + T 1)) (slabTerminalFiniteLift s n b t α a) =
      ∑ i ∈ s, slabThetaEvaluation t (α i a) (n i) (b i) Q := by
  simp only [slabTerminalFiniteLift, LinearMap.sum_apply, map_sum,
    LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact (slabThetaEvaluation_eq_exponentRightMap t (α i a) (n i) (b i) Q hside
    (fun _ j _ => slabTerminalDomain_crossingHeight_ne_zero
      ((mem_slabTerminalFiniteDomain s n b v Q).mp hQ i hi) j)).symm

/-- The two total chamber evaluations determine one common linear face lift.
There is no requirement that the individual branches have face lifts. -/
theorem slabTerminalFinite_commonLift_iff {v : ℝ} (hv : v ≠ 0)
    (l : H →ₗ[R] TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1))) :
    ((∀ Q ∈ slabTerminalFiniteDomain s n b v, Q.1 < 0 → ∀ a,
        exponentLeftMap (C t * (1 + T 1)) (l a) =
          ∑ i ∈ s, slabThetaEvaluation t (α i a) (n i) (b i) Q) ∧
      (∀ Q ∈ slabTerminalFiniteDomain s n b v, 0 < Q.1 → ∀ a,
        exponentRightMap (C t * (1 + T 1)) (l a) =
          ∑ i ∈ s, slabThetaEvaluation t (α i a) (n i) (b i) Q)) ↔
      l = slabTerminalFiniteLift s n b t α := by
  constructor
  · rintro ⟨hL, hU⟩
    obtain ⟨L, U, hLD, hUD, hLside, hUside⟩ :=
      slabTerminalFiniteDomain_meets_chambers s n b hv
    apply LinearMap.ext
    intro a
    apply exponentMaps_jointly_injective (C t * (1 + T 1))
    exact Prod.ext
      ((hL L hLD hLside a).trans
        (exponentLeftMap_slabTerminalFiniteLift s n b t α hLD hLside a).symm)
      ((hU U hUD hUside a).trans
        (exponentRightMap_slabTerminalFiniteLift s n b t α hUD hUside a).symm)
  · rintro rfl
    exact ⟨fun _ hQ hs a => exponentLeftMap_slabTerminalFiniteLift s n b t α hQ hs a,
      fun _ hQ hs a => exponentRightMap_slabTerminalFiniteLift s n b t α hQ hs a⟩

/-- Precomposing the incoming parameter maps precomposes the common total lift.
In particular every finite free input test uses the very same neighborhood. -/
theorem slabTerminalFiniteLift_comp {E : Type*} [AddCommMonoid E] [Module R E]
    (a : E →ₗ[R] H) :
    (slabTerminalFiniteLift s n b t α).comp a =
      slabTerminalFiniteLift s n b t (fun i => (α i).comp a) := by
  apply LinearMap.ext
  intro x
  simp only [slabTerminalFiniteLift, LinearMap.comp_apply, LinearMap.sum_apply]

end Coefficients

end Mei.FocusFocus
