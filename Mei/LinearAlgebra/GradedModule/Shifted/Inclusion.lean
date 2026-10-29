/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Component
public import Mei.LinearAlgebra.ModuleFiltration.Map

/-!
# Inclusions between shifted coefficient supports

When `p - q` belongs to the positive monoid, support in `p + P` implies support
in `q + P`. The inclusion keeps the ambient coefficients unchanged. Relative
orders can only increase, so the identity cutoff gives a map of completions.
All ambient homogeneous components are preserved, making the completed map
injective even though its finite quotient maps need not be injective.
-/

public section
noncomputable section

namespace Mei

variable {Γ R M : Type*} [AddCommGroup Γ] [Semiring R] [AddCommMonoid M] [Module R M]
  (ℳ : Γ → Submodule R M) (P : AddSubmonoid Γ) (p q : Γ)

/-- Containment of translates gives containment of their supported modules. -/
theorem shiftedSubmodule_le_of_sub_mem (hpq : p - q ∈ P) :
    shiftedSubmodule ℳ P p ≤ shiftedSubmodule ℳ P q := by
  rw [shiftedSubmodule_def]
  refine iSup_le fun n => ?_
  have he : q + (p - q + n) = p + n := by abel
  simpa only [he] using le_shiftedSubmodule ℳ P q (P.add_mem hpq n.property)

/-- Include a smaller translated support without changing its ambient coefficients. -/
def shiftedSupportInclusion (hpq : p - q ∈ P) :
    shiftedSubmodule ℳ P p →ₗ[R] shiftedSubmodule ℳ P q :=
  Submodule.inclusion (shiftedSubmodule_le_of_sub_mem ℳ P p q hpq)

/-- The support inclusion is the identity on ambient coefficients. -/
@[simp]
theorem coe_shiftedSupportInclusion (hpq : p - q ∈ P) (x : shiftedSubmodule ℳ P p) :
    (shiftedSupportInclusion ℳ P p q hpq x : M) = x := (rfl)

/-- The support inclusion is injective. -/
theorem shiftedSupportInclusion_injective (hpq : p - q ∈ P) :
    Function.Injective (shiftedSupportInclusion ℳ P p q hpq) := by
  intro x y h
  apply Subtype.ext
  simpa only [coe_shiftedSupportInclusion] using
    congrArg (fun z : shiftedSubmodule ℳ P q => (z : M)) h

end Mei

namespace Mei.PositiveDegrees

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] (p q : Γ) (hpq : p - q ∈ d.monoid)

/-- Origin inclusion can only increase relative filtration order. -/
theorem shiftedSupportInclusion_filtered (k : ℕ) :
    (d.shiftedFiltration ℳ p).submodule k ≤
      ((d.shiftedFiltration ℳ q).submodule k).comap
        (shiftedSupportInclusion ℳ d.monoid p q hpq) := by
  intro x hx
  rw [Submodule.mem_comap, d.mem_shiftedFiltration_iff ℳ q]
  rw [d.mem_shiftedFiltration_iff ℳ p] at hx
  intro u hu
  rw [coe_shiftedSupportInclusion]
  have he : d.degree (u - q) = d.degree (u - p) + d.degree (p - q) := by
    rw [← map_add]
    congr 1
    abel
  have hnonneg := d.degree_nonneg hpq
  exact hx u (by omega)

/-- The finite quotient map induced by containment of shifted supports. -/
def shiftedQuotientInclusion (k : ℕ) :
    (d.shiftedFiltration ℳ p).quotient k →ₗ[R] (d.shiftedFiltration ℳ q).quotient k :=
  ((d.shiftedFiltration ℳ p).submodule (k + 1)).mapQ
    ((d.shiftedFiltration ℳ q).submodule (k + 1))
    (shiftedSupportInclusion ℳ d.monoid p q hpq)
    (d.shiftedSupportInclusion_filtered ℳ p q hpq (k + 1))

/-- A finite inclusion keeps the representative's ambient coefficients. -/
@[simp]
theorem shiftedQuotientInclusion_mk (k : ℕ) (x : shiftedSubmodule ℳ d.monoid p) :
    d.shiftedQuotientInclusion ℳ p q hpq k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (shiftedSupportInclusion ℳ d.monoid p q hpq x) :=
  Submodule.mapQ_apply _ _ _ x

/-- The identity cutoff extends origin inclusion to shifted completions. -/
def shiftedCompletedInclusion : d.ShiftedCoefficients ℳ p →ₗ[R] d.ShiftedCoefficients ℳ q :=
  (d.shiftedFiltration ℳ p).completionMap (d.shiftedFiltration ℳ q)
    (shiftedSupportInclusion ℳ d.monoid p q hpq) id monotone_id
    (fun k => d.shiftedSupportInclusion_filtered ℳ p q hpq (k + 1))

/-- The completed inclusion has the corresponding finite quotient maps as projections. -/
@[simp]
theorem projection_shiftedCompletedInclusion (k : ℕ) (x : d.ShiftedCoefficients ℳ p) :
    (d.shiftedFiltration ℳ q).projection k (d.shiftedCompletedInclusion ℳ p q hpq x) =
      d.shiftedQuotientInclusion ℳ p q hpq k ((d.shiftedFiltration ℳ p).projection k x) :=
  ModuleFiltration.projection_completionMap _ _ _ _ _ _ k x

/-- The completed inclusion extends inclusion of ordinary shifted coefficients. -/
@[simp]
theorem shiftedCompletedInclusion_of (x : shiftedSubmodule ℳ d.monoid p) :
    d.shiftedCompletedInclusion ℳ p q hpq ((d.shiftedFiltration ℳ p).of x) =
      (d.shiftedFiltration ℳ q).of (shiftedSupportInclusion ℳ d.monoid p q hpq x) :=
  ModuleFiltration.completionMap_of _ _ _ _ _ _ x

/-- Every component retained by both finite quotients is unchanged by inclusion. -/
theorem shiftedQuotientComponent_inclusion (u : Γ) (k : ℕ)
    (hp : d.degree (u - p) ≤ k) (hq : d.degree (u - q) ≤ k)
    (x : (d.shiftedFiltration ℳ p).quotient k) :
    d.shiftedQuotientComponent ℳ q u k hq (d.shiftedQuotientInclusion ℳ p q hpq k x) =
      d.shiftedQuotientComponent ℳ p u k hp x := by
  obtain ⟨a, rfl⟩ := ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ_surjective x
  simp

/-- Origin inclusion preserves every ambient homogeneous component. -/
@[simp]
theorem shiftedHomogeneousComponent_inclusion (u : Γ) (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedHomogeneousComponent ℳ q u (d.shiftedCompletedInclusion ℳ p q hpq x) =
      d.shiftedHomogeneousComponent ℳ p u x := by
  let k := max (d.degree (u - p)).toNat (d.degree (u - q)).toNat
  have hp : d.degree (u - p) ≤ k :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.mpr (le_max_left _ _))
  have hq : d.degree (u - q) ≤ k :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.mpr (le_max_right _ _))
  rw [d.shiftedHomogeneousComponent_eq ℳ q u k hq,
    d.shiftedHomogeneousComponent_eq ℳ p u k hp, projection_shiftedCompletedInclusion,
    d.shiftedQuotientComponent_inclusion ℳ p q hpq u k hp hq]

/-- The completed support inclusion is injective, as it preserves all components. -/
theorem shiftedCompletedInclusion_injective :
    Function.Injective (d.shiftedCompletedInclusion ℳ p q hpq) := by
  intro x y h
  apply d.shiftedCoefficients_ext ℳ p
  intro u
  simpa only [d.shiftedHomogeneousComponent_inclusion ℳ p q hpq] using
    congrArg (d.shiftedHomogeneousComponent ℳ q u) h

/-- The identity-cutoff inclusion preserves every completed filtration order. -/
theorem shiftedCompletedInclusion_mem_completedFiltration (k : ℕ)
    {x : d.ShiftedCoefficients ℳ p}
    (hx : x ∈ (d.shiftedFiltration ℳ p).completedFiltration.submodule k) :
    d.shiftedCompletedInclusion ℳ p q hpq x ∈
      (d.shiftedFiltration ℳ q).completedFiltration.submodule k := by
  cases k with
  | zero => simp
  | succ k =>
    exact ModuleFiltration.completionMap_mem_completedFiltration _ _ _ _ _ _ k hx

omit hpq q in
/-- Inclusion from a shifted support into itself is the identity. -/
@[simp]
theorem shiftedCompletedInclusion_refl (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedCompletedInclusion ℳ p p (by simp) x = x := by
  apply d.shiftedCoefficients_ext ℳ p
  intro u
  simp

/-- Nested support inclusions compose without changing any ambient component. -/
theorem shiftedCompletedInclusion_trans (r : Γ) (hqr : q - r ∈ d.monoid)
    (hpr : p - r ∈ d.monoid) (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedCompletedInclusion ℳ q r hqr (d.shiftedCompletedInclusion ℳ p q hpq x) =
      d.shiftedCompletedInclusion ℳ p r hpr x := by
  apply d.shiftedCoefficients_ext ℳ r
  intro u
  simp

end Mei.PositiveDegrees
