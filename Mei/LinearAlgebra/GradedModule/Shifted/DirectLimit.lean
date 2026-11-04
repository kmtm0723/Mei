/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Inclusion
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Direct limits of shifted completed coefficient modules

Finite multisets of positive degrees index translates by the negative of their
sum. Enlarging a multiset includes its coefficient support into a larger one.
This is a directed system of the existing shifted completions. Its module direct
limit uses Mathlib's carrier and universal property. Every chart includes
injectively, and every limit element is represented in one chart.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ]

/-- The translate associated to a finite multiset of positive degrees. -/
def coefficientOrigin (s : Multiset d.monoid) : Γ := -(s.sum : d.monoid)

omit [DecidableEq Γ] in
/-- The chart origin is the negative sum of its positive multiset. -/
theorem coefficientOrigin_eq_neg_sum (s : Multiset d.monoid) :
    d.coefficientOrigin s = -(s.sum : d.monoid) := (rfl)

omit [DecidableEq Γ] in
/-- A larger positive multiset defines a containing translate. -/
theorem coefficientOrigin_sub_mem {s t : Multiset d.monoid} (h : s ≤ t) :
    d.coefficientOrigin s - d.coefficientOrigin t ∈ d.monoid := by
  obtain ⟨u, rfl⟩ := exists_add_of_le h
  have he : d.coefficientOrigin s - d.coefficientOrigin (s + u) = (u.sum : Γ) := by
    simp only [coefficientOrigin, Multiset.sum_add, AddSubmonoid.coe_add]
    abel_nf
  rw [he]
  exact u.sum.property

/-- The inclusion maps of the multiset-indexed shifted completion system. -/
def coefficientInclusion (s t : Multiset d.monoid) (h : s ≤ t) :
    d.ShiftedCoefficients ℳ (d.coefficientOrigin s) →ₗ[R]
      d.ShiftedCoefficients ℳ (d.coefficientOrigin t) :=
  d.shiftedCompletedInclusion ℳ _ _ (d.coefficientOrigin_sub_mem h)

instance instDirectedSystemCoefficientInclusion :
    DirectedSystem (fun s : Multiset d.monoid => d.ShiftedCoefficients ℳ (d.coefficientOrigin s))
      (fun s t h => d.coefficientInclusion ℳ s t h) where
  map_self s x := d.shiftedCompletedInclusion_refl ℳ (d.coefficientOrigin s) x
  map_map _ _ _ hst htu x := d.shiftedCompletedInclusion_trans ℳ _ _
    (d.coefficientOrigin_sub_mem hst) _ (d.coefficientOrigin_sub_mem htu)
    (d.coefficientOrigin_sub_mem (hst.trans htu)) x

omit [DirectSum.Decomposition ℳ] [DecidableEq Γ] in
/-- The direct-system transition is the original completed support inclusion. -/
theorem coefficientInclusion_eq (s t : Multiset d.monoid) (h : s ≤ t) :
    d.coefficientInclusion ℳ s t h =
      d.shiftedCompletedInclusion ℳ _ _ (d.coefficientOrigin_sub_mem h) := (rfl)

/-- Coefficients supported in some negatively positive translate, as a module direct limit. -/
abbrev ShiftedDirectLimit :=
  Module.DirectLimit (fun s : Multiset d.monoid => d.ShiftedCoefficients ℳ (d.coefficientOrigin s))
    (fun s t h => d.coefficientInclusion ℳ s t h)

/-- Include one completed coefficient chart in the direct limit. -/
def toShiftedDirectLimit (s : Multiset d.monoid) :
    d.ShiftedCoefficients ℳ (d.coefficientOrigin s) →ₗ[R] d.ShiftedDirectLimit ℳ :=
  Module.DirectLimit.of R (Multiset d.monoid)
    (fun s => d.ShiftedCoefficients ℳ (d.coefficientOrigin s))
    (fun s t h => d.coefficientInclusion ℳ s t h) s

omit [DirectSum.Decomposition ℳ] in
/-- The chart embedding is Mathlib's canonical direct-limit inclusion. -/
theorem toShiftedDirectLimit_apply (s : Multiset d.monoid)
    (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    d.toShiftedDirectLimit ℳ s x =
      Module.DirectLimit.of R (Multiset d.monoid)
        (fun s => d.ShiftedCoefficients ℳ (d.coefficientOrigin s))
        (fun s t h => d.coefficientInclusion ℳ s t h) s x := (rfl)

omit [DirectSum.Decomposition ℳ] in
/-- Enlarging a chart leaves its direct-limit element unchanged. -/
@[simp]
theorem toShiftedDirectLimit_inclusion {s t : Multiset d.monoid} (h : s ≤ t)
    (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    d.toShiftedDirectLimit ℳ t (d.coefficientInclusion ℳ s t h x) =
      d.toShiftedDirectLimit ℳ s x := by
  simp only [toShiftedDirectLimit]
  exact Module.DirectLimit.of_f

omit [DirectSum.Decomposition ℳ] in
/-- Every direct-limit coefficient is represented in a single completed chart. -/
theorem exists_toShiftedDirectLimit (x : d.ShiftedDirectLimit ℳ) :
    ∃ s a, d.toShiftedDirectLimit ℳ s a = x := by
  simp only [toShiftedDirectLimit]
  exact Module.DirectLimit.exists_of x

/-- The canonical map of each completed chart is injective. -/
theorem toShiftedDirectLimit_injective (s : Multiset d.monoid) :
    Function.Injective (d.toShiftedDirectLimit ℳ s) := by
  intro x y h
  simp only [toShiftedDirectLimit] at h
  obtain ⟨t, hst, ht⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  apply d.shiftedCompletedInclusion_injective ℳ _ _ (d.coefficientOrigin_sub_mem hst)
  simpa only [coefficientInclusion] using ht

omit [DecidableEq Γ] in
/-- If every lattice degree is a difference of positive degrees, these charts
contain every translated support. -/
theorem exists_coefficientOrigin_of_spanning
    (hspan : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b) (p : Γ) :
    ∃ s : Multiset d.monoid, p - d.coefficientOrigin s ∈ d.monoid := by
  obtain ⟨a, b, hp⟩ := hspan p
  refine ⟨{b}, ?_⟩
  simpa only [hp, coefficientOrigin, Multiset.sum_singleton, sub_neg_eq_add,
    sub_add_cancel] using a.property

/-- Include an arbitrary origin using a specified containing multiset chart. -/
def toShiftedDirectLimitOfChart (p : Γ) (s : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid) :
    d.ShiftedCoefficients ℳ p →ₗ[R] d.ShiftedDirectLimit ℳ :=
  (d.toShiftedDirectLimit ℳ s).comp
    (d.shiftedCompletedInclusion ℳ p (d.coefficientOrigin s) hp)

omit [DirectSum.Decomposition ℳ] in
/-- An arbitrary-origin embedding first includes its support in the specified chart. -/
theorem toShiftedDirectLimitOfChart_apply (p : Γ) (s : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid) (x : d.ShiftedCoefficients ℳ p) :
    d.toShiftedDirectLimitOfChart ℳ p s hp x =
      d.toShiftedDirectLimit ℳ s (d.shiftedCompletedInclusion ℳ p (d.coefficientOrigin s) hp x) :=
  (rfl)

/-- Each arbitrary-origin chart includes injectively as soon as a containing chart is given. -/
theorem toShiftedDirectLimitOfChart_injective (p : Γ) (s : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid) :
    Function.Injective (d.toShiftedDirectLimitOfChart ℳ p s hp) := by
  exact (d.toShiftedDirectLimit_injective ℳ s).comp
    (d.shiftedCompletedInclusion_injective ℳ p (d.coefficientOrigin s) hp)

omit [DirectSum.Decomposition ℳ] in
/-- The embedding of an origin is independent of which containing chart is used. -/
theorem toShiftedDirectLimitOfChart_eq (p : Γ) (s t : Multiset d.monoid)
    (hs : p - d.coefficientOrigin s ∈ d.monoid)
    (ht : p - d.coefficientOrigin t ∈ d.monoid) (x : d.ShiftedCoefficients ℳ p) :
    d.toShiftedDirectLimitOfChart ℳ p s hs x =
      d.toShiftedDirectLimitOfChart ℳ p t ht x := by
  have hsu : s ≤ s + t := le_add_right le_rfl
  have htu : t ≤ s + t := le_add_left le_rfl
  have hu : p - d.coefficientOrigin (s + t) ∈ d.monoid := by
    have h := d.monoid.add_mem hs (d.coefficientOrigin_sub_mem hsu)
    simpa only [sub_add_sub_cancel] using h
  have hf (v : Multiset d.monoid) (hv : v ≤ s + t)
      (hpv : p - d.coefficientOrigin v ∈ d.monoid) :
      d.toShiftedDirectLimitOfChart ℳ p v hpv x =
        d.toShiftedDirectLimitOfChart ℳ p (s + t) hu x := by
    simp only [toShiftedDirectLimitOfChart, LinearMap.comp_apply]
    rw [← d.toShiftedDirectLimit_inclusion ℳ hv]
    congr 1
    exact d.shiftedCompletedInclusion_trans ℳ p (d.coefficientOrigin v) hpv
      (d.coefficientOrigin (s + t)) (d.coefficientOrigin_sub_mem hv) hu x
  exact (hf s hsu hs).trans (hf t htu ht).symm

end Mei.PositiveDegrees
