/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Maximal Dyck paths

The maximal Dyck path of `(d₁, d₂) ∈ ℕ²` is the lattice path from `(0, 0)` to `(d₁, d₂)` by
horizontal and vertical unit steps which stays weakly below the diagonal and is closest to it.
We record a horizontal step as `DyckStep.U` and a vertical step as `DyckStep.D`. For `d₁ > 0`
the path consists of `d₁` blocks: the `i`-th horizontal step is followed by vertical steps up
to height `⌊i d₂ / d₁⌋`, the greatest height weakly below the diagonal. For `d₁ = 0` it is
vertical.

The path has `d₁` horizontal and `d₂` vertical steps. It is the Dyck word `(UD)^a` for
`(a, a)`, the vertical path `D^b` for `(0, b)` and the horizontal path `U^a` for `(a, 0)`.
-/

public section

open DyckStep

namespace Mei

/-- The maximal Dyck path of `(d₁, d₂)`, with horizontal steps `U` and vertical steps `D`:
after its `i`-th horizontal step it rises to height `⌊i * d₂ / d₁⌋`. -/
def maximalDyckPath (d₁ d₂ : ℕ) : List DyckStep :=
  if d₁ = 0 then List.replicate d₂ D
  else (List.range d₁).flatMap fun i ↦ U :: List.replicate ((i + 1) * d₂ / d₁ - i * d₂ / d₁) D

/-- A path with no horizontal steps is vertical. -/
@[simp]
theorem maximalDyckPath_zero_left (d₂ : ℕ) : maximalDyckPath 0 d₂ = List.replicate d₂ D := by
  simp [maximalDyckPath]

/-- For `d₁ ≠ 0`, the path is the concatenation of its `d₁` horizontal blocks. -/
theorem maximalDyckPath_of_ne_zero {d₁ : ℕ} (d₂ : ℕ) (h : d₁ ≠ 0) :
    maximalDyckPath d₁ d₂ = (List.range d₁).flatMap
      fun i ↦ U :: List.replicate ((i + 1) * d₂ / d₁ - i * d₂ / d₁) D := by
  simp [maximalDyckPath, h]

/-- The first `n` horizontal blocks reach height `⌊n * d₂ / d₁⌋` after `n` horizontal steps. -/
private theorem counts_blocks (d₁ d₂ n : ℕ) :
    ((List.range n).flatMap fun i ↦
        U :: List.replicate ((i + 1) * d₂ / d₁ - i * d₂ / d₁) D).count U = n ∧
      ((List.range n).flatMap fun i ↦
        U :: List.replicate ((i + 1) * d₂ / d₁ - i * d₂ / d₁) D).count D = n * d₂ / d₁ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hle : n * d₂ / d₁ ≤ (n + 1) * d₂ / d₁ :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ n))
    simp only [List.range_succ, List.flatMap_append, List.count_append, ih.1, ih.2,
      List.flatMap_singleton, List.count_cons, List.count_replicate]
    constructor
    · simp
    · simp
      omega

/-- The path has `d₁` horizontal steps. -/
@[simp]
theorem count_U_maximalDyckPath (d₁ d₂ : ℕ) : (maximalDyckPath d₁ d₂).count U = d₁ := by
  rcases eq_or_ne d₁ 0 with rfl | h
  · simp [List.count_replicate]
  · rw [maximalDyckPath_of_ne_zero _ h]
    exact (counts_blocks d₁ d₂ d₁).1

/-- The path has `d₂` vertical steps. -/
@[simp]
theorem count_D_maximalDyckPath (d₁ d₂ : ℕ) : (maximalDyckPath d₁ d₂).count D = d₂ := by
  rcases eq_or_ne d₁ 0 with rfl | h
  · simp
  · rw [maximalDyckPath_of_ne_zero _ h, (counts_blocks d₁ d₂ d₁).2,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h)]

/-- A list of steps has as many entries as `U`s and `D`s together. -/
private theorem length_eq_count_U_add_count_D (l : List DyckStep) :
    l.length = l.count U + l.count D := by
  induction l with
  | nil => simp
  | cons s l ih => cases s <;> simp [ih] <;> omega

/-- The path has `d₁ + d₂` steps. -/
@[simp]
theorem length_maximalDyckPath (d₁ d₂ : ℕ) : (maximalDyckPath d₁ d₂).length = d₁ + d₂ := by
  rw [length_eq_count_U_add_count_D, count_U_maximalDyckPath, count_D_maximalDyckPath]

/-- A path with no vertical steps is horizontal. -/
@[simp]
theorem maximalDyckPath_zero_right (d₁ : ℕ) : maximalDyckPath d₁ 0 = List.replicate d₁ U := by
  rcases eq_or_ne d₁ 0 with rfl | h
  · simp
  · rw [maximalDyckPath_of_ne_zero _ h]
    simp only [mul_zero, Nat.zero_div, Nat.sub_self, List.replicate_zero]
    induction d₁ with
    | zero => simp
    | succ n ih =>
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [List.range_succ, List.flatMap_append, ih hn, List.replicate_succ']
        simp

/-- The diagonal path alternates horizontal and vertical steps. -/
theorem maximalDyckPath_self (a : ℕ) :
    maximalDyckPath a a = (List.replicate a [U, D]).flatten := by
  rcases eq_or_ne a 0 with rfl | h
  · simp
  · rw [maximalDyckPath_of_ne_zero _ h]
    have hblock (i : ℕ) : (i + 1) * a / a - i * a / a = 1 := by
      rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero h), Nat.mul_div_cancel _ (Nat.pos_of_ne_zero h)]
      omega
    simp only [hblock, List.replicate_one]
    clear hblock h
    induction a with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ', List.flatten_append]
      simp

end Mei
