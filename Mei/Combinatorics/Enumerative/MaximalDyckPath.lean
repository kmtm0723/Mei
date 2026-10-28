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

/-- The first `m` horizontal blocks of the path. -/
private def blocks (d₁ d₂ m : ℕ) : List DyckStep :=
  (List.range m).flatMap fun i ↦ U :: List.replicate ((i + 1) * d₂ / d₁ - i * d₂ / d₁) D

private theorem blocks_succ (d₁ d₂ m : ℕ) :
    blocks d₁ d₂ (m + 1) =
      blocks d₁ d₂ m ++ U :: List.replicate ((m + 1) * d₂ / d₁ - m * d₂ / d₁) D := by
  simp [blocks, List.range_succ, List.flatMap_append]

/-- The first `n` horizontal blocks reach height `⌊n * d₂ / d₁⌋` after `n` horizontal steps. -/
private theorem counts_blocks (d₁ d₂ n : ℕ) :
    (blocks d₁ d₂ n).count U = n ∧ (blocks d₁ d₂ n).count D = n * d₂ / d₁ := by
  induction n with
  | zero => simp [blocks]
  | succ n ih =>
    have hle : n * d₂ / d₁ ≤ (n + 1) * d₂ / d₁ :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ n))
    simp only [blocks_succ, List.count_append, ih.1, ih.2, List.count_cons, List.count_replicate]
    constructor
    · simp
    · simp
      omega

/-- Every prefix of the first `m` blocks lies weakly below the diagonal and less than `d₁ + d₂`
below it, in the lattice distance `d₂ x - d₁ y`. -/
private theorem count_take_blocks {d₁ : ℕ} (d₂ : ℕ) (hd₁ : 0 < d₁) (m k : ℕ) :
    d₁ * ((blocks d₁ d₂ m).take k).count D ≤ d₂ * ((blocks d₁ d₂ m).take k).count U ∧
      d₂ * ((blocks d₁ d₂ m).take k).count U <
        d₁ * ((blocks d₁ d₂ m).take k).count D + (d₁ + d₂) := by
  induction m generalizing k with
  | zero => simp [blocks]; omega
  | succ m ih =>
    rw [blocks_succ, List.take_append]
    by_cases hk : k ≤ (blocks d₁ d₂ m).length
    · rw [Nat.sub_eq_zero_of_le hk, List.take_zero, List.append_nil]
      exact ih k
    obtain ⟨j, hj⟩ : ∃ j, k - (blocks d₁ d₂ m).length = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
      (by omega)).symm⟩
    rw [List.take_of_length_le (by omega), hj, List.take_succ_cons, List.take_replicate]
    simp only [List.count_append, (counts_blocks d₁ d₂ m).1, (counts_blocks d₁ d₂ m).2,
      List.count_cons, List.count_replicate]
    simp only [beq_self_eq_true, ↓reduceIte, reduceCtorEq, beq_iff_eq]
    set a := m * d₂ / d₁
    set b := (m + 1) * d₂ / d₁
    have hab : a ≤ b := Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ m))
    have hb : b * d₁ ≤ (m + 1) * d₂ := Nat.div_mul_le_self _ _
    have ha : m * d₂ < a * d₁ + d₁ := Nat.lt_div_mul_add hd₁
    have hi : a + min j (b - a) ≤ b := by omega
    have hi' : d₁ * (a + min j (b - a)) ≤ d₁ * b := Nat.mul_le_mul_left _ hi
    have ha' : d₁ * a ≤ d₁ * (a + min j (b - a)) := Nat.mul_le_mul_left _ (by omega)
    constructor <;> nlinarith

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
  · rw [maximalDyckPath_of_ne_zero _ h, ← blocks, (counts_blocks d₁ d₂ d₁).2,
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

/-- **The path stays near the diagonal.** With `x` horizontal and `y` vertical steps in a prefix,
`d₁ y ≤ d₂ x < d₁ y + d₁ + d₂`: the prefix lies weakly below the diagonal, at lattice distance
less than `d₁ + d₂`. -/
theorem count_take_maximalDyckPath {d₁ d₂ : ℕ} (hd : 0 < d₁ + d₂) (k : ℕ) :
    d₁ * ((maximalDyckPath d₁ d₂).take k).count D ≤
        d₂ * ((maximalDyckPath d₁ d₂).take k).count U ∧
      d₂ * ((maximalDyckPath d₁ d₂).take k).count U <
        d₁ * ((maximalDyckPath d₁ d₂).take k).count D + (d₁ + d₂) := by
  rcases Nat.eq_zero_or_pos d₁ with rfl | hd₁
  · simp only [maximalDyckPath_zero_left, List.take_replicate, List.count_replicate]
    simp
    omega
  · rw [maximalDyckPath_of_ne_zero _ hd₁.ne', ← blocks]
    exact count_take_blocks d₂ hd₁ d₁ k

end Mei
