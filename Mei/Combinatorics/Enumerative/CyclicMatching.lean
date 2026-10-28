/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Matching tokens with sinks on a cycle

Arrange `n` positions on a cycle, call the positions in `B` sinks, and put `τ k` tokens at
every other position `k`. Give a sink the weight `-1` and any other position the weight `τ k`.
A sink `v` is *matched* if some non-sink `h` reaches it before balancing: every cyclic window
from `h` that stops strictly before `v` has nonzero total weight.

The number of matched sinks is `min #B (∑ k ∉ B, τ k)`. Equivalently a sink is matched
exactly when some cyclic window ending just before it has positive weight, and the unmatched
sinks are the record lows of the periodic walk of partial weight sums. Each period lowers that
walk by `#B - ∑ τ`, one record at a time.

This is a cycle lemma in the style of Dvoretzky–Motzkin; it counts the total shadows of gradings
of maximal Dyck paths.
-/

public section

open Finset

namespace Mei.CyclicMatching

variable {n : ℕ}

/-- The cyclic interval from `e` to `e'`, both included. -/
def cyclicIcc (e e' : Fin n) : Finset (Fin n) := {k | (k - e).val ≤ (e' - e).val}

@[simp]
theorem mem_cyclicIcc {e e' k : Fin n} : k ∈ cyclicIcc e e' ↔ (k - e).val ≤ (e' - e).val := by
  simp [cyclicIcc]

/-- The offset of `k` from `e` vanishes exactly at `e`. -/
theorem val_sub_eq_zero_iff {k e : Fin n} : (k - e).val = 0 ↔ k = e := by
  have : NeZero n := ⟨e.pos.ne'⟩
  rw [Fin.val_eq_zero_iff]
  exact sub_eq_zero

/-- The offset of a position from itself is zero. -/
@[simp]
theorem val_sub_self (e : Fin n) : (e - e).val = 0 :=
  val_sub_eq_zero_iff.mpr rfl

/-- The one-point cyclic interval. -/
@[simp]
theorem cyclicIcc_self (e : Fin n) : cyclicIcc e e = {e} := by
  ext k
  rw [mem_cyclicIcc, val_sub_self, Nat.le_zero, val_sub_eq_zero_iff, mem_singleton]

/-- A position lies in the cyclic interval `[a, c]` exactly when its distance to `c` is at most
the length of the interval. -/
theorem val_sub_le_val_sub_iff (a b c : Fin n) :
    (c - b).val ≤ (c - a).val ↔ (b - a).val ≤ (c - a).val := by
  have : NeZero n := ⟨a.pos.ne'⟩
  have hcb : c - b = (c - a) - (b - a) := by abel
  rw [hcb]
  generalize b - a = x
  generalize c - a = y
  rcases le_or_gt x y with hxy | hxy
  · rw [Fin.coe_sub_iff_le.mpr hxy]
    exact iff_of_true (Nat.sub_le _ _) hxy
  · rw [Fin.coe_sub_iff_lt.mpr hxy]
    have := x.isLt
    exact iff_of_false (by omega) (not_le.mpr hxy)

/-- Negation reverses cyclic intervals. -/
theorem neg_mem_cyclicIcc {e v x : Fin n} : -x ∈ cyclicIcc e v ↔ x ∈ cyclicIcc (-v) (-e) := by
  have : NeZero n := ⟨e.pos.ne'⟩
  rw [mem_cyclicIcc, mem_cyclicIcc, ← val_sub_le_val_sub_iff e (-x) v,
    show x - -v = v - -x by abel, show -e - -v = v - e by abel]

/-- Reindexing a sum over a cyclic interval by negation. -/
theorem sum_cyclicIcc_neg {M : Type*} [AddCommMonoid M] (f : Fin n → M) (a b : Fin n) :
    ∑ k ∈ cyclicIcc (-b) (-a), f k = ∑ k ∈ cyclicIcc a b, f (-k) :=
  sum_nbij' Neg.neg Neg.neg (fun _ hk ↦ neg_mem_cyclicIcc.mpr hk)
    (fun _ hk ↦ neg_mem_cyclicIcc.mpr (by rwa [neg_neg, neg_neg])) (fun k _ ↦ neg_neg k)
    (fun k _ ↦ neg_neg k) (fun k _ ↦ by rw [neg_neg])

variable (B : Finset (Fin n)) (τ : Fin n → ℕ)

/-- The weight of a position: `-1` at a sink and the number of tokens elsewhere. -/
def weight (k : Fin n) : ℤ := if k ∈ B then -1 else τ k

theorem weight_def (k : Fin n) : weight B τ k = if k ∈ B then -1 else (τ k : ℤ) := (rfl)

/-- A sink has weight `-1`. -/
theorem weight_of_mem {k : Fin n} (hk : k ∈ B) : weight B τ k = -1 := by
  simp [weight, hk]

/-- A non-sink has nonnegative weight. -/
theorem weight_nonneg {k : Fin n} (hk : k ∉ B) : 0 ≤ weight B τ k := by
  simp [weight, hk]

/-- A non-sink carries its tokens as weight. -/
theorem weight_of_notMem {k : Fin n} (hk : k ∉ B) : weight B τ k = τ k := by
  simp [weight, hk]

/-- Every weight is at least `-1`. -/
theorem neg_one_le_weight (k : Fin n) : -1 ≤ weight B τ k := by
  unfold weight
  split_ifs
  · exact le_rfl
  · exact le_trans (by decide) (Int.natCast_nonneg _)

/-- A position of negative weight is a sink. -/
theorem mem_of_weight_neg {k : Fin n} (hk : weight B τ k < 0) : k ∈ B := by
  by_contra h
  exact absurd hk (not_lt.mpr (weight_nonneg B τ h))

/-- A weight sum counts tokens off the sinks and subtracts the sinks. -/
theorem sum_weight_eq (S : Finset (Fin n)) :
    ∑ k ∈ S, weight B τ k = (∑ k ∈ S ∩ Bᶜ, τ k : ℕ) - (#(S ∩ B) : ℤ) := by
  rw [← sum_filter_add_sum_filter_not S (· ∈ B)]
  rw [sum_congr rfl fun k hk ↦ weight_of_mem B τ (mem_filter.mp hk).2,
    sum_congr rfl fun k hk ↦ (show weight B τ k = τ k by simp [weight, (mem_filter.mp hk).2])]
  rw [filter_mem_eq_inter, show S.filter (· ∉ B) = S ∩ Bᶜ by ext; simp]
  simp [sub_eq_neg_add]

/-- The total weight is the number of tokens minus the number of sinks. -/
theorem sum_weight : ∑ i : Fin n, weight B τ i = (∑ k ∈ Bᶜ, τ k : ℕ) - (#B : ℤ) := by
  rw [← sum_add_sum_compl B, sum_congr rfl fun k hk ↦ weight_of_mem B τ hk,
    sum_congr rfl fun k hk ↦ (show weight B τ k = τ k by simp [weight, mem_compl.mp hk])]
  simp [sub_eq_neg_add]

/-- A sink `v` is matched if from some non-sink `h`, every cyclic window `[h, e]` stopping
strictly before `v` has nonzero total weight. -/
@[expose]
def Matched (v : Fin n) : Prop :=
  ∃ h ∉ B, ∀ e : Fin n, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0

instance : DecidablePred (Matched B τ) := fun _ ↦
  inferInstanceAs (Decidable (∃ _, _))

section Walk

variable [NeZero n]

/-- The position of the periodic extension at time `k`. -/
private def pos (k : ℕ) : Fin n := Fin.ofNat n k

/-- The walk of partial weight sums along the periodic extension. -/
private def walk (k : ℕ) : ℤ := ∑ j ∈ range k, weight B τ (pos j)

private theorem pos_add_self (k : ℕ) : pos (k + n) = (pos k : Fin n) := by
  simp [pos, Fin.ext_iff]

private theorem walk_succ (k : ℕ) : walk B τ (k + 1) = walk B τ k + weight B τ (pos k) := by
  simp [walk, sum_range_succ]

/-- One period changes the walk by the total weight. -/
private theorem walk_add_self (k : ℕ) :
    walk B τ (k + n) = walk B τ k + ∑ i : Fin n, weight B τ i := by
  induction k with
  | zero =>
    rw [zero_add, walk, ← Fin.sum_univ_eq_sum_range (fun j ↦ weight B τ (pos j)) n]
    simp [walk, pos]
  | succ k ih =>
    rw [show k + 1 + n = k + n + 1 by omega, walk_succ, ih, walk_succ, pos_add_self,
      add_right_comm]

/-- A cyclic window sum is an increment of the walk. -/
private theorem sum_cyclicIcc (h e : Fin n) :
    ∑ k ∈ cyclicIcc h e, weight B τ k = walk B τ (h.val + (e - h).val + 1) - walk B τ h.val := by
  have himage : cyclicIcc h e = (range ((e - h).val + 1)).image fun j ↦ h + pos j := by
    ext k
    simp only [mem_cyclicIcc, mem_image, mem_range, Nat.lt_succ_iff]
    constructor
    · intro hk
      exact ⟨(k - h).val, hk, by simp [pos]⟩
    · rintro ⟨j, hj, rfl⟩
      have hjn : j < n := lt_of_le_of_lt hj (e - h).isLt
      simpa [pos, Nat.mod_eq_of_lt hjn] using hj
  have hinj : Set.InjOn (fun j ↦ h + pos j) (range ((e - h).val + 1) : Set ℕ) := by
    intro i hi j hj hij
    have hin : i < n := lt_of_le_of_lt (Nat.lt_succ_iff.mp (mem_range.mp hi)) (e - h).isLt
    have hjn : j < n := lt_of_le_of_lt (Nat.lt_succ_iff.mp (mem_range.mp hj)) (e - h).isLt
    have := congrArg Fin.val (add_left_cancel hij)
    simpa [pos, Nat.mod_eq_of_lt hin, Nat.mod_eq_of_lt hjn] using this
  rw [himage, sum_image hinj, walk, walk, add_assoc,
    sum_range_add (fun j ↦ weight B τ (pos j)) h.val ((e - h).val + 1), add_sub_cancel_left]
  refine sum_congr rfl fun j _ ↦ ?_
  congr 1
  simp [pos, Fin.ext_iff, Fin.val_add, Nat.add_mod]


private theorem pos_add (a b : ℕ) : pos (a + b) = (pos a + pos b : Fin n) := by
  simp [pos, Fin.ext_iff, Fin.val_add, Nat.add_mod]

private theorem pos_val (k : Fin n) : pos k.val = k := by
  simp [pos]

/-- The walk is periodic up to the total weight. -/
private theorem walk_add_self_sub (a b : ℕ) :
    walk B τ (b + n) - walk B τ (a + n) = walk B τ b - walk B τ a := by
  rw [walk_add_self, walk_add_self]
  abel

/-- Starting at a non-sink, a walk whose increments never vanish stays above its start. -/
private theorem lt_walk_of_ne {a s : ℕ} (ha : pos a ∉ B)
    (hne : ∀ t < s, walk B τ (a + t + 1) ≠ walk B τ a) :
    ∀ t < s, walk B τ a < walk B τ (a + t + 1) := by
  intro t
  induction t with
  | zero =>
    intro hs
    have h₀ := weight_nonneg B τ ha
    have h₁ := hne 0 hs
    rw [add_zero, walk_succ] at h₁ ⊢
    omega
  | succ t ih =>
    intro hs
    have h₀ := ih (by omega)
    have h₁ := hne (t + 1) hs
    have h₂ := neg_one_le_weight B τ (pos (a + t + 1))
    rw [show a + (t + 1) + 1 = a + t + 1 + 1 by omega, walk_succ] at h₁ ⊢
    omega

/-- A sink is matched exactly when some cyclic window ending just before it has positive
weight, read on the walk over the preceding period. -/
private theorem matched_iff {v : Fin n} (hv : v ∈ B) :
    Matched B τ v ↔
      ∃ a, v.val < a ∧ a < v.val + n ∧ walk B τ a < walk B τ (v.val + n) := by
  constructor
  · rintro ⟨h, hh, hwin⟩
    have hhv : h ≠ v := fun e ↦ hh (e ▸ hv)
    set s := (v - h).val with hs_def
    have hs0 : s ≠ 0 := fun h0 ↦ hhv (by
      have : NeZero n := inferInstance
      rw [hs_def, Fin.val_eq_zero_iff, sub_eq_zero] at h0
      exact h0.symm)
    have hne : ∀ t < s, walk B τ (h.val + t + 1) ≠ walk B τ h.val := by
      intro t ht heq
      have htn : t < n := lt_trans ht (v - h).isLt
      have he : (h + pos t - h).val = t := by
        simp [pos, Nat.mod_eq_of_lt htn]
      have := hwin (h + pos t) (by rw [he]; exact ht)
      rw [sum_cyclicIcc, he, heq, sub_self] at this
      exact this rfl
    have hlt := lt_walk_of_ne B τ (by rw [pos_val]; exact hh) hne (s - 1) (by omega)
    rw [show h.val + (s - 1) + 1 = h.val + s by omega] at hlt
    rcases le_or_gt h v with hle | hlt'
    · have hs : s = v.val - h.val := Fin.coe_sub_iff_le.mpr hle
      have hhv' : h.val < v.val := lt_of_le_of_ne hle (fun e ↦ hhv (Fin.ext e))
      refine ⟨h.val + n, by omega, by omega, ?_⟩
      have := walk_add_self_sub B τ h.val v.val
      rw [show h.val + s = v.val by omega] at hlt
      linarith
    · have hs : s = n + v.val - h.val := Fin.coe_sub_iff_lt.mpr hlt'
      refine ⟨h.val, by omega, by omega, ?_⟩
      rw [show h.val + s = v.val + n by omega] at hlt
      exact hlt
  · rintro ⟨a, hva, hai, hwa⟩
    set i := v.val + n
    set F := (Ioo v.val i).filter fun a ↦ walk B τ a < walk B τ i
    have hF : F.Nonempty := ⟨a, by simp [F, hva, hai, hwa]⟩
    set a' := F.max' hF
    have ha'F : a' ∈ F := F.max'_mem hF
    simp only [F, mem_filter, mem_Ioo] at ha'F
    obtain ⟨⟨hva', ha'i⟩, hwa'⟩ := ha'F
    have habove : ∀ j, a' < j → j ≤ i → walk B τ a' < walk B τ j := by
      intro j hj hji
      rcases lt_or_eq_of_le hji with hji | rfl
      · by_contra hle
        have hjF : j ∈ F := by
          simp only [F, mem_filter, mem_Ioo]
          exact ⟨⟨by omega, hji⟩, by linarith [not_lt.mp hle]⟩
        exact absurd (F.le_max' j hjF) (not_le.mpr hj)
      · exact hwa'
    refine ⟨pos a', fun hmem ↦ ?_, fun e he ↦ ?_⟩
    · have h₁ := habove (a' + 1) (by omega) (by omega)
      rw [walk_succ, weight_of_mem B τ hmem] at h₁
      omega
    · have hdiff : (v - pos a').val = i - a' := by
        have hv' : v = pos a' + pos (i - a') := by
          rw [← pos_add, show a' + (i - a') = v.val + n by omega, pos_add_self, pos_val]
        rw [hv', add_sub_cancel_left]
        simp [pos, Nat.mod_eq_of_lt (show i - a' < n by omega)]
      rw [hdiff] at he
      have hshift : walk B τ ((pos a' : Fin n).val + (e - pos a').val + 1) -
          walk B τ (pos a' : Fin n).val =
          walk B τ (a' + (e - pos a').val + 1) - walk B τ a' := by
        have hmod : (pos a' : Fin n).val = a' % n := by simp [pos]
        generalize (e - pos a').val = t
        rcases lt_or_ge a' n with han | han
        · rw [hmod, Nat.mod_eq_of_lt han]
        · have ha'' : a' = a' % n + n := by
            rw [Nat.mod_eq_sub_mod han, Nat.mod_eq_of_lt (by omega)]
            omega
          rw [hmod]
          have := walk_add_self_sub B τ (a' % n) (a' % n + t + 1)
          rw [show a' % n + t + 1 + n = a' + t + 1 by omega, ← ha''] at this
          exact this.symm
      rw [sum_cyclicIcc, hshift]
      have := habove (a' + (e - pos a').val + 1) (by omega) (by omega)
      linarith

/-- The running minimum of the walk up to time `k`. -/
private def runMin (k : ℕ) : ℤ := ((range (k + 1)).image (walk B τ)).min' (by simp)

private theorem runMin_le {a k : ℕ} (h : a ≤ k) : runMin B τ k ≤ walk B τ a :=
  min'_le _ _ (mem_image_of_mem _ (mem_range.mpr (Nat.lt_succ_of_le h)))

private theorem exists_runMin (k : ℕ) : ∃ a ≤ k, walk B τ a = runMin B τ k := by
  obtain ⟨a, ha, he⟩ := mem_image.mp (min'_mem ((range (k + 1)).image (walk B τ)) (by simp))
  exact ⟨a, Nat.lt_succ_iff.mp (mem_range.mp ha), he⟩

private theorem runMin_succ (k : ℕ) :
    runMin B τ (k + 1) = min (runMin B τ k) (walk B τ (k + 1)) := by
  apply le_antisymm
  · obtain ⟨a, ha, he⟩ := exists_runMin B τ k
    exact le_min (he ▸ runMin_le B τ (by omega)) (runMin_le B τ le_rfl)
  · obtain ⟨a, ha, he⟩ := exists_runMin B τ (k + 1)
    rw [← he]
    rcases Nat.lt_or_ge a (k + 1) with h | h
    · exact min_le_of_left_le (runMin_le B τ (by omega))
    · exact min_le_of_right_le (le_of_eq (by rw [show a = k + 1 by omega]))

/-- The running minimum drops by at most one per step. -/
private theorem runMin_succ_ge (k : ℕ) : runMin B τ k - 1 ≤ runMin B τ (k + 1) := by
  rw [runMin_succ]
  refine le_min (by omega) ?_
  have h₁ := runMin_le B τ (le_refl k)
  have h₂ := neg_one_le_weight B τ (pos k)
  rw [walk_succ]
  omega

/-- After a period of negative total weight, the running minimum has dropped by that weight. -/
private theorem runMin_add_self (hT : ∑ i : Fin n, weight B τ i < 0) :
    runMin B τ (n + n) = runMin B τ n + ∑ i : Fin n, weight B τ i := by
  apply le_antisymm
  · obtain ⟨a, ha, he⟩ := exists_runMin B τ n
    rw [← he, ← walk_add_self]
    exact runMin_le B τ (by omega)
  · obtain ⟨a, ha, he⟩ := exists_runMin B τ (n + n)
    rw [← he]
    rcases Nat.lt_or_ge a n with h | h
    · have := runMin_le B τ h.le
      omega
    · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [add_comm n b, walk_add_self]
      have := runMin_le B τ (show b ≤ n by omega)
      omega

/-- When the total weight is negative, an unmatched sink at time `i` of the second period is
exactly a step at which the running minimum drops. -/
private theorem unmatched_iff_drop (hT : ∑ i : Fin n, weight B τ i < 0) {i : ℕ} (hni : n ≤ i)
    (hi : i < n + n) :
    (pos i ∈ B ∧ ∀ a, i - n < a → a < i → walk B τ i ≤ walk B τ a) ↔
      runMin B τ (i + 1) < runMin B τ i := by
  constructor
  · rintro ⟨hB, hmin⟩
    have hwi : walk B τ i ≤ runMin B τ i := by
      obtain ⟨a, ha, he⟩ := exists_runMin B τ i
      rw [← he]
      rcases lt_or_eq_of_le ha with ha | rfl
      · rcases Nat.lt_or_ge (i - n) a with h | h
        · exact hmin a h ha
        · have hb : a + n ≤ i := by omega
          have hwalk := walk_add_self B τ a
          rcases lt_or_eq_of_le hb with hb | hb
          · have := hmin (a + n) (by omega) hb
            omega
          · rw [hb] at hwalk
            omega
      · exact le_rfl
    have := runMin_le B τ (show i + 1 ≤ i + 1 from le_rfl)
    rw [walk_succ, weight_of_mem B τ hB] at this
    omega
  · intro hdrop
    rw [runMin_succ] at hdrop
    have hlt : walk B τ (i + 1) < runMin B τ i := by
      by_contra h
      exact absurd hdrop (not_lt.mpr (le_min le_rfl (not_lt.mp h)))
    have hle := runMin_le B τ (le_refl i)
    have hB : pos i ∈ B := mem_of_weight_neg B τ (by rw [walk_succ] at hlt; omega)
    refine ⟨hB, fun a _ ha ↦ ?_⟩
    have := runMin_le B τ ha.le
    rw [walk_succ, weight_of_mem B τ hB] at hlt
    omega

/-- A sink `v` is matched exactly when some cyclic interval `[u, v]` with `u ≠ v` has
nonnegative weight, that is, when the window ending just before `v` has positive weight. -/
theorem matched_iff_exists_nonneg {v : Fin n} (hv : v ∈ B) :
    Matched B τ v ↔ ∃ u, u ≠ v ∧ 0 ≤ ∑ k ∈ cyclicIcc u v, weight B τ k := by
  have hvn : walk B τ (v.val + n + 1) = walk B τ (v.val + n) - 1 := by
    rw [walk_succ, pos_add_self, pos_val, weight_of_mem B τ hv]
    ring_nf
  have hv1 : walk B τ (v.val + 1) = walk B τ v.val - 1 := by
    rw [walk_succ, pos_val, weight_of_mem B τ hv]
    ring_nf
  have hper := walk_add_self B τ v.val
  rw [matched_iff B τ hv]
  constructor
  · rintro ⟨a, hva, hav, hwa⟩
    refine ⟨pos a, fun he ↦ ?_, ?_⟩
    · have hmod : a % n = v.val := by
        have := congrArg Fin.val he
        simpa [pos] using this
      rcases lt_or_ge a n with han | han
      · rw [Nat.mod_eq_of_lt han] at hmod
        omega
      · rw [Nat.mod_eq_sub_mod han, Nat.mod_eq_of_lt (by omega)] at hmod
        omega
    · have hdiff : (v - pos a).val = v.val + n - a := by
        have key : v = pos a + pos (v.val + n - a) := by
          rw [← pos_add, show a + (v.val + n - a) = v.val + n by omega, pos_add_self, pos_val]
        rw [sub_eq_iff_eq_add'.mpr key]
        simp [pos, Nat.mod_eq_of_lt (show v.val + n - a < n by omega)]
      rw [sum_cyclicIcc, hdiff]
      have hmod : (pos a : Fin n).val = a % n := by simp [pos]
      rw [hmod]
      rcases lt_or_ge a n with han | han
      · rw [Nat.mod_eq_of_lt han, show a + (v.val + n - a) + 1 = v.val + n + 1 by omega, hvn]
        omega
      · have ha : a % n = a - n := by
          rw [Nat.mod_eq_sub_mod han, Nat.mod_eq_of_lt (by omega)]
        rw [ha, show a - n + (v.val + n - a) + 1 = v.val + 1 by omega, hv1]
        have := walk_add_self B τ (a - n)
        rw [show a - n + n = a by omega] at this
        omega
  · rintro ⟨u, huv, hsum⟩
    rw [sum_cyclicIcc] at hsum
    rcases le_or_gt u v with hle | hlt
    · have hlt : u.val < v.val := lt_of_le_of_ne hle (fun e ↦ huv (Fin.ext e))
      rw [Fin.coe_sub_iff_le.mpr hle, show u.val + (v.val - u.val) + 1 = v.val + 1 by omega,
        hv1] at hsum
      refine ⟨u.val + n, by omega, by omega, ?_⟩
      have := walk_add_self B τ u.val
      omega
    · rw [Fin.coe_sub_iff_lt.mpr hlt, show u.val + (n + v.val - u.val) + 1 = v.val + n + 1 by
        omega, hvn] at hsum
      exact ⟨u.val, by omega, by omega, by omega⟩

/-- Several periods change the walk by a multiple of the total weight. -/
private theorem walk_add_mul (k j : ℕ) :
    walk B τ (k + j * n) = walk B τ k + j * ∑ i : Fin n, weight B τ i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show k + (j + 1) * n = k + j * n + n by ring, walk_add_self, ih]
    push_cast
    ring

/-- Walk increments only depend on the starting position modulo `n`. -/
private theorem walk_mod_sub (x t : ℕ) :
    walk B τ (x % n + t) - walk B τ (x % n) = walk B τ (x + t) - walk B τ x := by
  have hx : x = x % n + x / n * n := by rw [mul_comm]; exact (Nat.mod_add_div x n).symm
  conv_rhs => rw [hx, show x % n + x / n * n + t = x % n + t + x / n * n by ring]
  rw [walk_add_mul, walk_add_mul]
  ring

/-- With nonnegative total weight, the walk never goes below its minimum over one period. -/
private theorem walk_ge_of_nonneg (hA : 0 ≤ ∑ i : Fin n, weight B τ i) {m : ℕ}
    (hm : ∀ y < n, walk B τ m ≤ walk B τ y) (y : ℕ) : walk B τ m ≤ walk B τ y := by
  have hy : y = y % n + y / n * n := by rw [mul_comm]; exact (Nat.mod_add_div y n).symm
  rw [hy, walk_add_mul]
  have := hm (y % n) (Nat.mod_lt _ (NeZero.pos n))
  have : (0 : ℤ) ≤ (y / n : ℕ) * ∑ i : Fin n, weight B τ i := mul_nonneg (by positivity) hA
  linarith

omit [NeZero n] in
private theorem weight_compl (σ : Fin n → ℕ) (k : Fin n) :
    weight Bᶜ σ k = if k ∈ B then (σ k : ℤ) else -1 := by
  by_cases hk : k ∈ B <;> simp [weight, hk]

omit [NeZero n] in
private theorem weight_compl_of_mem (σ : Fin n → ℕ) {k : Fin n} (hk : k ∈ B) :
    weight Bᶜ σ k = σ k := by
  simp [weight_compl, hk]

/-- From a segment `[s, e]` on which the first walk stays strictly above its start and the
second walk does not decrease, starting at a non-sink, produce a mutually visible pair: the
sink is reached when the second walk first rises above its value after the first step. -/
private theorem mutual_of_segment (σ : Fin n → ℕ) {s e : ℕ} (hse2 : s + 1 < e)
    (hen : e ≤ s + n) (habove : ∀ y, s < y → y < e → walk B τ s < walk B τ y)
    (hβe : walk Bᶜ σ s ≤ walk Bᶜ σ e) (hsB : pos s ∉ B) :
    ∃ h ∉ B, ∃ v ∈ B,
      (∀ e, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0) ∧
      ∀ e, (v - e).val < (v - h).val → ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k ≠ 0 := by
  set β := walk Bᶜ σ with hβ
  have hβs1 : β (s + 1) = β s - 1 := by
    rw [hβ, walk_succ, weight_of_mem Bᶜ σ (mem_compl.mpr hsB)]
    ring
  -- The first time after `s + 1` that `β` rises above its value at `s + 1`.
  set G := (Ioc (s + 1) e).filter fun y ↦ β (s + 1) < β y
  have hGne : G.Nonempty := ⟨e, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hse2, le_rfl⟩, by omega⟩⟩
  set y₀ := G.min' hGne
  obtain ⟨hy₀I, hy₀β⟩ := mem_filter.mp (G.min'_mem hGne)
  obtain ⟨hy₀l, hy₀r⟩ := mem_Ioc.mp hy₀I
  set k := y₀ - 1
  have hk1 : k + 1 = y₀ := by omega
  have hbelow : ∀ z, s + 1 ≤ z → z ≤ k → β z < β (k + 1) := by
    intro z hz₁ hz₂
    rw [hk1]
    rcases eq_or_lt_of_le hz₁ with rfl | hz₁
    · exact hy₀β
    · by_contra hle
      have hzG : z ∈ G := mem_filter.mpr ⟨mem_Ioc.mpr ⟨hz₁, by omega⟩, by
        have := not_lt.mp hle; linarith [hy₀β]⟩
      exact absurd (G.min'_le z hzG) (by omega)
  have hkB : pos k ∈ B := by
    have h₁ := hbelow k (by omega) le_rfl
    rw [hβ, walk_succ, weight_compl] at h₁
    by_contra hk
    simp only [hk, ↓reduceIte] at h₁
    omega
  have hkn : k - s < n := by omega
  have hvh : (pos k - pos s : Fin n).val = k - s := by
    have hk' : (pos k : Fin n) = pos s + pos (k - s) := by
      rw [← pos_add, show s + (k - s) = k by omega]
    rw [hk', add_sub_cancel_left]
    simp [pos, Nat.mod_eq_of_lt hkn]
  have hps : (pos s : Fin n).val = s % n := by simp [pos]
  refine ⟨pos s, hsB, pos k, hkB, fun e' he' ↦ ?_, fun e' he' ↦ ?_⟩
  · rw [hvh] at he'
    rw [sum_cyclicIcc, hps, add_assoc, walk_mod_sub, ← add_assoc]
    have h2 := habove (s + (e' - pos s).val + 1) (by omega) (by omega)
    exact sub_ne_zero.mpr (ne_of_gt h2)
  · rw [hvh] at he'
    set u := (pos k - e').val with hu
    have he'k : e' = pos (k - u) := by
      have : (pos k : Fin n) = e' + pos u := by
        rw [hu]
        simp [pos]
      have h2 : (pos k : Fin n) = pos (k - u) + pos u := by
        rw [← pos_add, show k - u + u = k by omega]
      exact add_right_cancel (this.symm.trans h2)
    rw [sum_cyclicIcc]
    have hval : e'.val = (k - u) % n := by rw [he'k]; simp [pos]
    have hsum : e'.val + (pos k - e').val + 1 = (k - u) % n + (u + 1) := by
      rw [hval, ← hu]; ring
    rw [hsum, hval, walk_mod_sub, show k - u + (u + 1) = k + 1 by omega]
    have h2 := hbelow (k - u) (by omega) (by omega)
    exact sub_ne_zero.mpr (ne_of_gt h2)

/-- **Double cycle lemma.** Put `τ` tokens on the non-sinks and `σ` tokens on the sinks `B`.
If there are at least as many `τ` tokens as sinks and at least as many `σ` tokens as non-sinks,
then some non-sink `h` and sink `v` see each other: every window from `h` stopping before `v`
has nonzero weight for `(B, τ)`, and every window ending at `v` and starting after `h` has
nonzero weight for `(Bᶜ, σ)`. -/
theorem exists_mutual (σ : Fin n → ℕ) (hτ : #B ≤ ∑ k ∈ Bᶜ, τ k)
    (hσ : #Bᶜ ≤ ∑ k ∈ B, σ k) :
    ∃ h ∉ B, ∃ v ∈ B,
      (∀ e, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0) ∧
      ∀ e, (v - e).val < (v - h).val → ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k ≠ 0 := by
  -- The two walks and their total increments.
  have hA : 0 ≤ ∑ i : Fin n, weight B τ i := by
    rw [sum_weight]
    exact sub_nonneg.mpr (by exact_mod_cast hτ)
  have hAσ : 0 ≤ ∑ i : Fin n, weight Bᶜ σ i := by
    rw [sum_weight, compl_compl]
    exact sub_nonneg.mpr (by exact_mod_cast hσ)
  set α := walk B τ with hα
  set β := walk Bᶜ σ with hβ
  -- A global minimum of `α` and the first position attaining it.
  obtain ⟨m0, hm0, hmin⟩ := (range n).exists_min_image α ⟨0, by simp [NeZero.pos n]⟩
  have hglob : ∀ y, α m0 ≤ α y := walk_ge_of_nonneg B τ hA
    (fun y hy ↦ hmin y (mem_range.mpr hy))
  set Z := (range n).filter fun y ↦ α y = α m0 with hZ
  have hZne : Z.Nonempty := ⟨m0, by simp [Z, hm0]⟩
  set m1 := Z.min' hZne
  have hm1 : m1 ∈ Z := Z.min'_mem hZne
  -- Among the minima, choose one where `β` is smallest.
  obtain ⟨s, hsZ, hsβ⟩ := Z.exists_min_image β hZne
  have hsn : s < n := mem_range.mp (mem_filter.mp hsZ).1
  have hsα : α s = α m0 := (mem_filter.mp hsZ).2
  have hm1s : m1 ≤ s := Z.min'_le s hsZ
  have hm1n : m1 < n := mem_range.mp (mem_filter.mp hm1).1
  have hβper : β (m1 + n) = β m1 + ∑ i : Fin n, weight Bᶜ σ i := walk_add_self Bᶜ σ m1
  -- The next return of `α` to its minimum, or one period after `m1`.
  set F := (Ioc s (m1 + n)).filter fun y ↦ α y ≤ α m0
  set e := if hF : F.Nonempty then F.min' hF else m1 + n with he_def
  have hse : s < e ∧ e ≤ m1 + n := by
    by_cases hF : F.Nonempty
    · have := mem_Ioc.mp (mem_filter.mp (F.min'_mem hF)).1
      rw [he_def, dite_eq_left hF]
      exact this
    · rw [he_def, dite_eq_right hF]
      omega
  have habove : ∀ y, s < y → y < e → α m0 < α y := by
    intro y h₁ h₂
    by_contra hle
    have hyF : y ∈ F := mem_filter.mpr ⟨mem_Ioc.mpr ⟨h₁, by omega⟩, not_lt.mp hle⟩
    have hF : F.Nonempty := ⟨y, hyF⟩
    have : e ≤ y := by rw [he_def, dite_eq_left hF]; exact F.min'_le y hyF
    omega
  have hβe : β s ≤ β e := by
    by_cases hF : F.Nonempty
    · have heF := F.min'_mem hF
      have hee : e = F.min' hF := by rw [he_def, dite_eq_left hF]
      rw [← hee] at heF
      obtain ⟨heI, heα⟩ := mem_filter.mp heF
      have heα' : α e = α m0 := le_antisymm heα (hglob e)
      rcases lt_or_ge e n with hen | hen
      · exact hsβ e (mem_filter.mpr ⟨mem_range.mpr hen, heα'⟩)
      · set r := e - n with hr_def
        have her : e = r + n := by omega
        have hper : α (r + n) = α r + ∑ i : Fin n, weight B τ i := walk_add_self B τ r
        rw [her] at heα' heI ⊢
        have hrα : α r = α m0 := le_antisymm (by linarith [hglob r]) (hglob r)
        have hrZ : r ∈ Z := mem_filter.mpr ⟨mem_range.mpr (by omega), hrα⟩
        have hr : r = m1 := le_antisymm (by have := (mem_Ioc.mp heI).2; omega) (Z.min'_le r hrZ)
        rw [hr, hβper]
        linarith [hsβ m1 hm1]
    · have hee : e = m1 + n := by rw [he_def, dite_eq_right hF]
      rw [hee, hβper]
      linarith [hsβ m1 hm1]
  -- The first step from `s` is a non-sink carrying tokens.
  have hpos_s : (pos s : Fin n).val = s := by simp [pos, Nat.mod_eq_of_lt hsn]
  have hsB : pos s ∉ B := by
    intro hmem
    have := hglob (s + 1)
    rw [hα, walk_succ, weight_of_mem B τ hmem, ← hα, hsα] at this
    omega
  have hβs1 : β (s + 1) = β s - 1 := by
    rw [hβ, walk_succ, weight_of_mem Bᶜ σ (mem_compl.mpr hsB)]
    ring
  have hse2 : s + 1 < e := by
    by_contra h
    have : e = s + 1 := by omega
    rw [this, hβs1] at hβe
    omega
  exact mutual_of_segment B τ σ hse2 (by omega)
    (fun y h₁ h₂ ↦ by have := habove y h₁ h₂; rw [← hsα] at this; exact this) hβe hsB

/-- A time at which the first walk is at its running minimum. -/
private def IsBase (y : ℕ) : Prop := ∀ x ≤ y, walk B τ y ≤ walk B τ x

/-- A sink stepped from a running minimum after the first period is unmatched, so it carries
no `σ` tokens when every token-carrying sink is matched. -/
private theorem sigma_eq_zero_of_isBase (σ : Fin n → ℕ)
    (hm : ∀ v ∈ B, σ v ≠ 0 → Matched B τ v) {y : ℕ} (hy : n ≤ y) (hb : IsBase B τ y)
    (hyB : pos y ∈ B) : σ (pos y) = 0 := by
  by_contra hσ
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := (matched_iff B τ hyB).mp (hm _ hyB hσ)
  have hval : (pos y : Fin n).val = y % n := by simp [pos]
  rw [hval] at ha₁ ha₂ ha₃
  have hy' : y = y % n + n + (y / n - 1) * n := by
    have h₁ := Nat.mod_add_div y n
    have h₂ : 1 ≤ y / n := (Nat.le_div_iff_mul_le (NeZero.pos n)).mpr (by omega)
    rw [Nat.mul_comm] at h₁
    calc y = y % n + y / n * n := h₁.symm
      _ = _ := by
        obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h₂
        rw [ht, add_comm 1 t, Nat.add_sub_cancel, add_mul, one_mul]
        ring
  have h₁ := walk_add_mul B τ a (y / n - 1)
  have h₂ := walk_add_mul B τ (y % n + n) (y / n - 1)
  rw [← hy'] at h₂
  have := hb (a + (y / n - 1) * n) (by omega)
  linarith

/-- A running minimum followed by a sink step is again a running minimum. -/
private theorem isBase_succ {y : ℕ} (hb : IsBase B τ y) (hyB : pos y ∈ B) :
    IsBase B τ (y + 1) := by
  intro x hx
  rw [walk_succ, weight_of_mem B τ hyB]
  rcases Nat.lt_or_ge x (y + 1) with h | h
  · have := hb x (by omega)
    linarith
  · rw [show x = y + 1 by omega, walk_succ, weight_of_mem B τ hyB]

/-- From a running minimum, a stretch of unmatched sinks does not move the second walk. -/
private theorem walk_compl_eq_of_sinks (σ : Fin n → ℕ)
    (hm : ∀ v ∈ B, σ v ≠ 0 → Matched B τ v) {c : ℕ} (hc : n ≤ c) (hb : IsBase B τ c) :
    ∀ d, (∀ j, c ≤ j → j < c + d → pos j ∈ B) → walk Bᶜ σ (c + d) = walk Bᶜ σ c := by
  intro d
  induction d with
  | zero => intro; rfl
  | succ d ih =>
    intro hsink
    have hbase : IsBase B τ (c + d) := by
      clear ih
      induction d with
      | zero => simpa using hb
      | succ d ih' =>
        rw [← add_assoc]
        exact isBase_succ B τ (ih' fun j h₁ h₂ ↦ hsink j h₁ (by omega)) (hsink _ (by omega)
          (by omega))
    have hB := hsink (c + d) (by omega) (by omega)
    rw [← add_assoc, walk_succ, ih fun j h₁ h₂ ↦ hsink j h₁ (by omega), weight_compl_of_mem B σ hB,
      sigma_eq_zero_of_isBase B τ σ hm (by omega) hbase hB]
    simp

/-- Between two running minima across which the second walk does not decrease and which
contain a non-sink, there is an excursion of the first walk over which the second walk does not
decrease. -/
private theorem exists_segment (σ : Fin n → ℕ) (hm : ∀ v ∈ B, σ v ≠ 0 → Matched B τ v) :
    ∀ d a b, b - a = d → n ≤ a → a ≤ b → IsBase B τ a → IsBase B τ b →
      walk Bᶜ σ a ≤ walk Bᶜ σ b → (∃ j, a ≤ j ∧ j < b ∧ pos j ∉ B) →
      ∃ s e, a ≤ s ∧ e ≤ b ∧ s + 1 < e ∧
        (∀ y, s < y → y < e → walk B τ s < walk B τ y) ∧ walk Bᶜ σ s ≤ walk Bᶜ σ e ∧
        pos s ∉ B := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro a b hd ha hab hba hbb hβ ⟨j, hj₁, hj₂, hjB⟩
  -- The next return of the first walk to the level at `a`.
  set F := (Ioc a b).filter fun y ↦ walk B τ y ≤ walk B τ a
  have hF : F.Nonempty := ⟨b, mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, le_rfl⟩, hbb a hab⟩⟩
  obtain ⟨c, hcF, hcmin⟩ : ∃ c ∈ F, ∀ y ∈ F, c ≤ y :=
    ⟨F.min' hF, F.min'_mem hF, fun y hy ↦ F.min'_le y hy⟩
  obtain ⟨hcI, hcα⟩ := mem_filter.mp hcF
  obtain ⟨hac, hcb⟩ := mem_Ioc.mp hcI
  have hbetween : ∀ y, a < y → y < c → walk B τ a < walk B τ y := by
    intro y h₁ h₂
    by_contra hle
    have hyF : y ∈ F := mem_filter.mpr ⟨mem_Ioc.mpr ⟨h₁, by omega⟩, not_lt.mp hle⟩
    exact absurd (hcmin y hyF) (by omega)
  have hcb' : IsBase B τ c := by
    intro x hx
    rcases Nat.lt_or_ge a x with h | h
    · rcases lt_or_eq_of_le hx with h' | rfl
      · have := hbetween x h h'; linarith
      · exact le_rfl
    · exact le_trans hcα (hba x h)
  -- If `[c, b)` had no non-sink, the second walk would not move there.
  have hHc : walk Bᶜ σ c < walk Bᶜ σ b → ∃ j, c ≤ j ∧ j < b ∧ pos j ∉ B := by
    intro hlt
    by_contra hno
    simp only [not_exists, not_and, not_not] at hno
    have := walk_compl_eq_of_sinks B τ σ hm (by omega) hcb' (b - c)
      (fun j h₁ h₂ ↦ hno j h₁ (by omega))
    rw [show c + (b - c) = b by omega] at this
    omega
  have hrec : walk Bᶜ σ c < walk Bᶜ σ a → ∃ s e, a ≤ s ∧ e ≤ b ∧ s + 1 < e ∧
      (∀ y, s < y → y < e → walk B τ s < walk B τ y) ∧ walk Bᶜ σ s ≤ walk Bᶜ σ e ∧
      pos s ∉ B := by
    intro hlt
    have hd' : b - c < d := hd ▸ Nat.sub_lt_sub_left (hac.trans_le hcb) hac
    have hnc : n ≤ c := ha.trans hac.le
    obtain ⟨s, e, h₁, h₂, h₃, h₄, h₅, h₆⟩ := ih (b - c) hd' c b rfl hnc hcb hcb' hbb
      (hlt.le.trans hβ) (hHc (hlt.trans_le hβ))
    exact ⟨s, e, hac.le.trans h₁, h₂, h₃, h₄, h₅, h₆⟩
  by_cases haB : pos a ∈ B
  · -- A sink step: an unmatched sink, so the second walk stays put.
    have hc1 : c = a + 1 := by
      have h₁ : a + 1 ∈ F := mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by
        rcases eq_or_lt_of_le hj₁ with rfl | h
        · exact absurd haB hjB
        · omega⟩, by rw [walk_succ, weight_of_mem B τ haB]; omega⟩
      exact le_antisymm (hcmin _ h₁) (by omega)
    have hβc : walk Bᶜ σ c = walk Bᶜ σ a := by
      rw [hc1, walk_succ, weight_compl_of_mem B σ haB,
        sigma_eq_zero_of_isBase B τ σ hm ha hba haB]
      simp
    have hjc : c ≤ j := by
      rcases eq_or_lt_of_le hj₁ with rfl | h
      · exact absurd haB hjB
      · omega
    have hlt : b - c < d := hd ▸ Nat.sub_lt_sub_left (hac.trans_le hcb) hac
    have hnc : n ≤ c := ha.trans hac.le
    obtain ⟨s, e, h₁, h₂, h₃, h₄, h₅, h₆⟩ := ih (b - c) hlt c b rfl hnc hcb hcb' hbb
      (hβc ▸ hβ) ⟨j, hjc, hj₂, hjB⟩
    exact ⟨s, e, hac.le.trans h₁, h₂, h₃, h₄, h₅, h₆⟩
  · have hβa1 : walk Bᶜ σ (a + 1) = walk Bᶜ σ a - 1 := by
      rw [walk_succ, weight_of_mem Bᶜ σ (mem_compl.mpr haB)]
      ring
    by_cases hτa : τ (pos a) = 0
    · -- A non-sink without tokens: the second walk drops.
      have hc1 : c = a + 1 := by
        have h₁ : a + 1 ∈ F := mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, by
          rw [walk_succ, weight_of_notMem B τ haB, hτa]; simp⟩
        exact le_antisymm (hcmin _ h₁) (by omega)
      exact hrec (by rw [hc1, hβa1]; omega)
    · -- An excursion of the first walk.
      have hca : a + 1 < c := by
        by_contra h
        have hc1 : c = a + 1 := by omega
        rw [hc1, walk_succ, weight_of_notMem B τ haB] at hcα
        have : (0 : ℤ) < τ (pos a) := by exact_mod_cast Nat.pos_of_ne_zero hτa
        linarith
      rcases le_or_gt (walk Bᶜ σ a) (walk Bᶜ σ c) with hle | hlt
      · exact ⟨a, c, le_rfl, hcb, hca, hbetween, hle, haB⟩
      · exact hrec hlt

/-- **Double cycle lemma, matched form.** If every sink carrying `σ` tokens is matched for
`(B, τ)`, there is a non-sink, and there are at least as many `σ` tokens as non-sinks, then some
non-sink `h` and sink `v` see each other as in `exists_mutual`. -/
theorem exists_mutual_of_forall_matched (σ : Fin n → ℕ) (hBc : Bᶜ.Nonempty)
    (hm : ∀ v ∈ B, σ v ≠ 0 → Matched B τ v) (hσ : #Bᶜ ≤ ∑ k ∈ B, σ k) :
    ∃ h ∉ B, ∃ v ∈ B,
      (∀ e, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0) ∧
      ∀ e, (v - e).val < (v - h).val → ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k ≠ 0 := by
  by_cases hτ : #B ≤ ∑ k ∈ Bᶜ, τ k
  · exact exists_mutual B τ σ hτ hσ
  have hA : ∑ i : Fin n, weight B τ i < 0 := by
    rw [sum_weight]; exact sub_neg.mpr (by exact_mod_cast not_le.mp hτ)
  have hAσ : 0 ≤ ∑ i : Fin n, weight Bᶜ σ i := by
    rw [sum_weight, compl_compl]; exact sub_nonneg.mpr (by exact_mod_cast hσ)
  -- A running minimum `a` in the second period, and the same point one period later.
  obtain ⟨a, haI, hamin⟩ := (Icc n (n + n)).exists_min_image (walk B τ)
    ⟨n, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨ha₁, ha₂⟩ := mem_Icc.mp haI
  have hper (x : ℕ) := walk_add_self B τ x
  have hba : IsBase B τ a := by
    intro x hx
    rcases Nat.lt_or_ge x n with h | h
    · have := hamin (x + n) (mem_Icc.mpr ⟨by omega, by omega⟩)
      linarith [hper x]
    · exact hamin x (mem_Icc.mpr ⟨h, by omega⟩)
  have hbb : IsBase B τ (a + n) := by
    intro x hx
    rcases Nat.lt_or_ge a x with h | h
    · obtain ⟨t, rfl⟩ : ∃ t, x = t + n := ⟨x - n, by omega⟩
      have := hba t (by omega)
      linarith [hper t, hper a]
    · have := hba x h
      linarith [hper a]
  have hβ : walk Bᶜ σ a ≤ walk Bᶜ σ (a + n) := by
    linarith [walk_add_self Bᶜ σ a]
  obtain ⟨k, hk⟩ := hBc
  have hj : ∃ j, a ≤ j ∧ j < a + n ∧ pos j ∉ B := by
    refine ⟨a + (k - pos a).val, by omega, by have := (k - pos a).isLt; omega, ?_⟩
    rw [pos_add, pos_val, add_sub_cancel]
    exact mem_compl.mp hk
  obtain ⟨s, e, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_segment B τ σ hm n a (a + n) (by omega) ha₁
    (by omega) hba hbb hβ hj
  exact mutual_of_segment B τ σ h₃ (by omega) h₄ h₅ h₆

/-- **Double cycle lemma, reversed matched form.** If every non-sink carrying `τ` tokens is
matched backwards for `(Bᶜ, σ)`, there is a sink, and there are at least as many `τ` tokens as
sinks, then some non-sink `h` and sink `v` see each other as in `exists_mutual`. -/
theorem exists_mutual_of_forall_matched_rev (σ : Fin n → ℕ) (hB : B.Nonempty)
    (hm : ∀ h ∉ B, τ h ≠ 0 → ∃ v ∈ B,
      ∀ e, (v - e).val < (v - h).val → ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k ≠ 0)
    (hτ : #B ≤ ∑ k ∈ Bᶜ, τ k) :
    ∃ h ∉ B, ∃ v ∈ B,
      (∀ e, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0) ∧
      ∀ e, (v - e).val < (v - h).val → ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k ≠ 0 := by
  -- Reflect the cycle: the reflected non-sinks are the sinks, with the roles of `τ` and `σ`
  -- exchanged.
  set ν := (Equiv.neg (Fin n)).toEmbedding
  set B' := Bᶜ.map ν
  have hmem (k : Fin n) : k ∈ B' ↔ -k ∉ B := by
    rw [mem_map_equiv, Equiv.neg_symm, Equiv.neg_apply, mem_compl]
  have hcompl : B'ᶜ = B.map ν := by
    ext k
    rw [mem_compl, hmem, not_not, mem_map_equiv, Equiv.neg_symm, Equiv.neg_apply]
  have hw (k : Fin n) : weight B' (σ ∘ Neg.neg) k = weight Bᶜ σ (-k) := by
    simp only [weight_def, hmem, mem_compl, Function.comp_apply]
  have hw' (k : Fin n) : weight B'ᶜ (τ ∘ Neg.neg) k = weight B τ (-k) := by
    simp only [weight_def, mem_compl, hmem, not_not, Function.comp_apply]
  have hA (x y : Fin n) : ∑ k ∈ cyclicIcc (-y) (-x), weight Bᶜ σ k =
      ∑ k ∈ cyclicIcc x y, weight B' (σ ∘ Neg.neg) k :=
    (sum_cyclicIcc_neg _ x y).trans (sum_congr rfl fun k _ ↦ (hw k).symm)
  have hA' (x y : Fin n) : ∑ k ∈ cyclicIcc (-y) (-x), weight B τ k =
      ∑ k ∈ cyclicIcc x y, weight B'ᶜ (τ ∘ Neg.neg) k :=
    (sum_cyclicIcc_neg _ x y).trans (sum_congr rfl fun k _ ↦ (hw' k).symm)
  obtain ⟨h', hh', v', hv', hfwd, hbwd⟩ := exists_mutual_of_forall_matched B' (σ ∘ Neg.neg)
    (τ ∘ Neg.neg) (by
      obtain ⟨k, hk⟩ := hB
      refine ⟨-k, ?_⟩
      rw [hcompl, mem_map_equiv, Equiv.neg_symm, Equiv.neg_apply, neg_neg]
      exact hk)
    (fun v' hv' hτv ↦ by
      obtain ⟨v, hv, hall⟩ := hm (-v') ((hmem v').mp hv') hτv
      refine ⟨-v, by rw [hmem, neg_neg, not_not]; exact hv, fun e' he' ↦ ?_⟩
      have := hall (-e') (by rwa [show v - -e' = e' - -v by abel, show v - -v' = v' - -v by abel])
      rw [← hA (-v) e', neg_neg]
      exact this)
    (by rw [hcompl, card_map, sum_map]; simpa [ν] using hτ)
  rw [hmem, not_not] at hh'
  refine ⟨-v', (hmem v').mp hv', -h', hh', fun e he ↦ ?_, fun e he ↦ ?_⟩
  · have := hbwd (-e) (by rwa [show v' - -e = e - -v' by abel, show v' - h' = -h' - -v' by abel])
    rwa [← hA' (-e) v', neg_neg] at this
  · have := hfwd (-e) (by rwa [show -e - h' = -h' - e by abel, show v' - h' = -h' - -v' by abel])
    rwa [← hA h' (-e), neg_neg] at this

end Walk

/-- **Cyclic matching.** The number of matched sinks is the smaller of the number of sinks and
the number of tokens. -/
theorem card_matched : #{v ∈ B | Matched B τ v} = min #B (∑ k ∈ Bᶜ, τ k) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Finset.eq_empty_of_isEmpty B]
  have : NeZero n := ⟨hn.ne'⟩
  have hT := sum_weight B τ
  rcases le_or_gt #B (∑ k ∈ Bᶜ, τ k) with hle | hlt
  · -- Enough tokens: every sink is matched.
    rw [min_eq_left hle, filter_true_of_mem]
    intro v hv
    have hcompl : (Bᶜ).Nonempty := by
      by_contra hc
      rw [not_nonempty_iff_eq_empty.mp hc, sum_empty] at hle
      exact absurd hle (not_le.mpr (card_pos.mpr ⟨v, hv⟩))
    have hn2 : 1 < n := by
      by_contra h
      obtain ⟨k, hk⟩ := hcompl
      exact mem_compl.mp hk (by
        have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
        exact Subsingleton.elim v k ▸ hv)
    refine (matched_iff B τ hv).mpr ⟨v.val + 1, by omega, by omega, ?_⟩
    have h₁ := walk_add_self B τ v.val
    rw [walk_succ, pos_val, weight_of_mem B τ hv]
    omega
  · -- Too few tokens: the unmatched sinks are the record lows of one period.
    rw [min_eq_right hlt.le]
    have hneg : ∑ i : Fin n, weight B τ i < 0 := by omega
    have hun : #{v ∈ B | ¬Matched B τ v} = #{i ∈ Ico n (n + n) |
        runMin B τ (i + 1) < runMin B τ i} := by
      refine card_nbij' (fun v ↦ v.val + n) (fun i ↦ pos i) ?_ ?_ ?_ ?_
      · intro v hv
        simp only [coe_filter, Set.mem_ofPred_eq] at hv ⊢
        obtain ⟨hvB, hvm⟩ := hv
        refine ⟨mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
        refine (unmatched_iff_drop B τ hneg (by omega) (by omega)).mp ⟨?_, fun a h₁ h₂ ↦ ?_⟩
        · rw [pos_add_self, pos_val]
          exact hvB
        · by_contra hlt'
          exact hvm ((matched_iff B τ hvB).mpr ⟨a, by omega, h₂, not_le.mp hlt'⟩)
      · intro i hi
        simp only [coe_filter, Set.mem_ofPred_eq, mem_Ico] at hi ⊢
        obtain ⟨⟨hni, hi2⟩, hdrop⟩ := hi
        obtain ⟨hB, hmin⟩ := (unmatched_iff_drop B τ hneg hni hi2).mpr hdrop
        have hval : (pos i : Fin n).val = i - n := by
          simp only [pos, Fin.val_ofNat]
          rw [Nat.mod_eq_sub_mod hni, Nat.mod_eq_of_lt (by omega)]
        refine ⟨hB, fun hm ↦ ?_⟩
        obtain ⟨a, h₁, h₂, h₃⟩ := (matched_iff B τ hB).mp hm
        rw [hval, show i - n + n = i by omega] at h₂ h₃
        rw [hval] at h₁
        exact absurd (hmin a h₁ h₂) (not_le.mpr h₃)
      · intro v _
        simp only
        rw [pos_add_self, pos_val]
      · intro i hi
        simp only [coe_filter, Set.mem_ofPred_eq, mem_Ico] at hi
        simp only [pos, Fin.val_ofNat]
        rw [Nat.mod_eq_sub_mod hi.1.1, Nat.mod_eq_of_lt (by omega)]
        omega
    have hdrops : (#{i ∈ Ico n (n + n) | runMin B τ (i + 1) < runMin B τ i} : ℤ) =
        runMin B τ n - runMin B τ (n + n) := by
      rw [card_filter, Nat.cast_sum, sum_Ico_eq_sum_range, show n + n - n = n by omega]
      have htel := sum_range_sub' (fun k ↦ runMin B τ (n + k)) n
      simp only [add_zero] at htel
      rw [← htel]
      refine sum_congr rfl fun k _ ↦ ?_
      have h₁ := runMin_succ_ge B τ (n + k)
      have h₂ : runMin B τ (n + k + 1) ≤ runMin B τ (n + k) := by
        rw [runMin_succ]; exact min_le_left _ _
      rw [show n + (k + 1) = n + k + 1 by omega]
      split_ifs <;> push_cast <;> omega
    rw [runMin_add_self B τ hneg] at hdrops
    have htot : #{v ∈ B | Matched B τ v} + #{v ∈ B | ¬Matched B τ v} = #B :=
      card_filter_add_card_filter_not _
    rw [hun] at htot
    omega


end Mei.CyclicMatching
