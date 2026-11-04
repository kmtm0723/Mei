/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.PositiveDegrees.Ray.Basic

/-!
# Commensurable degrees on supported rays

Two allowed degrees `n`, `n'` are commensurable when `p • n' = q • n` for some nonzero natural
numbers `p`, `q`. In a free integer module, an allowed degree commensurable with an actual degree
of a supported ray is itself an actual degree of that ray. Thus nonprimitive indices of walls
that are commensurable share one supported primitive ray.

For instance, if `2 • m` and `3 • m` are allowed while `m` is not, both lie on a common supported
ray whose generator divides `m` positively, and `m` is not an actual degree of this ray. This is
the setting of reindexing walls by supported rays in Gross–Hacking–Keel–Kontsevich, *Canonical
bases for cluster algebras*, §1.1 (arXiv:1411.1394v2).

Ray uniqueness is `Mei.SupportedRay.eq_of_mem_rayDegrees`, and existence of the supported ray of a
nonzero allowed degree is `Mei.PositiveDegrees.exists_supportedRay`.
-/

public section

namespace Mei

variable {N : Type*} [AddCommGroup N] {d : PositiveDegrees N}

namespace SupportedRay

/-- Nonzero natural multiples of an actual ray degree remain on that ray. -/
theorem nsmul_mem_rayDegrees {w : SupportedRay d} {n : N} (hn : n ∈ w.rayDegrees) {p : ℕ}
    (hp : p ≠ 0) : p • n ∈ w.rayDegrees := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  exact succ_nsmul_mem_rayDegrees hn j

/-- In a free integer module, an allowed degree commensurable with an actual degree of a supported
ray is an actual degree of that ray. -/
theorem mem_rayDegrees_of_nsmul_eq_nsmul [Module.Free ℤ N] {w : SupportedRay d} {n n' : N}
    (hn : n ∈ w.rayDegrees) (hn' : n' ∈ d.monoid) {p q : ℕ} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : p • n' = q • n) : n' ∈ w.rayDegrees := by
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  have hn'0 : n' ≠ 0 := by
    rintro rfl
    exact ne_zero_of_mem_rayDegrees (nsmul_mem_rayDegrees hn hq) (by rw [← h, smul_zero])
  obtain ⟨v, hv⟩ := d.exists_supportedRay hn' hn'0
  obtain rfl : v = w :=
    eq_of_mem_rayDegrees (nsmul_mem_rayDegrees hv hp) (h ▸ nsmul_mem_rayDegrees hn hq)
  exact hv

end SupportedRay

namespace PositiveDegrees

variable (d)

/-- In a free integer module, if `2 • m` and `3 • m` are allowed degrees but `m` is not, then
`2 • m` and `3 • m` are actual degrees of one supported ray, `m` is a positive multiple of its
generator, and `m` is not an actual degree of this ray. -/
theorem exists_supportedRay_two_nsmul_three_nsmul [Module.Free ℤ N] {m : N}
    (h2 : 2 • m ∈ d.monoid) (h3 : 3 • m ∈ d.monoid) (hm : m ∉ d.monoid) :
    ∃ w : SupportedRay d, 2 • m ∈ w.rayDegrees ∧ 3 • m ∈ w.rayDegrees ∧
      m ∉ w.rayDegrees ∧ ∃ a : ℤ, 0 < a ∧ m = a • w.generator := by
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  have hm0 : 2 • m ≠ 0 := fun h0 =>
    hm (nsmul_right_injective two_ne_zero (h0.trans (smul_zero 2).symm) ▸ d.monoid.zero_mem)
  obtain ⟨w, hw⟩ := d.exists_supportedRay h2 hm0
  have hw3 : 3 • m ∈ w.rayDegrees :=
    SupportedRay.mem_rayDegrees_of_nsmul_eq_nsmul hw h3 two_ne_zero three_ne_zero
      (by rw [smul_smul, smul_smul, mul_comm])
  obtain ⟨-, a, ha, hma⟩ := SupportedRay.mem_rayDegrees.mp hw
  obtain ⟨-, b, -, hmb⟩ := SupportedRay.mem_rayDegrees.mp hw3
  -- Comparing `6 • m` computed from `2 • m` and from `3 • m` gives `3 * a = 2 * b`.
  have hab : 3 * a = 2 * b := w.isPrimitive.zsmul_left_injective (by
    dsimp only
    rw [mul_smul, mul_smul, ← hma, ← hmb]
    abel)
  refine ⟨w, hw, hw3, fun h => hm (w.rayDegrees_subset h), b - a, by omega, ?_⟩
  rw [sub_smul, ← hma, ← hmb]
  abel

end PositiveDegrees

end Mei
