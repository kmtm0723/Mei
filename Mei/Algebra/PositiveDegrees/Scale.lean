/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.PositiveDegrees.Grading

/-!
# Positive multiples of a positive degree

For positive degree data `δ` on an allowed monoid `P` and a positive integer `c`, the multiple
`c δ` is again a positive degree on `P`. A grading that is positive for `δ` is positive for
`c δ`, since positivity only depends on `P`, and the pieces of `c δ`-degree above `k` are the
pieces of `δ`-degree above `⌊k / c⌋`.

Consequently the identity change of degree from `δ` to `c δ`
(`Mei.PositiveDegreeMap.changeDegree`) has cutoff modulus at most `⌊k / c⌋`, and the reverse
change has cutoff modulus at most `c k`. Both bounds are equalities when `δ` takes the value
one on `P`, for instance for the orthant degrees.
-/

public section

namespace Mei

variable {N : Type*} [AddCommMonoid N]

namespace PositiveDegrees

variable (d : PositiveDegrees N) (c : ℕ) [NeZero c]

/-- The positive degree `c δ` on the same allowed monoid, for a positive integer `c`. -/
def scale : PositiveDegrees N where
  monoid := d.monoid
  degree := (AddMonoidHom.mulLeft (c : ℤ)).comp d.degree
  degree_pos hn hne :=
    mul_pos (by exact_mod_cast NeZero.pos c) (d.degree_pos hn hne)
  finite_le k := (d.finite_le k).subset fun n ⟨hn, hk⟩ =>
    ⟨hn, (le_mul_of_one_le_left (d.degree_nonneg hn)
      (by exact_mod_cast NeZero.one_le)).trans hk⟩

/-- Scaling keeps the allowed monoid. -/
@[simp]
theorem scale_monoid : (d.scale c).monoid = d.monoid := (rfl)

/-- The scaled degree is the multiple `c δ`. -/
@[simp]
theorem scale_degree (n : N) : (d.scale c).degree n = c * d.degree n := (rfl)

/-- Scaling by one is the identity. -/
@[simp]
theorem scale_one : d.scale 1 = d :=
  PositiveDegrees.ext (d.scale_monoid 1) (AddMonoidHom.ext fun n => by simp)

/-- The degree `c δ` exceeds `k` exactly when `δ` exceeds `⌊k / c⌋`. -/
theorem lt_scale_degree_iff {k : ℕ} {n : N} :
    (k : ℤ) < (d.scale c).degree n ↔ ((k / c : ℕ) : ℤ) < d.degree n := by
  rw [scale_degree, Int.natCast_div, Int.ediv_lt_iff_lt_mul (by exact_mod_cast NeZero.pos c),
    mul_comm]

end PositiveDegrees

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (ℒ : N → Submodule R M)

/-- A grading positive for `δ` is positive for `c δ`, which has the same allowed monoid. -/
instance IsPositiveGrading.scale (d : PositiveDegrees N) (c : ℕ) [NeZero c]
    [IsPositiveGrading d ℒ] : IsPositiveGrading (d.scale c) ℒ :=
  ⟨IsPositiveGrading.eq_bot (d := d)⟩

namespace PositiveDegrees

variable (d : PositiveDegrees N) (c : ℕ) [NeZero c]

/-- The pieces of `c δ`-degree above `k` are those of `δ`-degree above `⌊k / c⌋`. -/
theorem degreeSubmodule_scale (k : ℕ) :
    (d.scale c).degreeSubmodule ℒ k = d.degreeSubmodule ℒ (k / c) := by
  apply le_antisymm
  · rw [degreeSubmodule_def]
    exact iSup_le fun n => d.le_degreeSubmodule ℒ ((d.lt_scale_degree_iff c).mp n.2)
  · rw [degreeSubmodule_def]
    exact iSup_le fun n => (d.scale c).le_degreeSubmodule ℒ ((d.lt_scale_degree_iff c).mpr n.2)

end PositiveDegrees

namespace PositiveDegreeMap

variable (d : PositiveDegrees N) (c : ℕ) [NeZero c]

/-- Changing from `δ` to `c δ` needs source cutoff at most `⌊k / c⌋` at target order `k`. -/
theorem changeDegree_scale_modulus_le (k : ℕ) :
    (changeDegree d (d.scale c) (d.scale_monoid c).symm).modulus k ≤ k / c :=
  (changeDegree_modulus_le_iff _ _ _ _ _).mpr fun _ _ hk =>
    not_lt.mp fun h => (not_lt.mpr hk) ((d.lt_scale_degree_iff c).mpr h)

/-- Changing from `c δ` back to `δ` needs source cutoff at most `c k` at target order `k`. -/
theorem changeDegree_scale_symm_modulus_le (k : ℕ) :
    (changeDegree (d.scale c) d (d.scale_monoid c)).modulus k ≤ c * k :=
  (changeDegree_modulus_le_iff _ _ _ _ _).mpr fun _ _ hk => by
    rw [PositiveDegrees.scale_degree, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hk (Int.natCast_nonneg c)

variable {d}

/-- If `δ` takes the value one on the allowed monoid, the change from `δ` to `c δ` has
modulus exactly `⌊k / c⌋`. -/
theorem changeDegree_scale_modulus {n : N} (hn : n ∈ d.monoid) (h1 : d.degree n = 1)
    (k : ℕ) : (changeDegree d (d.scale c) (d.scale_monoid c).symm).modulus k = k / c := by
  refine le_antisymm (changeDegree_scale_modulus_le d c k) ?_
  have hm : (k / c) • n ∈ d.monoid := d.monoid.nsmul_mem hn _
  have h := (changeDegree d (d.scale c) (d.scale_monoid c).symm).degree_le k hm (by
    rw [changeDegree_apply, PositiveDegrees.scale_degree, map_nsmul, h1, nsmul_eq_mul, mul_one]
    exact_mod_cast Nat.mul_div_le k c)
  rw [map_nsmul, h1, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- If `δ` takes the value one on the allowed monoid, the change from `c δ` back to `δ` has
modulus exactly `c k`. -/
theorem changeDegree_scale_symm_modulus {n : N} (hn : n ∈ d.monoid) (h1 : d.degree n = 1)
    (k : ℕ) : (changeDegree (d.scale c) d (d.scale_monoid c)).modulus k = c * k := by
  refine le_antisymm (changeDegree_scale_symm_modulus_le d c k) ?_
  have hm : k • n ∈ (d.scale c).monoid := d.monoid.nsmul_mem hn _
  have h := (changeDegree (d.scale c) d (d.scale_monoid c)).degree_le k hm (by
    rw [changeDegree_apply, map_nsmul, h1, nsmul_eq_mul, mul_one])
  rw [PositiveDegrees.scale_degree, map_nsmul, h1, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

end PositiveDegreeMap

end Mei
