/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.BCH.Ray.Basic
public import Mei.Algebra.PositiveDegrees.Ray.Commensurable

/-!
# Labels on commensurable nonprimitive indices

A wall indexed by a nonzero allowed degree `n`, rather than by a supported ray, carries a
completed label whose logarithmic coefficients vanish off the positive multiples `(j + 1) • n`.
Such a label lies in the completed subgroup of the supported ray through `n`. When rays are
abelian (`IsAbelianRays`), labels indexed by two commensurable allowed degrees therefore commute
as elements of the completed group of their common supported ray, although neither set of
positive multiples need contain the other.

In particular, if `2 • m` and `3 • m` are allowed and `m` is not, labels indexed by `2 • m` and by
`3 • m` commute. Their common supported ray has a generator dividing `m` positively, while `m`
itself is not an actual degree of this ray. This is the merging of labels on coincident supports
in the abelian-ray description of scattering diagrams in Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2), and Bridgeland, *Scattering
diagrams, Hall algebras and stability conditions*, §§2–3 (arXiv:1603.00416v4).

Membership in the ray group uses `Mei.PositiveDegrees.mem_completedRaySubgroup_iff_logComponent`
and commutation is `Mei.PositiveDegrees.commute_of_mem_completedRaySubgroup`.
-/

public section

namespace Mei.PositiveDegrees

variable {N R L : Type*} [AddCommGroup N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- A completed label whose logarithmic coefficients vanish off the positive multiples of an
actual degree `n` of a supported ray lies in the completed subgroup of that ray. -/
theorem mem_completedRaySubgroup_of_logComponent_eq_zero {w : SupportedRay d} {n : N}
    (hn : n ∈ w.rayDegrees) {g : d.completedBCHGroup ℒ}
    (hg : ∀ m, (∀ j : ℕ, (j + 1) • n ≠ m) → d.logComponent ℒ g m = 0) :
    g ∈ d.completedRaySubgroup ℒ w :=
  (d.mem_completedRaySubgroup_iff_logComponent ℒ w g).mpr fun m hm =>
    hg m fun j hj => hm (hj ▸ SupportedRay.succ_nsmul_mem_rayDegrees hn j)

/-- With abelian rays over a free degree lattice, completed labels supported on the positive
multiples of two commensurable nonzero allowed degrees commute. -/
theorem commute_of_logComponent_eq_zero_of_nsmul_eq_nsmul [Module.Free ℤ N]
    [IsAbelianRays d ℒ] {n n' : N} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (hn' : n' ∈ d.monoid)
    {p q : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) (h : p • n' = q • n) {g g' : d.completedBCHGroup ℒ}
    (hg : ∀ m, (∀ j : ℕ, (j + 1) • n ≠ m) → d.logComponent ℒ g m = 0)
    (hg' : ∀ m, (∀ j : ℕ, (j + 1) • n' ≠ m) → d.logComponent ℒ g' m = 0) :
    Commute g g' := by
  obtain ⟨w, hw⟩ := d.exists_supportedRay hn hn0
  exact d.commute_of_mem_completedRaySubgroup ℒ
    (d.mem_completedRaySubgroup_of_logComponent_eq_zero ℒ hw hg)
    (d.mem_completedRaySubgroup_of_logComponent_eq_zero ℒ
      (SupportedRay.mem_rayDegrees_of_nsmul_eq_nsmul hw hn' hp hq h) hg')

/-- With abelian rays over a free degree lattice, if `2 • m` and `3 • m` are allowed degrees
but `m` is not, completed labels supported on the positive multiples of `2 • m` commute with those
supported on the positive multiples of `3 • m`. Both lie in the completed group of the supported
ray of `exists_supportedRay_two_nsmul_three_nsmul`. -/
theorem commute_of_logComponent_eq_zero_two_nsmul_three_nsmul [Module.Free ℤ N]
    [IsAbelianRays d ℒ] {m : N} (h2 : 2 • m ∈ d.monoid) (h3 : 3 • m ∈ d.monoid)
    (hm : m ∉ d.monoid) {g g' : d.completedBCHGroup ℒ}
    (hg : ∀ n, (∀ j : ℕ, (j + 1) • (2 • m) ≠ n) → d.logComponent ℒ g n = 0)
    (hg' : ∀ n, (∀ j : ℕ, (j + 1) • (3 • m) ≠ n) → d.logComponent ℒ g' n = 0) :
    Commute g g' := by
  obtain ⟨w, hw2, hw3, -⟩ := d.exists_supportedRay_two_nsmul_three_nsmul h2 h3 hm
  exact d.commute_of_mem_completedRaySubgroup ℒ
    (d.mem_completedRaySubgroup_of_logComponent_eq_zero ℒ hw2 hg)
    (d.mem_completedRaySubgroup_of_logComponent_eq_zero ℒ hw3 hg')

end Mei.PositiveDegrees
