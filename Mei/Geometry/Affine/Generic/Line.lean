/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Generic
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Finite exceptional times on affine lines

An affine line starting outside an affine obstacle meets it at most once. Thus a
line starting at a generic point of a finite exceptional arrangement has only
finitely many nongeneric parameter values. The other endpoint can be arbitrary;
a constant line at a generic point has no exceptional times.
-/

public section

namespace AffineSubspace

/-- The inverse image of an affine obstacle under a scalar-parametrized affine
map has at most one point if at least one parameter avoids the obstacle. -/
theorem subsingleton_preimage_of_not_mem
    {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]
    (S : AffineSubspace k P) (f : k →ᵃ[k] P) {t₀ : k} (ht₀ : f t₀ ∉ S) :
    (f ⁻¹' (S : Set P)).Subsingleton := by
  let A := S.comap f
  have hA : A ≠ ⊤ := by
    intro he
    have hmem : t₀ ∈ A := he.symm ▸ AffineSubspace.mem_top k k t₀
    exact ht₀ hmem
  intro s hs t ht
  rcases eq_bot_or_eq_top A.direction with hd | hd
  · exact (direction_eq_bot_iff.mp hd) hs ht
  · exact (hA ((direction_eq_top_iff_of_nonempty ⟨s, hs⟩).mp hd)).elim

end AffineSubspace

namespace Mei.ExceptionalArrangement

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A line starting at a generic point meets a finite exceptional arrangement
at finitely many parameter values. No transversality or distinctness assumption
on its second endpoint is required. -/
theorem finite_nonGeneric_lineMap (E : ExceptionalArrangement V)
    {x : V} (hx : E.IsGeneric x) (y : V) :
    {t : ℝ | ¬ E.IsGeneric (AffineMap.lineMap x y t)}.Finite := by
  classical
  have hS (S : AffineSubspace ℝ V) (hS : S ∈ E.exceptions) :
      {t : ℝ | AffineMap.lineMap x y t ∈ S}.Subsingleton :=
    S.subsingleton_preimage_of_not_mem (AffineMap.lineMap x y)
      (t₀ := 0) (by simpa only [AffineMap.lineMap_apply_zero] using
        (isGeneric_iff.mp hx) S hS)
  have he : {t : ℝ | ¬ E.IsGeneric (AffineMap.lineMap x y t)} =
      ⋃ S ∈ E.exceptions, {t : ℝ | AffineMap.lineMap x y t ∈ S} := by
    ext t
    simp only [Set.mem_ofPred_eq, isGeneric_iff, not_forall, not_not,
      Set.mem_iUnion, exists_prop]
  rw [he]
  exact E.exceptions.finite_toSet.biUnion fun S hmem => (hS S hmem).finite

end Mei.ExceptionalArrangement
