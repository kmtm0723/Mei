/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted
public import TauCeti.Algebra.Module.GradedModule.Quotient

/-!
# Homogeneous pieces of finite shifted coefficient modules

The relative-degree filtration of a shifted module is homogeneous, so each
finite quotient inherits its internal grading. Its degree-`n` piece is the
image of the original relative piece; it vanishes above the cutoff. Retained
homogeneous coefficients embed faithfully, and quotient transitions preserve
the homogeneous pieces.

The construction uses `TauCeti.InternalGrading.quotient` for the existing
shifted filtration, keeping the quotient carrier used by filtered Lie actions.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {Γ : Type} {R M : Type*} [AddCommGroup Γ] [Ring R]
  [AddCommGroup M] [Module R M] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] (p : Γ)

private theorem shiftedFiltration_isHomogeneous (k : ℕ) :
    DirectSum.SetLike.IsHomogeneous (shiftedGrading ℳ d.monoid p)
      ((d.shiftedFiltration ℳ p).submodule (k + 1)) := by
  rw [shiftedFiltration_succ]
  exact d.degreeSubmodule_isHomogeneous _ k

/-- The internal relative grading of the existing order-`k` shifted module. -/
def shiftedQuotientGrading (k : ℕ) :
    TauCeti.InternalGrading R ((d.shiftedFiltration ℳ p).quotient k) Γ :=
  (TauCeti.InternalGrading.ofDecomposition (shiftedGrading ℳ d.monoid p)).quotient
    ((d.shiftedFiltration ℳ p).submodule (k + 1))
    (by simpa using d.shiftedFiltration_isHomogeneous ℳ p k)

/-- A finite relative piece is the quotient image of its original piece. -/
@[simp]
theorem shiftedQuotientGrading_piece (k : ℕ) (n : Γ) :
    (d.shiftedQuotientGrading ℳ p k).piece n =
      (shiftedGrading ℳ d.monoid p n).map
        ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ := by
  unfold shiftedQuotientGrading
  rw [TauCeti.InternalGrading.quotient_piece,
    TauCeti.InternalGrading.ofDecomposition_piece]
  rfl

/-- A finite homogeneous coefficient has a homogeneous representative. -/
theorem mem_shiftedQuotientGrading_iff {k : ℕ} {n : Γ}
    {x : (d.shiftedFiltration ℳ p).quotient k} :
    x ∈ (d.shiftedQuotientGrading ℳ p k).piece n ↔
      ∃ a ∈ shiftedGrading ℳ d.monoid p n, Submodule.Quotient.mk a = x := by
  rw [shiftedQuotientGrading_piece]
  exact Submodule.mem_map

/-- Relative homogeneous pieces strictly above the retained order vanish. -/
theorem shiftedQuotientGrading_eq_bot {k : ℕ} {n : Γ} (hn : (k : ℤ) < d.degree n) :
    (d.shiftedQuotientGrading ℳ p k).piece n = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (d.mem_shiftedQuotientGrading_iff ℳ p).mp hx
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, shiftedFiltration_succ]
  exact d.le_degreeSubmodule _ hn ha

/-- An allowed homogeneous coefficient survives exactly when it is nonzero,
provided its relative degree is retained. -/
theorem mk_shiftedInclusion_eq_zero_iff (n : d.monoid) (a : ℳ (p + n))
    {k : ℕ} (hn : d.degree n ≤ k) :
    (Submodule.Quotient.mk (shiftedInclusion ℳ d.monoid p n a) :
      (d.shiftedFiltration ℳ p).quotient k) = 0 ↔ a = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, shiftedInclusion_mem_shiftedFiltration_iff]
  constructor
  · rintro (ha | hd)
    · exact ha
    · omega
  · exact Or.inl

/-- Changing the cutoff preserves the ambient relative degree of every coefficient. -/
theorem transition_mem_shiftedQuotientGrading {k l : ℕ} (h : k ≤ l) {n : Γ}
    {x : (d.shiftedFiltration ℳ p).quotient l}
    (hx : x ∈ (d.shiftedQuotientGrading ℳ p l).piece n) :
    (d.shiftedFiltration ℳ p).transition h x ∈ (d.shiftedQuotientGrading ℳ p k).piece n := by
  obtain ⟨a, ha, rfl⟩ := (d.mem_shiftedQuotientGrading_iff ℳ p).mp hx
  exact (d.mem_shiftedQuotientGrading_iff ℳ p).mpr ⟨a, ha, by simp⟩

end Mei.PositiveDegrees
