/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.Exp
public import Mei.RingTheory.FilteredAlgebra.Map

/-!
# Naturality of completed exponentials and logarithms

A filtered ring map preserving the first ideal induces a map of exponential
coordinates. The cutoff modulus may change orders. Preservation of the first
ideal is a separate hypothesis: continuity alone need not preserve that ideal.

We use the existing completion map and naturality of finite nilpotent
exponentials and logarithms. All statements allow noncommutative rational
algebras and noninjective maps.
-/

public section

namespace Mei.AlgFiltration

variable {A B : Type*} [Ring A] [Ring B]
  (F : AlgFiltration A) (G : AlgFiltration B)
  (f : A →+* B) (l : ℕ → ℕ) (hl : Monotone l)
  (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap f)
  (h₁ : F.ideal 1 ≤ (G.ideal 1).comap f)

include h₁ in
/-- A map preserving the first original ideal preserves the first completed ideal,
even when its chosen cutoff modulus does not send zero to zero. -/
theorem mapCompletion_mem_first {x : F.completion} (hx : x ∈ F.completionIdeal 1) :
    F.mapCompletion G f l hl hf x ∈ G.completionIdeal 1 := by
  have hx₀ : F.projection 0 x = 0 := by
    simpa only [completionIdeal_succ, RingHom.mem_ker] using hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection (l 0) x)
  have ha₀ : Ideal.Quotient.mk (F.ideal 1) a = 0 := by
    have he := F.factor_projection (Nat.zero_le (l 0)) x
    rw [← ha, Ideal.Quotient.factor_mk, hx₀] at he
    exact he
  have hfa := h₁ ((Ideal.Quotient.eq_zero_iff_mem).mp ha₀)
  rw [completionIdeal_succ, RingHom.mem_ker,
    projection_mapCompletion, ← ha, Ideal.quotientMap_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hfa

variable [Algebra ℚ A] [Algebra ℚ B]

/-- Completed exponentiation commutes with filtered ring maps preserving the first ideal. -/
@[simp]
theorem mapCompletion_completedExp (x : F.completionIdeal 1) :
    F.mapCompletion G f l hl hf (F.completedExp x) =
      G.completedExp ⟨F.mapCompletion G f l hl hf x,
        F.mapCompletion_mem_first G f l hl hf h₁ x.property⟩ := by
  apply G.completion_ext
  intro k
  rw [projection_mapCompletion, projection_completedExp, projection_completedExp,
    projection_mapCompletion]
  exact (F.isNilpotent_projection x.property (l k)).map_exp _

/-- Completed logarithms commute with the same maps on elements congruent to one. -/
@[simp]
theorem mapCompletion_completedLog
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.mapCompletion G f l hl hf (F.completedLog u) =
      G.completedLog ⟨F.mapCompletion G f l hl hf u, by
        simpa only [map_sub, map_one] using
          F.mapCompletion_mem_first G f l hl hf h₁ u.property⟩ := by
  apply G.completion_ext
  intro k
  rw [projection_mapCompletion, projection_completedLog, projection_completedLog,
    projection_mapCompletion]
  have hu : IsNilpotent (F.projection (l k) u - 1) := by
    simpa only [map_sub, map_one] using F.isNilpotent_projection u.property (l k)
  exact hu.map_log _

end Mei.AlgFiltration
