/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Map
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Algebra automorphisms from completed scalar series

A unit power series evaluated at a positive completed element acts by inner
algebra automorphisms. This action preserves every completed ideal, and the
inverse series supplies the inverse automorphism. Simultaneous scalar and
coefficient maps intertwine these actions on arbitrary completed coefficients.

The construction uses the existing conjugation action of units and completed
power series evaluation; the coefficient algebra need not be commutative.
-/

public section

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (F : AlgFiltration A)

/-- Evaluated unit series act on the completion by algebra automorphisms. -/
noncomputable def completedSeriesAction (x : F.completionIdeal 1) :
    (PowerSeries R)ˣ →* (F.completion ≃ₐ[R] F.completion) :=
  (MulSemiringAction.toAlgAut (ConjAct F.completionˣ) R F.completion).comp
    (ConjAct.toConjAct.toMonoidHom.comp (Units.map (F.completedAeval x).toMonoidHom))

/-- The series action is conjugation by its completed evaluation. -/
theorem completedSeriesAction_apply (x : F.completionIdeal 1) (H : (PowerSeries R)ˣ)
    (a : F.completion) :
    F.completedSeriesAction x H a =
      F.completedAeval x (H : PowerSeries R) * a *
        F.completedAeval x (↑(H⁻¹) : PowerSeries R) := by
  -- This apply lemma exposes the defining ConjAct action and Units.map value;
  -- both evaluate pointwise, so the displayed product is definitionally equal.
  rfl

/-- Reversing the unit series gives the inverse algebra automorphism. -/
@[simp]
theorem completedSeriesAction_inv (x : F.completionIdeal 1) (H : (PowerSeries R)ˣ) :
    F.completedSeriesAction x (H⁻¹) = (F.completedSeriesAction x H).symm :=
  map_inv (F.completedSeriesAction x) H

/-- Conjugation by an evaluated series preserves every completed ideal. -/
theorem completedSeriesAction_mem (x : F.completionIdeal 1) (H : (PowerSeries R)ˣ)
    (k : ℕ) {a : F.completion} (ha : a ∈ F.completionIdeal k) :
    F.completedSeriesAction x H a ∈ F.completionIdeal k := by
  rw [completedSeriesAction_apply]
  exact (F.completionIdeal k).mul_mem_right _ ((F.completionIdeal k).mul_mem_left _ ha)

/-- A series action preserves the exact filtration membership of every coefficient. -/
theorem completedSeriesAction_mem_iff (x : F.completionIdeal 1) (H : (PowerSeries R)ˣ)
    (k : ℕ) (a : F.completion) :
    F.completedSeriesAction x H a ∈ F.completionIdeal k ↔ a ∈ F.completionIdeal k := by
  constructor
  · intro ha
    have he := F.completedSeriesAction_mem x (H⁻¹) k ha
    simpa only [completedSeriesAction_inv, AlgEquiv.symm_apply_apply] using he
  · exact F.completedSeriesAction_mem x H k

variable {S B : Type*} [CommRing S] [Ring B] [Algebra S B]
  (G : AlgFiltration B) (φ : R →+* S) (ψ : A →+* B)
  (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap S B (φ r))
  (l : ℕ → ℕ) (hl : Monotone l)
  (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap ψ)
  (h₁ : F.ideal 1 ≤ (G.ideal 1).comap ψ)

include hψ in
/-- Simultaneous scalar and coefficient transport intertwines completed series actions. -/
theorem mapCompletion_completedSeriesAction (x : F.completionIdeal 1)
    (H : (PowerSeries R)ˣ) (a : F.completion) :
    F.mapCompletion G ψ l hl hf (F.completedSeriesAction x H a) =
      G.completedSeriesAction
        ⟨F.mapCompletion G ψ l hl hf x,
          F.mapCompletion_mem_first G ψ l hl hf h₁ x.property⟩
        (Units.map (PowerSeries.map φ).toMonoidHom H) (F.mapCompletion G ψ l hl hf a) := by
  simp only [completedSeriesAction_apply, map_mul, Units.coe_map, Units.coe_map_inv,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  rw [F.mapCompletion_completedAeval G φ ψ hψ l hl hf h₁,
    F.mapCompletion_completedAeval G φ ψ hψ l hl hf h₁]

end Mei.AlgFiltration
