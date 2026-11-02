/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.Resolution
public import Mei.LinearAlgebra.GradedModule.History.UniformConcatenation

/-!
# Uniform finite concatenation of BCH coefficient histories

Two finite BCH blocks have a nested component-history expansion on the whole
incoming module. Both branch sets are fixed by the cutoff, independently of the
input. Every retained outgoing projection commutes with this expansion. The
right block acts first; intermediate decorations and zero terms are retained.

The proof joins the uniform history supports, applies their selected-sum
reindexing, and uses the existing finite BCH expansion for each block. This is
coefficient concatenation; it does not assert geometric realizations of histories.
-/

public noncomputable section

namespace Mei.PositiveDegrees

variable {Γ : Type} {R L M E : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommMonoid E] [Module R E] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] (p : Γ)

local notation "F" => d.shiftedLieFiltration ℒ ℳ p
local notation "G(" k ")" => TauCeti.InternalGrading.piece (d.shiftedQuotientGrading ℳ p k)

/-- The nested finite sums of two BCH blocks recover their composite action in
any retained outgoing degree, simultaneously for every incoming input. -/
theorem sum_component_homogeneousHistory_append_truncatedBCHAction
    (k : ℕ) {n m : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (u : Fin m → d.truncatedGroup ℒ k) (q : Γ) (hq : d.degree (q - p) ≤ k)
    (a : E →ₗ[R] (F).quotient k) :
    (∑ r ∈ Fintype.piFinset (fun _ : Fin m => (d.finite_cutoff k).toFinset),
      ∑ s ∈ Fintype.piFinset (fun _ : Fin n => (d.finite_cutoff k).toFinset),
        (d.shiftedQuotientComponent ℳ p q k hq).comp
          ((homogeneousHistory G(k)
            (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) s).comp
            ((homogeneousHistory G(k)
              (fun j => ((F).truncatedBCHAction d ℒ k (u j)).toLinearMap) r).comp a))) =
      (d.shiftedQuotientComponent ℳ p q k hq).comp
        (((F).truncatedBCHAction d ℒ k (List.ofFn g).prod).toLinearMap.comp
          (((F).truncatedBCHAction d ℒ k (List.ofFn u).prod).toLinearMap.comp a)) := by
  classical
  let T j := ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap
  let U j := ((F).truncatedBCHAction d ℒ k (u j)).toLinearMap
  let S := (d.finite_cutoff k).toFinset
  have hS (r : Γ) (hr : r ∉ S) : G(k) r = ⊥ :=
    d.shiftedQuotientGrading_piece_eq_bot ℳ p
      (fun hmem => hr ((d.finite_cutoff k).mem_toFinset.mpr hmem))
  have hz {l : ℕ} (v : Fin l → Module.End R ((F).quotient k))
      (b : E →ₗ[R] (F).quotient k) (r : Fin l → Γ)
      (hr : r ∉ Fintype.piFinset (fun _ => S)) :
      (homogeneousHistory G(k) v r).comp b = 0 := by
    rw [homogeneousHistory_eq_zero_of_notMem_piFinset G(k) S hS v r hr,
      LinearMap.zero_comp]
  have he := sum_homogeneousHistory_comp_appendHistorySupport G(k) T U a
    (Fintype.piFinset (fun _ : Fin m => S))
    (fun _ => Fintype.piFinset (fun _ : Fin n => S)) (hz U a)
    (fun r _ => hz T ((homogeneousHistory G(k) U r).comp a))
  have hreindex := sum_ite_homogeneousHistory_comp_appendHistorySupport G(k) T U a
    (Fintype.piFinset (fun _ : Fin m => S))
    (fun _ => Fintype.piFinset (fun _ : Fin n => S)) (fun _ => True)
  simp only [ite_true] at hreindex
  rw [hreindex] at he
  have hT : (List.ofFn T).prod =
      ((F).truncatedBCHAction d ℒ k (List.ofFn g).prod).toLinearMap :=
    (sum_homogeneousHistory_eq_prod G(k) S hS T).symm.trans
      (d.sum_homogeneousHistory_truncatedBCHAction ℒ ℳ p k g)
  have hU : (List.ofFn U).prod =
      ((F).truncatedBCHAction d ℒ k (List.ofFn u).prod).toLinearMap :=
    (sum_homogeneousHistory_eq_prod G(k) S hS U).symm.trans
      (d.sum_homogeneousHistory_truncatedBCHAction ℒ ℳ p k u)
  rw [hT, hU] at he
  apply LinearMap.ext
  intro x
  have hx := congrArg (d.shiftedQuotientComponent ℳ p q k hq) (LinearMap.congr_fun he x)
  simpa only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum] using hx

end Mei.PositiveDegrees
