/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.Algebra.Lie.Filtered.BCH
public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient
public import Mei.LinearAlgebra.GradedModule.History.Expansion

/-!
# Finite component-map identities for BCH histories

At a fixed cutoff, all shifted coefficient pieces outside the finite positive
degree cutoff vanish. Expanding a word of BCH actions over histories in this
cutoff therefore gives an identity of linear maps, simultaneously for every
incoming coefficient. Equal BCH words, including words of different lengths,
have equal sums of component maps in each retained outgoing degree. Two blocks
also admit a nested finite expansion before any output linear map.

These are the coefficient identities needed when comparing local histories
through a consistent wall configuration. They do not assert that every algebraic
history admits a geometric broken-line realization. Whole components and shifts
of zero spatial direction are retained, and no freeness or finite generation of
homogeneous pieces is required.

The expansion combines `sum_homogeneousHistory_eq_prod`,
`PositiveDegrees.mem_cutoff_of_mem_shiftedQuotientGrading_ne_zero`, and the monoid
homomorphism `ModuleFiltration.truncatedBCHAction`. The local component-map
interpretation follows Gross–Hacking–Siebert, *Theta functions on varieties with
effective anti-canonical class*, §3.2 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.PositiveDegrees

variable {Γ : Type} {R L M : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] (p : Γ)

local notation "F" => d.shiftedLieFiltration ℒ ℳ p
local notation "G(" k ")" => TauCeti.InternalGrading.piece (d.shiftedQuotientGrading ℳ p k)

/-- The action of a BCH word is the finite sum of its whole-component history
maps over the positive degree cutoff. This is an equality of endomorphisms,
with a finite index set independent of the incoming coefficient. -/
theorem sum_homogeneousHistory_truncatedBCHAction (k : ℕ) {n : ℕ}
    (g : Fin n → d.truncatedGroup ℒ k) :
    ∑ r : Fin n → (d.finite_cutoff k).toFinset,
      homogeneousHistory G(k)
        (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap)
        (fun j => (r j).val) =
      ((F).truncatedBCHAction d ℒ k (List.ofFn g).prod).toLinearMap := by
  classical
  rw [sum_homogeneousHistory_eq_prod G(k) _
    (d.shiftedQuotientGrading_piece_eq_bot ℳ p)]
  let act := (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
    (R := R) (M := (F).quotient k)).comp
    ((F).truncatedBCHAction d ℒ k)
  simpa only [List.map_ofFn, Function.comp_def, act, MonoidHom.comp_apply,
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] using
    (map_list_prod act (List.ofFn g)).symm

/-- BCH factorizations with the same product have identical finite sums of
component maps in any retained outgoing degree. Precomposition allows an
arbitrary incoming parameter module, so the identity holds linearly for all
inputs at once. The two words need not have the same length. -/
theorem sum_component_homogeneousHistory_eq_of_prod_eq
    {E : Type*} [AddCommMonoid E] [Module R E]
    (k : ℕ) {n m : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (g' : Fin m → d.truncatedGroup ℒ k)
    (hg : (List.ofFn g).prod = (List.ofFn g').prod)
    (q : Γ) (hq : d.degree (q - p) ≤ k) (a : E →ₗ[R] (F).quotient k) :
    ∑ r : Fin n → (d.finite_cutoff k).toFinset,
      (d.shiftedQuotientComponent ℳ p q k hq).comp
        ((homogeneousHistory G(k)
          (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap)
          (fun j => (r j).val)).comp a) =
    ∑ r : Fin m → (d.finite_cutoff k).toFinset,
      (d.shiftedQuotientComponent ℳ p q k hq).comp
        ((homogeneousHistory G(k)
          (fun j => ((F).truncatedBCHAction d ℒ k (g' j)).toLinearMap)
          (fun j => (r j).val)).comp a) := by
  classical
  ext x
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rw [← map_sum, ← LinearMap.sum_apply,
    d.sum_homogeneousHistory_truncatedBCHAction ℒ ℳ p k g,
    ← map_sum, ← LinearMap.sum_apply,
    d.sum_homogeneousHistory_truncatedBCHAction ℒ ℳ p k g', hg]

/-- The nested finite sums of two BCH blocks recover their composite action in
the whole quotient, followed by any output linear map. The right block acts first,
and both finite index sets are independent of the incoming input. -/
theorem sum_comp_homogeneousHistory_append_truncatedBCHAction
    {E O : Type*} [AddCommMonoid E] [Module R E] [AddCommMonoid O] [Module R O]
    (k : ℕ) {n m : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (u : Fin m → d.truncatedGroup ℒ k)
    (a : E →ₗ[R] (F).quotient k) (b : (F).quotient k →ₗ[R] O) :
    (∑ r ∈ Fintype.piFinset (fun _ : Fin m => (d.finite_cutoff k).toFinset),
      ∑ s ∈ Fintype.piFinset (fun _ : Fin n => (d.finite_cutoff k).toFinset),
        b.comp
          ((homogeneousHistory G(k)
            (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) s).comp
            ((homogeneousHistory G(k)
              (fun j => ((F).truncatedBCHAction d ℒ k (u j)).toLinearMap) r).comp a))) =
      b.comp
        (((F).truncatedBCHAction d ℒ k (List.ofFn g).prod).toLinearMap.comp
          (((F).truncatedBCHAction d ℒ k (List.ofFn u).prod).toLinearMap.comp a)) := by
  classical
  let T j := ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap
  let U j := ((F).truncatedBCHAction d ℒ k (u j)).toLinearMap
  let S := (d.finite_cutoff k).toFinset
  have hS := d.shiftedQuotientGrading_piece_eq_bot ℳ p (k := k)
  have hz {l : ℕ} (v : Fin l → Module.End R ((F).quotient k))
      (b : E →ₗ[R] (F).quotient k) (r : Fin l → Γ)
      (hr : r ∉ Fintype.piFinset (fun _ => S)) :
      (homogeneousHistory G(k) v r).comp b = 0 := by
    rw [homogeneousHistory_eq_zero_of_notMem_piFinset G(k) S hS v r hr,
      LinearMap.zero_comp]
  have hT : (List.ofFn T).prod =
      ((F).truncatedBCHAction d ℒ k (List.ofFn g).prod).toLinearMap :=
    (sum_homogeneousHistory_eq_prod G(k) S hS T).symm.trans
      (d.sum_homogeneousHistory_truncatedBCHAction ℒ ℳ p k g)
  have hU : (List.ofFn U).prod =
      ((F).truncatedBCHAction d ℒ k (List.ofFn u).prod).toLinearMap :=
    (sum_homogeneousHistory_eq_prod G(k) S hS U).symm.trans
      (d.sum_homogeneousHistory_truncatedBCHAction ℒ ℳ p k u)
  change (∑ r ∈ Fintype.piFinset (fun _ : Fin m => S),
    ∑ s ∈ Fintype.piFinset (fun _ : Fin n => S),
      b.comp ((homogeneousHistory G(k) T s).comp
        ((homogeneousHistory G(k) U r).comp a))) = _
  simp_rw [sum_comp_homogeneousHistory_comp_eq G(k) T _ b _ (hz T _)]
  simpa only [LinearMap.comp_assoc, hT, hU] using
    sum_comp_homogeneousHistory_comp_eq G(k) U a
      (b.comp (List.ofFn T).prod) _ (hz U a)

end Mei.PositiveDegrees
