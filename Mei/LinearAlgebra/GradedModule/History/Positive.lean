/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Basic
public import Mei.LinearAlgebra.GradedModule.Positive

/-!
# Positive homogeneous propagation histories

Choose an additive submonoid of positive coefficients for each homogeneous degree.
If each selected component map preserves these monoids on its homogeneous
input degree, every segment of a homogeneous history is positive.
Mixed-degree inputs with positive components also have positive history outputs
when each selected map preserves positivity along the recorded degrees for every
possible initial degree. In particular each
homogeneous component of its final decoration is positive. No order on the
coefficient semiring, additive inverses, or basis of the homogeneous pieces is
required.

The history and segment equations are those of `Mei.homogeneousHistoryStage`.
For whole-component propagation in broken lines, see Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Definition 3.1 and Theorem 1.13
(arXiv:1411.1394v2).
-/

public noncomputable section

namespace Mei

variable {R M Γ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (Pos : Γ → AddSubmonoid M)

/-- Positive propagation along the selected degrees makes every segment decoration positive
in its recorded degree, including the original incoming segment. The monoid
`Pos p` is tested only on homogeneous elements of degree `p`. -/
theorem homogeneousHistoryStage_mem_addSubmonoid {n : ℕ}
    (T : Fin n → Module.End R M)
    (p : Fin n → Γ) {p₀ : Γ}
    (hT : ∀ j x, x ∈ ℳ (Fin.snoc (α := fun _ => Γ) p p₀ j.succ) →
      x ∈ Pos (Fin.snoc (α := fun _ => Γ) p p₀ j.succ) →
        (DirectSum.decompose ℳ (T j x) (p j) : M) ∈ Pos (p j))
    (a : ℳ p₀) (ha : (a : M) ∈ Pos p₀)
    (j : Fin (n + 1)) :
    homogeneousHistoryStage ℳ T p j a ∈ Pos (Fin.snoc (α := fun _ => Γ) p p₀ j) := by
  have hstage (j : Fin (n + 1)) :
      homogeneousHistoryStage ℳ T p j a ∈ ℳ (Fin.snoc (α := fun _ => Γ) p p₀ j) ∧
      homogeneousHistoryStage ℳ T p j a ∈ Pos (Fin.snoc (α := fun _ => Γ) p p₀ j) := by
    induction j using Fin.reverseInduction with
    | last => simpa only [homogeneousHistoryStage_last, LinearMap.id_apply, Fin.snoc_last]
        using And.intro a.property ha
    | cast j ih =>
      rw [homogeneousHistoryStage_castSucc_apply, Fin.snoc_castSucc]
      exact ⟨(DirectSum.decompose ℳ _ _).property, hT j _ ih.1 ih.2⟩
  exact (hstage j).2

/-- Every component of a final whole decoration is positive: in its selected
output degree it is the positive decoration, and in other degrees it is zero.
This also covers the empty history. -/
theorem homogeneousHistory_component_mem_addSubmonoid {n : ℕ}
    (T : Fin n → Module.End R M)
    (p : Fin n → Γ) {p₀ : Γ}
    (hT : ∀ j x, x ∈ ℳ (Fin.snoc (α := fun _ => Γ) p p₀ j.succ) →
      x ∈ Pos (Fin.snoc (α := fun _ => Γ) p p₀ j.succ) →
        (DirectSum.decompose ℳ (T j x) (p j) : M) ∈ Pos (p j))
    (a : ℳ p₀) (ha : (a : M) ∈ Pos p₀) (q : Γ) :
    (DirectSum.decompose ℳ (homogeneousHistory ℳ T p a) q : M) ∈ Pos q := by
  have hp := homogeneousHistoryStage_mem_addSubmonoid ℳ Pos T p hT a ha 0
  rw [homogeneousHistoryStage_zero] at hp
  have hm : homogeneousHistory ℳ T p a ∈ ℳ (Fin.snoc (α := fun _ => Γ) p p₀ 0) := by
    cases n with
    | zero => simpa only [homogeneousHistory_zero, LinearMap.id_apply, Fin.snoc_zero]
        using a.property
    | succ n => simpa only [Fin.snoc_apply_zero] using homogeneousHistory_mem ℳ T p a
  by_cases hq : Fin.snoc (α := fun _ => Γ) p p₀ 0 = q
  · subst q
    rwa [DirectSum.decompose_of_mem_same ℳ hm]
  · rw [DirectSum.decompose_of_mem_ne ℳ hm hq]
    exact (Pos q).zero_mem

/-- Componentwise positive inputs, possibly in several degrees, have positive
history outputs when the selected maps preserve positivity along the recorded
degrees for every possible initial degree. -/
theorem homogeneousHistory_component_mem_addSubmonoid_of_components {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → Γ)
    (hT : ∀ i j x, x ∈ ℳ (Fin.snoc (α := fun _ => Γ) p i j.succ) →
      x ∈ Pos (Fin.snoc (α := fun _ => Γ) p i j.succ) →
        (DirectSum.decompose ℳ (T j x) (p j) : M) ∈ Pos (p j))
    (a : M) (ha : ∀ i, (DirectSum.decompose ℳ a i : M) ∈ Pos i) (q : Γ) :
    (DirectSum.decompose ℳ (homogeneousHistory ℳ T p a) q : M) ∈ Pos q := by
  exact (mem_componentwisePositive ℳ Pos _).mp
    (map_mem_componentwisePositive ℳ Pos (homogeneousHistory ℳ T p)
      (fun i q x hx hp => homogeneousHistory_component_mem_addSubmonoid ℳ Pos T p
        (hT i) ⟨x, hx⟩ hp q)
      ((mem_componentwisePositive ℳ Pos a).mpr ha)) q

end Mei
