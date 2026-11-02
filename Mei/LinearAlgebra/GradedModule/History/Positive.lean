/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Basic

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
  classical
  rw [← DirectSum.sum_support_decompose ℳ a]
  simp only [map_sum, DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  apply (Pos q).sum_mem
  intro i _
  exact homogeneousHistory_component_mem_addSubmonoid ℳ Pos T p
    (hT i) (DirectSum.decompose ℳ a i) (ha i) q

/-- Elements whose homogeneous components belong to the chosen positive monoids. -/
def componentwisePositive : AddSubmonoid M where
  carrier := {x | ∀ q, (DirectSum.decompose ℳ x q : M) ∈ Pos q}
  zero_mem' := by
    intro q
    simpa only [DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
      using (Pos q).zero_mem
  add_mem' := by
    intro x y hx hy q
    simpa only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      using (Pos q).add_mem (hx q) (hy q)

@[simp]
theorem mem_componentwisePositive (x : M) :
    x ∈ componentwisePositive ℳ Pos ↔
      ∀ q, (DirectSum.decompose ℳ x q : M) ∈ Pos q := Iff.rfl

/-- Homogeneous componentwise positivity implies preservation of the whole positive monoid. -/
theorem map_mem_componentwisePositive (U : Module.End R M)
    (hU : ∀ i q x, x ∈ ℳ i → x ∈ Pos i →
      (DirectSum.decompose ℳ (U x) q : M) ∈ Pos q)
    {a : M} (ha : a ∈ componentwisePositive ℳ Pos) :
    U a ∈ componentwisePositive ℳ Pos := by
  classical
  rw [mem_componentwisePositive] at ha ⊢
  intro q
  rw [← DirectSum.sum_support_decompose ℳ a]
  simp only [map_sum, DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  exact (Pos q).sum_mem (fun i _ => hU i q _ (DirectSum.decompose ℳ a i).property (ha i))

end Mei
