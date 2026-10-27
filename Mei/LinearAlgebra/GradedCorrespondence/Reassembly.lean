/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedCorrespondence.Hom

/-!
# Reassembling homogeneous lifts and transfers

If every left degree of a graded correspondence is admissible, its chosen lifts
extend linearly to the whole left module. This gives a section of the left leg
and a propagation map to the right module. Its homogeneous output components
are the original transfers. Morphisms commute with these reassembled maps,
including morphisms whose degree maps identify different degrees.

This advances [ScatteringDiagrams §0.8, Morphisms and transfers]
(https://github.com/yuma-mizuno/TauCetiRoadmap/blob/mei/TauCetiRoadmap/ScatteringDiagrams/README.md#08-homogeneous-coefficient-correspondences).
It supplies finite-sum coefficient propagation for the weighted evaluations of §5.2;
it does not identify the two whole modules or assume inverse transfers.
The construction uses `DirectSum.toModule` and `DirectSum.decompose_lhom_ext`.
-/

public section

namespace Mei.GradedCorrespondence

variable {R B U V ι κ : Type*} [Semiring R]
  [AddCommMonoid B] [Module R B] [AddCommMonoid U] [Module R U]
  [AddCommMonoid V] [Module R V]
  {𝒰 : ι → Submodule R U} {𝒱 : κ → Submodule R V} {I : Set ι} {J : Set κ}
  [DecidableEq ι] [DirectSum.Decomposition 𝒰]

/-- Reassemble the chosen homogeneous lifts when every left degree is admissible. -/
noncomputable def liftLinearMap (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (hI : ∀ i, i ∈ I) : U →ₗ[R] B :=
  (DirectSum.toModule R ι B (fun i ↦ C.liftLeft ⟨i, hI i⟩)).comp
    (DirectSum.decomposeLinearEquiv 𝒰).toLinearMap

/-- Reassembly agrees with the chosen lift on each homogeneous piece. -/
@[simp]
theorem liftLinearMap_apply_coe (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (hI : ∀ i, i ∈ I) (i : ι) (a : 𝒰 i) :
    C.liftLinearMap hI a = C.liftLeft ⟨i, hI i⟩ a := by
  simp [liftLinearMap, DirectSum.decomposeLinearEquiv_apply_coe]

/-- The reassembled lift is a section of the left leg on the whole module. -/
@[simp]
theorem left_comp_liftLinearMap (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (hI : ∀ i, i ∈ I) : C.left.comp (C.liftLinearMap hI) = LinearMap.id := by
  apply DirectSum.decompose_lhom_ext 𝒰
  intro i
  ext a
  simp

/-- Propagate a whole coefficient by reassembling its chosen homogeneous lifts. -/
noncomputable def transferLinearMap (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (hI : ∀ i, i ∈ I) : U →ₗ[R] V :=
  C.right.comp (C.liftLinearMap hI)

/-- The output components of whole-coefficient propagation are the original transfers. -/
theorem component_transferLinearMap [DecidableEq κ] [DirectSum.Decomposition 𝒱]
    (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) (hI : ∀ i, i ∈ I)
    (i : ι) (a : 𝒰 i) (j : κ) :
    DirectSum.decompose 𝒱 (C.transferLinearMap hI a) j =
      C.transfer ⟨i, hI i⟩ j a := by
  simp [transferLinearMap]

/-- Each output component is the finite sum of the transfers of the actual nonzero
input components. No finiteness of the grading type or of degree-map fibers is needed. -/
theorem component_transferLinearMap_eq_sum
    [DecidableEq κ] [DirectSum.Decomposition 𝒱]
    [∀ i (a : 𝒰 i), Decidable (a ≠ 0)]
    (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) (hI : ∀ i, i ∈ I)
    (x : U) (j : κ) :
    DirectSum.decompose 𝒱 (C.transferLinearMap hI x) j =
      ∑ i ∈ (DirectSum.decompose 𝒰 x).support,
        C.transfer ⟨i, hI i⟩ j (DirectSum.decompose 𝒰 x i) := by
  let P : U →ₗ[R] 𝒱 j :=
    (DirectSum.component R κ (fun j ↦ 𝒱 j) j).comp
      ((DirectSum.decomposeLinearEquiv 𝒱).toLinearMap.comp (C.transferLinearMap hI))
  change P x = _
  calc
    P x = ∑ i ∈ (DirectSum.decompose 𝒰 x).support,
        P (DirectSum.decompose 𝒰 x i : U) := by
      rw [← map_sum, DirectSum.sum_support_decompose]
    _ = _ := Finset.sum_congr rfl fun i _ ↦
      C.component_transferLinearMap hI i _ j

namespace Hom

variable {B' U' V' ι' κ' : Type*}
  [AddCommMonoid B'] [Module R B'] [AddCommMonoid U'] [Module R U']
  [AddCommMonoid V'] [Module R V']
  {𝒰' : ι' → Submodule R U'} {𝒱' : κ' → Submodule R V'}
  {I' : Set ι'} {J' : Set κ'} [DecidableEq ι'] [DirectSum.Decomposition 𝒰']
  {C : GradedCorrespondence (B := B) 𝒰 𝒱 I J}
  {D : GradedCorrespondence (B := B') 𝒰' 𝒱' I' J'}
  {σ : ι → ι'} {τ : κ → κ'}

/-- A correspondence morphism preserves reassembled lifts, even when degrees merge. -/
theorem middle_comp_liftLinearMap (f : Hom C D σ τ)
    (hI : ∀ i, i ∈ I) (hI' : ∀ i, i ∈ I') :
    f.middle.comp (C.liftLinearMap hI) = (D.liftLinearMap hI').comp f.left := by
  apply DirectSum.decompose_lhom_ext 𝒰
  intro i
  ext a
  change f.middle (C.liftLinearMap hI a) = D.liftLinearMap hI' (f.left a)
  rw [liftLinearMap_apply_coe, f.middle_liftLeft]
  exact (D.liftLinearMap_apply_coe hI' (σ i) ⟨f.left a, f.left_mem i a a.property⟩).symm

/-- Whole-coefficient propagation commutes with correspondence morphisms without
injectivity assumptions on either degree map. -/
theorem right_comp_transferLinearMap (f : Hom C D σ τ)
    (hI : ∀ i, i ∈ I) (hI' : ∀ i, i ∈ I') :
    f.right.comp (C.transferLinearMap hI) = (D.transferLinearMap hI').comp f.left := by
  simp only [transferLinearMap, ← LinearMap.comp_assoc, f.right_comm]
  rw [LinearMap.comp_assoc, f.middle_comp_liftLinearMap hI hI', ← LinearMap.comp_assoc]

end Hom

end Mei.GradedCorrespondence
