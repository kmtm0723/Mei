/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Map

/-!
# Completion of filtration-preserving linear equivalences

A linear equivalence identifying every filtration term extends to a linear
equivalence of compatible-family completions. This reuses completion maps
in both directions; no separatedness or finite-dimensionality is needed.
-/

public section

namespace Mei.ModuleFiltration

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  (F : ModuleFiltration R M) (G : ModuleFiltration R N)
  (e : M ≃ₗ[R] N) (he : ∀ k, (G.submodule k).comap e.toLinearMap = F.submodule k)

include he

private theorem equiv_filtered (k : ℕ) :
    F.submodule (k + 1) ≤ (G.submodule (k + 1)).comap e.toLinearMap := by
  rw [he]

private theorem equiv_symm_filtered (k : ℕ) :
    G.submodule (k + 1) ≤ (F.submodule (k + 1)).comap e.symm.toLinearMap := by
  intro y hy
  rw [← he]
  simpa only [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hy

/-- Exact preservation of filtration terms also holds for the inverse equivalence. -/
theorem comap_submodule_equiv_symm (k : ℕ) :
    (F.submodule k).comap e.symm.toLinearMap = G.submodule k := by
  ext y
  rw [Submodule.mem_comap, ← he k]
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- A filtration-preserving linear equivalence extends to completed modules. -/
def completionEquiv : F.completion ≃ₗ[R] G.completion where
  __ := F.completionMap G e.toLinearMap id monotone_id (F.equiv_filtered G e he)
  invFun := G.completionMap F e.symm.toLinearMap id monotone_id
    (F.equiv_symm_filtered G e he)
  left_inv x := by
    have h := F.completionMap_comp G e.toLinearMap id monotone_id
      (F.equiv_filtered G e he) F e.symm.toLinearMap id monotone_id
      (F.equiv_symm_filtered G e he)
    simp only [e.symm_comp, Function.id_comp, completionMap_id] at h
    exact (LinearMap.congr_fun h x).symm
  right_inv x := by
    have h := G.completionMap_comp F e.symm.toLinearMap id monotone_id
      (F.equiv_symm_filtered G e he) G e.toLinearMap id monotone_id
      (F.equiv_filtered G e he)
    simp only [e.comp_symm, Function.id_comp, completionMap_id] at h
    exact (LinearMap.congr_fun h x).symm

/-- The completed equivalence sends original elements to their original images. -/
@[simp]
theorem completionEquiv_of (x : M) :
    F.completionEquiv G e he (F.of x) = G.of (e x) :=
  F.completionMap_of G e.toLinearMap id monotone_id (F.equiv_filtered G e he) x

/-- Projection computes the completed equivalence with the induced finite map. -/
@[simp]
theorem projection_completionEquiv (k : ℕ) (x : F.completion) :
    G.projection k (F.completionEquiv G e he x) =
      (F.submodule (k + 1)).mapQ (G.submodule (k + 1)) e.toLinearMap
        (by rw [he]) (F.projection k x) :=
  F.projection_completionMap G e.toLinearMap id monotone_id (F.equiv_filtered G e he) k x

/-- The inverse completed equivalence is the completion of the inverse equivalence. -/
theorem completionEquiv_symm :
    (F.completionEquiv G e he).symm =
      G.completionEquiv F e.symm (F.comap_submodule_equiv_symm G e he) := by
  ext x
  rfl

/-- The inverse completed equivalence computes on canonical images. -/
@[simp]
theorem completionEquiv_symm_of (y : N) :
    (F.completionEquiv G e he).symm (G.of y) = F.of (e.symm y) := by
  rw [completionEquiv_symm, completionEquiv_of]

/-- Projection computes the inverse completed equivalence on arbitrary elements. -/
@[simp]
theorem projection_completionEquiv_symm (k : ℕ) (y : G.completion) :
    F.projection k ((F.completionEquiv G e he).symm y) =
      (G.submodule (k + 1)).mapQ (F.submodule (k + 1)) e.symm.toLinearMap
        (by rw [F.comap_submodule_equiv_symm G e he]) (G.projection k y) := by
  rw [completionEquiv_symm, projection_completionEquiv]

/-- Completion preserves the exact identification of every filtration term. -/
@[simp]
theorem completionEquiv_mem_completedFiltration_iff (k : ℕ) (x : F.completion) :
    F.completionEquiv G e he x ∈ G.completedFiltration.submodule k ↔
      x ∈ F.completedFiltration.submodule k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [G.completedFiltration_succ, F.completedFiltration_succ]
    simp only [LinearMap.mem_ker, projection_completionEquiv]
    obtain ⟨a, ha⟩ := (F.submodule (k + 1)).mkQ_surjective (F.projection k x)
    rw [← ha, Submodule.mkQ_apply, Submodule.mapQ_apply]
    simp only [Submodule.Quotient.mk_eq_zero, ← Submodule.mem_comap, he]

end Mei.ModuleFiltration
