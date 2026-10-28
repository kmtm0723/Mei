/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Completion
public import Mei.RingTheory.FilteredAlgebra.Algebra

/-!
# The underlying module filtration of a filtered algebra

Restricting scalars in the ideals of an algebra filtration gives a module filtration over
the coefficient semiring. This allows results on filtered modules to apply to coefficient
algebras without losing their original ideal filtration. In particular, the quotient
representation of a filtration-raising Lie action can be used on the original quotient rings.

The underlying module completion is canonically linearly equivalent to the algebra
completion. The equivalence identifies projections, original elements, and every
completed filtration term, without a separatedness hypothesis.
-/

public section

namespace Mei.AlgFiltration

variable (R : Type*) {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  (F : AlgFiltration A)

/-- The ideal filtration viewed as submodules over the coefficient semiring. -/
abbrev toModuleFiltration : ModuleFiltration R A where
  submodule k := (F.ideal k).restrictScalars R
  antitone := fun _ _ h => Submodule.restrictScalars_mono R (F.antitone h)
  zero_eq_top := by simp

/-- Each module filtration term is the scalar restriction of the original ideal. -/
@[simp]
theorem toModuleFiltration_submodule (k : ℕ) :
    (F.toModuleFiltration R).submodule k = (F.ideal k).restrictScalars R := (rfl)

end Mei.AlgFiltration

noncomputable section

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (F : AlgFiltration A)

/-- Scalar restriction of finite quotients commutes with every filtration transition. -/
@[simp]
theorem quotientScalarEquiv_transition {k l : ℕ} (h : k ≤ l)
    (a : (F.toModuleFiltration R).quotient l) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
        (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (l + 1)) a) =
      Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
        ((F.toModuleFiltration R).transition h a) := by
  obtain ⟨a, rfl⟩ := ((F.toModuleFiltration R).submodule (l + 1)).mkQ_surjective a
  simp

private def moduleCompletionToAlgebra : (F.toModuleFiltration R).completion →ₗ[R]
    F.completion where
  toFun x := ⟨fun k => Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k.unop + 1))
    ((F.toModuleFiltration R).projection k.unop x),
    (F.mem_completion_iff _).mpr (by
      intro k l h
      rw [F.quotientScalarEquiv_transition h,
        (F.toModuleFiltration R).transition_projection h x])⟩
  map_add' x y := by
    apply F.completion_ext
    intro k
    simp only [map_add, projection_apply]
  map_smul' r x := by
    apply F.completion_ext
    intro k
    have hs (z : F.completion) : F.projection k (r • z) = r • F.projection k z := by
      simpa only [projectionₐ_apply] using map_smul (F.projectionₐ (R := R) k) r z
    rw [RingHom.id_apply, hs]
    simp only [projection_apply]
    exact map_smul
      ((Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).toLinearMap.comp
        ((F.toModuleFiltration R).projection k)) r x

private theorem projection_moduleCompletionToAlgebra (k : ℕ)
    (x : (F.toModuleFiltration R).completion) :
    F.projection k (F.moduleCompletionToAlgebra x) =
      Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
        ((F.toModuleFiltration R).projection k x) := by
  rw [projection_apply]
  rfl

/-- The module and algebra completions of an ideal filtration are linearly equivalent. -/
def moduleCompletionEquiv : (F.toModuleFiltration R).completion ≃ₗ[R] F.completion where
  __ := F.moduleCompletionToAlgebra
  invFun := (F.toModuleFiltration R).lift
    (fun k => (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).symm.toLinearMap.comp
      (F.projectionₐ k).toLinearMap) (by
        intro k l h
        ext x
        apply (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).injective
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
          projectionₐ_apply, ← quotientScalarEquiv_transition, LinearEquiv.apply_symm_apply]
        exact F.factor_projection h x)
  left_inv x := by
    apply (F.toModuleFiltration R).completion_ext
    intro k
    simp only [LinearMap.toFun_eq_coe, ModuleFiltration.projection_lift, LinearMap.comp_apply,
      LinearEquiv.coe_coe,
      AlgHom.toLinearMap_apply, projectionₐ_apply, projection_moduleCompletionToAlgebra,
      LinearEquiv.symm_apply_apply]
  right_inv x := by
    apply F.completion_ext
    intro k
    simp only [LinearMap.toFun_eq_coe, projection_moduleCompletionToAlgebra,
      ModuleFiltration.projection_lift,
      LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, projectionₐ_apply,
      LinearEquiv.apply_symm_apply]

/-- The comparison uses the scalar-restriction equivalence at every finite order. -/
@[simp]
theorem projection_moduleCompletionEquiv (k : ℕ)
    (x : (F.toModuleFiltration R).completion) :
    F.projection k (F.moduleCompletionEquiv x) =
      Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
        ((F.toModuleFiltration R).projection k x) :=
  F.projection_moduleCompletionToAlgebra k x

/-- The inverse comparison uses the inverse scalar-restriction equivalence. -/
@[simp]
theorem projection_moduleCompletionEquiv_symm (k : ℕ) (x : F.completion) :
    (F.toModuleFiltration R).projection k ((F.moduleCompletionEquiv (R := R)).symm x) =
      (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).symm
        (F.projection k x) := by
  apply (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).injective
  rw [← F.projection_moduleCompletionEquiv, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- The comparison sends original elements to their canonical algebra completion images. -/
@[simp]
theorem moduleCompletionEquiv_of (x : A) :
    F.moduleCompletionEquiv ((F.toModuleFiltration R).of x) = F.toCompletion x := by
  apply F.completion_ext
  intro k
  simp

/-- Every completed module filtration term corresponds exactly to the completion ideal. -/
@[simp]
theorem moduleCompletionEquiv_mem_completionIdeal_iff (k : ℕ)
    (x : (F.toModuleFiltration R).completion) :
    F.moduleCompletionEquiv x ∈ F.completionIdeal k ↔
      x ∈ (F.toModuleFiltration R).completedFiltration.submodule k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [F.completionIdeal_succ, (F.toModuleFiltration R).completedFiltration_succ]
    simp only [RingHom.mem_ker, LinearMap.mem_ker, projection_moduleCompletionEquiv,
      LinearEquiv.map_eq_zero_iff]

/-- The inverse comparison recovers the module image of an original element. -/
@[simp]
theorem moduleCompletionEquiv_symm_toCompletion (x : A) :
    (F.moduleCompletionEquiv (R := R)).symm (F.toCompletion x) =
      (F.toModuleFiltration R).of x := by
  rw [← F.moduleCompletionEquiv_of (R := R), LinearEquiv.symm_apply_apply]

/-- Pulling back a completion ideal gives the completed module filtration exactly. -/
theorem comap_completionIdeal_moduleCompletionEquiv (k : ℕ) :
    ((F.completionIdeal k).restrictScalars R).comap
        (F.moduleCompletionEquiv (R := R)).toLinearMap =
      (F.toModuleFiltration R).completedFiltration.submodule k := by
  ext x
  exact F.moduleCompletionEquiv_mem_completionIdeal_iff k x

end Mei.AlgFiltration
