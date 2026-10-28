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

The module/algebra completion comparison API `moduleCompletionEquiv`, including
its projection and filtration compatibility lemmas, incorporates the comparison
introduced in [Mei #419](https://github.com/yuma-mizuno-lean/Mei/pull/419).
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
theorem factor_restrictScalarsEquiv {k l : ℕ} (h : k ≤ l)
    (a : (F.toModuleFiltration R).quotient l) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
        (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (l + 1)) a) =
      Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
        ((F.toModuleFiltration R).transition h a) := by
  obtain ⟨a, rfl⟩ := ((F.toModuleFiltration R).submodule (l + 1)).mkQ_surjective a
  simp

/-- The module and algebra completions of an ideal filtration are linearly equivalent. -/
def moduleCompletionEquiv : (F.toModuleFiltration R).completion ≃ₗ[R] F.completion := by
  let e := (LinearEquiv.piCongrRight fun k : ℕᵒᵖ =>
    Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k.unop + 1))).ofSubmodules
      (F.toModuleFiltration R).completionSubmodule
      (F.completionSubalgebra (R := R)).toSubmodule (by
        ext x
        rw [Submodule.mem_map_equiv]
        change _ ∈ (F.toModuleFiltration R).completionSubmodule ↔
          x ∈ F.completionSubalgebra
        rw [F.mem_completionSubalgebra_iff]
        rw [ModuleFiltration.mem_completionSubmodule_iff, F.mem_completion_iff]
        simp only [LinearEquiv.piCongrRight_symm, LinearEquiv.piCongrRight_apply]
        constructor
        · intro hx k l h
          have he := congrArg (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1)))
            (hx k l h)
          simpa only [← factor_restrictScalarsEquiv, LinearEquiv.apply_symm_apply] using he
        · intro hx k l h
          apply (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).injective
          simpa only [← factor_restrictScalarsEquiv, LinearEquiv.apply_symm_apply] using hx h)
  let E : (F.toModuleFiltration R).completion ≃ F.completion :=
    e.toEquiv.trans (Equiv.subtypeEquivRight fun x =>
      F.mem_completionSubalgebra_iff (R := R) x)
  have hproj (k : ℕ) (x : (F.toModuleFiltration R).completion) :
      F.projection k (E x) =
        Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
          ((F.toModuleFiltration R).projection k x) := by
    obtain ⟨x, hx⟩ := x
    rw [projection_apply, ModuleFiltration.projection_mk]
    rfl
  refine { E with map_add' := ?_, map_smul' := ?_ }
  · intro x y
    change E (x + y) = E x + E y
    apply F.completion_ext
    intro k
    rw [map_add (F.projection k), hproj, hproj, hproj, map_add, map_add]
  · intro r x
    change E (r • x) = r • E x
    apply F.completion_ext
    intro k
    have hs := map_smul (F.projectionₐ (R := R) k) r (E x)
    simp only [projectionₐ_apply] at hs
    rw [hproj, hs, hproj, map_smul, map_smul]

/-- The comparison uses the scalar-restriction equivalence at every finite order. -/
@[simp]
theorem projection_moduleCompletionEquiv (k : ℕ)
    (x : (F.toModuleFiltration R).completion) :
    F.projection k (F.moduleCompletionEquiv x) =
      Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
        ((F.toModuleFiltration R).projection k x) :=
  by
    obtain ⟨x, hx⟩ := x
    simp only [moduleCompletionEquiv, projection_apply, ModuleFiltration.projection_mk]
    rfl

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
