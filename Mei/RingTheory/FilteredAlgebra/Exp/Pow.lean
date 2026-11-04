/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.RingTheory.FilteredAlgebra.Exp.Basic

/-!
# Powers in exponential coordinates of a filtered completion

In the completion of a rational filtered algebra, the completed exponential turns natural
multiples into powers, `exp (r • x) = (exp x) ^ r`, and the completed logarithm turns powers of
elements congruent to one into natural multiples, `log (u ^ r) = r • log u`.
-/

public section

namespace Mei.AlgFiltration

variable {A : Type*} [Ring A] [Algebra ℚ A] (F : AlgFiltration A)

/-- The completed exponential turns natural multiples into powers. -/
theorem completedExp_nsmul (x : F.completionIdeal 1) (r : ℕ) :
    F.completedExp (r • x) = F.completedExp x ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [succ_nsmul, F.completedExp_add _ _ ((Commute.refl (x : F.completion)).smul_left r),
      ih, pow_succ]

/-- A power of an element congruent to one is congruent to one. -/
theorem pow_sub_one_mem (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) (r : ℕ) :
    (u : F.completion) ^ r - 1 ∈ F.completionIdeal 1 := by
  rw [← F.completedExp_completedLog u, ← completedExp_nsmul]
  exact F.completedExp_sub_one_mem _

/-- The completed logarithm turns powers of elements congruent to one into natural
multiples. -/
@[simp]
theorem completedLog_pow (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) (r : ℕ) :
    F.completedLog ⟨(u : F.completion) ^ r, F.pow_sub_one_mem u r⟩ = r • F.completedLog u := by
  let x : F.completionIdeal 1 := r • ⟨F.completedLog u, F.completedLog_mem u⟩
  have hx : F.completedExp x = (u : F.completion) ^ r := by
    rw [completedExp_nsmul, completedExp_completedLog]
  calc F.completedLog ⟨(u : F.completion) ^ r, F.pow_sub_one_mem u r⟩
      = F.completedLog ⟨F.completedExp x, F.completedExp_sub_one_mem x⟩ := by
        simp only [hx]
    _ = r • F.completedLog u := by
        rw [F.completedLog_completedExp x]
        exact Submodule.coe_smul_of_tower r _

end Mei.AlgFiltration
