/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Nilpotent.Exp

/-!
# Nilpotent exponentials and bilinear pairings

A bilinear pairing intertwining three endomorphisms by the Leibniz rule
intertwines their nilpotent exponentials. This extends the tensor-product
argument of `Module.End.exp_mul_of_derivation` to three different modules.
The proof reuses the existing exponential intertwining theorem and the
exponential of a sum of commuting nilpotent endomorphisms.
-/

public section

namespace Module.End

open IsNilpotent TensorProduct

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [Module ℚ M]
  [AddCommGroup N] [Module R N] [Module ℚ N]
  [AddCommGroup P] [Module R P] [Module ℚ P]

/-- A Leibniz-compatible bilinear pairing intertwines nilpotent exponentials. -/
theorem exp_bilinear_of_leibniz
    (f : M →ₗ[R] N →ₗ[R] P)
    (D₁ : Module.End R M) (D₂ : Module.End R N) (D₃ : Module.End R P)
    (h : ∀ x y, D₃ (f x y) = f x (D₂ y) + f (D₁ x) y)
    (h₁ : IsNilpotent D₁) (h₂ : IsNilpotent D₂) (h₃ : IsNilpotent D₃)
    (x : M) (y : N) :
    exp D₃ (f x y) = f (exp D₁ x) (exp D₂ y) := by
  let DL : Module.End R (M ⊗[R] N) := D₂.lTensor M
  let DR : Module.End R (M ⊗[R] N) := D₁.rTensor N
  have h_nilL : IsNilpotent DL := h₂.map <| Module.End.lTensorAlgHom R N M
  have h_nilR : IsNilpotent DR := h₁.map <| Module.End.rTensorAlgHom R M N
  have h_comm : Commute DL DR := by ext; simp [DL, DR]
  let m : M ⊗[R] N →ₗ[R] P := TensorProduct.lift f
  have hc : exp D₃ ∘ₗ m = m ∘ₗ exp (DL + DR) := by
    apply Module.End.commute_exp_left_of_commute (h_comm.isNilpotent_add h_nilL h_nilR) h₃
    ext
    simp [DL, DR, m, h]
  have hl : exp DL = (exp D₂).lTensor M :=
    (h₂.map_exp (Module.End.lTensorAlgHom R N M)).symm
  have hr : exp DR = (exp D₁).rTensor N :=
    (h₁.map_exp (Module.End.rTensorAlgHom R M N)).symm
  have he := LinearMap.congr_fun hc (x ⊗ₜ[R] y)
  simpa [exp_add_of_commute h_comm h_nilL h_nilR, hl, hr, m] using he

end Module.End
