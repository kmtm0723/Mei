/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Bilinear
public import Mei.LinearAlgebra.TensorProduct.Filtration

/-!
# Pure tensors in completed filtered modules

The total-degree tensor filtration of two filtered modules is a module filtration.
Its completion receives a bilinear pure-tensor map from the two completions,
computed by the ordinary tensor map on finite quotient representatives.
Neither factor needs an algebra structure, flatness, or separatedness.
-/

public section

open scoped TensorProduct

namespace Mei.ModuleFiltration

section Semiring

variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  (F : ModuleFiltration R M) (G : ModuleFiltration R N)

/-- The total-degree filtration on the tensor product of filtered modules. -/
def tensorProduct : ModuleFiltration R (M ⊗[R] N) where
  submodule := Mei.tensorFiltration F.submodule G.submodule
  antitone := Mei.tensorFiltration_antitone F.submodule G.submodule
  zero_eq_top := Mei.tensorFiltration_zero F.submodule G.submodule F.zero_eq_top G.zero_eq_top

@[simp]
theorem tensorProduct_submodule (k : ℕ) :
    (F.tensorProduct G).submodule k = Mei.tensorFiltration F.submodule G.submodule k :=
  (rfl)

/-- The tensor of two elements has at least the sum of their filtration orders. -/
theorem tmul_mem_tensorProduct {a b : ℕ} {x : M} {y : N}
    (hx : x ∈ F.submodule a) (hy : y ∈ G.submodule b) :
    x ⊗ₜ[R] y ∈ (F.tensorProduct G).submodule (a + b) :=
  Mei.tmul_mem_tensorFiltration F.submodule G.submodule hx hy le_rfl

end Semiring

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (F : ModuleFiltration R M) (G : ModuleFiltration R N)

/-- Pure tensors of completed filtered modules, with the total-degree filtration. -/
def completedTensor : F.completion →ₗ[R] G.completion →ₗ[R] (F.tensorProduct G).completion :=
  completionBilinear F G (F.tensorProduct G) (TensorProduct.mk R M N)
    (fun _ _ _ _ hx hy => F.tmul_mem_tensorProduct G hx hy)

/-- A finite projection of a completed tensor uses only the two finite projections. -/
@[simp]
theorem projection_completedTensor (k : ℕ) (x : F.completion) (y : G.completion) :
    (F.tensorProduct G).projection k (F.completedTensor G x y) =
      quotientBilinear F G (F.tensorProduct G) (TensorProduct.mk R M N)
        (fun _ _ _ _ hx hy => F.tmul_mem_tensorProduct G hx hy) k
        (F.projection k x) (G.projection k y) :=
  projection_completionBilinear F G (F.tensorProduct G) (TensorProduct.mk R M N)
    (fun _ _ _ _ hx hy => F.tmul_mem_tensorProduct G hx hy) k x y

/-- Any representatives of the finite projections compute the projected pure tensor. -/
theorem projection_completedTensor_of_representatives (k : ℕ)
    (x : F.completion) (y : G.completion) (m : M) (n : N)
    (hm : (F.submodule (k + 1)).mkQ m = F.projection k x)
    (hn : (G.submodule (k + 1)).mkQ n = G.projection k y) :
    (F.tensorProduct G).projection k (F.completedTensor G x y) =
      ((F.tensorProduct G).submodule (k + 1)).mkQ (m ⊗ₜ[R] n) := by
  rw [projection_completedTensor, ← hm, ← hn]
  exact quotientBilinear_mk F G (F.tensorProduct G) (TensorProduct.mk R M N)
    (fun _ _ _ _ hx hy => F.tmul_mem_tensorProduct G hx hy) k m n

/-- The completed pure-tensor map extends the ordinary tensor map. -/
@[simp]
theorem completedTensor_of (x : M) (y : N) :
    F.completedTensor G (F.of x) (G.of y) = (F.tensorProduct G).of (x ⊗ₜ[R] y) :=
  completionBilinear_of F G (F.tensorProduct G) (TensorProduct.mk R M N)
    (fun _ _ _ _ hx hy => F.tmul_mem_tensorProduct G hx hy) x y

/-- Completed pure tensors add the orders of their two factors. -/
theorem completedTensor_mem_completedFiltration {a b : ℕ} {x : F.completion} {y : G.completion}
    (hx : x ∈ F.completedFiltration.submodule a)
    (hy : y ∈ G.completedFiltration.submodule b) :
    F.completedTensor G x y ∈ (F.tensorProduct G).completedFiltration.submodule (a + b) :=
  completionBilinear_mem_completedFiltration F G (F.tensorProduct G) (TensorProduct.mk R M N)
    (fun _ _ _ _ hx hy => F.tmul_mem_tensorProduct G hx hy) hx hy

end Mei.ModuleFiltration
