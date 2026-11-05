/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code, Codex
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The determinant bilinear form on pairs

`Prod.det` is the alternating bilinear form `x₁ y₂ - x₂ y₁` on `R × R`.
Over a linearly ordered field, `Prod.det_trans` expresses transitivity of its sign relative
to a scalar for vectors in the open half-plane `x₁ + x₂ < 0`. Over `ℤ`, the vectors `x` with
`det x (p, q) = 0` for coprime `p, q` are the integral multiples of `(p, q)`
(`Prod.exists_eq_zsmul_of_det_eq_zero`), and an additive map on `ℤ × ℤ` is determined by its
values on the coordinate vectors (`AddMonoidHom.apply_eq_fst_mul_add_snd_mul`).
-/

public section

namespace Prod

/-- The determinant bilinear form on pairs over a commutative ring. -/
def det {R : Type*} [CommRing R] : (R × R) →ₗ[R] (R × R) →ₗ[R] R :=
  LinearMap.mk₂ R (fun x y => x.1 * y.2 - x.2 * y.1) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

/-- Evaluate the determinant bilinear form in coordinates. -/
@[simp] theorem det_apply {R : Type*} [CommRing R] (x y : R × R) :
    det x y = x.1 * y.2 - x.2 * y.1 := by
  simp [det]

/-- The determinant bilinear form is alternating. -/
theorem isAlt_det {R : Type*} [CommRing R] : (det (R := R)).IsAlt := fun x => by
  rw [det_apply]
  ring

/-- For vectors in the open half-plane `x₁ + x₂ < 0`, the relation "`det x y` is a positive
multiple of `c`" is transitive. -/
theorem det_trans {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {c : R} {x y z : R × R} (hx : x.1 + x.2 < 0) (hy : y.1 + y.2 < 0)
    (hz : z.1 + z.2 < 0) (hxy : ∃ α > 0, det x y = c * α)
    (hyz : ∃ α > 0, det y z = c * α) : ∃ α > 0, det x z = c * α := by
  obtain ⟨α, hα, hxy⟩ := hxy
  obtain ⟨γ, hγ, hyz⟩ := hyz
  refine ⟨(γ * (x.1 + x.2) + α * (z.1 + z.2)) / (y.1 + y.2),
    div_pos_of_neg_of_neg (by nlinarith) hy, ?_⟩
  rw [det_apply] at hxy hyz ⊢
  rw [mul_div_assoc', eq_div_iff hy.ne]
  linear_combination (z.1 + z.2) * hxy + (x.1 + x.2) * hyz

/-- If `p` and `q` are coprime integers, the integral vectors `x` with `det x (p, q) = 0` are the
integral multiples of `(p, q)`. -/
theorem exists_eq_zsmul_of_det_eq_zero {p q : ℤ} (hpq : IsCoprime p q) {x : ℤ × ℤ}
    (hx : det x (p, q) = 0) : ∃ k : ℤ, x = k • (p, q) := by
  obtain ⟨u, v, huv⟩ := hpq
  rw [det_apply] at hx
  dsimp only at hx
  refine ⟨u * x.1 + v * x.2, Prod.ext ?_ ?_⟩
  · simp only [Prod.smul_fst, smul_eq_mul]
    linear_combination (-1 : ℤ) * x.1 * huv + v * hx
  · simp only [Prod.smul_snd, smul_eq_mul]
    linear_combination (-1 : ℤ) * x.2 * huv - u * hx

end Prod

/-- An additive map `ℤ × ℤ → ℤ` is determined by its values on the coordinate vectors. -/
theorem AddMonoidHom.apply_eq_fst_mul_add_snd_mul (μ : ℤ × ℤ →+ ℤ) (x : ℤ × ℤ) :
    μ x = x.1 * μ (1, 0) + x.2 * μ (0, 1) := by
  have hx : x = x.1 • ((1, 0) : ℤ × ℤ) + x.2 • ((0, 1) : ℤ × ℤ) := by
    ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul]
