/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.SquareZero.Consistency
public import Mei.Geometry.ScatteringDiagram.WallSpace.BaseChange
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Square-zero local scattering over `ℚ[t₀, t₁]/(t₀², t₁²)`

Let `x₀ ∈ h_{n₀,m₀}` and `x₁ ∈ h_{n₁,m₁}` be wall-space elements of a positively graded Lie
algebra `g` over a commutative ring `R`. For a commutative `R`-algebra `S` and scalars
`t₀, t₁ ∈ S` with `t₀² = t₁² = 0`, the elements `1 ⊗ x₀` and `1 ⊗ x₁` lie in the extended
wall spaces `S ⊗[R] h_{n,m}` (`DirectedWallSpaces.baseChange`) and give a `SquareZeroPair`
(`SquareZeroPair.baseChange`). For `R = ℚ` and `S = ℚ[t₀, t₁]/(t₀², t₁²)`
(`SquareZeroPair.DualNumbers₂`), the outgoing completion of the hyperplanes labelled
`exp (t₀ x₀)` and `exp (t₁ x₁)` adds the single wall `exp (t₀ t₁ ⁅x₀, x₁⁆)` with normal
`μ = m₀(ρ n₁) m₁ - m₁(ρ n₀) m₀` on the joint swept by `-i(ρ(n₀ + n₁))`, and no wall if `μ = 0`
(`SquareZeroPair.scat_baseChange_eq_toClass_completion`).

This is the scattering of two lines over `ℂ[t₁, t₂]/(t₁², t₂²)` in Gross–Pandharipande–Siebert,
*Quivers, curves, and the tropical vertex*, [arXiv:0902.1260](https://arxiv.org/abs/0902.1260),
§1, in the directed setting of Travis Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, [arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), Theorem 2.6.
-/

public section

noncomputable section

open TensorProduct

namespace Mei.DirectedDiagram.SquareZeroPair

section BaseChange

variable {Γ Λ R L : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  {H : DirectedWallSpaces ρ ℒ} (P : SquareZeroPair d H)
  (S : Type*) [CommRing S] [Algebra R S] (t : Fin 2 → S) (ht : ∀ j, t j * t j = 0)

/-- The coefficients `1 ⊗ x_j` in the scalar extension `S ⊗[R] L`, with the square-zero
scalars `t_j ∈ S` in place of those of `P`. -/
def baseChange : SquareZeroPair d (H.baseChange S) where
  normal := P.normal
  normal_ne_zero := P.normal_ne_zero
  ray := P.ray
  normal_ray := P.normal_ray
  degree := P.degree
  degree_mem := P.degree_mem
  coeff j := 1 ⊗ₜ P.coeff j
  coeff_mem j := by
    rw [DirectedWallSpaces.baseChange_wall]
    exact Submodule.tmul_mem_baseChange_of_mem (1 : S) (P.coeff_mem j)
  scalar := t
  scalar_mul_self := ht

/-- Scalar extension keeps the normals. -/
@[simp]
theorem baseChange_normal : (P.baseChange S t ht).normal = P.normal := (rfl)

/-- Scalar extension keeps the degrees. -/
@[simp]
theorem baseChange_degree : (P.baseChange S t ht).degree = P.degree := (rfl)

/-- The coefficients of the scalar extension are `1 ⊗ x_j`. -/
@[simp]
theorem baseChange_coeff (j : Fin 2) : (P.baseChange S t ht).coeff j = 1 ⊗ₜ P.coeff j := (rfl)

/-- The scalars of the scalar extension are `t_j`. -/
@[simp]
theorem baseChange_scalar : (P.baseChange S t ht).scalar = t := (rfl)

/-- Scalar extension keeps the bracket normal. -/
@[simp]
theorem bracketNormal_baseChange : (P.baseChange S t ht).bracketNormal = P.bracketNormal := by
  rw [bracketNormal_eq, bracketNormal_eq, baseChange_normal, baseChange_degree]

end BaseChange

/-- The coefficient ring `ℚ[t₀, t₁]/(t₀², t₁²)`. -/
abbrev DualNumbers₂ : Type :=
  MvPolynomial (Fin 2) ℚ ⧸
    (Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2} : Ideal (MvPolynomial (Fin 2) ℚ))

/-- The generators `t₀, t₁` of `ℚ[t₀, t₁]/(t₀², t₁²)`. -/
def DualNumbers₂.gen (j : Fin 2) : DualNumbers₂ :=
  Ideal.Quotient.mk _ (MvPolynomial.X j)

/-- The generators of `ℚ[t₀, t₁]/(t₀², t₁²)` square to zero. -/
theorem DualNumbers₂.gen_mul_self (j : Fin 2) : DualNumbers₂.gen j * DualNumbers₂.gen j = 0 := by
  rw [DualNumbers₂.gen, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  fin_cases j
  · exact Ideal.subset_span (Set.mem_insert _ _)
  · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

section DualNumbers

variable {Γ Λ L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ] [LieRing L] [LieAlgebra ℚ L]
  [DecidableEq Γ] [Module.Free ℤ Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule ℚ L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {H : DirectedWallSpaces ρ ℒ} (P : SquareZeroPair d H) (θ₀ : V)

/-- **Local scattering over `ℚ[t₀, t₁]/(t₀², t₁²)`.** With wall spaces
`ℚ[t₀, t₁]/(t₀², t₁²) ⊗ h_{n,m}`, the hyperplanes labelled `exp (t₀ x₀)` and `exp (t₁ x₁)`
have the scattering class of the diagram obtained by adding the single wall
`exp (t₀ t₁ ⁅x₀, x₁⁆)` with normal `μ ≠ 0` on the joint swept by `-i(ρ(n₀ + n₁))`. -/
theorem scat_baseChange_eq_toClass_completion {w : SupportedRay d}
    (hw : P.degree 0 + P.degree 1 ∈ w.rayDegrees) (hμ : P.bracketNormal ≠ 0) :
    ((P.baseChange DualNumbers₂ DualNumbers₂.gen DualNumbers₂.gen_mul_self).input h θ₀).Scat
        (input_full _ h θ₀) =
      ((P.baseChange DualNumbers₂ DualNumbers₂.gen DualNumbers₂.gen_mul_self).completion
        h θ₀ (w := w) (by rwa [baseChange_degree]) (by rwa [bracketNormal_baseChange])).toClass :=
  scat_input_eq_toClass_completion _ h θ₀ _ _

/-- **Local scattering over `ℚ[t₀, t₁]/(t₀², t₁²)` without correction.** If `μ = 0`, the
hyperplanes labelled `exp (t₀ x₀)` and `exp (t₁ x₁)` alone represent their scattering class. -/
theorem scat_baseChange_eq_toClass_of_bracketNormal_eq_zero (hμ : P.bracketNormal = 0) :
    ((P.baseChange DualNumbers₂ DualNumbers₂.gen DualNumbers₂.gen_mul_self).input h θ₀).Scat
        (input_full _ h θ₀) =
      ((P.baseChange DualNumbers₂ DualNumbers₂.gen
        DualNumbers₂.gen_mul_self).inputWithoutCorrection h θ₀).toClass :=
  scat_input_eq_toClass_of_bracketNormal_eq_zero _ h θ₀ (by rwa [bracketNormal_baseChange])

end DualNumbers

end Mei.DirectedDiagram.SquareZeroPair
