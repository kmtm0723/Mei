/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Principal.Positive
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Positive adapted polynomial walls of a form vanishing on the unfrozen part

Take `N = ℤ³` with the skew form `{x, y} = x₀ y₂ - x₂ y₀`, the unfrozen basis vectors `e₀, e₁`,
the frozen basis vector `e₂` and multipliers one. The form is nonzero, since `{e₀, e₂} = 1`, but
it vanishes on `N_uf = ℤ e₀ ⊕ ℤ e₁` (`frozenDatum_form_ne_zero`,
`frozenDatum_form_unfrozen_eq_zero`). With multiplicities `ℓ = (2, 2)` and independent
coefficients `aᵢₛ` the adapted polynomial input has the initial wall functions
`1 + aᵢ₀ q^{eᵢ} + aᵢ₁ q^{2 eᵢ}` on the principal coefficient algebra.

* `exists_isPositiveWallRepresentative_frozenDatum`: for every integral lattice structure on
  `L_pr,ℝ`, the outgoing scattering class of this input has a representative whose grouped
  wall functions have monomial coefficients in `ℕ[aᵢₛ]`.
* `coe_completedPolynomialWallFunction_frozenDatum`: the grouped wall function at `eᵢ` is
  `1 + aᵢ₀ z^{r(eᵢ)} + aᵢ₁ z^{2 r(eᵢ)}`.
* `exists_isPositiveWallRepresentative_frozenDatum_binomial`,
  `coe_completedPolynomialWallFunction_frozenDatum_binomial`: the binomial input over `ℚ` with
  walls `(eᵢ⊥, 1 + q^{eᵢ})` has a representative of its scattering class whose grouped wall
  functions `1 + q^{eᵢ}` have natural-number coefficients.

These are instances of
`Mei.SkewLatticeDatum.AdaptedBasis.exists_isPositiveWallRepresentative_of_forall_form_eq_zero`;
see Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, Theorem 1.13
(arXiv:1411.1394v2).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.Examples

open _root_.AddMonoidAlgebra
open scoped Mei.TropicalVertexCoefficientAction

/-- The skew form `{x, y} = x₀ y₂ - x₂ y₀` on `ℤ³`, pairing `e₀` with `e₂`. -/
def frozenForm : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) →ₗ[ℤ] ℚ :=
  LinearMap.mk₂ ℤ (fun x y => ((x 0 * y 2 - x 2 * y 0 : ℤ) : ℚ))
    (fun x x' y => by push_cast [Pi.add_apply]; ring)
    (fun c x y => by push_cast [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by push_cast [Pi.add_apply]; ring)
    (fun c x y => by push_cast [Pi.smul_apply, smul_eq_mul]; ring)

/-- The values of `frozenForm`. -/
@[simp]
theorem frozenForm_apply (x y : Fin 3 → ℤ) :
    frozenForm x y = ((x 0 * y 2 - x 2 * y 0 : ℤ) : ℚ) :=
  LinearMap.mk₂_apply ..

/-- The skew lattice datum on `ℤ³` with form `frozenForm`, unfrozen basis vectors `e₀, e₁`, frozen
basis vector `e₂` and multipliers one. -/
def frozenDatum : SkewLatticeDatum (Fin 3 → ℤ) :=
  ofBasis (Pi.basisFun ℤ (Fin 3)) {0, 1} (fun _ => 1) frozenForm (fun _ => one_pos)
    (fun x => by simp [mul_comm]) (fun _ _ _ => ⟨_, frozenForm_apply _ _⟩)
    (fun _ _ _ => ⟨_, frozenForm_apply _ _⟩)

/-- The standard basis of `ℤ³` as an adapted basis of `frozenDatum`. -/
def frozenBasis : frozenDatum.AdaptedBasis (Fin 3) :=
  AdaptedBasis.ofBasis ..

/-- The form of `frozenDatum` is `frozenForm`. -/
@[simp]
theorem frozenDatum_form : frozenDatum.form = frozenForm :=
  ofBasis_form ..

/-- The basis of `frozenBasis` is the standard basis. -/
@[simp]
theorem frozenBasis_basis : frozenBasis.basis = Pi.basisFun ℤ (Fin 3) :=
  AdaptedBasis.ofBasis_basis

/-- The unfrozen indices of `frozenBasis` are `0` and `1`. -/
@[simp]
theorem frozenBasis_unfrozenIndex : frozenBasis.unfrozenIndex = {0, 1} :=
  AdaptedBasis.ofBasis_unfrozenIndex

/-- The form of `frozenDatum` is not zero: `{e₀, e₂} = 1`. -/
theorem frozenDatum_form_ne_zero : frozenDatum.form ≠ 0 := by
  intro h
  have h' := LinearMap.congr_fun₂ h (Pi.single 0 1) (Pi.single 2 1)
  simp at h'

/-- The form of `frozenDatum` vanishes on the unfrozen sublattice `ℤ e₀ ⊕ ℤ e₁`. -/
theorem frozenDatum_form_unfrozen_eq_zero (n m : frozenDatum.unfrozen) :
    frozenDatum.form n m = 0 := by
  have hn := frozenBasis.mem_unfrozen_iff.mp n.2 2 (by simp)
  have hm := frozenBasis.mem_unfrozen_iff.mp m.2 2 (by simp)
  simp only [frozenBasis_basis, Pi.basisFun_repr] at hn hm
  simp [hn, hm]

local notation "𝒅" => frozenBasis.unfrozenBasis.positiveDegrees
local notation "Lpr" => Module.Dual ℤ frozenDatum.sublattice × frozenDatum.unfrozen
local notation "Qpr" => frozenDatum.principalCoefficientMonoid 𝒅

/-- The principal positive monoid lies in the principal coefficient monoid. -/
instance : Fact ((frozenDatum.principalPositiveDegrees 𝒅).monoid ≤ Qpr) :=
  ⟨frozenDatum.principalPositiveDegrees_le_coefficientMonoid 𝒅⟩

/-- The principal lattice `M° × N_uf` of `frozenDatum` is free. -/
instance : Module.Free ℤ Lpr := by
  have := Module.Free.of_basis frozenBasis.sublatticeBasis
  have := Module.Finite.of_basis frozenBasis.sublatticeBasis
  have := Module.Free.of_basis frozenBasis.unfrozenBasis
  infer_instance

/-- The principal coefficient monoid contains every character `(χ, 0)`. -/
theorem mem_principalCoefficientMonoid_frozenDatum (χ : Module.Dual ℤ frozenDatum.sublattice) :
    ((χ, 0) : Lpr) ∈ Qpr := by
  simp

/-- The independent coefficients `aᵢₛ ∈ ℚ[a]`, `s < 2`, of the input. -/
def frozenCoefficient (i : frozenBasis.unfrozenIndex) (s : Fin 2) :
    MvPolynomial (frozenBasis.unfrozenIndex × Fin 2) ℚ :=
  MvPolynomial.X (i, s)

local notation "F" A => TropicalVertexCoefficientAction.filtration (R := A)
  (frozenDatum.principalPositiveDegrees 𝒅) Qpr
local notation "σ" A => MonoidHom.comp (AlgFiltration.completedBCHAction (F A)
  (frozenDatum.principalPositiveDegrees 𝒅)
  (tropicalVertexGrading (R := A) (frozenDatum.principalPositiveDegrees 𝒅) (AddMonoidHom.id Lpr)))
  (GradedLieHom.completedMap (frozenDatum.principalGraphGradedLieHom (R := A) 𝒅))

variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p : Lpr →+ V}
  (h : TauCeti.Toric.IsIntegralLattice p) [AddCommGroup M] (π : Lpr →+ M)

open scoped Classical in
/-- For every integral lattice structure on `L_pr,ℝ`, the outgoing scattering class of the
adapted polynomial input of `frozenDatum` with multiplicities `(2, 2)` and independent
coefficients has a representative whose grouped wall functions have monomial coefficients in
`ℕ[aᵢₛ]`. -/
theorem exists_isPositiveWallRepresentative_frozenDatum :
    ∃ (κ : Type) (E : DirectedDiagram (d := frozenDatum.principalPositiveDegrees 𝒅) h
        (frozenDatum.principalGraphWallSpaces
          (R := MvPolynomial (frozenBasis.unfrozenIndex × Fin 2) ℚ) 𝒅) κ),
      E.toClass = (frozenBasis.adaptedPolynomialInput (fun _ => 2) frozenCoefficient h).Scat
        (frozenBasis.adaptedPolynomialInput_full _ _ h) ∧
      E.IsPositiveWallRepresentative (σ (MvPolynomial (frozenBasis.unfrozenIndex × Fin 2) ℚ))
        (mapRingHom Qpr (MvPolynomial.map (Nat.castRingHom ℚ))).rangeS π :=
  frozenBasis.exists_isPositiveWallRepresentative_of_forall_form_eq_zero _ _ Qpr h π
    frozenDatum_form_unfrozen_eq_zero mem_principalCoefficientMonoid_frozenDatum _
    fun i s => ⟨MvPolynomial.X (i, s), by simp [frozenCoefficient]⟩

open scoped Classical in
/-- The grouped wall function of the input wall at `eᵢ` is
`1 + aᵢ₀ z^{r(eᵢ)} + aᵢ₁ z^{2 r(eᵢ)}`. -/
theorem coe_completedPolynomialWallFunction_frozenDatum (i : frozenBasis.unfrozenIndex) :
    (frozenBasis.completedPolynomialWallFunction (fun _ => 2) frozenCoefficient Qpr i :
        (F (MvPolynomial (frozenBasis.unfrozenIndex × Fin 2) ℚ)).completion) =
      (F (MvPolynomial (frozenBasis.unfrozenIndex × Fin 2) ℚ)).toCompletion
        (1 + single (frozenBasis.principalExponent Qpr i) (MvPolynomial.X (i, 0)) +
          single (2 • frozenBasis.principalExponent Qpr i) (MvPolynomial.X (i, 1))) := by
  simp only [AdaptedBasis.coe_completedPolynomialWallFunction, Fin.sum_univ_two, add_assoc,
    Fin.val_zero, Fin.val_one, zero_add, one_smul, one_add_one_eq_two, frozenCoefficient]

open scoped Classical in
/-- The binomial input over `ℚ`, with walls `(eᵢ⊥, 1 + q^{eᵢ})`: its outgoing scattering class
has a representative whose grouped wall functions have natural-number coefficients. -/
theorem exists_isPositiveWallRepresentative_frozenDatum_binomial :
    ∃ (κ : Type) (E : DirectedDiagram (d := frozenDatum.principalPositiveDegrees 𝒅) h
        (frozenDatum.principalGraphWallSpaces (R := ℚ) 𝒅) κ),
      E.toClass = (frozenBasis.adaptedPolynomialInput (fun _ => 1) (fun _ _ => (1 : ℚ)) h).Scat
        (frozenBasis.adaptedPolynomialInput_full _ _ h) ∧
      E.IsPositiveWallRepresentative (σ ℚ) (mapRingHom Qpr (Nat.castRingHom ℚ)).rangeS π :=
  frozenBasis.exists_isPositiveWallRepresentative_of_forall_form_eq_zero _ _ Qpr h π
    frozenDatum_form_unfrozen_eq_zero mem_principalCoefficientMonoid_frozenDatum _
    fun _ _ => ⟨1, map_one _⟩

open scoped Classical in
/-- The grouped wall function of the binomial input at `eᵢ` is `1 + z^{r(eᵢ)}`. -/
theorem coe_completedPolynomialWallFunction_frozenDatum_binomial
    (i : frozenBasis.unfrozenIndex) :
    (frozenBasis.completedPolynomialWallFunction (fun _ => 1) (fun _ _ => (1 : ℚ)) Qpr i :
        (F ℚ).completion) =
      (F ℚ).toCompletion (1 + single (frozenBasis.principalExponent Qpr i) 1) := by
  simp

end Mei.SkewLatticeDatum.Examples
