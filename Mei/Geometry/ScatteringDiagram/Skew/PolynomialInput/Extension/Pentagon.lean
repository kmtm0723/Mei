/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Extension.Basic
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Pentagon
public import Mei.Geometry.ScatteringDiagram.Skew.Principal.Pentagon

/-!
# Type `A₂` with isolated indices for the principal BLM extension

Let `B` be an adapted basis of a skew lattice datum, `ℓ_i` positive integers at the unfrozen
indices, and `i₁, i₂` two unfrozen indices. Suppose that `B` is of type `A₂` with isolated indices
at `i₁, i₂` (`SkewLatticeDatum.AdaptedBasis.IsTypeA₂WithIsolated`) and `ℓ_{i₁} = ℓ_{i₂} = 1`.
Then the principal BLM extension
(`SkewLatticeDatum.AdaptedBasis.principalBLMExtension`) is a polynomial input of type `A₂` with
isolated indices at the unfrozen indices `a_{i₁}, a_{i₂}`
(`SkewLatticeDatum.AdaptedBasis.principalBLMExtension_isTypeA₂WithIsolated`): the multiplicities
`ℓ_i` at the isolated indices are arbitrary. The extension carries a polynomial input for every
adapted basis, so this applies to degenerate forms, and it identifies the exponents of the
extension, `w_i(a_j) = d_j {e_i, e_j}`, with the pairings of the original basis.

The extension is the realization of the principal initial walls of Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Appendix B (arXiv:1411.1394v2), as a polynomial input of
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, §8.1
(arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis

variable {N ι : Type*} [AddCommGroup N] {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι}
  [DecidableEq ι] [Fintype ι] [Nonempty ι] (ℓ : B.unfrozenIndex → ℕ+)

/-- In the principal BLM extension, the multiplier and the form at the unfrozen vectors `a_i`,
`a_j` satisfy `d^B_{a_i} {a_i, a_j} = ℓ_i d_j {e_i, e_j}`. -/
theorem principalBLMExtension_multiplier_mul_form (i j : B.unfrozenIndex) :
    ((B.principalBLMBasis ℓ).multiplier (B.principalBLMUnfrozenEquiv ℓ i) : ℚ) *
        (B.principalBLMDatum ℓ).form
          ((B.principalBLMBasis ℓ).basis (B.principalBLMUnfrozenEquiv ℓ i))
          ((B.principalBLMBasis ℓ).basis (B.principalBLMUnfrozenEquiv ℓ j)) =
      ℓ i * (B.multiplier j * D.form (B.basis i) (B.basis j)) := by
  have h := (B.principalBLMExtension ℓ).multiplicity_mul_exponent
    (B.principalBLMUnfrozenEquiv ℓ i) ((B.principalBLMBasis ℓ).basis
      (B.principalBLMUnfrozenEquiv ℓ j))
  rw [principalBLMExtension_multiplicity, principalBLMExtension_exponent] at h
  rw [← h]
  simp

variable {i₁ i₂ : B.unfrozenIndex}

/-- **The principal BLM extension of type `A₂` with isolated indices.** If the adapted basis is of
type `A₂` with isolated indices at `i₁, i₂` and `ℓ_{i₁} = ℓ_{i₂} = 1`, the principal BLM extension
is a polynomial input of type `A₂` with isolated indices at the unfrozen indices `a_{i₁}, a_{i₂}`,
whatever the multiplicities `ℓ_i` at the isolated indices are. -/
theorem principalBLMExtension_isTypeA₂WithIsolated (hB : B.IsTypeA₂WithIsolated i₁ i₂)
    (hℓ₁ : ℓ i₁ = 1) (hℓ₂ : ℓ i₂ = 1) :
    (B.principalBLMExtension ℓ).IsTypeA₂WithIsolated (B.principalBLMUnfrozenEquiv ℓ i₁)
      (B.principalBLMUnfrozenEquiv ℓ i₂) where
  multiplicity_fst := by simp [hℓ₁]
  multiplicity_snd := by simp [hℓ₂]
  multiplier_mul_form_fst := by
    rw [principalBLMExtension_multiplier_mul_form, hℓ₁, hB.multiplier_snd, hB.form_eq_one]
    simp
  multiplier_mul_form_snd := by
    rw [(B.principalBLMDatum ℓ).form_swap, mul_neg, principalBLMExtension_multiplier_mul_form,
      hℓ₂, D.form_swap]
    simp [hB.multiplier_fst, hB.form_eq_one]
  form_eq_zero i hi₁ hi₂ j := by
    obtain ⟨i, rfl⟩ := (B.principalBLMUnfrozenEquiv ℓ).surjective i
    obtain ⟨j, rfl⟩ := (B.principalBLMUnfrozenEquiv ℓ).surjective j
    have h := principalBLMExtension_multiplier_mul_form ℓ i j
    rw [hB.form_eq_zero i (fun he => hi₁ (he ▸ rfl)) (fun he => hi₂ (he ▸ rfl)) j, mul_zero,
      mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast
      ((B.principalBLMBasis ℓ).multiplier_pos _).ne')

end Mei.SkewLatticeDatum.AdaptedBasis
