/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Module.Primitive
public import Mei.LinearAlgebra.Determinant.Prod
public import Mathlib.GroupTheory.IndexNSmul
import Mathlib.Tactic.LinearCombination

/-!
# Coordinates of a rank-two lattice change

Let `M = ℤ²` and let `M₀ ⊆ M` be spanned by linearly independent vectors `m₁, m₂`, ordered so
that `ℓ = det(m₁, m₂)` is positive. This file sets up integral coordinates for the inclusion
`M ⊆ ℓ⁻¹M₀` used in the lattice change of Burcroff–Lee–Mou, *Positivity of generalized cluster
scattering diagrams*, Theorem 9.5 (arXiv:2503.03719v1):

* the vector `a m₁ + b m₂` has coordinates `coord m₁ m₂ (a, b)` in `M` and
  `sublatticeCoord m₁ m₂ (a, b) = (ℓ a, ℓ b)` in `ℓ⁻¹M₀`, with basis `ℓ⁻¹m₁, ℓ⁻¹m₂`;
* the inclusion `M ⊆ ℓ⁻¹M₀` is `change m₁ m₂ x = (det(x, m₂), det(m₁, x))`, by Cramer's rule
  (`coord_change`, `change_coord`); it is injective with image of finite index;
* the normal map `normalMap m₁ m₂` sends an integral normal `μ` of `M` to the integral normal
  `(μ m₁ / g) e₁* + (μ m₂ / g) e₂*` of `ℓ⁻¹M₀`, `g = gcd(μ m₁, μ m₂)`, and
  `normalScalar m₁ m₂ μ = ℓ / g` is the positive rational with
  `normalMap μ ∘ change = normalScalar μ • μ` (`normalMap_apply_change`).

The scalar is `1` on the normals `det(m₁, ·)` and `det(·, m₂)` of the lines `ℝm₁` and `ℝm₂`,
which go to the coordinate normals `e₂*` and `e₁*` of `ℓ⁻¹M₀` (`normalMap_lineNormal`,
`normalScalar_lineNormal`). For `m° = p m₁ + q m₂ = r • m` with `p, q` coprime, the normal
`det(·, m)` of the line `ℝm°` goes to the normal `det(·, (p, q))` of `ℓ⁻¹M₀` with scalar `r`
(`normalMap_normal`, `normalScalar_normal`). Here `ℓ` is the index of `M₀` in `M`; this file only
uses it as the determinant.

The line `ℝm°` meets the coordinate lattice of `M₀` along `ℤ(p, q)`: a vector `a m₁ + b m₂` lies
on it exactly when `(a, b)` is an integral multiple of `(p, q)`
(`exists_eq_zsmul_of_normal_coord_eq_zero`). For primitive `m`, every integral normal vanishing
on `m` is an integral multiple of `det(·, m)` (`exists_eq_zsmul_normal`).
-/

public section

namespace Mei.RankTwoLatticeChange

variable (m₁ m₂ : ℤ × ℤ)

/-- The coordinates `a • m₁ + b • m₂` in `M` of the vector with coefficients `(a, b)`. -/
def coord : ℤ × ℤ →+ ℤ × ℤ :=
  ((LinearMap.fst ℤ ℤ ℤ).smulRight m₁ + (LinearMap.snd ℤ ℤ ℤ).smulRight m₂).toAddMonoidHom

/-- The vector with coefficients `(a, b)` is `a • m₁ + b • m₂`. -/
@[simp]
theorem coord_apply (x : ℤ × ℤ) : coord m₁ m₂ x = x.1 • m₁ + x.2 • m₂ := by
  simp [coord]

/-- The coordinates `(ℓ a, ℓ b)`, `ℓ = det(m₁, m₂)`, of the vector `a • m₁ + b • m₂` in the
lattice `ℓ⁻¹M₀` with basis `ℓ⁻¹m₁, ℓ⁻¹m₂`. -/
def sublatticeCoord : ℤ × ℤ →+ ℤ × ℤ := Prod.det m₁ m₂ • AddMonoidHom.id (ℤ × ℤ)

/-- The coordinates in `ℓ⁻¹M₀` are `det(m₁, m₂)` times the coefficients. -/
@[simp]
theorem sublatticeCoord_apply (x : ℤ × ℤ) : sublatticeCoord m₁ m₂ x = Prod.det m₁ m₂ • x := by
  simp [sublatticeCoord]

/-- The inclusion `M ⊆ ℓ⁻¹M₀` in coordinates: `x ↦ (det(x, m₂), det(m₁, x))`. -/
def change : ℤ × ℤ →+ ℤ × ℤ := ((Prod.det.flip m₂).prod (Prod.det m₁)).toAddMonoidHom

/-- The inclusion `M ⊆ ℓ⁻¹M₀` evaluates by Cramer's rule. -/
@[simp]
theorem change_apply (x : ℤ × ℤ) : change m₁ m₂ x = (Prod.det x m₂, Prod.det m₁ x) := by
  simp [change]

/-- The integral normal `x ↦ det(x, m)` of the line `ℝm`. -/
def normal (m : ℤ × ℤ) : ℤ × ℤ →+ ℤ := (Prod.det.flip m).toAddMonoidHom

/-- The normal of `ℝm` evaluates as a determinant. -/
@[simp]
theorem normal_apply (m x : ℤ × ℤ) : normal m x = Prod.det x m := by
  simp [normal]

/-- **Cramer's rule.** The coordinates in `M` of the image of `x` are `det(m₁, m₂) • x`. -/
theorem coord_change (x : ℤ × ℤ) : coord m₁ m₂ (change m₁ m₂ x) = Prod.det m₁ m₂ • x := by
  simp only [coord_apply, change_apply, Prod.det_apply, Prod.ext_iff, Prod.fst_add,
    Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> ring

/-- The inclusion sends `a • m₁ + b • m₂` to `det(m₁, m₂) • (a, b)`. -/
theorem change_coord (x : ℤ × ℤ) : change m₁ m₂ (coord m₁ m₂ x) = Prod.det m₁ m₂ • x := by
  simp only [coord_apply, change_apply, Prod.det_apply, Prod.ext_iff, Prod.fst_add,
    Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> ring

/-- The two coordinate maps are compatible with the inclusion `M ⊆ ℓ⁻¹M₀`. -/
theorem sublatticeCoord_eq_change_coord (x : ℤ × ℤ) :
    sublatticeCoord m₁ m₂ x = change m₁ m₂ (coord m₁ m₂ x) := by
  rw [sublatticeCoord_apply, change_coord]

variable {m₁ m₂}

/-- The inclusion `M ⊆ ℓ⁻¹M₀` is injective when `m₁` and `m₂` are independent. -/
theorem change_injective (hD : Prod.det m₁ m₂ ≠ 0) : Function.Injective (change m₁ m₂) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  have h := coord_change m₁ m₂ x
  rw [hx, map_zero, eq_comm] at h
  exact (smul_eq_zero.mp h).resolve_left hD

/-- The image of `M` in `ℓ⁻¹M₀` contains `ℓ • ℓ⁻¹M₀`, so it has finite index. -/
theorem finiteIndex_range_change (hD : 0 < Prod.det m₁ m₂) : (change m₁ m₂).range.FiniteIndex := by
  have : (nsmulAddMonoidHom (α := ℤ × ℤ) (Prod.det m₁ m₂).toNat).range.FiniteIndex :=
    ⟨by rw [AddSubgroup.index_range_nsmul]; exact pow_ne_zero _ (by omega)⟩
  refine AddSubgroup.finiteIndex_of_le
    (H := (nsmulAddMonoidHom (α := ℤ × ℤ) (Prod.det m₁ m₂).toNat).range) ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨coord m₁ m₂ x, ?_⟩
  rw [change_coord, nsmulAddMonoidHom_apply, ← natCast_zsmul, Int.toNat_of_nonneg hD.le]

variable (m₁ m₂)

/-- The content `gcd(μ m₁, μ m₂)` of the normal `μ` on the generators: the largest integer
dividing `μ` on `M₀`. -/
def normalContent (μ : ℤ × ℤ →+ ℤ) : ℕ := Int.gcd (μ m₁) (μ m₂)

/-- The normal map of `M ⊆ ℓ⁻¹M₀`: `μ` goes to `(μ m₁ / g) e₁* + (μ m₂ / g) e₂*`, where `g` is
the content of `μ` on the generators. For `μ ≠ 0` its coefficients are coprime, and it is
proportional to `μ ∘ change⁻¹` (`normalMap_apply_change`). -/
def normalMap (μ : ℤ × ℤ →+ ℤ) : ℤ × ℤ →+ ℤ :=
  (μ m₁ / normalContent m₁ m₂ μ) • AddMonoidHom.fst ℤ ℤ +
    (μ m₂ / normalContent m₁ m₂ μ) • AddMonoidHom.snd ℤ ℤ

/-- The comparison scalar of `normalMap`: `det(m₁, m₂) / gcd(μ m₁, μ m₂)`, and `1` when the
content vanishes. -/
def normalScalar (μ : ℤ × ℤ →+ ℤ) : ℚ :=
  if normalContent m₁ m₂ μ = 0 then 1 else (Prod.det m₁ m₂ : ℚ) / normalContent m₁ m₂ μ

/-- The normal map evaluates on the coefficients of `μ` divided by its content. -/
@[simp]
theorem normalMap_apply (μ : ℤ × ℤ →+ ℤ) (x : ℤ × ℤ) :
    normalMap m₁ m₂ μ x =
      μ m₁ / normalContent m₁ m₂ μ * x.1 + μ m₂ / normalContent m₁ m₂ μ * x.2 := by
  simp [normalMap]

/-- A normal evaluated on the coordinates `a • m₁ + b • m₂`. -/
theorem apply_coord (μ : ℤ × ℤ →+ ℤ) (x : ℤ × ℤ) :
    μ (coord m₁ m₂ x) = x.1 * μ m₁ + x.2 * μ m₂ := by
  rw [coord_apply, map_add, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul]

/-- Multiplying the normal map by the content recovers `μ` on the coordinates of `M₀`. -/
theorem normalContent_mul_normalMap_apply (μ : ℤ × ℤ →+ ℤ) (x : ℤ × ℤ) :
    (normalContent m₁ m₂ μ : ℤ) * normalMap m₁ m₂ μ x = μ (coord m₁ m₂ x) := by
  have h₁ : (normalContent m₁ m₂ μ : ℤ) ∣ μ m₁ := Int.gcd_dvd_left ..
  have h₂ : (normalContent m₁ m₂ μ : ℤ) ∣ μ m₂ := Int.gcd_dvd_right ..
  rw [normalMap_apply, apply_coord, mul_add, ← mul_assoc, ← mul_assoc,
    Int.mul_ediv_cancel' h₁, Int.mul_ediv_cancel' h₂, mul_comm (μ m₁), mul_comm (μ m₂)]

variable {m₁ m₂}

/-- The content of a normal vanishes only for the zero normal. -/
theorem eq_zero_of_normalContent_eq_zero (hD : Prod.det m₁ m₂ ≠ 0) {μ : ℤ × ℤ →+ ℤ}
    (hμ : normalContent m₁ m₂ μ = 0) : μ = 0 := by
  obtain ⟨h₁, h₂⟩ := Int.gcd_eq_zero_iff.mp hμ
  refine AddMonoidHom.ext fun x => ?_
  have h := apply_coord m₁ m₂ μ (change m₁ m₂ x)
  rw [coord_change, map_zsmul, h₁, h₂, mul_zero, mul_zero, add_zero, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hD

/-- The comparison scalars are positive. -/
theorem normalScalar_pos (hD : 0 < Prod.det m₁ m₂) (μ : ℤ × ℤ →+ ℤ) :
    0 < normalScalar m₁ m₂ μ := by
  unfold normalScalar
  split_ifs with hμ
  · exact one_pos
  · exact div_pos (by exact_mod_cast hD) (by exact_mod_cast Nat.pos_of_ne_zero hμ)

/-- The normal map pulls back along `M ⊆ ℓ⁻¹M₀` to the comparison scalar times the original
normal. -/
theorem normalMap_apply_change (hD : 0 < Prod.det m₁ m₂) (μ : ℤ × ℤ →+ ℤ) (x : ℤ × ℤ) :
    (normalMap m₁ m₂ μ (change m₁ m₂ x) : ℚ) = normalScalar m₁ m₂ μ * μ x := by
  by_cases hμ : normalContent m₁ m₂ μ = 0
  · rw [eq_zero_of_normalContent_eq_zero hD.ne' hμ]
    simp [normalMap, normalContent]
  · have h := normalContent_mul_normalMap_apply m₁ m₂ μ (change m₁ m₂ x)
    rw [coord_change, map_zsmul, smul_eq_mul] at h
    have hc : (normalContent m₁ m₂ μ : ℚ) ≠ 0 := by exact_mod_cast hμ
    rw [normalScalar, ite_eq_right hμ, div_mul_eq_mul_div, eq_div_iff hc, mul_comm]
    exact_mod_cast h

/-- A normal with the given content and coefficients on the generators: if
`gcd(μ m₁, μ m₂) = c ≠ 0`, `μ m₁ = a c` and `μ m₂ = b c`, then `normalMap μ = a e₁* + b e₂*` and
the comparison scalar is `det(m₁, m₂) / c`. -/
theorem normalMap_eq_and_normalScalar_eq {μ : ℤ × ℤ →+ ℤ} {a b c : ℤ}
    (hc : (normalContent m₁ m₂ μ : ℤ) = c) (hc0 : c ≠ 0) (h₁ : μ m₁ = a * c) (h₂ : μ m₂ = b * c) :
    normalMap m₁ m₂ μ = a • AddMonoidHom.fst ℤ ℤ + b • AddMonoidHom.snd ℤ ℤ ∧
      normalScalar m₁ m₂ μ = (Prod.det m₁ m₂ : ℚ) / c := by
  have hμ : normalContent m₁ m₂ μ ≠ 0 := by omega
  refine ⟨?_, ?_⟩
  · rw [normalMap, hc, h₁, h₂, Int.mul_ediv_cancel _ hc0, Int.mul_ediv_cancel _ hc0]
  · rw [normalScalar, ite_eq_right hμ, ← hc, Int.cast_natCast]

variable (m₁ m₂)

/-- The normals `det(m₁, ·)` of the line `ℝm₁` and `det(·, m₂)` of the line `ℝm₂` in `M`. -/
def lineNormal : Fin 2 → ℤ × ℤ →+ ℤ := ![(Prod.det m₁).toAddMonoidHom, normal m₂]

/-- The normal of `ℝm₁` in `M` is `det(m₁, ·)`. -/
@[simp]
theorem lineNormal_zero_apply (x : ℤ × ℤ) : lineNormal m₁ m₂ 0 x = Prod.det m₁ x := by
  simp [lineNormal]

/-- The normal of `ℝm₂` in `M` is `det(·, m₂)`. -/
@[simp]
theorem lineNormal_one_apply (x : ℤ × ℤ) : lineNormal m₁ m₂ 1 x = Prod.det x m₂ := by
  simp [lineNormal]

/-- The normals `e₂*` of the line `ℝm₁` and `e₁*` of the line `ℝm₂` in `ℓ⁻¹M₀`. -/
def sublatticeLineNormal : Fin 2 → ℤ × ℤ →+ ℤ := ![AddMonoidHom.snd ℤ ℤ, AddMonoidHom.fst ℤ ℤ]

/-- The normal of `ℝm₁` in `ℓ⁻¹M₀` is `e₂*`. -/
@[simp]
theorem sublatticeLineNormal_zero : sublatticeLineNormal 0 = AddMonoidHom.snd ℤ ℤ := by
  simp [sublatticeLineNormal]

/-- The normal of `ℝm₂` in `ℓ⁻¹M₀` is `e₁*`. -/
@[simp]
theorem sublatticeLineNormal_one : sublatticeLineNormal 1 = AddMonoidHom.fst ℤ ℤ := by
  simp [sublatticeLineNormal]

/-- The normal of `ℝm_i` in `M` vanishes on `m_i`. -/
theorem lineNormal_apply_coord_finTwoProd (i : Fin 2) :
    lineNormal m₁ m₂ i (coord m₁ m₂ (Module.Basis.finTwoProd ℤ i)) = 0 := by
  fin_cases i <;> simp [Prod.det_apply, mul_comm]

/-- The normal of `ℝm_i` in `ℓ⁻¹M₀` vanishes on the coordinates of `m_i`. -/
theorem sublatticeLineNormal_apply_sublatticeCoord_finTwoProd (i : Fin 2) :
    sublatticeLineNormal i (sublatticeCoord m₁ m₂ (Module.Basis.finTwoProd ℤ i)) = 0 := by
  fin_cases i <;> simp

/-- The normals of the lines in `ℓ⁻¹M₀` restrict along `M ⊆ ℓ⁻¹M₀` to their normals in `M`. -/
theorem sublatticeLineNormal_apply_change (i : Fin 2) (x : ℤ × ℤ) :
    sublatticeLineNormal i (change m₁ m₂ x) = lineNormal m₁ m₂ i x := by
  fin_cases i <;> simp

variable {m₁ m₂}

/-- The normals of the lines in `M` are nonzero when `m₁` and `m₂` are independent. -/
theorem lineNormal_ne_zero (hD : Prod.det m₁ m₂ ≠ 0) (i : Fin 2) : lineNormal m₁ m₂ i ≠ 0 := by
  intro h0
  fin_cases i
  · exact hD (by simpa using DFunLike.congr_fun h0 m₂)
  · exact hD (by simpa using DFunLike.congr_fun h0 m₁)

/-- The normals of the lines in `ℓ⁻¹M₀` are nonzero. -/
theorem sublatticeLineNormal_ne_zero (i : Fin 2) : sublatticeLineNormal i ≠ 0 := fun h0 => by
  fin_cases i
  · simpa using DFunLike.congr_fun h0 (0, 1)
  · simpa using DFunLike.congr_fun h0 (1, 0)

/-- The normal map sends the normals of the lines `ℝm_i` in `M` to their normals in `ℓ⁻¹M₀`, with
comparison scalar one. -/
theorem normalMap_lineNormal_and_normalScalar_lineNormal (hD : 0 < Prod.det m₁ m₂) (i : Fin 2) :
    normalMap m₁ m₂ (lineNormal m₁ m₂ i) = sublatticeLineNormal i ∧
      normalScalar m₁ m₂ (lineNormal m₁ m₂ i) = 1 := by
  have hD' : ((Prod.det m₁ m₂).natAbs : ℤ) = Prod.det m₁ m₂ := Int.natAbs_of_nonneg hD.le
  have hQ : (Prod.det m₁ m₂ : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have h₀₁ : lineNormal m₁ m₂ 0 m₁ = 0 := by rw [lineNormal_zero_apply, Prod.isAlt_det.self_eq_zero]
  have h₁₂ : lineNormal m₁ m₂ 1 m₂ = 0 := by rw [lineNormal_one_apply, Prod.isAlt_det.self_eq_zero]
  fin_cases i
  · obtain ⟨h, hs⟩ := normalMap_eq_and_normalScalar_eq (m₁ := m₁) (m₂ := m₂)
      (μ := lineNormal m₁ m₂ 0) (a := 0) (b := 1)
      (by rw [normalContent, h₀₁, lineNormal_zero_apply, Int.gcd_zero_left, hD']) hD.ne'
      (by rw [h₀₁, zero_mul]) (by rw [lineNormal_zero_apply, one_mul])
    rw [div_self hQ] at hs
    exact ⟨by simpa using h, by simpa using hs⟩
  · obtain ⟨h, hs⟩ := normalMap_eq_and_normalScalar_eq (m₁ := m₁) (m₂ := m₂)
      (μ := lineNormal m₁ m₂ 1) (a := 1) (b := 0)
      (by rw [normalContent, h₁₂, lineNormal_one_apply, Int.gcd_zero_right, hD']) hD.ne'
      (by rw [lineNormal_one_apply, one_mul]) (by rw [h₁₂, zero_mul])
    rw [div_self hQ] at hs
    exact ⟨by simpa using h, by simpa using hs⟩

/-- The normal map sends the normals of the lines `ℝm_i` in `M` to their normals in `ℓ⁻¹M₀`. -/
theorem normalMap_lineNormal (hD : 0 < Prod.det m₁ m₂) (i : Fin 2) :
    normalMap m₁ m₂ (lineNormal m₁ m₂ i) = sublatticeLineNormal i :=
  (normalMap_lineNormal_and_normalScalar_lineNormal hD i).1

/-- The normals of the lines `ℝm_i` in `M` have comparison scalar one. -/
theorem normalScalar_lineNormal (hD : 0 < Prod.det m₁ m₂) (i : Fin 2) :
    normalScalar m₁ m₂ (lineNormal m₁ m₂ i) = 1 :=
  (normalMap_lineNormal_and_normalScalar_lineNormal hD i).2

section Ray

variable {p q : ℤ} {m : ℤ × ℤ} {r : ℕ}

/-- For `r • m = p • m₁ + q • m₂`, the normal `det(·, m)` of `ℝm` on `a • m₁ + b • m₂` is
`det(m₁, m₂) det((a, b), (p, q)) / r`. -/
theorem natCast_mul_normal_coord (hm : r • m = p • m₁ + q • m₂) (x : ℤ × ℤ) :
    (r : ℤ) * normal m (coord m₁ m₂ x) = Prod.det m₁ m₂ * Prod.det x (p, q) := by
  have h : (r : ℤ) * normal m (coord m₁ m₂ x) = Prod.det (coord m₁ m₂ x) (r • m) := by
    rw [normal_apply, map_nsmul, nsmul_eq_mul]
  rw [h, hm, coord_apply]
  simp only [Prod.det_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- For `r • m = p • m₁ + q • m₂`, the normal `det(·, (p, q))` of `ℓ⁻¹M₀` restricts along
`M ⊆ ℓ⁻¹M₀` to `r` times the normal `det(·, m)` of `M`. -/
theorem normal_apply_change (hm : r • m = p • m₁ + q • m₂) (x : ℤ × ℤ) :
    normal (p, q) (change m₁ m₂ x) = r * normal m x := by
  have h : (r : ℤ) * normal m x = Prod.det x (r • m) := by
    rw [normal_apply, map_nsmul, nsmul_eq_mul]
  rw [h, hm, normal_apply, change_apply]
  simp only [Prod.det_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- A pair of coprime integers is a primitive vector of `ℤ²`. -/
theorem isPrimitive_mk_of_isCoprime (hpq : IsCoprime p q) :
    TauCeti.IsPrimitive ((p, q) : ℤ × ℤ) := by
  have h := (Module.Basis.finTwoProd ℤ).isPrimitive_zsmul_add_zsmul (i := 0) (j := 1)
    zero_ne_one hpq
  simpa using h

/-- If `p` and `q` are coprime, the integral vectors `x` with `det(x, (p, q)) = 0` are the
integral multiples of `(p, q)`. -/
theorem exists_eq_zsmul_of_det_eq_zero (hpq : IsCoprime p q) {x : ℤ × ℤ}
    (hx : Prod.det x (p, q) = 0) : ∃ k : ℤ, x = k • (p, q) := by
  obtain ⟨u, v, huv⟩ := hpq
  rw [Prod.det_apply] at hx
  dsimp only at hx
  refine ⟨u * x.1 + v * x.2, Prod.ext ?_ ?_⟩
  · simp only [Prod.smul_fst, smul_eq_mul]
    linear_combination (-1 : ℤ) * x.1 * huv + v * hx
  · simp only [Prod.smul_snd, smul_eq_mul]
    linear_combination (-1 : ℤ) * x.2 * huv - u * hx

/-- **The line `ℝm°` in coefficient coordinates.** Let `m₁, m₂` be independent, `p, q` coprime and
`r • m = p • m₁ + q • m₂`. If the normal `det(·, m)` vanishes on `a • m₁ + b • m₂`, then `(a, b)` is
an integral multiple of `(p, q)`. -/
theorem exists_eq_zsmul_of_normal_coord_eq_zero (hD : Prod.det m₁ m₂ ≠ 0) (hpq : IsCoprime p q)
    (hm : r • m = p • m₁ + q • m₂) {x : ℤ × ℤ} (hx : normal m (coord m₁ m₂ x) = 0) :
    ∃ k : ℤ, x = k • (p, q) := by
  have h := natCast_mul_normal_coord hm x
  rw [hx, mul_zero, eq_comm] at h
  exact exists_eq_zsmul_of_det_eq_zero hpq ((mul_eq_zero.mp h).resolve_left hD)

/-- If `p` and `q` are coprime, `r • m = p • m₁ + q • m₂` forces `r ≠ 0` for independent `m₁, m₂`.
-/
theorem ne_zero_of_nsmul_eq (hD : Prod.det m₁ m₂ ≠ 0) (hpq : IsCoprime p q)
    (hm : r • m = p • m₁ + q • m₂) : r ≠ 0 := by
  rintro rfl
  have h₁ := natCast_mul_normal_coord hm (1, 0)
  have h₂ := natCast_mul_normal_coord hm (0, 1)
  rw [Nat.cast_zero, zero_mul, eq_comm, mul_eq_zero, or_iff_right hD, Prod.det_apply] at h₁ h₂
  simp only [one_mul, zero_mul, sub_zero, zero_sub, neg_eq_zero] at h₁ h₂
  rw [h₁, h₂] at hpq
  exact not_isCoprime_zero_zero hpq

/-- **The normal of `ℝm°` under the lattice change.** Let `m₁, m₂` be independent with
`det(m₁, m₂) > 0`, let `p, q` be coprime and `r • m = p • m₁ + q • m₂`. The normal map sends the
normal `det(·, m)` of `ℝm` in `M` to the normal `det(·, (p, q))` of `ℝm°` in `ℓ⁻¹M₀`, with
comparison scalar `r`. -/
theorem normalMap_normal_and_normalScalar_normal (hD : 0 < Prod.det m₁ m₂) (hpq : IsCoprime p q)
    (hm : r • m = p • m₁ + q • m₂) :
    normalMap m₁ m₂ (normal m) = normal (p, q) ∧ normalScalar m₁ m₂ (normal m) = r := by
  /- With `c = gcd(det(m₁, m), det(m₂, m))`, the identities `r det(m₁, m) = q ℓ` and
  `r det(m₂, m) = -p ℓ` give `r c = ℓ gcd(q, p) = ℓ`, hence `det(m₁, m) = q c` and
  `det(m₂, m) = -p c`. -/
  have hr : (r : ℤ) ≠ 0 := by exact_mod_cast ne_zero_of_nsmul_eq hD.ne' hpq hm
  have h₁ : (r : ℤ) * normal m m₁ = q * Prod.det m₁ m₂ := by
    simpa [Prod.det_apply, mul_comm] using natCast_mul_normal_coord hm (1, 0)
  have h₂ : (r : ℤ) * normal m m₂ = -p * Prod.det m₁ m₂ := by
    simpa [Prod.det_apply, mul_comm] using natCast_mul_normal_coord hm (0, 1)
  have hc : (r : ℤ) * normalContent m₁ m₂ (normal m) = Prod.det m₁ m₂ := by
    have h := Int.gcd_mul_left (r : ℤ) (normal m m₁) (normal m m₂)
    rw [h₁, h₂, mul_comm q, mul_comm (-p), Int.gcd_mul_left, Int.gcd_neg,
      Int.isCoprime_iff_gcd_eq_one.mp hpq.symm, mul_one, Int.natAbs_natCast] at h
    rw [normalContent, ← Int.natAbs_of_nonneg hD.le]
    exact_mod_cast h.symm
  have hc0 : (normalContent m₁ m₂ (normal m) : ℤ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc
    exact hD.ne hc
  obtain ⟨h, hs⟩ := normalMap_eq_and_normalScalar_eq (m₁ := m₁) (m₂ := m₂) (μ := normal m)
    (a := q) (b := -p) rfl hc0
    (mul_left_cancel₀ hr (by rw [h₁, ← hc]; ring))
    (mul_left_cancel₀ hr (by rw [h₂, ← hc]; ring))
  refine ⟨AddMonoidHom.ext fun x => ?_, ?_⟩
  · rw [h, normal_apply, Prod.det_apply]
    simp only [AddMonoidHom.add_apply, AddMonoidHom.smul_apply, AddMonoidHom.coe_fst,
      AddMonoidHom.coe_snd, smul_eq_mul]
    ring
  · rw [hs, ← hc, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
      mul_div_cancel_right₀ _ (by exact_mod_cast hc0)]

/-- The normal map sends the normal `det(·, m)` of `ℝm` in `M` to the normal `det(·, (p, q))` of
`ℝm°` in `ℓ⁻¹M₀`, for `r • m = p • m₁ + q • m₂` with `p, q` coprime and `det(m₁, m₂) > 0`. -/
theorem normalMap_normal (hD : 0 < Prod.det m₁ m₂) (hpq : IsCoprime p q)
    (hm : r • m = p • m₁ + q • m₂) : normalMap m₁ m₂ (normal m) = normal (p, q) :=
  (normalMap_normal_and_normalScalar_normal hD hpq hm).1

/-- The comparison scalar of the normal `det(·, m)` of `ℝm` is `r`, for
`r • m = p • m₁ + q • m₂` with `p, q` coprime and `det(m₁, m₂) > 0`. -/
theorem normalScalar_normal (hD : 0 < Prod.det m₁ m₂) (hpq : IsCoprime p q)
    (hm : r • m = p • m₁ + q • m₂) : normalScalar m₁ m₂ (normal m) = r :=
  (normalMap_normal_and_normalScalar_normal hD hpq hm).2

end Ray

variable {m : ℤ × ℤ}

/-- The normal `det(·, m)` of a nonzero vector `m` is nonzero at `(m₂, -m₁)`. -/
theorem normal_apply_ne_zero (hm : m ≠ 0) : normal m (m.2, -m.1) ≠ 0 := by
  rw [normal_apply, Prod.det_apply]
  intro h0
  apply hm
  have h₁ : m.1 = 0 := by nlinarith
  have h₂ : m.2 = 0 := by nlinarith
  exact Prod.ext h₁ h₂

/-- An additive map on `ℤ²` is determined by its values on the coordinate vectors. -/
theorem apply_eq_add (μ : ℤ × ℤ →+ ℤ) (x : ℤ × ℤ) : μ x = x.1 * μ (1, 0) + x.2 * μ (0, 1) := by
  simpa using apply_coord (1, 0) (0, 1) μ x

/-- If `m` is primitive, every integral normal vanishing on `m` is an integral multiple of
`det(·, m)`. -/
theorem exists_eq_zsmul_normal (hm : TauCeti.IsPrimitive m) {μ : ℤ × ℤ →+ ℤ} (hμ : μ m = 0) :
    ∃ c : ℤ, μ = c • normal m := by
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hm
  have hf' : m.1 * f (1, 0) + m.2 * f (0, 1) = 1 := by
    have h := apply_eq_add f.toAddMonoidHom m
    simp only [LinearMap.toAddMonoidHom_coe] at h
    rw [← h, hf]
  rw [apply_eq_add] at hμ
  refine ⟨μ (1, 0) * f (0, 1) - μ (0, 1) * f (1, 0), AddMonoidHom.ext fun x => ?_⟩
  rw [apply_eq_add, AddMonoidHom.smul_apply, normal_apply, Prod.det_apply, smul_eq_mul]
  linear_combination (x.1 * f (1, 0) + x.2 * f (0, 1)) * hμ -
    (x.1 * μ (1, 0) + x.2 * μ (0, 1)) * hf'

end Mei.RankTwoLatticeChange
