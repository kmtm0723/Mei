/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Module.Primitive
public import Mei.LinearAlgebra.Dual.Index

/-!
# A sublattice of index two in `ℤ²`

Let `M = ℤ²` and let `M₀` be the sublattice spanned by `m₁ = (1, 0)` and `m₂ = (1, 2)`
(`Mei.DualLatticeIndex.Examples.sublattice`). Then:

* `M₀` has index `ℓ = 2` in `M` (`Mei.DualLatticeIndex.Examples.index_sublattice`);
* `m₀ = m₁ + m₂ = (2, 2)` is primitive in `M₀`
  (`Mei.DualLatticeIndex.Examples.isPrimitive_generatorSum`) and equals `2 • (1, 1)` with
  `(1, 1)` primitive in `M` (`Mei.DualLatticeIndex.Examples.coe_generatorSum_eq_nsmul`);
* `r = 2` is the only `r` with `m₀ = r • m` for a primitive `m ∈ M`
  (`Mei.DualLatticeIndex.Examples.eq_two_of_coe_generatorSum_eq_nsmul`);
* `[m₀⊥ ∩ Dual ℤ M₀ : m₀⊥ ∩ Dual ℤ M] = 1`
  (`Mei.DualLatticeIndex.Examples.relIndex_ker_eval_generatorSum`), so the primitive normals of
  `ℝ m₀` in `Dual ℤ M` and `Dual ℤ M₀` agree up to sign
  (`Mei.DualLatticeIndex.Examples.dualRestrict_eq_or_eq_neg`).

This is the lattice change of Burcroff–Lee–Mou, *Positivity of generalized cluster scattering
diagrams*, Theorem 9.5 (arXiv:2503.03719v1), for `m₁ = (1, 0)` and `m₂ = (1, 2)`, where the
index `ℓ = r · [m₀⊥ ∩ Dual ℤ M₀ : m₀⊥ ∩ Dual ℤ M]` splits with outer power `r = 2` and
normal ratio `1`.
-/

public section

noncomputable section

namespace Mei.DualLatticeIndex.Examples

open Module

/-- The vectors `m₁ = (1, 0)` and `m₂ = (1, 2)` of `ℤ²`. -/
def generators : Fin 2 → Fin 2 → ℤ := ![![1, 0], ![1, 2]]

@[simp]
theorem generators_zero : generators 0 = ![1, 0] := (rfl)

@[simp]
theorem generators_one : generators 1 = ![1, 2] := (rfl)

theorem linearIndependent_generators : LinearIndependent ℤ generators :=
  Matrix.linearIndependent_rows_of_det_ne_zero (A := !![(1 : ℤ), 0; 1, 2])
    (by norm_num [Matrix.det_fin_two])

/-- The sublattice `M₀` of `ℤ²` spanned by `m₁ = (1, 0)` and `m₂ = (1, 2)`. -/
def sublattice : Submodule ℤ (Fin 2 → ℤ) := Submodule.span ℤ (Set.range generators)

/-- The basis `m₁, m₂` of `M₀`. -/
def sublatticeBasis : Basis (Fin 2) ℤ sublattice := Basis.span linearIndependent_generators

@[simp]
theorem coe_sublatticeBasis (i : Fin 2) : (sublatticeBasis i : Fin 2 → ℤ) = generators i :=
  congrArg Subtype.val (Basis.span_apply linearIndependent_generators i)

/-- The sublattice spanned by `(1, 0)` and `(1, 2)` has index `ℓ = 2` in `ℤ²`. -/
@[simp]
theorem index_sublattice : sublattice.toAddSubgroup.index = 2 := by
  rw [AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin 2)) _ sublatticeBasis, Basis.det_apply]
  simp only [Matrix.det_fin_two, Basis.toMatrix_apply, Pi.basisFun_repr]
  rw [coe_sublatticeBasis, coe_sublatticeBasis]
  simp

instance : sublattice.toAddSubgroup.FiniteIndex :=
  ⟨by simp⟩

/-- The vector `m₀ = m₁ + m₂` of `M₀`. -/
def generatorSum : sublattice := sublatticeBasis 0 + sublatticeBasis 1

@[simp]
theorem coe_generatorSum : (generatorSum : Fin 2 → ℤ) = ![2, 2] := by
  ext i
  fin_cases i <;> simp [generatorSum]

/-- `m₀ = (2, 2)` is `2 • (1, 1)`. -/
theorem coe_generatorSum_eq_nsmul : (generatorSum : Fin 2 → ℤ) = (2 : ℕ) • ![1, 1] := by
  ext i
  fin_cases i <;> simp

theorem generatorSum_ne_zero : generatorSum ≠ 0 := by
  intro h
  simpa [h] using congrFun coe_generatorSum 0

/-- `m₀ = m₁ + m₂` is primitive in `M₀`, its coefficients `(1, 1)` being coprime. -/
theorem isPrimitive_generatorSum : TauCeti.IsPrimitive generatorSum := by
  simpa [generatorSum] using sublatticeBasis.isPrimitive_zsmul_add_zsmul (i := 0) (j := 1)
    (p := 1) (q := 1) (by decide) isCoprime_one_left

/-- The vector `(1, 1)` is primitive in `ℤ²`. -/
theorem isPrimitive_one_one : TauCeti.IsPrimitive (![1, 1] : Fin 2 → ℤ) :=
  TauCeti.isPrimitive_def.mpr ⟨(Pi.basisFun ℤ (Fin 2)).coord 0, by simp⟩

/-- The index `[m₀⊥ ∩ Dual ℤ M₀ : m₀⊥ ∩ Dual ℤ M]` of the annihilators of `m₀ = (2, 2)` is `1`. -/
@[simp]
theorem relIndex_ker_eval_generatorSum :
    (LinearMap.range sublattice.dualRestrict).toAddSubgroup.relIndex
      (LinearMap.ker (Dual.eval ℤ sublattice generatorSum)).toAddSubgroup = 1 := by
  have := Submodule.index_eq_mul_relIndex_ker_eval sublattice isPrimitive_generatorSum
    isPrimitive_one_one coe_generatorSum_eq_nsmul
  rw [index_sublattice] at this
  omega

/-- The only `r` with `m₀ = r • m` for a primitive vector `m` of `ℤ²` is `r = 2`. -/
theorem eq_two_of_coe_generatorSum_eq_nsmul {m : Fin 2 → ℤ} (hm : TauCeti.IsPrimitive m)
    {r : ℕ} (hr : (generatorSum : Fin 2 → ℤ) = r • m) : r = 2 := by
  have := Submodule.index_eq_mul_relIndex_ker_eval sublattice isPrimitive_generatorSum hm hr
  rwa [index_sublattice, relIndex_ker_eval_generatorSum, mul_one, eq_comm] at this

/-- The primitive normals of the line `ℝ m₀` in `Dual ℤ ℤ²` and in `Dual ℤ M₀` agree up to
sign: the restriction to `M₀` of a primitive functional vanishing at `m₀` is `±` any primitive
functional on `M₀` vanishing at `m₀`. -/
theorem dualRestrict_eq_or_eq_neg {n₀ : Dual ℤ sublattice} (hn₀ : TauCeti.IsPrimitive n₀)
    (hn₀m₀ : n₀ generatorSum = 0) {n : Dual ℤ (Fin 2 → ℤ)} (hn : TauCeti.IsPrimitive n)
    (hnm₀ : n generatorSum = 0) :
    sublattice.dualRestrict n = n₀ ∨ sublattice.dualRestrict n = -n₀ := by
  obtain ⟨k, hk, hk₁⟩ := Submodule.exists_dualRestrict_eq_zsmul_natAbs_eq_relIndex (by simp)
    sublattice generatorSum_ne_zero hn₀ hn₀m₀ hn hnm₀
  rw [relIndex_ker_eval_generatorSum] at hk₁
  rcases Int.natAbs_eq_iff.mp hk₁ with rfl | rfl <;> simp [hk]

end Mei.DualLatticeIndex.Examples
