/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Toric.Algebraic.Lattice
public import Mathlib.GroupTheory.Index
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Real extension of finite-index lattice embeddings

An additive map of integral lattices whose image has finite index has surjective real
extension, since the extension hits every index multiple of a lattice vector. An injective
finite-index map therefore extends to a real linear equivalence, continuous when the real
spaces are normed. Its inverse is in general not the extension of a lattice map.

Real extension also transports rational proportionality of integral characters: if an
integral character `m'` of the target restricts along `f` to `q • m`, then the real extension
of `m'` pulls back to `q` times that of `m`.
-/

public section

noncomputable section

namespace TauCeti.Toric.IsIntegralLattice

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}

/-- Real extension of a lattice map with finite-index image is surjective. -/
theorem extend_surjective_of_finiteIndex (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (f : N →+ N') [f.range.FiniteIndex] : Function.Surjective (h.extend i' f) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← h'.span_range_eq_top, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := f.range.nsmul_index_mem y
  have hc : (f.range.index : ℝ) ≠ 0 := by exact_mod_cast f.range.index_ne_zero
  have hm : (f.range.index : ℝ) • i' y ∈ LinearMap.range (h.extend i' f) :=
    ⟨i x, by rw [extend_apply, hx, map_nsmul, Nat.cast_smul_eq_nsmul]⟩
  simpa only [inv_smul_smul₀ hc, SetLike.mem_coe] using
    (LinearMap.range (h.extend i' f)).smul_mem (f.range.index : ℝ)⁻¹ hm

/-- Extend an injective lattice map with finite-index image to a real linear equivalence. -/
def extendEquivOfFiniteIndex (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (f : N →+ N') (hf : Function.Injective f) [f.range.FiniteIndex] : V ≃ₗ[ℝ] V' :=
  LinearEquiv.ofBijective (h.extend i' f)
    ⟨h.extend_injective h' f hf, h.extend_surjective_of_finiteIndex h' f⟩

/-- The equivalence evaluates by the real extension of the lattice map. -/
@[simp]
theorem coe_extendEquivOfFiniteIndex (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (f : N →+ N') (hf : Function.Injective f) [f.range.FiniteIndex] :
    ⇑(h.extendEquivOfFiniteIndex h' f hf) = h.extend i' f := (rfl)

/-- The underlying linear map is the real extension of the lattice map. -/
@[simp]
theorem extendEquivOfFiniteIndex_toLinearMap (h : IsIntegralLattice i)
    (h' : IsIntegralLattice i') (f : N →+ N') (hf : Function.Injective f) [f.range.FiniteIndex] :
    (h.extendEquivOfFiniteIndex h' f hf).toLinearMap = h.extend i' f := (rfl)

section Normed

variable {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W'] [NormedSpace ℝ W'] {j : N →+ W} {j' : N' →+ W'}

/-- The real extension of an injective lattice map with finite-index image between normed
spaces, as a continuous affine equivalence. -/
def extendContinuousAffineEquivOfFiniteIndex (h : IsIntegralLattice j)
    (h' : IsIntegralLattice j') (f : N →+ N') (hf : Function.Injective f) [f.range.FiniteIndex] :
    W ≃ᴬ[ℝ] W' :=
  letI := h.finiteDimensional
  (h.extendEquivOfFiniteIndex h' f hf).toContinuousLinearEquiv.toContinuousAffineEquiv

/-- The continuous affine equivalence evaluates by the real extension of the lattice map. -/
@[simp]
theorem coe_extendContinuousAffineEquivOfFiniteIndex (h : IsIntegralLattice j)
    (h' : IsIntegralLattice j') (f : N →+ N') (hf : Function.Injective f) [f.range.FiniteIndex] :
    ⇑(h.extendContinuousAffineEquivOfFiniteIndex h' f hf) = h.extend j' f := (rfl)

/-- The linear part is the real linear equivalence extending the lattice map. -/
@[simp]
theorem extendContinuousAffineEquivOfFiniteIndex_linear (h : IsIntegralLattice j)
    (h' : IsIntegralLattice j') (f : N →+ N') (hf : Function.Injective f) [f.range.FiniteIndex] :
    (h.extendContinuousAffineEquivOfFiniteIndex h' f hf).toAffineEquiv.linear =
      h.extendEquivOfFiniteIndex h' f hf := (rfl)

end Normed

/-- If an integral character `m'` restricts along `f` to the rational multiple `q • m`, its
real extension pulls back along the real extension of `f` to `q` times that of `m`. -/
theorem realCharacter_comp_extend (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (f : N →+ N') {m : N →+ ℤ} {m' : N' →+ ℤ} {q : ℚ} (hq : ∀ x, (m' (f x) : ℚ) = q * m x) :
    (h'.realCharacter m').comp (h.extend i' f) = (q : ℝ) • h.realCharacter m := by
  refine h.isBaseChange.algHom_ext _ _ fun x => ?_
  have hx : (m' (f x) : ℝ) = (q : ℝ) * m x := by exact_mod_cast hq x
  simp [hx]

end TauCeti.Toric.IsIntegralLattice
