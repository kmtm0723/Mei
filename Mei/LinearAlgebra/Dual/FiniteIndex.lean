/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Algebra.Rat

/-!
# Rational characters along finite-index embeddings

An injective additive map with finite-index image induces an equivalence on
characters valued in a rational algebra. The forward map extends a
character across the embedding; the inverse restricts it. No freeness or finite
rank assumption on the additive groups is needed.

The extension divides evaluation on an index multiple by that index. The index multiple is
inverted by `AddMonoidHom.indexInverse`, the additive map `y ↦ f⁻¹(c • y)` for the index `c`
of the image. Composing with it turns an integral character `m` into the integral character
`c` times the rational inverse dual of `m`. We use Mathlib's `AddMonoidHom.ofInjective` to
invert the map onto its range and `LinearMap.lcomp` to bundle character restriction. This is
the rational inverse dual needed to transport logarithmic derivations through lattice
embeddings.
-/

public section

noncomputable section

namespace AddMonoidHom

variable {M N R : Type*} [AddCommGroup M] [AddCommGroup N]
  [Ring R] [Algebra ℚ R]

/-- For an injective additive map `f` whose image has index `c`, the additive map
`y ↦ f⁻¹(c • y)`. It inverts `f` up to the factor `c` on both sides; for an image of infinite
index, `c = 0` and the map is zero. -/
def indexInverse (f : M →+ N) (hf : Function.Injective f) : N →+ M :=
  (ofInjective hf).symm.toAddMonoidHom.comp
    ((nsmulAddMonoidHom f.range.index).codRestrict f.range (fun y => f.range.nsmul_index_mem y))

/-- `f` sends `f⁻¹(c • y)` back to `c • y`. -/
@[simp]
theorem map_indexInverse (f : M →+ N) (hf : Function.Injective f) (y : N) :
    f (f.indexInverse hf y) = f.range.index • y :=
  apply_ofInjective_symm hf _

/-- On the image of `f`, the index inverse is multiplication by the index. -/
@[simp]
theorem indexInverse_map (f : M →+ N) (hf : Function.Injective f) (x : M) :
    f.indexInverse hf (f x) = f.range.index • x :=
  hf (by rw [map_indexInverse, map_nsmul])

/-- Composing a character with the index inverse multiplies its values on the image by
the index. For integral characters this is the integral index multiple of the inverse dual. -/
theorem comp_indexInverse_apply_map {A : Type*} [AddCommGroup A] (f : M →+ N)
    (hf : Function.Injective f) (m : M →+ A) (x : M) :
    m.comp (f.indexInverse hf) (f x) = f.range.index • m x := by
  rw [comp_apply, indexInverse_map, map_nsmul]

/-- Extend rational-algebra-valued characters through an injective additive map
with finite-index image. Its inverse is precomposition with the embedding. -/
def rationalDualEquiv (f : M →+ N) (hf : Function.Injective f) [f.range.FiniteIndex] :
    (M →+ R) ≃ₗ[R] (N →+ R) := by
  let restriction : (N →+ R) →ₗ[R] (M →+ R) :=
    (addMonoidHomLequivInt R).symm.toLinearMap.comp
      ((LinearMap.lcomp R R f.toIntLinearMap).comp (addMonoidHomLequivInt R).toLinearMap)
  have restriction_apply (a : N →+ R) (x : M) : restriction a x = a (f x) := rfl
  let c := f.range.index
  have hc : (c : ℚ) ≠ 0 := by exact_mod_cast (f.range.index_ne_zero)
  let g : N →+ M := f.indexInverse hf
  have hfg (y : N) : f (g y) = c • y := f.map_indexInverse hf y
  have hgf (x : M) : g (f x) = c • x := f.indexInverse_map hf x
  refine (LinearEquiv.ofBijective restriction ⟨?_, ?_⟩).symm
  · intro a b hab
    ext y
    have h : c • a y = c • b y := by
      simpa only [restriction_apply, hfg, map_nsmul] using congrArg (fun m : M →+ R => m (g y)) hab
    have h' : (c : ℚ) • a y = (c : ℚ) • b y := by
      simpa only [Nat.cast_smul_eq_nsmul ℚ] using h
    simpa only [inv_smul_smul₀ hc] using congrArg (fun r : R => (c : ℚ)⁻¹ • r) h'
  · intro m
    refine ⟨(c : ℚ)⁻¹ • m.comp g, ?_⟩
    ext x
    rw [restriction_apply, smul_apply, comp_apply, hgf, map_nsmul,
      ← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ hc]

/-- The inverse of rational character extension is restriction. -/
@[simp]
theorem rationalDualEquiv_symm_apply (f : M →+ N) (hf : Function.Injective f)
    [f.range.FiniteIndex] (m : N →+ R) :
    (f.rationalDualEquiv hf).symm m = m.comp f := (rfl)

/-- Restricting the extended character recovers the original character. -/
@[simp]
theorem rationalDualEquiv_apply_map (f : M →+ N) (hf : Function.Injective f)
    [f.range.FiniteIndex] (m : M →+ R) (x : M) :
    f.rationalDualEquiv hf m (f x) = m x := by
  have h := (f.rationalDualEquiv hf).symm_apply_apply m
  rw [rationalDualEquiv_symm_apply] at h
  exact congrArg (fun a : M →+ R => a x) h

/-- An extension is characterized by its restriction to the source. -/
theorem rationalDualEquiv_eq_iff (f : M →+ N) (hf : Function.Injective f)
    [f.range.FiniteIndex] (m : M →+ R) (a : N →+ R) :
    f.rationalDualEquiv hf m = a ↔ a.comp f = m := by
  rw [← rationalDualEquiv_symm_apply (R := R) f hf]
  constructor
  · rintro rfl
    exact (f.rationalDualEquiv hf).symm_apply_apply m
  · intro h
    rw [← h]
    exact (f.rationalDualEquiv hf).apply_symm_apply a

/-- Evaluate an extended character by dividing any nonzero integral multiple
that lies in the image of the embedding. -/
theorem rationalDualEquiv_apply_of_map_eq_nsmul (f : M →+ N) (hf : Function.Injective f)
    [f.range.FiniteIndex] (m : M →+ R) {x : M} {y : N} {k : ℕ}
    (hk : k ≠ 0) (h : f x = k • y) :
    f.rationalDualEquiv hf m y = (k : ℚ)⁻¹ • m x := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have he : (k : ℚ) • f.rationalDualEquiv hf m y = m x := by
    rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← h, rationalDualEquiv_apply_map]
  simpa only [inv_smul_smul₀ hk'] using congrArg (fun r : R => (k : ℚ)⁻¹ • r) he

/-- The extension of an integral character `m` is `q⁻¹` times any integral character `m'` of
the target with `m' ∘ f = q • m`. -/
theorem rationalDualEquiv_intCast_comp (f : M →+ N) (hf : Function.Injective f)
    [f.range.FiniteIndex] {m : M →+ ℤ} {m' : N →+ ℤ} {q : ℚ} (hq : q ≠ 0)
    (h : ∀ x, (m' (f x) : ℚ) = q * m x) :
    f.rationalDualEquiv hf ((Int.castAddHom R).comp m) = q⁻¹ • (Int.castAddHom R).comp m' := by
  rw [rationalDualEquiv_eq_iff]
  ext x
  have hx : ((m' (f x) : ℤ) : R) = algebraMap ℚ R (q * m x) := by
    rw [← h, map_intCast]
  simp only [comp_apply, smul_apply, Int.coe_castAddHom, hx,
    Algebra.smul_def, ← map_mul, inv_mul_cancel_left₀ hq, map_intCast]

end AddMonoidHom
