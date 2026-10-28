/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Lattice

/-!
# Real extension of integral lattices

Real extension sends integer multiples of integral characters to the corresponding
real multiples. This identity lets rational-normal constructions clear denominators.
An equivalence of integral lattices extends to a real linear equivalence. Its
linear map is the existing scalar extension, and extension respects identity,
inverse and composition without choosing a new basis.
-/

public section

namespace TauCeti.Toric.IsIntegralLattice

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- Real extension carries integer multiples of characters to real scalar multiples. -/
theorem realCharacter_int_smul (h : IsIntegralLattice i) (a : ℤ)
    (m : Module.Dual ℤ N) :
    h.realCharacter (a • m).toAddMonoidHom =
      (a : ℝ) • h.realCharacter m.toAddMonoidHom := by
  symm
  apply h.eq_realCharacter
  intro n
  simp

section Equiv

variable {N' N'' V' V'' : Type*} [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V'] [AddCommGroup V''] [Module ℝ V'] [Module ℝ V'']
  {i' : N' →+ V'} {i'' : N'' →+ V''}

/-- Extend an equivalence of integral lattices to an equivalence of real vector spaces. -/
noncomputable def extendEquiv (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (σ : N ≃+ N') : V ≃ₗ[ℝ] V' :=
  LinearEquiv.ofLinearMap (h.extend i' σ.toAddMonoidHom)
    (h'.extend i σ.symm.toAddMonoidHom)
    ((h'.eq_extend (f := AddMonoidHom.id N') (fun n => by simp)).trans h'.extend_id)
    ((h.eq_extend (f := AddMonoidHom.id N) (fun n => by simp)).trans h.extend_id)

/-- The underlying linear map is the scalar extension of the lattice homomorphism. -/
@[simp]
theorem extendEquiv_toLinearMap (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (σ : N ≃+ N') :
    (h.extendEquiv h' σ).toLinearMap = h.extend i' σ.toAddMonoidHom := (rfl)

/-- The extended equivalence evaluates by the scalar extension of the lattice map. -/
@[simp]
theorem coe_extendEquiv (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (σ : N ≃+ N') : ⇑(h.extendEquiv h' σ) = h.extend i' σ.toAddMonoidHom := (rfl)

/-- Real extension takes the identity lattice equivalence to the identity linear equivalence. -/
@[simp]
theorem extendEquiv_refl (h : IsIntegralLattice i) :
    h.extendEquiv h (AddEquiv.refl N) = LinearEquiv.refl ℝ V := by
  apply LinearEquiv.toLinearMap_injective
  simp

/-- The inverse of the real extension extends the inverse lattice equivalence. -/
@[simp]
theorem extendEquiv_symm (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (σ : N ≃+ N') : (h.extendEquiv h' σ).symm = h'.extendEquiv h σ.symm := by
  ext x
  rfl

/-- Real extension respects composition between arbitrary integral lattices. -/
@[simp]
theorem extendEquiv_trans (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (h'' : IsIntegralLattice i'') (σ : N ≃+ N') (τ : N' ≃+ N'') :
    (h.extendEquiv h' σ).trans (h'.extendEquiv h'' τ) =
      h.extendEquiv h'' (σ.trans τ) := by
  ext x
  simpa only [LinearEquiv.trans_apply, coe_extendEquiv, LinearMap.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddEquiv.toAddMonoidHom_trans] using
    congrArg (fun F : V →ₗ[ℝ] V'' => F x)
      (h.extend_comp h' σ.toAddMonoidHom τ.toAddMonoidHom)

end Equiv

end TauCeti.Toric.IsIntegralLattice
