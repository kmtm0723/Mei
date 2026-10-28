/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted

/-!
# Homogeneous components of completed shifted modules

A homogeneous component of a completed shifted coefficient can be read from any
finite quotient retaining its relative degree. The quotient components descend
Mathlib's direct-sum projections, and compatibility with the existing quotient
tower makes their value independent of the chosen cutoff. All homogeneous
components together distinguish completed coefficients.

The shifted coefficient completion is the one used in Travis Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §2.1
(arXiv:1503.06183).
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] (p : Γ)

private def shiftedComponentLinear (q : Γ) : shiftedSubmodule ℳ d.monoid p →ₗ[R] ℳ q :=
  (DirectSum.component R Γ (fun q => ℳ q) q).comp
    ((DirectSum.decomposeLinearEquiv ℳ).toLinearMap.comp
      (shiftedSubmodule ℳ d.monoid p).subtype)

/-- The ambient degree-`q` component of a finite shifted quotient retaining that degree. -/
def shiftedQuotientComponent (q : Γ) (k : ℕ) (h : d.degree (q - p) ≤ k) :
    (d.shiftedFiltration ℳ p).quotient k →ₗ[R] ℳ q :=
  ((d.shiftedFiltration ℳ p).submodule (k + 1)).liftQ
    (d.shiftedComponentLinear ℳ p q) (by
      intro x hx
      apply Subtype.ext
      exact (d.mem_shiftedFiltration_iff ℳ p).mp hx q (by omega))

/-- On a representative, the quotient component is the original homogeneous projection. -/
@[simp]
theorem shiftedQuotientComponent_mk (q : Γ) (k : ℕ) (h : d.degree (q - p) ≤ k)
    (x : shiftedSubmodule ℳ d.monoid p) :
    d.shiftedQuotientComponent ℳ p q k h (Submodule.Quotient.mk x) =
      DirectSum.decompose ℳ (x : M) q := (rfl)

/-- Lowering the cutoff leaves every retained homogeneous component unchanged. -/
theorem shiftedQuotientComponent_transition (q : Γ) {k l : ℕ} (hkl : k ≤ l)
    (hk : d.degree (q - p) ≤ k) (hl : d.degree (q - p) ≤ l)
    (x : (d.shiftedFiltration ℳ p).quotient l) :
    d.shiftedQuotientComponent ℳ p q k hk ((d.shiftedFiltration ℳ p).transition hkl x) =
      d.shiftedQuotientComponent ℳ p q l hl x := by
  obtain ⟨x, rfl⟩ := ((d.shiftedFiltration ℳ p).submodule (l + 1)).mkQ_surjective x
  simp

/-- The ambient degree-`q` homogeneous component of a completed shifted coefficient. -/
def shiftedHomogeneousComponent (q : Γ) : d.ShiftedCoefficients ℳ p →ₗ[R] ℳ q :=
  (d.shiftedQuotientComponent ℳ p q (d.degree (q - p)).toNat (Int.self_le_toNat _)).comp
    ((d.shiftedFiltration ℳ p).projection (d.degree (q - p)).toNat)

/-- A completed component can be read at any cutoff that retains its relative degree. -/
theorem shiftedHomogeneousComponent_eq (q : Γ) (k : ℕ) (hk : d.degree (q - p) ≤ k)
    (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedHomogeneousComponent ℳ p q x =
      d.shiftedQuotientComponent ℳ p q k hk ((d.shiftedFiltration ℳ p).projection k x) := by
  have hkn : (d.degree (q - p)).toNat ≤ k := Int.toNat_le.mpr hk
  rw [shiftedHomogeneousComponent, LinearMap.comp_apply]
  rw [← (d.shiftedFiltration ℳ p).transition_projection hkn x]
  exact d.shiftedQuotientComponent_transition ℳ p q hkn (Int.self_le_toNat _) hk _

/-- The completed component of an original coefficient is its direct-sum component. -/
@[simp]
theorem shiftedHomogeneousComponent_of (q : Γ) (x : shiftedSubmodule ℳ d.monoid p) :
    d.shiftedHomogeneousComponent ℳ p q ((d.shiftedFiltration ℳ p).of x) =
      DirectSum.decompose ℳ (x : M) q := by
  rw [shiftedHomogeneousComponent, LinearMap.comp_apply, ModuleFiltration.projection_of,
    shiftedQuotientComponent_mk]

/-- Completed coefficients have no components outside the shifted support. -/
theorem shiftedHomogeneousComponent_eq_zero {q : Γ} (hq : q - p ∉ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) : d.shiftedHomogeneousComponent ℳ p q x = 0 := by
  let k := (d.degree (q - p)).toNat
  have hk : d.degree (q - p) ≤ k := Int.self_le_toNat _
  obtain ⟨a, ha⟩ := ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ_surjective
    ((d.shiftedFiltration ℳ p).projection k x)
  rw [d.shiftedHomogeneousComponent_eq ℳ p q k hk, ← ha,
    Submodule.mkQ_apply, shiftedQuotientComponent_mk]
  apply Subtype.ext
  exact (mem_shiftedSubmodule_iff ℳ d.monoid p).mp a.property q hq

/-- All homogeneous components together distinguish completed shifted coefficients. -/
theorem shiftedCoefficients_ext {x y : d.ShiftedCoefficients ℳ p}
    (h : ∀ q, d.shiftedHomogeneousComponent ℳ p q x =
      d.shiftedHomogeneousComponent ℳ p q y) : x = y := by
  apply (d.shiftedFiltration ℳ p).completion_ext
  intro k
  obtain ⟨a, ha⟩ := ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ_surjective
    ((d.shiftedFiltration ℳ p).projection k x)
  obtain ⟨b, hb⟩ := ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ_surjective
    ((d.shiftedFiltration ℳ p).projection k y)
  rw [← ha, ← hb, Submodule.mkQ_apply, Submodule.mkQ_apply,
    ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
  rw [mem_shiftedFiltration_iff]
  intro q hq
  have hk : d.degree (q - p) ≤ k := by omega
  have he := h q
  rw [d.shiftedHomogeneousComponent_eq ℳ p q k hk,
    d.shiftedHomogeneousComponent_eq ℳ p q k hk, ← ha, ← hb,
    Submodule.mkQ_apply, Submodule.mkQ_apply, shiftedQuotientComponent_mk,
    shiftedQuotientComponent_mk] at he
  simpa only [Submodule.coe_sub, DirectSum.decompose_sub, DirectSum.sub_apply,
    Submodule.coe_sub, sub_eq_zero] using congrArg Subtype.val he

end Mei.PositiveDegrees
