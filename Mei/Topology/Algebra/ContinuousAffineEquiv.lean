/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Linear parts of continuous affine equivalences

The linear part of a composite continuous affine equivalence is the composite of the
linear parts, and a continuous linear equivalence is the linear part of the continuous affine
equivalence it defines.
-/

public section

namespace ContinuousAffineEquiv

variable {k P₁ P₂ P₃ V₁ V₂ V₃ : Type*} [Ring k]
  [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
  [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃] [TopologicalSpace P₃]

/-- The linear part of a composite applies the two linear parts in order. -/
@[simp]
theorem linear_trans_apply (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) (v : V₁) :
    (e.trans e').toAffineEquiv.linear v = e'.toAffineEquiv.linear (e.toAffineEquiv.linear v) :=
  (rfl)

variable {E F : Type*} [AddCommGroup E] [Module k E] [TopologicalSpace E]
  [AddCommGroup F] [Module k F] [TopologicalSpace F]

/-- A continuous linear equivalence is the linear part of the continuous affine equivalence it
defines. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.linear_toContinuousAffineEquiv_apply (L : E ≃L[k] F)
    (v : E) : L.toContinuousAffineEquiv.toAffineEquiv.linear v = L v :=
  -- `ContinuousLinearEquiv.toContinuousAffineEquiv` is built from `LinearEquiv.toAffineEquiv`,
  -- whose `linear` field is the given linear equivalence; Mathlib has no lemma for this field.
  (rfl)

end ContinuousAffineEquiv
