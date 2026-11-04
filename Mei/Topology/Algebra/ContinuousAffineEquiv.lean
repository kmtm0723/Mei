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
linear parts.
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

end ContinuousAffineEquiv
