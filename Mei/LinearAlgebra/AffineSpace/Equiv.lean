/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Affine projection of a linear equivalence

Viewing a linear equivalence as an affine equivalence retains its linear part.
This projection complements Mathlib's equation for the underlying function.
-/

public section

namespace LinearEquiv

variable {R V W : Type*} [Ring R] [AddCommGroup V] [AddCommGroup W]
  [Module R V] [Module R W]

/-- Viewing a linear equivalence as affine retains its linear part. -/
@[simp]
theorem linear_toAffineEquiv (e : V ≃ₗ[R] W) : e.toAffineEquiv.linear = e := (rfl)

end LinearEquiv
