/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Algebra.Equiv

/-!
# Multiplicative linear actions as algebra automorphisms

A monoid homomorphism to linear automorphisms whose elements preserve products
lifts to algebra automorphisms. Invertibility supplies the unit law through
Mathlib's multiplicative-equivalence API.
-/

public section

namespace MonoidHom

variable {R A G : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Monoid G]
  (act : G →* (A ≃ₗ[R] A)) (hmul : ∀ g x y, act g (x * y) = act g x * act g y)

/-- Upgrade a multiplicative linear action to an action by algebra automorphisms. -/
def toAlgAut : G →* (A ≃ₐ[R] A) where
  toFun g := AlgEquiv.ofLinearEquiv (act g)
    (show act g 1 = 1 from
      ({ (act g).toEquiv with map_mul' := hmul g } : A ≃* A).map_one)
    (hmul g)
  map_one' := by
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun e : A ≃ₗ[R] A => e x) act.map_one
  map_mul' g h := by
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun e : A ≃ₗ[R] A => e x) (act.map_mul g h)

/-- Upgrading an action retains its underlying linear map. -/
@[simp]
theorem toAlgAut_apply (g : G) (x : A) : act.toAlgAut hmul g x = act g x := by
  -- The algebra-equivalence constructor retains the underlying linear map.
  rfl

end MonoidHom
