/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Logarithmic.Pairing.Basic

/-!
# Tropical pairings on the full tropical vertex Lie algebra

A tropical pairing whose character domain is the whole character space is defined on the
character restriction `tropicalSubalgebra ρ ⊤ d`, which is all of the positive tangent Lie
algebra `tropicalVertexLieAlgebra d ρ`. Composing with this identification gives a graded Lie
map between the tropical vertex Lie algebras themselves, over the degree map of the pairing.
On a homogeneous field `z^n ∂_m` it gives `z^{T n} ∂_{S m}`. Directed walls labelled in
`tropicalVertexWallSpaces` take their labels in these algebras.

The pairing and the logarithmic bracket follow Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei

namespace LogarithmicVectorField

variable {R Γ Λ : Type*} [CommRing R] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ)

/-- Every positive tangent field has its characters in the full character space. -/
theorem mem_tropicalSubalgebra_top (x : tropicalVertexLieAlgebra (R := R) d ρ) :
    x ∈ tropicalSubalgebra ρ (⊤ : Submodule R (Λ →+ R)) d := by
  simp

/-- The positive tangent Lie algebra, viewed in its restriction to all characters. -/
def toTropicalSubalgebraTop :
    tropicalVertexLieAlgebra (R := R) d ρ →ₗ⁅R⁆
      tropicalSubalgebra ρ (⊤ : Submodule R (Λ →+ R)) d :=
  { LinearMap.id.codRestrict (tropicalSubalgebra ρ (⊤ : Submodule R (Λ →+ R)) d).toSubmodule
      (mem_tropicalSubalgebra_top d ρ) with
    map_lie' := fun {_ _} => Subtype.ext (by simp) }

/-- The identification does not change the underlying field. -/
@[simp]
theorem coe_toTropicalSubalgebraTop (x : tropicalVertexLieAlgebra (R := R) d ρ) :
    (toTropicalSubalgebraTop d ρ x).val = x := (rfl)

end LogarithmicVectorField

namespace TropicalPairing

open LogarithmicVectorField

variable {R Γ Λ Γ' Λ' : Type*} [CommRing R]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [AddCommMonoid Γ'] [AddCommMonoid Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') (⊤ : Submodule R (Λ →+ R)))

/-- A pairing on all characters as a graded Lie map between the tropical vertex Lie
algebras, over its degree map. -/
def tropicalVertexGradedLieHom :
    GradedLieHom p.degreeMap (tropicalVertexGrading (R := R) d ρ) (tropicalVertexGrading e ρ')
    where
  toLieHom := p.gradedLieHom.toLieHom.comp (toTropicalSubalgebraTop d ρ)
  map_mem {n x} hx := p.gradedLieHom.map_mem (n := n) (x := toTropicalSubalgebraTop d ρ x) (by
    rw [tropicalSubalgebraGrading_def, Submodule.mem_comap]
    exact hx)

/-- The map on the full algebra is the pairing map on the restriction to all characters. -/
theorem tropicalVertexGradedLieHom_apply (x : tropicalVertexLieAlgebra (R := R) d ρ) :
    p.tropicalVertexGradedLieHom x = p.gradedLieHom (toTropicalSubalgebraTop d ρ x) := (rfl)

/-- On a homogeneous field `z^n ∂_m`, the pairing gives `z^{T n} ∂_{S m}`. -/
theorem coe_tropicalVertexGradedLieHom_of_homogeneous {n : Γ}
    (x : tropicalVertexLieAlgebra (R := R) d ρ) (m : Λ →+ R) (hm : single ρ n m = x.val) :
    (p.tropicalVertexGradedLieHom x).val =
      single ρ' (p.degreeMap n) (p.characterMap ⟨m, Submodule.mem_top⟩) :=
  p.coe_gradedLieHom_of_homogeneous _ ⟨m, Submodule.mem_top⟩ hm

end TropicalPairing

end Mei
