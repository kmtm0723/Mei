/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Logarithmic.WallFunction.Map
public import Mei.Geometry.ScatteringDiagram.DirectedWall.TropicalPairing

/-!
# Tangent fields under pushforward along tropical degree maps

A positive degree map `T` between degree lattices projecting to a common tangent lattice,
compatibly on allowed degrees, sends the degrees tangent to a character `m` to degrees tangent
to `m` (`PositiveDegreeMap.tropicalTangentMonoidHom`). Consider pushforward data over `T`
whose Lie map sends every homogeneous field `z^n ∂_μ` to `z^{T n} ∂_μ`, such as
`DirectedWall.Pushforward.ofTropicalDegreeMap` and
`DirectedWall.Pushforward.ofFiniteAlphabetLift`. It sends the tangent monomial field
`c z^q ∂_m` to `c z^{T q} ∂_m` (`DirectedWall.Pushforward.lieHom_tropicalTangentField_single`).
By `GradedLieHom.completedMap_completedBCHExp_completedTropicalTangentField_polynomial`, the
pushed label of `1 + ∑_s r_s z^{x_s}` is the label of `1 + ∑_s r_s z^{T x_s}`
(`DirectedWall.Pushforward.completedMap_lieHom_polynomial`).
-/

public section

noncomputable section

namespace Mei

open LogarithmicVectorField _root_.AddMonoidAlgebra

namespace DirectedWall.Pushforward

universe u

variable {R Γ Λ Γ' : Type u} {V : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup Γ']
  [NormedAddCommGroup V] [NormedSpace ℝ V] [DecidableEq Γ] [DecidableEq Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ}
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (P : Pushforward d e h h (tropicalVertexWallSpaces (R := R) d ρ)
    (tropicalVertexWallSpaces e ρ'))
  (hP : ∀ {n : Γ} (x : tropicalVertexLieAlgebra (R := R) d ρ) (μ : Λ →+ R),
    single ρ n μ = x.val → (P.lieHom x).val = single ρ' (P.degreeMap n) μ)
  (hT : ∀ n ∈ d.monoid, ρ' (P.degreeMap n) = ρ n) (m : Λ →+ R)

include hP in
/-- If the Lie map sends homogeneous fields `z^n ∂_μ` to `z^{T n} ∂_μ`, it sends the tangent
monomial field `c z^q ∂_m` to `c z^{T q} ∂_m`. -/
theorem lieHom_tropicalTangentField_single (q : tropicalTangentMonoid d ρ m) (c : R) :
    P.lieHom (tropicalTangentField d ρ m (single q c)) =
      tropicalTangentField e ρ' m (single (P.degreeMap.tropicalTangentMonoidHom hT m q) c) := by
  by_cases hq : (q : Γ) = 0
  · have hq' : q = 0 := Subtype.ext hq
    rw [hq', map_zero, tropicalTangentField_single_zero, map_zero,
      tropicalTangentField_single_zero]
  · apply Subtype.ext
    rw [hP _ (c • m) (coe_tropicalTangentField_single d ρ m hq c).symm,
      coe_tropicalTangentField_single e ρ' m (by
        simpa using P.degreeMap.map_ne_zero (tropicalTangentMonoid_le d ρ m q.property) hq),
      PositiveDegreeMap.coe_tropicalTangentMonoidHom]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d
  (tropicalTangentMonoid d ρ m)
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) e
  (tropicalTangentMonoid e ρ' m)

include hP hT in
/-- If the Lie map sends homogeneous fields `z^n ∂_μ` to `z^{T n} ∂_μ`, the completed group
map sends the label of the tangent polynomial `1 + ∑_s r_s z^{x_s}` to the label of
`1 + ∑_s r_s z^{x'_s}`, where `x'_s = T x_s`. -/
theorem completedMap_lieHom_polynomial {κ : Type*} [Fintype κ]
    (x : κ → tropicalTangentMonoid d ρ m) (x' : κ → tropicalTangentMonoid e ρ' m)
    (hx : ∀ s, (x' s : Γ') = P.degreeMap (x s)) (r : κ → R)
    (hg : (F).toCompletion (1 + ∑ s, single (x s) (r s)) - 1 ∈ (F).completionIdeal 1)
    (hg' : (G).toCompletion (1 + ∑ s, single (x' s) (r s)) - 1 ∈ (G).completionIdeal 1) :
    P.lieHom.completedMap
        (d.completedBCHExp (tropicalVertexGrading (R := R) d ρ)
          (completedTropicalTangentField d ρ m ((F).completedLog
            ⟨(F).toCompletion (1 + ∑ s, single (x s) (r s)), hg⟩))) =
      e.completedBCHExp (tropicalVertexGrading (R := R) e ρ')
        (completedTropicalTangentField e ρ' m ((G).completedLog
          ⟨(G).toCompletion (1 + ∑ s, single (x' s) (r s)), hg'⟩)) :=
  GradedLieHom.completedMap_completedBCHExp_completedTropicalTangentField_polynomial _
    (P.degreeMap.tropicalTangentMonoidHom hT m)
    (PositiveDegreeMap.coe_tropicalTangentMonoidHom _ hT m)
    (P.lieHom_tropicalTangentField_single hP hT m) x x'
    (fun s => Subtype.ext ((PositiveDegreeMap.coe_tropicalTangentMonoidHom _ hT m _).trans
      (hx s).symm)) r hg hg'

end DirectedWall.Pushforward

end Mei
