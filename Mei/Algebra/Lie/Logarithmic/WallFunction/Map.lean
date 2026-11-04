/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Logarithmic.Coefficient.MapDomain
public import Mei.Algebra.Lie.Logarithmic.WallFunction

/-!
# Function-wall labels under graded maps of tropical vertex algebras

Let `f` be a graded Lie map of tropical vertex Lie algebras over a positive degree map `U`.
Suppose that `f` sends the tangent monomial fields `c z^q ∂_m` to `c z^{φ q} ∂_{m'}`, for an
additive map `φ` from the degrees tangent to `m` to the degrees tangent to `m'` lifting `U`.
Then the monomial map `z^q ↦ z^{φ q}` of tangent coefficient algebras extends to completions
(`TropicalVertexCoefficientAction.completedMapDomain`), and the completed group map of `f` sends
the function-wall label `exp(log(g) ∂_m)` to `exp(log(φ_* g) ∂_{m'})`
(`GradedLieHom.completedMap_completedBCHExp_completedTropicalTangentField_completedLog`). For
a tangent polynomial `g = 1 + ∑_s r_s z^{x_s}` the image wall function is
`1 + ∑_s r_s z^{φ x_s}`
(`GradedLieHom.completedMap_completedBCHExp_completedTropicalTangentField_polynomial`).

A positive degree map compatible with projections to a common tangent lattice restricts to the
degrees tangent to `m` (`PositiveDegreeMap.tropicalTangentMonoidHom`); this is the map `φ` for
the pushforward along such degree maps, with `m' = m`. The function-wall labels and their maps
along tropical pairings follow Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei

open LogarithmicVectorField _root_.AddMonoidAlgebra

namespace GradedLieHom

open TropicalVertexCoefficientAction

universe u

variable {R Γ Λ Γ' Λ' : Type u} [CommRing R]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [AddCommMonoid Γ'] [AddCommMonoid Λ']
  [DecidableEq Γ] [DecidableEq Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {U : PositiveDegreeMap d e}
  (f : GradedLieHom U (tropicalVertexGrading (R := R) d ρ) (tropicalVertexGrading (R := R) e ρ'))
  {m : Λ →+ R} {m' : Λ' →+ R}
  (φ : tropicalTangentMonoid d ρ m →+ tropicalTangentMonoid e ρ' m')
  (hφ : ∀ q, (φ q : Γ') = U q)
  (hf : ∀ q c, f (tropicalTangentField d ρ m (single q c)) =
    tropicalTangentField e ρ' m' (single (φ q) c))

include hf in
/-- The map sends the tangent field `u ∂_m` to `φ_* u ∂_{m'}`. -/
theorem map_tropicalTangentField (v : R[tropicalTangentMonoid d ρ m]) :
    f (tropicalTangentField d ρ m v) =
      tropicalTangentField e ρ' m' (mapDomainAlgHom R R φ v) := by
  induction v using induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single q c => rw [hf, mapDomainAlgHom_apply, mapDomain_single]

local notation "F" => filtration (R := R) d (tropicalTangentMonoid d ρ m)
local notation "G" => filtration (R := R) e (tropicalTangentMonoid e ρ' m')
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "ℳ" => tropicalVertexGrading (R := R) e ρ'
local notation "π" => LieIdeal.completionProjection

include hf in
/-- At order `k`, the truncated map sends the completed tangent field `u ∂_m`, taken at the order
of the cutoff modulus, to `φ_* u ∂_{m'}`, given any representative `v` of the coefficient of `u`
at that order. -/
theorem truncatedMap_completionProjection_completedTropicalTangentField (k : ℕ)
    (u : (F).completion) (v : R[tropicalTangentMonoid d ρ m])
    (hv : Ideal.Quotient.mk _ v = (F).projection (U.modulus k) u) :
    f.truncatedMap k le_rfl
        (π (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) (U.modulus k)
          (completedTropicalTangentField d ρ m u)) =
      π (e.degreeIdeal ℳ) (e.degreeIdeal_antitone ℳ) k
        (completedTropicalTangentField e ρ' m' (completedMapDomain U φ hφ u)) := by
  have hv' : (G).projection k (completedMapDomain U φ hφ u) =
      Ideal.Quotient.mk _ (mapDomainAlgHom R R φ v) := by
    rw [projection_completedMapDomain, ← hv]
    exact Ideal.quotientMap_mk
  rw [completionProjection_completedTropicalTangentField d ρ m _ u v hv.symm,
    completionProjection_completedTropicalTangentField e ρ' m' k _ _ hv', LieIdeal.mkQ_apply,
    truncatedMap_mk, f.map_tropicalTangentField φ hf]
  rfl

variable [Algebra ℚ R]

include hf in
/-- The completed group map sends the label `exp(u ∂_m)` to `exp(φ_* u ∂_{m'})`. -/
theorem completedMap_completedBCHExp_completedTropicalTangentField (u : (F).completion) :
    f.completedMap (d.completedBCHExp ℒ (completedTropicalTangentField d ρ m u)) =
      e.completedBCHExp ℳ
        (completedTropicalTangentField e ρ' m' (completedMapDomain U φ hφ u)) := by
  refine CompletedGroup.ext fun k => ?_
  refine (Ideal.Quotient.mk_surjective (I := (F).ideal (U.modulus k + 1))
    ((F).projection (U.modulus k) u)).elim fun v hv => ?_
  -- Term-mode rewriting: `rw` is slow on these completed tropical vertex groups.
  exact (f.projection_completedMap k _).trans <|
    (congrArg _ (d.projection_completedBCHExp ℒ _ _)).trans <|
      (LieHom.bchGroupMap_exp _ _).trans <|
        (congrArg BCHGroup.exp
          (f.truncatedMap_completionProjection_completedTropicalTangentField φ hφ hf k u v
            hv)).trans (e.projection_completedBCHExp ℳ k _).symm

include hf in
/-- The completed group map sends the function-wall label `exp(log(g) ∂_m)` to
`exp(log(φ_* g) ∂_{m'})`. -/
theorem completedMap_completedBCHExp_completedTropicalTangentField_completedLog
    {g : (F).completion} (hg : g - 1 ∈ (F).completionIdeal 1) :
    f.completedMap (d.completedBCHExp ℒ
        (completedTropicalTangentField d ρ m ((F).completedLog ⟨g, hg⟩))) =
      e.completedBCHExp ℳ (completedTropicalTangentField e ρ' m'
        ((G).completedLog ⟨completedMapDomain U φ hφ g, by
          simpa only [map_sub, map_one] using
            completedMapDomain_mem_completionIdeal_one U φ hφ hg⟩)) :=
  (f.completedMap_completedBCHExp_completedTropicalTangentField φ hφ hf _).trans <|
    congrArg (fun y => e.completedBCHExp ℳ (completedTropicalTangentField e ρ' m' y))
      (completedMapDomain_completedLog U φ hφ hg)

include hφ hf in
/-- The completed group map sends the label of the tangent polynomial `1 + ∑_s r_s z^{x_s}` to
the label of `1 + ∑_s r_s z^{x'_s}`, where `x'_s = φ x_s`. -/
theorem completedMap_completedBCHExp_completedTropicalTangentField_polynomial {κ : Type*}
    [Fintype κ] (x : κ → tropicalTangentMonoid d ρ m)
    (x' : κ → tropicalTangentMonoid e ρ' m') (hx : ∀ s, φ (x s) = x' s) (r : κ → R)
    (hg : (F).toCompletion (1 + ∑ s, single (x s) (r s)) - 1 ∈ (F).completionIdeal 1)
    (hg' : (G).toCompletion (1 + ∑ s, single (x' s) (r s)) - 1 ∈ (G).completionIdeal 1) :
    f.completedMap (d.completedBCHExp ℒ (completedTropicalTangentField d ρ m ((F).completedLog
        ⟨(F).toCompletion (1 + ∑ s, single (x s) (r s)), hg⟩))) =
      e.completedBCHExp ℳ (completedTropicalTangentField e ρ' m' ((G).completedLog
        ⟨(G).toCompletion (1 + ∑ s, single (x' s) (r s)), hg'⟩)) := by
  have h : completedMapDomain U φ hφ ((F).toCompletion (1 + ∑ s, single (x s) (r s))) =
      (G).toCompletion (1 + ∑ s, single (x' s) (r s)) := by
    simp only [completedMapDomain_toCompletion, map_add, map_one, map_sum,
      mapDomainAlgHom_apply, mapDomain_single, hx]
  exact (f.completedMap_completedBCHExp_completedTropicalTangentField_completedLog φ hφ hf
    hg).trans <| congrArg (fun y => e.completedBCHExp ℳ (completedTropicalTangentField e ρ' m'
      ((G).completedLog y))) (Subtype.ext h)

end GradedLieHom

namespace PositiveDegreeMap

variable {R Γ Λ Γ' : Type*} [CommRing R]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [AddCommMonoid Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ}
  (T : PositiveDegreeMap d e) (hT : ∀ n ∈ d.monoid, ρ' (T n) = ρ n) (m : Λ →+ R)

include hT in
/-- A positive degree map compatible with projections to a common tangent lattice sends degrees
tangent to `m` to degrees tangent to `m`. -/
theorem map_tropicalTangentMonoid_le :
    (tropicalTangentMonoid d ρ m).map T.toAddMonoidHom ≤ tropicalTangentMonoid e ρ' m := by
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨hqP, hq0⟩ := (mem_tropicalTangentMonoid d ρ m q).mp hq
  exact (mem_tropicalTangentMonoid _ _ _ _).mpr ⟨T.map_mem hqP, by rw [hT q hqP]; exact hq0⟩

/-- The positive degree map on degrees tangent to `m`. -/
def tropicalTangentMonoidHom : tropicalTangentMonoid d ρ m →+ tropicalTangentMonoid e ρ' m :=
  (AddSubmonoid.inclusion (T.map_tropicalTangentMonoid_le hT m)).comp
    (T.toAddMonoidHom.addSubmonoidMap _)

/-- The tangent degree map is the positive degree map. -/
@[simp]
theorem coe_tropicalTangentMonoidHom (q : tropicalTangentMonoid d ρ m) :
    (T.tropicalTangentMonoidHom hT m q : Γ') = T q := (rfl)

end PositiveDegreeMap

end Mei
