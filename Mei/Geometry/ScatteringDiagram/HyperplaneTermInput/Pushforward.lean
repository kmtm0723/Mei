/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Scat
public import Mei.Algebra.Lie.Logarithmic.WallFunction.Map
public import Mei.Geometry.ScatteringDiagram.DirectedWall.TropicalPairing
public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.Basic

/-!
# Pushing polynomial function walls along degree maps

Let `T : (Γ, P, δ) → (Γ', P', δ')` be a positive degree map between degree lattices projecting
to a common tangent lattice `Λ`, compatibly on allowed degrees. A `HyperplaneTermInput` on `Γ`
is carried to the input on `Γ'` with the same hyperplanes and exponents `T n_α`
(`HyperplaneTermInput.map`).

Consider pushforward data `P` over `T` between the tropical vertex wall spaces whose Lie map
sends each homogeneous field `z^n ∂_μ` to `z^{T n} ∂_μ`, and which keep normals and supports;
for instance `DirectedWall.Pushforward.ofTropicalDegreeMap` and
`DirectedWall.Pushforward.ofFiniteAlphabetLift`. The degree map sends degrees tangent to a
hyperplane normal to degrees tangent to it (`HyperplaneTermInput.map_tropicalTangentMonoid_le`,
by `Mei.map_tropicalTangentMonoid_intCast_le`), and the completed group map of `P` sends the
function-wall label of `1 + ∑_α c_α z^{n_α}` on a hyperplane to that of
`1 + ∑_α c_α z^{T n_α}` (`HyperplaneTermInput.completedMap_label`). This is the case
`c = r = 1` of
`GradedLieHom.completedMap_completedBCHExp_completedTropicalTangentField_completedLog`. Hence
the pushforward of the ray presentation is equivalent to the ray presentation of the image
input (`HyperplaneTermInput.diagram_pushforward_equivalent`): on every hyperplane both have the
logarithm of the same label as family logarithm. The rays of the pushed walls are the reindexed
rays `SupportedRay.map`, several of which may coincide; the equivalence regroups them into the
ray factors of the image label. Consequently the pushforward of the scattering class of the input
is the scattering class of the image input (`HyperplaneTermInput.pushforward_scat_diagram`).

The pushforward along tropical pairings follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.HyperplaneTermInput

open DirectedWall DirectedDiagram

universe u

variable {R Γ Λ Γ' ι E : Type u} {V : Type*} [CommRing R]
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ}
  (I : HyperplaneTermInput d ρ ι E) (T : PositiveDegreeMap d e)
  (hT : ∀ n ∈ d.monoid, ρ' (T n) = ρ n)

/-- The input with the same hyperplanes and the exponents `T n_α`. -/
def map : HyperplaneTermInput e ρ' ι E where
  normal := I.normal
  normal_ne_zero := I.normal_ne_zero
  offset := I.offset
  wallIndex := I.wallIndex
  exponent α := T (I.exponent α)
  exponent_mem α := T.map_mem (I.exponent_mem α)
  exponent_ne_zero α := T.map_ne_zero (I.exponent_mem α) (I.exponent_ne_zero α)
  normal_exponent α := by
    rw [hT _ (I.exponent_mem α)]
    exact I.normal_exponent α

/-- The mapped input has the normals of the input. -/
@[simp]
theorem map_normal : (I.map T hT).normal = I.normal := by
  simp [map]

/-- The mapped input has the offsets of the input. -/
@[simp]
theorem map_offset : (I.map T hT).offset = I.offset := by
  simp [map]

/-- The mapped input places each term on the hyperplane of the input. -/
@[simp]
theorem map_wallIndex : (I.map T hT).wallIndex = I.wallIndex := by
  simp [map]

/-- The mapped input has the exponents `T n_α`. -/
@[simp]
theorem map_exponent (α : E) : (I.map T hT).exponent α = T (I.exponent α) := by
  simp [map]

variable {I T hT} in
/-- Inputs mapped along degree maps that agree on the exponents coincide. -/
theorem map_congr {T' : PositiveDegreeMap d e} {hT' : ∀ n ∈ d.monoid, ρ' (T' n) = ρ n}
    (hTT' : ∀ α, T (I.exponent α) = T' (I.exponent α)) : I.map T hT = I.map T' hT' :=
  HyperplaneTermInput.ext (by simp) (by simp) (by simp) (funext fun α => by simp [hTT'])

variable [Fintype E] [DecidableEq ι] [DecidableEq Γ] [DecidableEq Γ'] [Algebra ℚ R]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {j : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice j}
  (P : Pushforward d e h h (tropicalVertexWallSpaces (R := R) d ρ)
    (tropicalVertexWallSpaces e ρ'))
  (hP : ∀ {n : Γ} (x : tropicalVertexLieAlgebra (R := R) d ρ) (μ : Λ →+ R),
    LogarithmicVectorField.single ρ n μ = x.val →
      (P.lieHom x).val = LogarithmicVectorField.single ρ' (P.degreeMap n) μ)
  (hPT : ∀ n ∈ d.monoid, ρ' (P.degreeMap n) = ρ n) (c : E → R)

omit [Fintype E] [DecidableEq ι] [DecidableEq Γ] [DecidableEq Γ'] in
include hPT in
/-- The degree map of the pushforward data sends degrees tangent to the normal of a hyperplane to
degrees tangent to it. -/
theorem map_tropicalTangentMonoid_le (i : ι) :
    (tropicalTangentMonoid d ρ ((Int.castAddHom R).comp (I.normal i))).map
        P.degreeMap.toAddMonoidHom ≤
      tropicalTangentMonoid e ρ' ((Int.castAddHom R).comp (I.normal i)) :=
  map_tropicalTangentMonoid_intCast_le P.degreeMap (t := AddMonoidHom.id Λ)
    (fun n hn => (hPT n hn).trans (AddMonoidHom.id_apply Λ _).symm) (a := 1) fun _ => by simp

include hP in
/-- Pushforward data over a degree map `T` acting by `z^n ∂_μ ↦ z^{T n} ∂_μ` send the label
of `1 + ∑ c_α z^{n_α}` on a hyperplane to the label of `1 + ∑ c_α z^{T n_α}`. -/
theorem completedMap_label (i : ι) :
    P.lieHom.completedMap (I.label c i) = (I.map P.degreeMap hPT).label c i := by
  have hf₀ : completedTropicalTangentMap P.degreeMap (I.map_tropicalTangentMonoid_le P hPT i)
      ((TropicalVertexCoefficientAction.filtration (R := R) d
        (tropicalTangentMonoid d ρ ((Int.castAddHom R).comp (I.normal i)))).toCompletion
        (1 + ∑ α : I.Term i, AddMonoidAlgebra.single (I.tangentExponent i α) (c α))) =
      (TropicalVertexCoefficientAction.filtration (R := R) e
        (tropicalTangentMonoid e ρ' ((Int.castAddHom R).comp (I.normal i)))).toCompletion
        (1 + ∑ α : I.Term i,
          AddMonoidAlgebra.single ((I.map P.degreeMap hPT).tangentExponent i α) (c α)) ^ 1 := by
    rw [pow_one, completedTropicalTangentMap_toCompletion]
    congr 1
    simp only [map_add, map_one, map_sum, tropicalTangentMap_single]
    refine congrArg (1 + ·) (Finset.sum_congr rfl fun α _ => ?_)
    congr 1
    exact Subtype.ext <| (congrArg P.degreeMap (I.coe_tangentExponent (R := R) i α)).trans
      (((I.map P.degreeMap hPT).coe_tangentExponent (R := R) i α).trans
        (I.map_exponent _ hPT α)).symm
  exact (congrArg _ (I.label_def c i)).trans <|
    (GradedLieHom.completedMap_completedBCHExp_completedTropicalTangentField_completedLog
      P.lieHom (I.map_tropicalTangentMonoid_le P hPT i) (c := 1)
      (fun _ _ x hx => (hP x _ hx).trans (one_smul R _).symm) (r := 1) (by simp) _ _
      hf₀).trans ((I.map P.degreeMap hPT).label_def c i).symm

variable [Module.Free ℤ Γ] [Module.Free ℤ Γ'] (hν : ∀ μ, P.normalMap μ = μ)
  (hA : P.spatialMap = ContinuousAffineEquiv.refl ℝ V)

include hP hν hA in
/-- For pushforward data over a degree map `T` acting by `z^n ∂_μ ↦ z^{T n} ∂_μ`, keeping
normals and supports, the pushforward of the ray presentation is equivalent to the ray
presentation of the image input. -/
theorem diagram_pushforward_equivalent :
    ((I.diagram h c).pushforward P).Equivalent ((I.map P.degreeMap hPT).diagram h c) := by
  refine (DirectedDiagram.equivalent_iff _ _).mpr fun k =>
    DirectedDiagram.levelEquivalent_of_familyLog_eq _
      (fun i => {y | h.realCharacter (I.normal i) y = I.offset i}) I.normal _
      (a := Sigma.fst) (b := Sigma.fst) (fun x => ?_) (fun x => ?_) (fun x => ?_)
      (fun x => ?_) k fun i => ?_
  · simp [hA]
  · simp [hν]
  · simp
  · simp
  · refine (DirectedDiagram.familyLog_pushforward (D := I.diagram h c) (a := Sigma.fst) P k
      i).trans ?_
    refine (congrArg _ (familyLog_ofHyperplaneRayFactors _ _ _ _ _ _ _ _ i)).trans ?_
    refine (LieHom.log_bchGroupMap _ _).symm.trans ?_
    refine (congrArg BCHGroup.log ((P.lieHom.projection_completedMap k _).symm.trans
      (congrArg _ (I.completedMap_label P hP hPT c i)))).trans ?_
    exact (familyLog_ofHyperplaneRayFactors _ _ _ _ _ _ _ k i).symm

include hP hν hA in
/-- Under the same hypotheses, pushing forward the scattering class of the input gives the
scattering class of the image input. -/
theorem pushforward_scat_diagram :
    Class.pushforward P ((I.diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..)) =
      ((I.map P.degreeMap hPT).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..) :=
  ((I.diagram h c).pushforward_scat _ _).trans
    (DirectedDiagram.scat_eq_of_equivalent _ _ (I.diagram_pushforward_equivalent P hP hPT c hν hA))

end Mei.HyperplaneTermInput
