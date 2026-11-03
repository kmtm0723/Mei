/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Incoming
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall
public import Mei.Algebra.MonoidAlgebra.Range
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Function walls and positivity of rank-two polynomial inputs

The incoming diagram of a rank-two polynomial input splits each wall function
`f_j = 1 + ∑_n c_{j,n} z^n` into ray walls on the cylinder over the affine line `j`, one for
every supported ray of `L` tangent to it. Grouping these walls by their line is a
function-wall grouping for the projection `π : L → M` (`RankTwoPolynomialInput.incomingGrouping`):
the walls of a group share the cylinder and its primitive normal `ν_j ∘ π`, and the nontrivial
ones have generators projecting to positive multiples of the tangent `m_j`. The label of the
group of `j` is the unsplit label `exp(log(f_j) ∂_{ν_j ∘ π})`, which acts on monomials by
`z^p ↦ f_j^{⟨ν_j, π(p)⟩} z^p`, so `f_j` is the wall function of the group whenever the
coefficient monoid contains both signs of a degree of normal pairing one.

If the coefficients `c_{j,n}` lie in the image of a semiring map `φ : S →+* R`, the wall
functions are the images of polynomials over `S`, hence positive for the image of `S[Q]`, and
the incoming diagram is a positive wall representative
(`RankTwoPolynomialInput.isPositiveWallRepresentative_incomingDiagram`). For the independent
variables `c_{j,n}` of `ℚ[c_{j,n}]` and the full coefficient lattice, the grouped wall functions
have coefficients in `ℕ[c_{j,n}]`
(`RankTwoPolynomialInput.isPositiveWallRepresentative_incomingDiagram_variables`).

We use `RankTwoPolynomialInput.projection_initialLabel_eq_noncommProd_incomingDiagram`,
`RankTwoPolynomialInput.completedBCHAction_initialLabel` and the function-wall API of
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall`. The inputs and their positivity
follow Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*,
Definition 2.1 and Theorem 9.9 (arXiv:2503.03719v1), with the grouped wall functions of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2).
-/

public section

noncomputable section

namespace Mei.RankTwoPolynomialInput

open _root_.AddMonoidAlgebra

variable {L M ι R V : Type*} [AddCommGroup L] [AddCommGroup M] {d : PositiveDegrees L}
  (I : RankTwoPolynomialInput d M ι) [CommRing R] [DecidableEq L] [Algebra ℚ R]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {latticeMap : L →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap) (c : I.Variable → R)

local notation "ρ" => AddMonoidHom.id L
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ

/-- The grouping of the incoming ray walls by their line. -/
def incomingGrouping [Module.Free ℤ M] [Module.Finite ℤ M] :
    (I.incomingDiagram h c).FunctionWallGrouping I.projection ι where
  group := Sigma.fst
  support_eq hj := by simp only [incomingDiagram_support, hj]
  normal_eq hj := by simp only [incomingDiagram_normal, hj]
  projectedDirection_eq {j j'} hj hj0 hj'0 := by
    simp only [incomingDiagram_label] at hj0 hj'0
    obtain ⟨a, b, ha, hb, he⟩ := I.rayFactor_initialLabel_projectedDirection c j.1 hj0
    obtain ⟨a', b', ha', hb', he'⟩ := I.rayFactor_initialLabel_projectedDirection c j'.1 hj'0
    refine ⟨b' * a, b * a', Nat.mul_pos hb' ha, Nat.mul_pos hb ha', ?_⟩
    simp only [incomingDiagram_ray]
    rw [mul_smul, he, mul_smul, he', ← hj, smul_comm b' b]
  isPrimitive_normal j := by
    simpa only [incomingDiagram_normal] using I.isPrimitive_wallNormal j.1

variable [Module.Free ℤ M] [Module.Finite ℤ M]

/-- A ray wall belongs to the group of its line. -/
@[simp]
theorem incomingGrouping_group (j : I.IncomingIndex) :
    (I.incomingGrouping h c).group j = j.1 := (rfl)

/-- The label of the group of ray walls over the line `i` is its unsplit label
`exp(log(f_i) ∂_{ν_i ∘ π})`. -/
@[simp]
theorem label_incomingGrouping (i : ι) :
    (I.incomingGrouping h c).label i = I.initialLabel c i := by
  classical
  refine (((I.incomingGrouping h c).eq_label_iff i _).mpr fun k => ?_).symm
  let := h.free
  let : HasUniqueDiv L := .of_isTorsionFree ℤ _
  let T : Finset {w : SupportedRay d // I.wallNormal i w.generator = 0} :=
    (d.finite_raysAtOrder k).toFinset.subtype _
  let e : {w : SupportedRay d // I.wallNormal i w.generator = 0} ↪ I.IncomingIndex :=
    ⟨fun w => ⟨i, w⟩, fun _ _ hw => by simpa using hw⟩
  refine (I.projection_initialLabel_eq_noncommProd_incomingDiagram h c i k T
    fun w hw hw0 => by simpa [T] using hw).trans ((Finset.noncommProd_map T e _ _).symm.trans
      ((I.incomingGrouping h c).groupLabel_eq_noncommProd i k (T.map e) ?_ ?_).symm)
  · intro j hj
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.mp hj
    exact I.incomingGrouping_group h c _
  · intro j hact hj
    rw [incomingGrouping_group] at hj
    obtain ⟨i', w⟩ := j
    obtain rfl : i' = i := hj
    refine Finset.mem_map.mpr ⟨w, ?_, rfl⟩
    rw [Finset.mem_subtype, Set.Finite.mem_toFinset]
    by_contra hw
    apply ((I.incomingDiagram h c).mem_active k _).mp hact
    simpa only [incomingDiagram_label] using
      d.projection_eq_one_of_notMem_raysAtOrder ℒ
        (d.rayFactor_mem_completedRaySubgroup ℒ (I.initialLabel c i') w.val) k hw

section Action

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid L) [Fact (d.monoid ≤ Q)]

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d Q

/-- The wall function `f_i` is the wall function of the grouped ray walls over the line `i`,
when the coefficient monoid contains both signs of a degree of normal pairing one. -/
theorem isWallFunction_incomingGrouping (i : ι)
    (hQ : ∃ p : L, I.wallNormal i p = 1 ∧ p ∈ Q ∧ -p ∈ Q) :
    (I.incomingGrouping h c).IsWallFunction ((G).completedBCHAction d ℒ) i
      (I.completedInitialFunction c Q i) := by
  refine ((I.incomingGrouping h c).isWallFunction_iff _ i _).mpr fun j hj => ?_
  rw [incomingGrouping_group] at hj
  subst hj
  obtain ⟨p, hp, hpQ, hp'Q⟩ := hQ
  constructor
  · let p₁ : Q := ⟨p, hpQ⟩
    let p₂ : Q := ⟨-p, hp'Q⟩
    have hp₁₂ : p₁ + p₂ = 0 := Subtype.ext (by simp [p₁, p₂])
    have hmul : (single p₁ 1 * single p₂ 1 : R[Q]) = 1 := by
      rw [single_mul_single, hp₁₂, mul_one, one_def]
    refine ⟨p₁, by simpa [p₁] using hp, ?_⟩
    exact (isUnit_iff_exists_inv.mpr ⟨single p₂ 1, hmul⟩).map (G).toCompletion
  · intro p r
    rw [label_incomingGrouping]
    simpa only [incomingDiagram_normal, AddMonoidHom.id_apply] using
      I.completedBCHAction_initialLabel c Q j.1 p r

omit [DecidableEq L] [Algebra ℚ R] [Module.Free ℤ M] [Module.Finite ℤ M] in
/-- Coefficients in the image of a semiring map `φ : S →+* R` give wall functions positive
for the image of `S[Q]`. -/
theorem isPositive_completedInitialFunction {S : Type*} [Semiring S] (φ : S →+* R)
    (hc : ∀ v, c v ∈ φ.rangeS) (i : ι) :
    (G).IsPositive (AddMonoidAlgebra.mapRingHom Q φ).rangeS
      (I.completedInitialFunction c Q i).val := by
  rw [I.coe_completedInitialFunction c Q i]
  refine AlgFiltration.isPositive_toCompletion ?_
  choose s hs using hc
  refine ⟨1 + ∑ n : I.exponents i, single (⟨n, (Fact.out : d.monoid ≤ Q)
    (I.mem_monoid_of_mem_exponents n.property)⟩ : Q) (s ⟨i, n⟩), ?_⟩
  simp only [initialFunction_def, map_add, map_one, map_sum, mapRingHom_single, hs]

variable (hQ : ∀ i : ι, ∃ p : L, I.wallNormal i p = 1 ∧ p ∈ Q ∧ -p ∈ Q)
  {S : Type*} [Semiring S] (φ : S →+* R) (hc : ∀ v, c v ∈ φ.rangeS)

include hQ hc

/-- The grouping of the incoming diagram by line is positive for the image of `S[Q]` when the
coefficients lie in the image of `φ`. -/
theorem isPositive_incomingGrouping :
    (I.incomingGrouping h c).IsPositive ((G).completedBCHAction d ℒ)
      (AddMonoidAlgebra.mapRingHom Q φ).rangeS :=
  ((I.incomingGrouping h c).isPositive_iff _ _).mpr fun i =>
    ⟨I.completedInitialFunction c Q i, I.isWallFunction_incomingGrouping h c Q i (hQ i),
      I.isPositive_completedInitialFunction c Q φ hc i⟩

/-- The incoming diagram of a rank-two polynomial input is a positive wall representative
for the image of `S[Q]` when its coefficients lie in the image of `φ : S →+* R`. -/
theorem isPositiveWallRepresentative_incomingDiagram :
    (I.incomingDiagram h c).IsPositiveWallRepresentative
      ((G).completedBCHAction d ℒ) (AddMonoidAlgebra.mapRingHom Q φ).rangeS I.projection :=
  (I.isPositive_incomingGrouping h c Q hQ φ hc).isPositiveWallRepresentative

end Action

section Variables

open scoped Mei.TropicalVertexCoefficientAction

local instance : Fact (d.monoid ≤ (⊤ : AddSubmonoid L)) := ⟨le_top⟩

local notation "G" =>
  TropicalVertexCoefficientAction.filtration (R := MvPolynomial I.Variable ℚ) d
    (⊤ : AddSubmonoid L)

/-- For the independent variables `c_{j,n}` over `ℚ` and the full coefficient lattice, the
incoming diagram is a positive wall representative: its grouped wall functions have
coefficients in `ℕ[c_{j,n}]`. -/
theorem isPositiveWallRepresentative_incomingDiagram_variables :
    (I.incomingDiagram h MvPolynomial.X).IsPositiveWallRepresentative
      ((G).completedBCHAction d (tropicalVertexGrading (R := MvPolynomial I.Variable ℚ) d ρ))
      (AddMonoidAlgebra.mapRingHom (⊤ : AddSubmonoid L)
        (MvPolynomial.map (σ := I.Variable) (Nat.castRingHom ℚ))).rangeS I.projection :=
  I.isPositiveWallRepresentative_incomingDiagram h MvPolynomial.X ⊤
    (fun i => (I.exists_wallNormal_eq_one i).imp fun _ hp => ⟨hp, trivial, trivial⟩) _
    fun v => ⟨MvPolynomial.X v, MvPolynomial.map_X _ v⟩

end Variables

end Mei.RankTwoPolynomialInput
