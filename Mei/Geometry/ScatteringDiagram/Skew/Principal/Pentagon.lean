/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pentagon
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Halfspace
public import Mei.Geometry.ScatteringDiagram.Skew.Principal.Positive
public import Mei.Geometry.ScatteringDiagram.Skew.Pentagon
public import Mei.Geometry.ScatteringDiagram.Skew.Dilogarithm
public import Mei.Geometry.ScatteringDiagram.Skew.Examples

/-!
# The cluster scattering diagram of type `A₂`

An adapted basis of a skew lattice datum is *of type `A₂`* at two unfrozen indices `i₁, i₂`
(`SkewLatticeDatum.AdaptedBasis.IsTypeA₂`) when these are its only unfrozen indices,
`{e_{i₁}, e_{i₂}} = 1` and `d_{i₁} = d_{i₂} = 1`; frozen indices are allowed. Write `ν₁, ν₂` for the
principal normals of `e_{i₁}, e_{i₂}` on the principal lattice `L_pr = M° × N_uf`. The ordinary
binomial input is the adapted polynomial input with `ℓᵢ = 1` and coefficient one, with the full
hyperplanes `{νᵢ = 0}` and wall functions `1 + q^{eᵢ}`, over any commutative `ℚ`-algebra `R`.

* Adding the half-hyperplane `{ν₁ + ν₂ = 0, ν₁ ≥ 0}`, cooriented by `ν₁ + ν₂` and labelled by the
  principal image of the dilogarithm element `Ψ[e_{i₁} + e_{i₂}]`
  (`SkewLatticeDatum.AdaptedBasis.IsTypeA₂.outgoingWall`), gives a consistent diagram
  (`SkewLatticeDatum.AdaptedBasis.IsTypeA₂.pentagonDiagram_consistent`) whose new wall is
  outgoing. It is therefore an outgoing completion of the ordinary binomial input
  (`SkewLatticeDatum.AdaptedBasis.IsTypeA₂.isOutgoingCompletion_pentagonDiagram`) and represents
  its scattering class (`SkewLatticeDatum.AdaptedBasis.IsTypeA₂.scat_eq_toClass_pentagonDiagram`).
* Each wall of this diagram, at the degree `n` among `e_{i₁}`, `e_{i₂}` and `e_{i₁} + e_{i₂}`
  (`SkewLatticeDatum.AdaptedBasis.pentagonDegree`), has the wall function `1 + q^n = 1 + z^{r(n)}`
  for its principal normal. For a coefficient monoid `Q` containing every character `(χ, 0)`,
  the discrete grouping is positive for the image of `ℕ[Q]`
  (`SkewLatticeDatum.AdaptedBasis.IsTypeA₂.isPositive_discrete_pentagonDiagram`), so the diagram
  is a positive wall representative
  (`SkewLatticeDatum.AdaptedBasis.IsTypeA₂.isPositiveWallRepresentative_pentagonDiagram`,
  `SkewLatticeDatum.AdaptedBasis.IsTypeA₂.exists_isPositiveWallRepresentative_scat`).
* The standard basis of the unimodular rank-two datum is of type `A₂`
  (`SkewLatticeDatum.Examples.isTypeA₂_unimodularRankTwoAdaptedBasis`), with the corresponding
  positive representative
  (`SkewLatticeDatum.Examples.exists_isPositiveWallRepresentative_unimodularRankTwo`).

These are the ordinary binomial positivity of Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1.1 and Theorem 1.13 (arXiv:1411.1394v2), for rank two and type `A₂`, where
the consistency is the pentagon identity of Nakanishi, *Cluster algebras and scattering diagrams,
Part III*, §5 (arXiv:2111.00800v6).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis

open _root_.AddMonoidAlgebra PowerSeries
open scoped Mei.TropicalVertexCoefficientAction

variable {N R ι V M : Type*} [AddCommGroup N] {D : SkewLatticeDatum N} (B : D.AdaptedBasis ι)

/-- The sum of two unfrozen basis vectors is an allowed degree. -/
theorem unfrozenBasis_add_mem_positiveDegrees_monoid (i j : B.unfrozenIndex) :
    B.unfrozenBasis i + B.unfrozenBasis j ∈ B.unfrozenBasis.positiveDegrees.monoid :=
  add_mem (B.unfrozenBasis_mem_positiveDegrees_monoid i)
    (B.unfrozenBasis_mem_positiveDegrees_monoid j)

/-- The degrees of the walls of the diagram of type `A₂` at the unfrozen indices `i₁, i₂`: the
basis vector `eᵢ` for the input wall at `i`, and `e_{i₁} + e_{i₂}` for the outgoing wall. -/
def pentagonDegree (i₁ i₂ : B.unfrozenIndex) : B.unfrozenIndex ⊕ Unit → D.unfrozen :=
  Sum.elim B.unfrozenBasis fun _ => B.unfrozenBasis i₁ + B.unfrozenBasis i₂

/-- The degree of the input wall at `i` is `eᵢ`. -/
@[simp]
theorem pentagonDegree_inl (i₁ i₂ i : B.unfrozenIndex) :
    B.pentagonDegree i₁ i₂ (.inl i) = B.unfrozenBasis i := (rfl)

/-- The degree of the outgoing wall is `e_{i₁} + e_{i₂}`. -/
@[simp]
theorem pentagonDegree_inr (i₁ i₂ : B.unfrozenIndex) (u : Unit) :
    B.pentagonDegree i₁ i₂ (.inr u) = B.unfrozenBasis i₁ + B.unfrozenBasis i₂ := (rfl)

/-- The degrees of the walls are allowed degrees. -/
theorem pentagonDegree_mem_positiveDegrees_monoid (i₁ i₂ : B.unfrozenIndex)
    (j : B.unfrozenIndex ⊕ Unit) :
    B.pentagonDegree i₁ i₂ j ∈ B.unfrozenBasis.positiveDegrees.monoid := by
  rcases j with i | ⟨⟩
  · exact B.unfrozenBasis_mem_positiveDegrees_monoid i
  · exact B.unfrozenBasis_add_mem_positiveDegrees_monoid i₁ i₂

/-- An adapted basis is *of type `A₂`* at the unfrozen indices `i₁, i₂` when these are its only
unfrozen indices, `{e_{i₁}, e_{i₂}} = 1`, and both multipliers are one, `d_{i₁} = d_{i₂} = 1`.
Frozen indices are allowed. -/
structure IsTypeA₂ (i₁ i₂ : B.unfrozenIndex) : Prop where
  /-- The unfrozen indices are `i₁` and `i₂`. -/
  eq_or_eq (i : B.unfrozenIndex) : i = i₁ ∨ i = i₂
  /-- The skew pairing of the two unfrozen basis vectors is one. -/
  form_eq_one : D.form (B.basis i₁) (B.basis i₂) = 1
  /-- The first multiplier is one. -/
  multiplier_fst : B.multiplier i₁ = 1
  /-- The second multiplier is one. -/
  multiplier_snd : B.multiplier i₂ = 1

section Binomial

variable [Module.Free ℤ N] [CommRing R] [Algebra ℚ R]
  [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]

/-- At an unfrozen index with multiplier one, the label of the ordinary binomial input (the
adapted polynomial input with `ℓᵢ = 1` and coefficient `1`, of wall function `1 + T`) is the
principal image of the dilogarithm element `Ψ[eᵢ]`. -/
theorem coe_polynomialWallLabel_one {i : B.unfrozenIndex} (hi : B.multiplier i = 1) :
    (B.polynomialWallLabel (fun _ => 1) (fun _ _ => (1 : R)) i :
        (D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees).completedBCHGroup
          (D.principalGrading (R := R) B.unfrozenBasis.positiveDegrees)) =
      B.unfrozenBasis.positiveDegrees.graphBCHGroupEquiv
        (SkewLieAlgebra.positiveGrading (D.coefficientForm R) (D.isAlt_coefficientForm R)
          B.unfrozenBasis.positiveDegrees) D.principalCharacter.toAddMonoidHom
        (SkewLieAlgebra.dilogElement (D.coefficientForm R) (D.isAlt_coefficientForm R)
          (B.unfrozenBasis_mem_positiveDegrees_monoid i) (B.unfrozenBasis.ne_zero i)) := by
  have hf : B.polynomialWallFunction (fun _ => 1) (fun _ _ => (1 : R)) i = 1 + X := by
    simp [polynomialWallFunction_def, X_eq]
  rw [coe_polynomialWallLabel, SkewLieAlgebra.dilogElement_def]
  congr 2
  rw [hf, logOf_one_add_X, eulerDerivInv_log, coe_unfrozenBasis, B.rayIndex_basis, hi,
    Nat.cast_one, map_one, one_smul]

section Action

variable (Q : AddSubmonoid (Module.Dual ℤ D.sublattice × D.unfrozen))
  [Fact ((D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees).monoid ≤ Q)]

local notation "e" => D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees
local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) e Q

/-- Let `n` be a nonzero allowed degree with ray index one. The principal image of `Ψ[n]` acts on
every monomial by `z^p ↦ (1 + z^{r(n)})^{ν(p)} z^p`, where `ν` is the principal normal of `n`.
The unit `u` is specified by its value `1 + z^{r(n)}` in the completion. -/
theorem completedBCHAction_graphBCHGroupEquiv_dilogElement {n : D.unfrozen}
    (hn : n ∈ B.unfrozenBasis.positiveDegrees.monoid) (hn0 : n ≠ 0)
    (hκ : D.sublattice.toAddSubgroup.rayIndex (n : N) = 1) (q : Q)
    (hq : q.val = D.principalEmbedding n) (u : (F).completionˣ)
    (hu : (u : (F).completion) = 1 + (F).toCompletion (single q 1)) (p : Q) (c : R) :
    (F).completedBCHAction (R := R)
        (L := tropicalVertexLieAlgebra (R := R) e
          (AddMonoidHom.id (Module.Dual ℤ D.sublattice × D.unfrozen))) e
        (tropicalVertexGrading (R := R) e
          (AddMonoidHom.id (Module.Dual ℤ D.sublattice × D.unfrozen)))
        ((D.principalGraphGradedLieHom B.unfrozenBasis.positiveDegrees).completedMap
          (B.unfrozenBasis.positiveDegrees.graphBCHGroupEquiv
            (SkewLieAlgebra.positiveGrading (D.coefficientForm R) (D.isAlt_coefficientForm R)
              B.unfrozenBasis.positiveDegrees) D.principalCharacter.toAddMonoidHom
            (SkewLieAlgebra.dilogElement (D.coefficientForm R) (D.isAlt_coefficientForm R)
              hn hn0)))
        ((F).toCompletion (single p c)) =
      ((u ^ D.principalNormal n p.val : (F).completionˣ) : (F).completion) *
        (F).toCompletion (single p c) := by
  have hmap := DFunLike.congr_fun (D.completedMap_principalGradedLieHom (R := R)
    B.unfrozenBasis.positiveDegrees)
    (SkewLieAlgebra.dilogElement (D.coefficientForm R) (D.isAlt_coefficientForm R) hn hn0)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hmap
  -- The label is transported by `congrArg`: rewriting it in goals containing the completed
  -- coefficient algebra times out.
  refine (congrArg (fun z => (F).completedBCHAction (R := R) e
    (tropicalVertexGrading (R := R) e
      (AddMonoidHom.id (Module.Dual ℤ D.sublattice × D.unfrozen))) z
    ((F).toCompletion (single p c))) hmap.symm).trans ?_
  have hk : algebraMap ℚ R (((1 : ℤ) : ℚ) * D.sublattice.toAddSubgroup.rayIndex (n : N)) •
      negDilogNeg R = negDilogNeg R := by
    rw [hκ, Int.cast_one, mul_one, map_one, one_smul]
  have hl : SkewLieAlgebra.dilogElement (D.coefficientForm R) (D.isAlt_coefficientForm R) hn hn0 =
      SkewLieAlgebra.rayExp (D.coefficientForm R) (D.isAlt_coefficientForm R) hn hn0
        (algebraMap ℚ R (((1 : ℤ) : ℚ) * D.sublattice.toAddSubgroup.rayIndex (n : N)) •
          negDilogNeg R) := by
    rw [hk, SkewLieAlgebra.dilogElement_def]
  refine (congrArg (fun z => (F).completedBCHAction (R := R) e
    (tropicalVertexGrading (R := R) e
      (AddMonoidHom.id (Module.Dual ℤ D.sublattice × D.unfrozen)))
    ((D.principalGradedLieHom B.unfrozenBasis.positiveDegrees).completedMap z)
    ((F).toCompletion (single p c))) hl).trans
    ((D.completedBCHAction_completedMap_rayExp_smul_negDilogNeg
      B.unfrozenBasis.positiveDegrees hn hn0 1 Q q hq u hu p c).trans ?_)
  exact congrArg (fun k : ℤ => ((u ^ k : (F).completionˣ) : (F).completion) *
    (F).toCompletion (single p c)) (one_mul _)

end Action

end Binomial

namespace IsTypeA₂

variable {B} {i₁ i₂ : B.unfrozenIndex} (hA : B.IsTypeA₂ i₁ i₂)
include hA

/-- The two unfrozen indices are distinct. -/
theorem ne : i₁ ≠ i₂ := by
  rintro rfl
  simpa [D.form_self] using hA.form_eq_one

/-- The first unfrozen basis vector lies in `N°`. -/
theorem basis_fst_mem_sublattice : B.basis i₁ ∈ D.sublattice := by
  simpa [hA.multiplier_fst] using B.nsmul_basis_mem_sublattice i₁

/-- The second unfrozen basis vector lies in `N°`. -/
theorem basis_snd_mem_sublattice : B.basis i₂ ∈ D.sublattice := by
  simpa [hA.multiplier_snd] using B.nsmul_basis_mem_sublattice i₂

/-- The vector `e_{i₁} + e_{i₂}` is nonzero. -/
theorem add_ne_zero : B.unfrozenBasis i₁ + B.unfrozenBasis i₂ ≠ 0 := by
  intro h0
  have h := congrArg (B.unfrozenBasis.coord i₁) h0
  have hne : i₂ ≠ i₁ := hA.ne.symm
  simp [hne] at h

/-- The supported ray of the primitive allowed degree `e_{i₁} + e_{i₂}`. -/
def addRay : SupportedRay B.unfrozenBasis.positiveDegrees where
  generator := B.unfrozenBasis i₁ + B.unfrozenBasis i₂
  isPrimitive := TauCeti.isPrimitive_def.mpr ⟨B.unfrozenBasis.coord i₁, by
    have hne : i₂ ≠ i₁ := hA.ne.symm
    simp [hne]⟩
  supported := ⟨1, one_pos, by
    simpa using B.unfrozenBasis_add_mem_positiveDegrees_monoid i₁ i₂⟩

/-- The generator of the supported ray is `e_{i₁} + e_{i₂}`. -/
@[simp]
theorem addRay_generator : hA.addRay.generator = B.unfrozenBasis i₁ + B.unfrozenBasis i₂ :=
  (rfl)

variable [Module.Free ℤ N]

/-- The normalized vector `κ(e_{i₁}) e_{i₁}` is `e_{i₁}`. -/
theorem coe_rayVector_fst :
    (D.sublattice.toAddSubgroup.rayVector (B.basis i₁) : N) = B.basis i₁ := by
  simp [hA.multiplier_fst]

/-- The normalized vector `κ(e_{i₂}) e_{i₂}` is `e_{i₂}`. -/
theorem coe_rayVector_snd :
    (D.sublattice.toAddSubgroup.rayVector (B.basis i₂) : N) = B.basis i₂ := by
  simp [hA.multiplier_snd]

/-- The sublattice coordinates dual to `e_{i₁}` and `e_{i₂}` evaluate on the normalized vectors
`κ(e_{i₁}) e_{i₁} = e_{i₁}` and `κ(e_{i₂}) e_{i₂} = e_{i₂}` as the identity matrix. -/
theorem coord_rayVector :
    B.sublatticeBasis.coord i₁ (D.sublattice.toAddSubgroup.rayVector (B.basis i₁)) = 1 ∧
      B.sublatticeBasis.coord i₁ (D.sublattice.toAddSubgroup.rayVector (B.basis i₂)) = 0 ∧
      B.sublatticeBasis.coord i₂ (D.sublattice.toAddSubgroup.rayVector (B.basis i₁)) = 0 ∧
      B.sublatticeBasis.coord i₂ (D.sublattice.toAddSubgroup.rayVector (B.basis i₂)) = 1 := by
  have hv : ∀ i : B.unfrozenIndex,
      D.sublattice.toAddSubgroup.rayVector (B.basis i) = B.sublatticeBasis i := fun i =>
    Subtype.ext (by rw [B.coe_rayVector_basis, coe_sublatticeBasis])
  have hne : (i₁ : ι) ≠ i₂ := fun he => hA.ne (Subtype.ext he)
  simp [hv, hne, hne.symm]

/-- The ray index of `e_{i₁} + e_{i₂}` is one, since this vector lies in `N°` and pairs to one
with `e_{i₁}`. -/
theorem rayIndex_add : D.sublattice.toAddSubgroup.rayIndex (B.basis i₁ + B.basis i₂) = 1 :=
  D.rayIndex_eq_one_of_form_eq_one (a := B.basis i₁)
    (add_mem (B.basis_mem_unfrozen i₁) (B.basis_mem_unfrozen i₂))
    (add_mem hA.basis_fst_mem_sublattice hA.basis_snd_mem_sublattice)
    (by simp [D.form_self, hA.form_eq_one])

/-- The normalized vector of `e_{i₁} + e_{i₂}` is the sum of those of `e_{i₁}` and `e_{i₂}`. -/
theorem rayVector_add :
    D.sublattice.toAddSubgroup.rayVector (B.basis i₁ + B.basis i₂) =
      D.sublattice.toAddSubgroup.rayVector (B.basis i₁) +
        D.sublattice.toAddSubgroup.rayVector (B.basis i₂) := by
  apply Subtype.ext
  have h := D.sublattice.toAddSubgroup.den_rayIndex_zsmul_rayVector (B.basis i₁ + B.basis i₂)
  rw [hA.rayIndex_add] at h
  simp only [Rat.den_one, Nat.cast_one, one_smul, Rat.num_one] at h
  rw [AddSubgroup.coe_add, h, hA.coe_rayVector_fst, hA.coe_rayVector_snd]

/-- The principal normal of `e_{i₁} + e_{i₂}` is the sum of those of `e_{i₁}` and `e_{i₂}`. -/
theorem principalNormal_add :
    D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂) =
      D.principalNormal (B.unfrozenBasis i₁) + D.principalNormal (B.unfrozenBasis i₂) := by
  apply LinearMap.ext
  intro x
  simp only [principalNormal_apply, Submodule.coe_add, coe_unfrozenBasis, hA.rayVector_add,
    map_add, LinearMap.add_apply]

/-- A character `χ` of `N°`, extended by zero on `N_uf`, on which the principal normal of
`e_{i₁} + e_{i₂}` vanishes and that of `e_{i₁}` is one. -/
theorem exists_principalNormal_add_eq_zero :
    ∃ χ : Module.Dual ℤ D.sublattice,
      D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂) (χ, 0) = 0 ∧
        D.principalNormal (B.unfrozenBasis i₁) (χ, 0) = 1 := by
  obtain ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩ := hA.coord_rayVector
  refine ⟨B.sublatticeBasis.coord i₁ - B.sublatticeBasis.coord i₂, ?_, ?_⟩
  · rw [hA.principalNormal_add]
    simp [h₁₁, h₁₂, h₂₁, h₂₂]
  · simp [h₁₁, h₂₁]

omit [Module.Free ℤ N] in
/-- The degrees of the walls are nonzero. -/
theorem pentagonDegree_ne_zero (j : B.unfrozenIndex ⊕ Unit) : B.pentagonDegree i₁ i₂ j ≠ 0 := by
  rcases j with i | ⟨⟩
  · exact B.unfrozenBasis.ne_zero i
  · exact hA.add_ne_zero

/-- The degrees of the walls have ray index one. -/
theorem rayIndex_pentagonDegree (j : B.unfrozenIndex ⊕ Unit) :
    D.sublattice.toAddSubgroup.rayIndex (B.pentagonDegree i₁ i₂ j : N) = 1 := by
  rcases j with i | ⟨⟩
  · rcases hA.eq_or_eq i with rfl | rfl
    · simp [B.rayIndex_basis, hA.multiplier_fst]
    · simp [B.rayIndex_basis, hA.multiplier_snd]
  · simpa using hA.rayIndex_add

/-- The principal normal of each wall degree takes the value one on some character `(χ, 0)`. -/
theorem exists_principalNormal_pentagonDegree_eq_one (j : B.unfrozenIndex ⊕ Unit) :
    ∃ χ : Module.Dual ℤ D.sublattice, D.principalNormal (B.pentagonDegree i₁ i₂ j) (χ, 0) = 1 := by
  obtain ⟨h₁₁, h₁₂, -, -⟩ := hA.coord_rayVector
  rcases j with i | ⟨⟩
  · exact B.exists_principalNormal_eq_one i
  · refine ⟨B.sublatticeBasis.coord i₁, ?_⟩
    rw [pentagonDegree_inr, hA.principalNormal_add]
    simp [h₁₁, h₁₂]

variable [CommRing R] [Algebra ℚ R]
  [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : (Module.Dual ℤ D.sublattice × D.unfrozen) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

local notation "𝒅" => B.unfrozenBasis.positiveDegrees
local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "ℒ" => SkewLieAlgebra.positiveGrading
  (D.coefficientForm R) (D.isAlt_coefficientForm R) 𝒅
local notation "e" => D.principalPositiveDegrees 𝒅
local notation "𝓗" => D.principalGraphWallSpaces (R := R) 𝒅

/-- The principal image of the dilogarithm element `Ψ[e_{i₁} + e_{i₂}]`, as a wall label on the
principal graph ray through `r(e_{i₁} + e_{i₂})` with the principal normal of
`e_{i₁} + e_{i₂}`. -/
def addLabel : (𝓗).wallGroup (hA.addRay.graph D.principalCharacter.toAddMonoidHom)
    (D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)).toAddMonoidHom :=
  ⟨(𝒅).graphBCHGroupEquiv ℒ D.principalCharacter.toAddMonoidHom
    (SkewLieAlgebra.dilogElement (D.coefficientForm R) (D.isAlt_coefficientForm R)
      (B.unfrozenBasis_add_mem_positiveDegrees_monoid i₁ i₂) hA.add_ne_zero), by
    rw [← D.map_principalGraphWallGroup]
    exact Subgroup.mem_map.mpr ⟨_, D.rayExp_mem_principalWallGroup (R := R) 𝒅
      ((SupportedRay.generator_mem_rayDegrees_iff _).mpr
        (B.unfrozenBasis_add_mem_positiveDegrees_monoid i₁ i₂)) (negDilogNeg R), by
      -- The two sides differ only in the coercion of the graph comparison to a monoid hom.
      rw [SkewLieAlgebra.dilogElement_def]
      rfl⟩⟩

/-- The outgoing wall of type `A₂`: the half-hyperplane of the principal normal `ν₁₂` of
`e_{i₁} + e_{i₂}` on which the principal normal `ν₁` of `e_{i₁}` is nonnegative, cooriented by
`ν₁₂`, on the principal ray through `r(e_{i₁} + e_{i₂})`, with the principal image of the
dilogarithm element `Ψ[e_{i₁} + e_{i₂}]` as label. -/
def outgoingWall : DirectedWall (V := V) (d := e) h 𝓗 :=
  (DirectedWall.ofAffineHyperplane h 𝓗
    (D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)).toAddMonoidHom
    (fun hz => hA.add_ne_zero ((D.principalNormal_eq_zero_iff _).mp
      (LinearMap.toAddMonoidHom_injective hz))) 0
    (hA.addRay.graph D.principalCharacter.toAddMonoidHom)
    (by
      apply Int.cast_injective (α := ℚ)
      simp only [SupportedRay.graph_generator, addRay_generator, AddMonoidHom.id_apply,
        LinearMap.toAddMonoidHom_coe]
      rw [← D.principalEmbedding_apply, D.cast_principalNormal_principalEmbedding, D.form_self,
        mul_zero, Int.cast_zero])
    hA.addLabel).cutHalfspace (D.principalNormal (B.unfrozenBasis i₁)).toAddMonoidHom 0 (by
      obtain ⟨χ, h₀, h₁⟩ := hA.exists_principalNormal_add_eq_zero
      exact ⟨latticeMap (χ, 0), by simp [h₀], by simp [h₁]⟩)

/-- The outgoing wall is cooriented by the principal normal of `e_{i₁} + e_{i₂}`. -/
@[simp]
theorem outgoingWall_normal : (hA.outgoingWall (R := R) h).normal =
    (D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)).toAddMonoidHom := by
  simp [outgoingWall]

/-- The outgoing wall lies on the principal ray through `r(e_{i₁} + e_{i₂})`. -/
@[simp]
theorem outgoingWall_ray : (hA.outgoingWall (R := R) h).ray =
    hA.addRay.graph D.principalCharacter.toAddMonoidHom := by
  simp [outgoingWall]

/-- The support of the outgoing wall is the half-hyperplane `{ν₁₂ = 0, ν₁ ≥ 0}`. -/
@[simp]
theorem outgoingWall_support : (hA.outgoingWall (R := R) h).support =
    {x | h.realCharacter
        (D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)).toAddMonoidHom x = 0} ∩
      {x | 0 ≤ h.realCharacter (D.principalNormal (B.unfrozenBasis i₁)).toAddMonoidHom x} := by
  simp [outgoingWall]

/-- The label of the outgoing wall is the principal image of `Ψ[e_{i₁} + e_{i₂}]`. -/
@[simp]
theorem outgoingWall_label : (hA.outgoingWall (R := R) h).label =
    (𝒅).graphBCHGroupEquiv ℒ D.principalCharacter.toAddMonoidHom
      (SkewLieAlgebra.dilogElement (D.coefficientForm R) (D.isAlt_coefficientForm R)
        (B.unfrozenBasis_add_mem_positiveDegrees_monoid i₁ i₂) hA.add_ne_zero) := by
  simp [outgoingWall]
  -- The remaining goal is the definition of `addLabel`.
  rfl

/-- The outgoing wall is outgoing: the degree direction `r(e_{i₁} + e_{i₂})` pairs to
`{e_{i₁} + e_{i₂}, e_{i₁}} = -1` with `ν₁`, so it leaves the half-hyperplane. -/
theorem outgoingWall_outgoing : (hA.outgoingWall (R := R) h).Outgoing := by
  refine (DirectedWall.outgoing_iff _).mpr fun hrec => ?_
  have hinc := (DirectedWall.incoming_iff _).mpr (Set.mem_recessionCone.mp hrec)
  rw [outgoingWall, DirectedWall.incoming_cutHalfspace_iff _ _ _ _
    (DirectedWall.ofAffineHyperplane_incoming ..)] at hinc
  have hq : ((D.principalNormal (B.unfrozenBasis i₁) (D.principalEmbedding
      (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)) : ℤ) : ℚ) = -1 := by
    rw [D.cast_principalNormal_principalEmbedding]
    simp only [Submodule.coe_add, coe_unfrozenBasis, B.rayIndex_basis, hA.multiplier_fst,
      map_add, LinearMap.add_apply, D.form_self, D.form_swap (B.basis i₁), hA.form_eq_one]
    norm_num
  have hle' : 0 ≤ D.principalNormal (B.unfrozenBasis i₁) (D.principalEmbedding
      (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)) := by
    simpa [principalEmbedding_apply] using hinc
  have : (0 : ℚ) ≤ (D.principalNormal (B.unfrozenBasis i₁) (D.principalEmbedding
      (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)) : ℚ) := by exact_mod_cast hle'
  linarith

/-- The diagram of type `A₂`: the two walls of the ordinary binomial input, the adapted
polynomial input with `ℓ = 1` and coefficients `1`, together with the outgoing wall. -/
def pentagonDiagram : DirectedDiagram (V := V) (d := e) h 𝓗 (B.unfrozenIndex ⊕ Unit) :=
  DirectedDiagram.ofFinite (Sum.elim (B.adaptedPolynomialInput (V := V) (fun _ => 1)
    (fun _ _ => (1 : R)) h).wall fun _ => hA.outgoingWall h)

/-- The walls indexed by the unfrozen indices are those of the ordinary binomial input. -/
@[simp]
theorem pentagonDiagram_wall_inl (i : B.unfrozenIndex) :
    (hA.pentagonDiagram (R := R) h).wall (.inl i) =
      (B.adaptedPolynomialInput (V := V) (fun _ => 1) (fun _ _ => (1 : R)) h).wall i := by
  simp [pentagonDiagram]

/-- The remaining wall is the outgoing wall. -/
@[simp]
theorem pentagonDiagram_wall_inr (u : Unit) :
    (hA.pentagonDiagram (R := R) h).wall (.inr u) = hA.outgoingWall h := by
  simp [pentagonDiagram]

/-- The diagram of type `A₂` is in pentagon configuration: its walls are the hyperplanes of the
principal normals `ν₁, ν₂` of `e_{i₁}, e_{i₂}` and the half-hyperplane `{ν₁ + ν₂ = 0, ν₁ ≥ 0}`
cooriented by `ν₁ + ν₂`. -/
theorem isPentagonConfiguration :
    (hA.pentagonDiagram (R := R) h).IsPentagonConfiguration (.inl i₁) (.inl i₂) (.inr ())
      (D.principalNormal (B.unfrozenBasis i₁)).toAddMonoidHom
      (D.principalNormal (B.unfrozenBasis i₂)).toAddMonoidHom := by
  obtain ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩ := hA.coord_rayVector
  have hadd : (D.principalNormal (B.unfrozenBasis i₁ + B.unfrozenBasis i₂)).toAddMonoidHom =
      (D.principalNormal (B.unfrozenBasis i₁)).toAddMonoidHom +
        (D.principalNormal (B.unfrozenBasis i₂)).toAddMonoidHom := by
    ext x
    simp [hA.principalNormal_add]
  refine
    { eq_or_eq_or_eq := ?_
      normal_fst := by simp
      normal_snd := by simp
      normal_half := by simp [hadd]
      support_fst := by ext; simp
      support_snd := by ext; simp
      support_half := by ext; simp [hadd]
      exists_fst := ⟨latticeMap (B.sublatticeBasis.coord i₂, 0), by simp [h₂₁], by simp [h₂₂]⟩
      exists_snd := ⟨latticeMap (B.sublatticeBasis.coord i₁, 0), by simp [h₁₂], by simp [h₁₁]⟩ }
  rintro (i | ⟨⟩)
  · rcases hA.eq_or_eq i with rfl | rfl <;> simp
  · simp

/-- The labels of the diagram of type `A₂` satisfy the pentagon relation
`Ψ[e_{i₂}] Ψ[e_{i₁}] = Ψ[e_{i₁}] Ψ[e_{i₁} + e_{i₂}] Ψ[e_{i₂}]`. -/
theorem pentagonDiagram_label_pentagon :
    ((hA.pentagonDiagram (R := R) h).wall (.inl i₂)).label *
        ((hA.pentagonDiagram (R := R) h).wall (.inl i₁)).label =
      ((hA.pentagonDiagram (R := R) h).wall (.inl i₁)).label *
        ((hA.pentagonDiagram (R := R) h).wall (.inr ())).label *
        ((hA.pentagonDiagram (R := R) h).wall (.inl i₂)).label := by
  simp only [pentagonDiagram_wall_inl, pentagonDiagram_wall_inr, adaptedPolynomialInput_label,
    outgoingWall_label, B.coe_polynomialWallLabel_one hA.multiplier_fst,
    B.coe_polynomialWallLabel_one hA.multiplier_snd, ← map_mul]
  congr 1
  refine SkewLieAlgebra.dilogElement_pentagon _ _ _ _ _ _ _ ?_
  rw [coefficientForm_apply, coe_unfrozenBasis, coe_unfrozenBasis, hA.form_eq_one, map_one]

/-- The diagram of type `A₂` is consistent. -/
theorem pentagonDiagram_consistent : (hA.pentagonDiagram (R := R) h).Consistent :=
  (hA.isPentagonConfiguration h).consistent (hA.pentagonDiagram_label_pentagon h)

/-- The diagram of type `A₂` is an outgoing completion of the ordinary binomial input: its walls
at the unfrozen indices are the input walls, its remaining wall is outgoing, and it is
consistent. -/
theorem isOutgoingCompletion_pentagonDiagram :
    DirectedDiagram.IsOutgoingCompletion
      (B.adaptedPolynomialInput (V := V) (fun _ => 1) (fun _ _ => (1 : R)) h).wall
      (hA.pentagonDiagram h) where
  wall_inl := hA.pentagonDiagram_wall_inl h
  outgoing_inr _ := by
    rw [pentagonDiagram_wall_inr]
    exact hA.outgoingWall_outgoing h
  consistent := hA.pentagonDiagram_consistent h

/-- **The scattering diagram of type `A₂`.** For an adapted basis of type `A₂`, the outgoing
scattering class of the ordinary binomial input `(e_{i}⊥, 1 + q^{e_i})`, `i = i₁, i₂`, on the
principal lattice is the class of the diagram with the one additional outgoing wall
`{ν₁ + ν₂ = 0, ν₁ ≥ 0}` labelled by `Ψ[e_{i₁} + e_{i₂}]`. -/
theorem scat_eq_toClass_pentagonDiagram
    [Module.Free ℤ (Module.Dual ℤ D.sublattice × D.unfrozen)] :
    (B.adaptedPolynomialInput (V := V) (fun _ => 1) (fun _ _ => (1 : R)) h).Scat
        (B.adaptedPolynomialInput_full _ _ h) = (hA.pentagonDiagram h).toClass :=
  DirectedDiagram.scat_eq_toClass _ _ (hA.isOutgoingCompletion_pentagonDiagram h)

/-- The wall of the diagram of type `A₂` indexed by `j` has the principal normal of
`pentagonDegree i₁ i₂ j`. -/
theorem pentagonDiagram_normal (j : B.unfrozenIndex ⊕ Unit) :
    ((hA.pentagonDiagram (R := R) h).wall j).normal =
      (D.principalNormal (B.pentagonDegree i₁ i₂ j)).toAddMonoidHom := by
  rcases j with i | ⟨⟩ <;> simp

/-- The label of the wall of the diagram of type `A₂` indexed by `j` is the principal image of
the dilogarithm element `Ψ[n]` of `n = pentagonDegree i₁ i₂ j`. -/
theorem pentagonDiagram_label (j : B.unfrozenIndex ⊕ Unit) :
    ((hA.pentagonDiagram (R := R) h).wall j).label =
      (𝒅).graphBCHGroupEquiv ℒ D.principalCharacter.toAddMonoidHom
        (SkewLieAlgebra.dilogElement (D.coefficientForm R) (D.isAlt_coefficientForm R)
          (B.pentagonDegree_mem_positiveDegrees_monoid i₁ i₂ j) (hA.pentagonDegree_ne_zero j)) := by
  rcases j with i | ⟨⟩
  · rcases hA.eq_or_eq i with rfl | rfl
    -- The remaining goals differ only in the proofs that the degrees are allowed and nonzero.
    · simp [B.coe_polynomialWallLabel_one hA.multiplier_fst]
      rfl
    · simp [B.coe_polynomialWallLabel_one hA.multiplier_snd]
      rfl
  · simp
    rfl

variable [AddCommGroup M] (π : Module.Dual ℤ D.sublattice × D.unfrozen →+ M)

/-- The coorientations of the walls of the diagram of type `A₂` are primitive. -/
theorem isPrimitive_pentagonDiagram_normal (j : B.unfrozenIndex ⊕ Unit) :
    TauCeti.IsPrimitive ((hA.pentagonDiagram (R := R) h).wall j).normal := by
  have := Module.Free.of_basis B.sublatticeBasis
  have hp := ((addMonoidHomLequivInt (B := ℤ) ℤ).symm.isPrimitive_iff).mpr
    (D.isPrimitive_principalNormal (hA.pentagonDegree_ne_zero j))
  rwa [addMonoidHomLequivInt_symm_apply, ← hA.pentagonDiagram_normal (R := R) h j] at hp

variable (Q : AddSubmonoid (Module.Dual ℤ D.sublattice × D.unfrozen))
  [Fact ((D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees).monoid ≤ Q)]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) e Q
local notation "σ" => MonoidHom.comp (AlgFiltration.completedBCHAction (F) e
  (tropicalVertexGrading (R := R) e (AddMonoidHom.id Lpr)))
  (GradedLieHom.completedMap (D.principalGraphGradedLieHom (R := R) 𝒅))

/-- If the coefficient monoid `Q` contains every character `(χ, 0)`, the discrete grouping of the
diagram of type `A₂`, in which every wall is its own function wall, is positive for the image of
`ℕ[Q]`: the wall of a degree `n ∈ {e_{i₁}, e_{i₂}, e_{i₁} + e_{i₂}}` has the wall function
`1 + q^n = 1 + z^{r(n)}`. -/
theorem isPositive_discrete_pentagonDiagram
    (hQ : ∀ χ : Module.Dual ℤ D.sublattice, ((χ, 0) : Lpr) ∈ Q) :
    (DirectedDiagram.FunctionWallGrouping.discrete (hA.pentagonDiagram (R := R) h)
      (hA.isPrimitive_pentagonDiagram_normal h) π).IsPositive σ
      (mapRingHom Q (Nat.castRingHom R)).rangeS := by
  rw [DirectedDiagram.FunctionWallGrouping.isPositive_iff]
  intro j
  -- Destructuring with `obtain` re-elaborates the goal and times out.
  let χ := (hA.exists_principalNormal_pentagonDegree_eq_one j).choose
  have hχ := (hA.exists_principalNormal_pentagonDegree_eq_one j).choose_spec
  have hn := B.pentagonDegree_mem_positiveDegrees_monoid i₁ i₂ j
  have hn0 := hA.pentagonDegree_ne_zero j
  have hν := hA.pentagonDiagram_normal (R := R) h j
  have hl := hA.pentagonDiagram_label (R := R) h j
  have hr : D.principalEmbedding (B.pentagonDegree i₁ i₂ j) ∈ (e).monoid := by
    rw [principalEmbedding_apply, PositiveDegrees.mem_graph_monoid]
    exact ⟨hn, by simp⟩
  let q : Q := ⟨D.principalEmbedding (B.pentagonDegree i₁ i₂ j), (Fact.out : (e).monoid ≤ Q) hr⟩
  have hq := D.toCompletion_single_principalEmbedding_mem_first (R := R) 𝒅 hn hn0 Q q rfl
  let u : (F).completionˣ := ((F).isUnit_of_sub_one_mem (u := 1 + (F).toCompletion (single q 1))
    (by rwa [add_sub_cancel_left])).unit
  have hu : (u : (F).completion) = 1 + (F).toCompletion (single q 1) := IsUnit.unit_spec _
  refine ⟨u, ?_, ?_⟩
  · rw [DirectedDiagram.FunctionWallGrouping.isWallFunction_iff]
    intro j' hj'
    rw [DirectedDiagram.FunctionWallGrouping.discrete_group] at hj'
    subst hj'
    have hmul : (single (⟨(χ, 0), hQ χ⟩ : Q) (1 : R) *
        single ⟨(-χ, 0), hQ (-χ)⟩ 1 : AddMonoidAlgebra R Q) = 1 := by
      rw [single_mul_single, mul_one, one_def]
      exact congrArg (single · 1) (Subtype.ext (by simp))
    refine ⟨⟨⟨(χ, 0), hQ χ⟩, by rw [hν]; exact hχ,
      (isUnit_iff_exists_inv.mpr ⟨_, hmul⟩).map (F).toCompletion⟩, fun p c => ?_⟩
    -- The label and the normal are transported by `congrArg`: rewriting them with `rw` in
    -- goals containing the completed coefficient algebra times out.
    refine (congrArg (fun g => (σ) g ((F).toCompletion (single p c)))
      ((DirectedDiagram.FunctionWallGrouping.label_discrete _ j').trans hl)).trans
      ((B.completedBCHAction_graphBCHGroupEquiv_dilogElement Q hn hn0
        (hA.rayIndex_pentagonDegree j') q rfl u hu p c).trans ?_)
    exact congrArg (fun k : ℤ => ((u ^ k : (F).completionˣ) : (F).completion) *
      (F).toCompletion (single p c)) (congrArg (fun ν : Lpr →+ ℤ => ν p.val) hν).symm
  · rw [hu, ← map_one (F).toCompletion, ← map_add]
    refine AlgFiltration.isPositive_toCompletion (add_mem (one_mem _) ⟨single q 1, ?_⟩)
    simp

/-- Under the hypothesis of `isPositive_discrete_pentagonDiagram`, the diagram of type `A₂` is a
positive wall representative for the image of `ℕ[Q]`. -/
theorem isPositiveWallRepresentative_pentagonDiagram
    (hQ : ∀ χ : Module.Dual ℤ D.sublattice, ((χ, 0) : Lpr) ∈ Q) :
    (hA.pentagonDiagram (R := R) h).IsPositiveWallRepresentative σ
      (mapRingHom Q (Nat.castRingHom R)).rangeS π :=
  (hA.isPositive_discrete_pentagonDiagram h π Q hQ).isPositiveWallRepresentative

/-- **Positivity of the ordinary binomial walls of type `A₂`.** For an adapted basis of type
`A₂` and a coefficient monoid `Q` containing every character `(χ, 0)`, the outgoing scattering
class of the ordinary binomial input on the principal lattice has a consistent outgoing
representative, the diagram of type `A₂`, whose grouped wall functions `1 + q^{e_{i₁}}`,
`1 + q^{e_{i₂}}` and `1 + q^{e_{i₁} + e_{i₂}}` are positive for the image of `ℕ[Q]`. -/
theorem exists_isPositiveWallRepresentative_scat
    [Module.Free ℤ (Module.Dual ℤ D.sublattice × D.unfrozen)]
    (hQ : ∀ χ : Module.Dual ℤ D.sublattice, ((χ, 0) : Lpr) ∈ Q) :
    ∃ (κ : Type) (E : DirectedDiagram (V := V) (d := e) h 𝓗 (B.unfrozenIndex ⊕ κ)),
      DirectedDiagram.IsOutgoingCompletion
        (B.adaptedPolynomialInput (V := V) (fun _ => 1) (fun _ _ => (1 : R)) h).wall E ∧
      E.toClass = (B.adaptedPolynomialInput (V := V) (fun _ => 1) (fun _ _ => (1 : R)) h).Scat
        (B.adaptedPolynomialInput_full _ _ h) ∧
      E.IsPositiveWallRepresentative σ (mapRingHom Q (Nat.castRingHom R)).rangeS π :=
  ⟨Unit, hA.pentagonDiagram h, hA.isOutgoingCompletion_pentagonDiagram h,
    (hA.scat_eq_toClass_pentagonDiagram h).symm,
    hA.isPositiveWallRepresentative_pentagonDiagram h π Q hQ⟩

end IsTypeA₂


end Mei.SkewLatticeDatum.AdaptedBasis

namespace Mei.SkewLatticeDatum.Examples

open AdaptedBasis

/-- The standard basis of the unimodular rank-two datum, with `{e₁, e₂} = 1` and `N° = N`, is of
type `A₂` at its two indices. -/
theorem isTypeA₂_unimodularRankTwoAdaptedBasis :
    unimodularRankTwoAdaptedBasis.IsTypeA₂ ⟨0, by simp⟩ ⟨1, by simp⟩ where
  eq_or_eq i := by
    obtain ⟨i, hi⟩ := i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  form_eq_one := by simp
  multiplier_fst := unimodularRankTwoAdaptedBasis_multiplier _
  multiplier_snd := unimodularRankTwoAdaptedBasis_multiplier _

variable {R V M : Type*} [CommRing R] [Algebra ℚ R] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : Module.Dual ℤ unimodularRankTwo.sublattice × unimodularRankTwo.unfrozen →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap) [AddCommGroup M]
  (π : Module.Dual ℤ unimodularRankTwo.sublattice × unimodularRankTwo.unfrozen →+ M)

open scoped Mei.TropicalVertexCoefficientAction

open scoped Classical in
/-- **The cluster scattering diagram of type `A₂`.** For the unimodular rank-two datum with
`{e₁, e₂} = 1`, the outgoing scattering class of the ordinary binomial input
`(e₁⊥, 1 + q^{e₁})`, `(e₂⊥, 1 + q^{e₂})` on the principal lattice has a consistent outgoing
representative with the single additional wall `{ν_{e₁} + ν_{e₂} = 0, ν_{e₁} ≥ 0}`, whose
grouped wall functions `1 + q^{e₁}`, `1 + q^{e₂}` and `1 + q^{e₁ + e₂}` are positive for the image
of `ℕ[Q]`, `Q` the principal coefficient monoid. -/
theorem exists_isPositiveWallRepresentative_unimodularRankTwo :
    letI : Fact ((unimodularRankTwo.principalPositiveDegrees
        unimodularRankTwoAdaptedBasis.unfrozenBasis.positiveDegrees).monoid ≤
        unimodularRankTwo.principalCoefficientMonoid
          unimodularRankTwoAdaptedBasis.unfrozenBasis.positiveDegrees) :=
      ⟨unimodularRankTwo.principalPositiveDegrees_le_coefficientMonoid _⟩
    ∃ (κ : Type) (E : DirectedDiagram (V := V) h
        (unimodularRankTwo.principalGraphWallSpaces (R := R)
          unimodularRankTwoAdaptedBasis.unfrozenBasis.positiveDegrees)
        (unimodularRankTwoAdaptedBasis.unfrozenIndex ⊕ κ)),
      DirectedDiagram.IsOutgoingCompletion (unimodularRankTwoAdaptedBasis.adaptedPolynomialInput
        (V := V) (fun _ => 1) (fun _ _ => (1 : R)) h).wall E ∧
      E.IsPositiveWallRepresentative
        ((AlgFiltration.completedBCHAction (TropicalVertexCoefficientAction.filtration (R := R)
          (unimodularRankTwo.principalPositiveDegrees
            unimodularRankTwoAdaptedBasis.unfrozenBasis.positiveDegrees)
          (unimodularRankTwo.principalCoefficientMonoid
            unimodularRankTwoAdaptedBasis.unfrozenBasis.positiveDegrees))
          (unimodularRankTwo.principalPositiveDegrees
            unimodularRankTwoAdaptedBasis.unfrozenBasis.positiveDegrees)
          (tropicalVertexGrading (R := R) (unimodularRankTwo.principalPositiveDegrees
            unimodularRankTwoAdaptedBasis.unfrozenBasis.positiveDegrees) (AddMonoidHom.id _))).comp
          (unimodularRankTwo.principalGraphGradedLieHom (R := R)
            unimodularRankTwoAdaptedBasis.unfrozenBasis.positiveDegrees).completedMap)
        (AddMonoidAlgebra.mapRingHom _ (Nat.castRingHom R)).rangeS π := by
  have : Fact ((unimodularRankTwo.principalPositiveDegrees
      unimodularRankTwoAdaptedBasis.unfrozenBasis.positiveDegrees).monoid ≤
      unimodularRankTwo.principalCoefficientMonoid
        unimodularRankTwoAdaptedBasis.unfrozenBasis.positiveDegrees) :=
    ⟨unimodularRankTwo.principalPositiveDegrees_le_coefficientMonoid _⟩
  exact ⟨Unit, isTypeA₂_unimodularRankTwoAdaptedBasis.pentagonDiagram h,
    isTypeA₂_unimodularRankTwoAdaptedBasis.isOutgoingCompletion_pentagonDiagram h,
    isTypeA₂_unimodularRankTwoAdaptedBasis.isPositiveWallRepresentative_pentagonDiagram h π _
      fun _ => (unimodularRankTwo.mem_principalCoefficientMonoid _ _).mpr (zero_mem _)⟩

end Mei.SkewLatticeDatum.Examples
