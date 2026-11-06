/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Incoming
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.Binomial
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pentagon
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Append
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Halfspace
public import Mei.Algebra.Lie.Logarithmic.Pentagon

/-!
# Rank-two polynomial inputs of type `A₂`

A rank-two polynomial input `I` is *of type `A₂`* at two lines `j₁, j₂` with exponents `n₁, n₂`
(`RankTwoPolynomialInput.IsTypeA₂`) when it has no other lines, both lines pass through the
origin, their wall functions are the binomials `1 + c₁ z^{n₁}` and `1 + c₂ z^{n₂}`, and the
cylinder normals `νᵢ = ν_{jᵢ} ∘ π` satisfy `ν₁(n₂) = -1` and `ν₂(n₁) = 1`. The
coefficients `c₁, c₂` are arbitrary.

* Adding to the incoming diagram the half-hyperplane `{ν₁ + ν₂ = 0, ν₁ ≥ 0}`, the cylinder over
  the ray `ℝ_{≥0} π(-(n₁ + n₂))`, cooriented by `ν₁ + ν₂` and labelled by the binomial label of
  `1 + c₁ c₂ z^{n₁ + n₂}` (`IsTypeA₂.outgoingWall`), gives a consistent diagram, the *pentagon
  diagram* (`IsTypeA₂.pentagonDiagram_consistent`). Its new wall is outgoing, so it is an outgoing
  completion of the input (`IsTypeA₂.isOutgoingCompletion_pentagonDiagram`) and represents its
  scattering class (`IsTypeA₂.scat_eq_toClass_pentagonDiagram`).
* In the discrete grouping the three nontrivial walls have the wall functions `1 + c₁ z^{n₁}`,
  `1 + c₂ z^{n₂}` and `1 + c₁ c₂ z^{n₁ + n₂}` and all other walls have wall function `1`, when the
  coefficient monoid `Q` contains `-n₁` and `-n₂`. If `c₁, c₂` lie in the image of a semiring map
  `φ : S →+* R`, the pentagon diagram is a positive wall representative of the scattering class
  for the image of `S[Q]` (`IsTypeA₂.exists_isPositiveWallRepresentative_scat`); for independent
  variables over `ℚ` the grouped wall functions have coefficients in `ℕ[c₁, c₂]`.

The walls at `n₁`, `n₂` and the outgoing wall are in pentagon configuration
(`IsTypeA₂.isPentagonConfiguration`), and their labels satisfy the pentagon identity of the
tropical vertex group `Mei.binomialLabel_pentagon`. The ray walls of the two lines on the other
supported rays have trivial labels (`IsTypeA₂.incomingDiagram_label_eq_one`).

This is the case of two binomial lines with unimodular pairing of Burcroff–Lee–Mou, *Positivity of
generalized cluster scattering diagrams*, Theorem 9.9 (arXiv:2503.03719v1): the consistent
completion is the scattering diagram of type `A₂` of Gross–Pandharipande–Siebert, *Quivers, curves,
and the tropical vertex*, Example 1.6 (arXiv:0902.0779v3), and Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Example 1.15 (arXiv:1411.1394v2).
-/

public section

noncomputable section

namespace Mei.RankTwoPolynomialInput

open _root_.AddMonoidAlgebra

variable {L M ι : Type*} [AddCommGroup L] [AddCommGroup M] {d : PositiveDegrees L}
  (I : RankTwoPolynomialInput d M ι)

/-- A rank-two polynomial input is *of type `A₂`* at the lines `j₁, j₂` with exponents `n₁, n₂`
when every line is `j₁` or `j₂`, the wall functions of `j₁` and `j₂` have the single terms
`c₁ z^{n₁}` and `c₂ z^{n₂}`, both lines pass through the origin, and the cylinder normals satisfy
`ν_{j₁}(π(n₂)) = -1` and `ν_{j₂}(π(n₁)) = 1`. -/
structure IsTypeA₂ (j₁ j₂ : ι) (n₁ n₂ : L) : Prop where
  /-- Every line is one of the two. -/
  eq_or_eq (j : ι) : j = j₁ ∨ j = j₂
  /-- The only exponent of the first line is `n₁`. -/
  exponents_fst : I.exponents j₁ = {n₁}
  /-- The only exponent of the second line is `n₂`. -/
  exponents_snd : I.exponents j₂ = {n₂}
  /-- The first line passes through the origin. -/
  offset_fst : I.offset j₁ = 0
  /-- The second line passes through the origin. -/
  offset_snd : I.offset j₂ = 0
  /-- The first cylinder normal pairs to `-1` with the second exponent. -/
  wallNormal_fst_snd : I.wallNormal j₁ n₂ = -1
  /-- The second cylinder normal pairs to `1` with the first exponent. -/
  wallNormal_snd_fst : I.wallNormal j₂ n₁ = 1

namespace IsTypeA₂

variable {I} {j₁ j₂ : ι} {n₁ n₂ : L} (hA : I.IsTypeA₂ j₁ j₂ n₁ n₂)
include hA

/-- The exponent of the first line is `n₁`. -/
theorem mem_exponents_fst : n₁ ∈ I.exponents j₁ :=
  I.mem_exponents_of_eq_singleton hA.exponents_fst

/-- The exponent of the second line is `n₂`. -/
theorem mem_exponents_snd : n₂ ∈ I.exponents j₂ :=
  I.mem_exponents_of_eq_singleton hA.exponents_snd

/-- The first exponent is an allowed degree. -/
theorem mem_monoid_fst : n₁ ∈ d.monoid := I.mem_monoid_of_mem_exponents hA.mem_exponents_fst

/-- The second exponent is an allowed degree. -/
theorem mem_monoid_snd : n₂ ∈ d.monoid := I.mem_monoid_of_mem_exponents hA.mem_exponents_snd

/-- The first exponent is nonzero. -/
theorem ne_zero_fst : n₁ ≠ 0 := I.ne_zero_of_mem_exponents hA.mem_exponents_fst

/-- The second exponent is nonzero. -/
theorem ne_zero_snd : n₂ ≠ 0 := I.ne_zero_of_mem_exponents hA.mem_exponents_snd

/-- The first exponent is tangent to the first cylinder. -/
theorem wallNormal_fst_fst : I.wallNormal j₁ n₁ = 0 :=
  I.wallNormal_eq_zero_of_mem_exponents hA.mem_exponents_fst

/-- The second exponent is tangent to the second cylinder. -/
theorem wallNormal_snd_snd : I.wallNormal j₂ n₂ = 0 :=
  I.wallNormal_eq_zero_of_mem_exponents hA.mem_exponents_snd

/-- The two lines are distinct. -/
theorem fst_ne_snd : j₁ ≠ j₂ := by
  intro he
  have h₁ := hA.wallNormal_snd_fst
  rw [← he, hA.wallNormal_fst_fst] at h₁
  exact zero_ne_one h₁

/-- The sum `n₁ + n₂` is tangent to the sum `ν₁ + ν₂` of the cylinder normals. -/
theorem wallNormal_add_add : (I.wallNormal j₁ + I.wallNormal j₂) (n₁ + n₂) = 0 := by
  simp [hA.wallNormal_fst_fst, hA.wallNormal_fst_snd, hA.wallNormal_snd_fst,
    hA.wallNormal_snd_snd]

/-- The first cylinder normal pairs to `-1` with `n₁ + n₂`. -/
theorem wallNormal_fst_add : I.wallNormal j₁ (n₁ + n₂) = -1 := by
  rw [map_add, hA.wallNormal_fst_fst, hA.wallNormal_fst_snd, zero_add]

/-- The second cylinder normal pairs to `1` with `n₁ + n₂`. -/
theorem wallNormal_snd_add : I.wallNormal j₂ (n₁ + n₂) = 1 := by
  rw [map_add, hA.wallNormal_snd_fst, hA.wallNormal_snd_snd, add_zero]

/-- The sum `ν₁ + ν₂` of the cylinder normals takes the value `1` at `-n₂`. -/
theorem wallNormal_add_neg_snd : (I.wallNormal j₁ + I.wallNormal j₂) (-n₂) = 1 := by
  simp [hA.wallNormal_fst_snd, hA.wallNormal_snd_snd]

/-- The sum `n₁ + n₂` is an allowed degree. -/
theorem add_mem_monoid : n₁ + n₂ ∈ d.monoid := add_mem hA.mem_monoid_fst hA.mem_monoid_snd

/-- The sum `n₁ + n₂` is nonzero. -/
theorem add_ne_zero : n₁ + n₂ ≠ 0 :=
  d.add_ne_zero hA.mem_monoid_fst hA.mem_monoid_snd hA.ne_zero_fst

/-- The supported ray through `n₁`: the exponent `n₁` is primitive, since `ν₂(n₁) = 1`. -/
def fstRay : SupportedRay d :=
  SupportedRay.ofMem n₁ hA.mem_monoid_fst
    (TauCeti.isPrimitive_def.mpr ⟨(I.wallNormal j₂).toIntLinearMap, hA.wallNormal_snd_fst⟩)

/-- The supported ray through `n₂`: the exponent `n₂` is primitive, since `-ν₁(n₂) = 1`. -/
def sndRay : SupportedRay d :=
  SupportedRay.ofMem n₂ hA.mem_monoid_snd
    (TauCeti.isPrimitive_def.mpr ⟨(-I.wallNormal j₁).toIntLinearMap, by
      simp [hA.wallNormal_fst_snd]⟩)

/-- The supported ray through `n₁ + n₂`: the degree `n₁ + n₂` is primitive, since
`ν₂(n₁ + n₂) = 1`. -/
def addRay : SupportedRay d :=
  SupportedRay.ofMem (n₁ + n₂) hA.add_mem_monoid
    (TauCeti.isPrimitive_def.mpr ⟨(I.wallNormal j₂).toIntLinearMap, hA.wallNormal_snd_add⟩)

/-- The generator of the first ray is `n₁`. -/
@[simp]
theorem fstRay_generator : hA.fstRay.generator = n₁ := SupportedRay.generator_ofMem ..

/-- The generator of the second ray is `n₂`. -/
@[simp]
theorem sndRay_generator : hA.sndRay.generator = n₂ := SupportedRay.generator_ofMem ..

/-- The generator of the ray through `n₁ + n₂` is `n₁ + n₂`. -/
@[simp]
theorem addRay_generator : hA.addRay.generator = n₁ + n₂ := SupportedRay.generator_ofMem ..

/-- The degree `n₁` lies on the first ray. -/
theorem mem_fstRay_rayDegrees : n₁ ∈ hA.fstRay.rayDegrees :=
  SupportedRay.mem_rayDegrees_ofMem ..

/-- The degree `n₂` lies on the second ray. -/
theorem mem_sndRay_rayDegrees : n₂ ∈ hA.sndRay.rayDegrees :=
  SupportedRay.mem_rayDegrees_ofMem ..

/-- The degree `n₁ + n₂` lies on the ray through it. -/
theorem mem_addRay_rayDegrees : n₁ + n₂ ∈ hA.addRay.rayDegrees :=
  SupportedRay.mem_rayDegrees_ofMem ..

/-- The coefficient variable `c₁` of the term `c₁ z^{n₁}` of the first line. -/
def fstVariable : I.Variable := ⟨j₁, n₁, hA.mem_exponents_fst⟩

/-- The coefficient variable `c₂` of the term `c₂ z^{n₂}` of the second line. -/
def sndVariable : I.Variable := ⟨j₂, n₂, hA.mem_exponents_snd⟩

/-- The first coefficient variable belongs to the first line and the exponent `n₁`. -/
theorem fstVariable_def : hA.fstVariable = ⟨j₁, n₁, hA.mem_exponents_fst⟩ := (rfl)

/-- The second coefficient variable belongs to the second line and the exponent `n₂`. -/
theorem sndVariable_def : hA.sndVariable = ⟨j₂, n₂, hA.mem_exponents_snd⟩ := (rfl)

/-- The first ray is tangent to the first cylinder. -/
theorem wallNormal_fst_fstRay : I.wallNormal j₁ hA.fstRay.generator = 0 := by
  rw [fstRay_generator]
  exact hA.wallNormal_fst_fst

/-- The second ray is tangent to the second cylinder. -/
theorem wallNormal_snd_sndRay : I.wallNormal j₂ hA.sndRay.generator = 0 := by
  rw [sndRay_generator]
  exact hA.wallNormal_snd_snd

/-- The incoming wall of the first line on the ray through `n₁`. -/
def fstIndex : I.IncomingIndex := ⟨j₁, hA.fstRay, hA.wallNormal_fst_fstRay⟩

/-- The defining line and ray of `fstIndex`. -/
theorem fstIndex_def : hA.fstIndex = ⟨j₁, hA.fstRay, hA.wallNormal_fst_fstRay⟩ := (rfl)

/-- The incoming wall of the second line on the ray through `n₂`. -/
def sndIndex : I.IncomingIndex := ⟨j₂, hA.sndRay, hA.wallNormal_snd_sndRay⟩

/-- The defining line and ray of `sndIndex`. -/
theorem sndIndex_def : hA.sndIndex = ⟨j₂, hA.sndRay, hA.wallNormal_snd_sndRay⟩ := (rfl)

section Diagram

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {latticeMap : L →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap) (c : I.Variable → R)

local notation "ρ" => AddMonoidHom.id L
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

/-- The unsplit label of the first line is the binomial label of `1 + c₁ z^{n₁}`. -/
theorem initialLabel_fst : I.initialLabel c j₁ = binomialLabel d ρ (I.wallNormal j₁)
    hA.mem_monoid_fst hA.ne_zero_fst hA.wallNormal_fst_fst (c hA.fstVariable) :=
  (I.initialLabel_eq_binomialLabel c hA.exponents_fst).trans (by rw [fstVariable_def])

/-- The unsplit label of the second line is the binomial label of `1 + c₂ z^{n₂}`. -/
theorem initialLabel_snd : I.initialLabel c j₂ = binomialLabel d ρ (I.wallNormal j₂)
    hA.mem_monoid_snd hA.ne_zero_snd hA.wallNormal_snd_snd (c hA.sndVariable) :=
  (I.initialLabel_eq_binomialLabel c hA.exponents_snd).trans (by rw [sndVariable_def])

/-- The incoming wall of the first line on the ray through `n₁` is labelled by the binomial label
of `1 + c₁ z^{n₁}`. -/
theorem incomingDiagram_label_fstIndex :
    ((I.incomingDiagram h c).wall hA.fstIndex).label = binomialLabel d ρ (I.wallNormal j₁)
      hA.mem_monoid_fst hA.ne_zero_fst hA.wallNormal_fst_fst (c hA.fstVariable) := by
  rw [incomingDiagram_label, fstIndex_def, hA.initialLabel_fst c]
  exact rayFactor_binomialLabel_self d ρ _ _ _ _ _ hA.mem_fstRay_rayDegrees

/-- The incoming wall of the second line on the ray through `n₂` is labelled by the binomial
label of `1 + c₂ z^{n₂}`. -/
theorem incomingDiagram_label_sndIndex :
    ((I.incomingDiagram h c).wall hA.sndIndex).label = binomialLabel d ρ (I.wallNormal j₂)
      hA.mem_monoid_snd hA.ne_zero_snd hA.wallNormal_snd_snd (c hA.sndVariable) := by
  rw [incomingDiagram_label, sndIndex_def, hA.initialLabel_snd c]
  exact rayFactor_binomialLabel_self d ρ _ _ _ _ _ hA.mem_sndRay_rayDegrees

/-- The incoming walls other than those on the rays through `n₁` and `n₂` have trivial labels. -/
theorem incomingDiagram_label_eq_one {j : I.IncomingIndex} (h₁ : j ≠ hA.fstIndex)
    (h₂ : j ≠ hA.sndIndex) : ((I.incomingDiagram h c).wall j).label = 1 := by
  let := h.free
  let : HasUniqueDiv L := .of_isTorsionFree ℤ L
  obtain ⟨j, w, hw⟩ := j
  rw [incomingDiagram_label]
  rcases hA.eq_or_eq j with rfl | rfl
  · refine (hA.initialLabel_fst c).symm ▸
      rayFactor_binomialLabel_of_ne d ρ _ _ _ _ _ hA.mem_fstRay_rayDegrees fun he => h₁ ?_
    subst he
    exact hA.fstIndex_def.symm
  · refine (hA.initialLabel_snd c).symm ▸
      rayFactor_binomialLabel_of_ne d ρ _ _ _ _ _ hA.mem_sndRay_rayDegrees fun he => h₂ ?_
    subst he
    exact hA.sndIndex_def.symm

/-- The binomial label of `1 + c₁ c₂ z^{n₁ + n₂}` with the normal `ν₁ + ν₂`, as a wall label of the
ray through `n₁ + n₂`. -/
def outgoingLabel : (H).wallGroup hA.addRay (I.wallNormal j₁ + I.wallNormal j₂) :=
  ⟨binomialLabel d ρ (I.wallNormal j₁ + I.wallNormal j₂) hA.add_mem_monoid hA.add_ne_zero
    hA.wallNormal_add_add (c hA.fstVariable * c hA.sndVariable),
    binomialLabel_mem_wallGroup d ρ _ _ _ _ _ hA.mem_addRay_rayDegrees⟩

/-- The outgoing label is the binomial label of `1 + c₁ c₂ z^{n₁ + n₂}`. -/
@[simp]
theorem coe_outgoingLabel : (hA.outgoingLabel c).1 =
    binomialLabel d ρ (I.wallNormal j₁ + I.wallNormal j₂) hA.add_mem_monoid hA.add_ne_zero
      hA.wallNormal_add_add (c hA.fstVariable * c hA.sndVariable) :=
  (rfl)

omit [DecidableEq L] in
/-- The cylinder normals `ν₁, ν₂` take the values `1` and `-1` at the image of `-(n₁ + n₂)`. -/
theorem realCharacter_neg_add :
    h.realCharacter (I.wallNormal j₁) (latticeMap (-(n₁ + n₂))) = 1 ∧
      h.realCharacter (I.wallNormal j₂) (latticeMap (-(n₁ + n₂))) = -1 := by
  simp [hA.wallNormal_fst_fst, hA.wallNormal_fst_snd, hA.wallNormal_snd_fst,
    hA.wallNormal_snd_snd]

/-- The outgoing wall of the pentagon diagram: the half-hyperplane `{ν₁ + ν₂ = 0, ν₁ ≥ 0}`,
cooriented by `ν₁ + ν₂`, on the ray through `n₁ + n₂`, labelled by the binomial label of
`1 + c₁ c₂ z^{n₁ + n₂}`. -/
def outgoingWall : DirectedWall (d := d) h H :=
  (DirectedWall.ofAffineHyperplane h H (I.wallNormal j₁ + I.wallNormal j₂)
    (fun he => by simpa [he] using hA.wallNormal_add_neg_snd)
    0 hA.addRay (by rw [addRay_generator]; exact hA.wallNormal_add_add) (hA.outgoingLabel c))
    |>.cutHalfspace (I.wallNormal j₁) 0 ⟨latticeMap (-(n₁ + n₂)), by
      simp only [DirectedWall.ofAffineHyperplane_support, Set.mem_ofPred_eq, map_add,
        LinearMap.add_apply, (hA.realCharacter_neg_add h).1, (hA.realCharacter_neg_add h).2,
        add_neg_cancel], by
      rw [(hA.realCharacter_neg_add h).1]
      exact one_pos⟩

/-- The outgoing wall is cooriented by `ν₁ + ν₂`. -/
@[simp]
theorem outgoingWall_normal : (hA.outgoingWall h c).normal = I.wallNormal j₁ + I.wallNormal j₂ := by
  rw [outgoingWall, DirectedWall.cutHalfspace_normal, DirectedWall.ofAffineHyperplane_normal]

/-- The outgoing wall lies on the ray through `n₁ + n₂`. -/
@[simp]
theorem outgoingWall_ray : (hA.outgoingWall h c).ray = hA.addRay := by
  rw [outgoingWall, DirectedWall.cutHalfspace_ray, DirectedWall.ofAffineHyperplane_ray]

/-- The outgoing wall is supported on the half-hyperplane `{ν₁ + ν₂ = 0, ν₁ ≥ 0}`. -/
@[simp]
theorem outgoingWall_support : (hA.outgoingWall h c).support =
    {x | h.realCharacter (I.wallNormal j₁ + I.wallNormal j₂) x = 0} ∩
      {x | 0 ≤ h.realCharacter (I.wallNormal j₁) x} := by
  rw [outgoingWall, DirectedWall.cutHalfspace_support, DirectedWall.ofAffineHyperplane_support]

/-- The outgoing wall is labelled by the binomial label of `1 + c₁ c₂ z^{n₁ + n₂}`. -/
@[simp]
theorem outgoingWall_label : (hA.outgoingWall h c).label =
    binomialLabel d ρ (I.wallNormal j₁ + I.wallNormal j₂) hA.add_mem_monoid hA.add_ne_zero
      hA.wallNormal_add_add (c hA.fstVariable * c hA.sndVariable) := by
  rw [outgoingWall, DirectedWall.cutHalfspace_label, DirectedWall.ofAffineHyperplane_label,
    coe_outgoingLabel]

/-- The outgoing wall is outgoing: its degree direction `n₁ + n₂` is not a recession direction of
its support. -/
theorem outgoingWall_outgoing : (hA.outgoingWall h c).Outgoing := by
  refine (DirectedWall.outgoing_iff _).mpr fun hrec => ?_
  have hinc := (DirectedWall.incoming_iff _).mpr (Set.mem_recessionCone.mp hrec)
  rw [outgoingWall, DirectedWall.incoming_cutHalfspace_iff _ _ _ _
    (DirectedWall.ofAffineHyperplane_incoming ..)] at hinc
  simp only [DirectedWall.ofAffineHyperplane_ray, addRay_generator, AddMonoidHom.id_apply,
    hA.wallNormal_fst_add] at hinc
  exact absurd hinc (by decide)

/-- The pentagon diagram: the incoming diagram of the input together with the outgoing wall. -/
def pentagonDiagram : DirectedDiagram (d := d) h H (I.IncomingIndex ⊕ Unit) :=
  (I.incomingDiagram h c).append (DirectedDiagram.ofFinite fun _ : Unit => hA.outgoingWall h c)

/-- The walls of the pentagon diagram indexed by the incoming index are the incoming walls. -/
@[simp]
theorem pentagonDiagram_wall_inl (j : I.IncomingIndex) :
    (hA.pentagonDiagram h c).wall (.inl j) = (I.incomingDiagram h c).wall j := by
  rw [pentagonDiagram, DirectedDiagram.append_wall_inl]

/-- The remaining wall of the pentagon diagram is the outgoing wall. -/
@[simp]
theorem pentagonDiagram_wall_inr (u : Unit) :
    (hA.pentagonDiagram h c).wall (.inr u) = hA.outgoingWall h c := by
  rw [pentagonDiagram, DirectedDiagram.append_wall_inr, DirectedDiagram.ofFinite_wall]

/-- The three walls of the pentagon diagram with nontrivial labels: the incoming walls on the rays
through `n₁` and `n₂` and the outgoing wall. -/
def pentagonIndices : Set (I.IncomingIndex ⊕ Unit) :=
  {.inl hA.fstIndex, .inl hA.sndIndex, .inr ()}

omit [DecidableEq L] in
/-- Membership in the three nontrivial walls. -/
theorem mem_pentagonIndices {j : I.IncomingIndex ⊕ Unit} :
    j ∈ hA.pentagonIndices ↔ j = .inl hA.fstIndex ∨ j = .inl hA.sndIndex ∨ j = .inr () :=
  Iff.rfl

/-- The walls of the pentagon diagram outside the three nontrivial ones have trivial labels. -/
theorem pentagonDiagram_label_eq_one {j : I.IncomingIndex ⊕ Unit} (hj : j ∉ hA.pentagonIndices) :
    ((hA.pentagonDiagram h c).wall j).label = 1 := by
  rw [mem_pentagonIndices, not_or, not_or] at hj
  rcases j with j | u
  · rw [pentagonDiagram_wall_inl]
    exact hA.incomingDiagram_label_eq_one h c (fun he => hj.1 (he ▸ rfl))
      fun he => hj.2.1 (he ▸ rfl)
  · exact absurd rfl hj.2.2

/-- The three nontrivial walls of the pentagon diagram are in pentagon configuration: the
hyperplanes `{ν₁ = 0}`, `{ν₂ = 0}` of the cylinder normals and the half-hyperplane
`{ν₁ + ν₂ = 0, ν₁ ≥ 0}` cooriented by `ν₁ + ν₂`. -/
theorem isPentagonConfiguration :
    ((hA.pentagonDiagram h c).restrict hA.pentagonIndices).IsPentagonConfiguration
      ⟨.inl hA.fstIndex, hA.mem_pentagonIndices.mpr (Or.inl rfl)⟩
      ⟨.inl hA.sndIndex, hA.mem_pentagonIndices.mpr (Or.inr (Or.inl rfl))⟩
      ⟨.inr (), hA.mem_pentagonIndices.mpr (Or.inr (Or.inr rfl))⟩
      (I.wallNormal j₁) (I.wallNormal j₂) where
  eq_or_eq_or_eq := by
    rintro ⟨j, hj⟩
    rcases hA.mem_pentagonIndices.mp hj with rfl | rfl | rfl
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
  normal_fst := by simp [fstIndex_def]
  normal_snd := by simp [sndIndex_def]
  normal_half := by simp
  support_fst := by simp [fstIndex_def, hA.offset_fst]
  support_snd := by simp [sndIndex_def, hA.offset_snd]
  support_half := by
    ext x
    simp
  exists_fst := ⟨latticeMap n₁, by simp [hA.wallNormal_fst_fst], by simp [hA.wallNormal_snd_fst]⟩
  exists_snd := ⟨latticeMap n₂, by simp [hA.wallNormal_snd_snd], by simp [hA.wallNormal_fst_snd]⟩

section Positive

open scoped Mei.TropicalVertexCoefficientAction

/-- The coorientations of the walls of the pentagon diagram are primitive. -/
theorem isPrimitive_pentagonDiagram_normal [Module.Free ℤ M] [Module.Finite ℤ M]
    (j : I.IncomingIndex ⊕ Unit) :
    TauCeti.IsPrimitive ((hA.pentagonDiagram h c).wall j).normal := by
  rcases j with j | u
  · rw [pentagonDiagram_wall_inl, incomingDiagram_normal]
    exact I.isPrimitive_wallNormal j.1
  · rw [pentagonDiagram_wall_inr, outgoingWall_normal]
    exact TauCeti.isPrimitive_def.mpr
      ⟨AddMonoidHom.toIntLinearMap (AddMonoidHom.eval (-n₂)), hA.wallNormal_add_neg_snd⟩

variable (Q : AddSubmonoid L) [Fact (d.monoid ≤ Q)] (hQ₁ : -n₁ ∈ Q) (hQ₂ : -n₂ ∈ Q)

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q

include hQ₁ hQ₂ in
/-- If `Q` contains `-n₁` and `-n₂`, the normal of every wall of the pentagon diagram takes the
value one at an exponent `p` of `Q` whose monomial `z^p` is invertible: `p = -n₂` for the walls
cooriented by `ν₁` or `ν₁ + ν₂`, and `p = n₁` for those cooriented by `ν₂`. -/
theorem exists_normal_eq_one_isUnit (j : I.IncomingIndex ⊕ Unit) :
    ∃ p : Q, ((hA.pentagonDiagram h c).wall j).normal (ρ p) = 1 ∧
      IsUnit ((F).toCompletion (single p (1 : R))) := by
  have hn₂ : n₂ ∈ Q := (Fact.out : d.monoid ≤ Q) hA.mem_monoid_snd
  have hn₁ : n₁ ∈ Q := (Fact.out : d.monoid ≤ Q) hA.mem_monoid_fst
  rcases j with ⟨j, w⟩ | u
  · rw [pentagonDiagram_wall_inl, incomingDiagram_normal]
    rcases hA.eq_or_eq j with rfl | rfl
    · refine ⟨⟨-n₂, hQ₂⟩, ?_, TropicalVertexCoefficientAction.isUnit_toCompletion_single hQ₂
        (by rwa [neg_neg])⟩
      rw [AddMonoidHom.id_apply, map_neg, hA.wallNormal_fst_snd, neg_neg]
    · exact ⟨⟨n₁, hn₁⟩, hA.wallNormal_snd_fst,
        TropicalVertexCoefficientAction.isUnit_toCompletion_single hn₁ hQ₁⟩
  · rw [pentagonDiagram_wall_inr, outgoingWall_normal]
    exact ⟨⟨-n₂, hQ₂⟩, hA.wallNormal_add_neg_snd,
      TropicalVertexCoefficientAction.isUnit_toCompletion_single hQ₂ (by rwa [neg_neg])⟩

omit [Fact (d.monoid ≤ Q)] in
/-- Each of the three nontrivial walls of the pentagon diagram is cooriented by a character `μ`
and labelled by the binomial label of `μ`, a degree `n` and a coefficient `b` among `c₁`, `c₂` and
`c₁ c₂`. -/
theorem exists_label_eq_binomialLabel {j : I.IncomingIndex ⊕ Unit} (hj : j ∈ hA.pentagonIndices) :
    ∃ (μ : L →+ ℤ) (n : L) (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (hμ : μ (ρ n) = 0) (b : R),
      (b = c hA.fstVariable ∨ b = c hA.sndVariable ∨
        b = c hA.fstVariable * c hA.sndVariable) ∧
      ((hA.pentagonDiagram h c).wall j).normal = μ ∧
      ((hA.pentagonDiagram h c).wall j).label = binomialLabel d ρ μ hn hn0 hμ b := by
  rcases hA.mem_pentagonIndices.mp hj with rfl | rfl | rfl
  · refine ⟨I.wallNormal j₁, n₁, hA.mem_monoid_fst, hA.ne_zero_fst, hA.wallNormal_fst_fst, _,
      Or.inl rfl, ?_, ?_⟩
    · rw [pentagonDiagram_wall_inl, incomingDiagram_normal, fstIndex_def]
    · rw [pentagonDiagram_wall_inl, hA.incomingDiagram_label_fstIndex]
  · refine ⟨I.wallNormal j₂, n₂, hA.mem_monoid_snd, hA.ne_zero_snd, hA.wallNormal_snd_snd, _,
      Or.inr (Or.inl rfl), ?_, ?_⟩
    · rw [pentagonDiagram_wall_inl, incomingDiagram_normal, sndIndex_def]
    · rw [pentagonDiagram_wall_inl, hA.incomingDiagram_label_sndIndex]
  · exact ⟨I.wallNormal j₁ + I.wallNormal j₂, n₁ + n₂, hA.add_mem_monoid, hA.add_ne_zero,
      hA.wallNormal_add_add, _, Or.inr (Or.inr rfl),
      by rw [pentagonDiagram_wall_inr, outgoingWall_normal],
      by rw [pentagonDiagram_wall_inr, outgoingWall_label]⟩

variable [Module.Free ℤ M] [Module.Finite ℤ M] {S : Type*} [Semiring S] (φ : S →+* R)
  (hc₁ : c hA.fstVariable ∈ φ.rangeS)
  (hc₂ : c hA.sndVariable ∈ φ.rangeS)

include hQ₁ hQ₂ hc₁ hc₂ in
/-- If `Q` contains `-n₁` and `-n₂` and the coefficients `c₁, c₂` lie in the image of a semiring
map `φ : S →+* R`, the discrete grouping of the pentagon diagram is positive for the image of
`S[Q]`: its wall functions are `1 + c₁ z^{n₁}`, `1 + c₂ z^{n₂}` and `1 + c₁ c₂ z^{n₁ + n₂}` on the
three nontrivial walls and `1` on all other walls. -/
theorem isPositive_discrete_pentagonDiagram :
    (DirectedDiagram.FunctionWallGrouping.discrete (hA.pentagonDiagram h c)
      (hA.isPrimitive_pentagonDiagram_normal h c) I.projection).IsPositive
      ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS := by
  refine (DirectedDiagram.FunctionWallGrouping.isPositive_iff _ _ _).mpr fun j => ?_
  obtain ⟨p, hp, hunit⟩ := hA.exists_normal_eq_one_isUnit h c Q hQ₁ hQ₂ j
  by_cases hj : j ∈ hA.pentagonIndices
  · obtain ⟨μ, n, hn, hn0, hμ, b, hb, hnormal, hlabel⟩ := hA.exists_label_eq_binomialLabel h c hj
    have hbφ : b ∈ φ.rangeS := by
      rcases hb with rfl | rfl | rfl
      exacts [hc₁, hc₂, mul_mem hc₁ hc₂]
    refine ⟨binomialUnit d Q hn hn0 b,
      DirectedDiagram.FunctionWallGrouping.isWallFunction_discrete _ _ hp hunit fun q r => ?_,
      isPositive_binomialUnit d Q φ hn hn0 hbφ⟩
    rw [hlabel, completedBCHAction_binomialLabel, hnormal]
  · refine ⟨1, DirectedDiagram.FunctionWallGrouping.isWallFunction_discrete _ _ hp hunit
      fun q r => ?_, AlgFiltration.isPositive_one⟩
    rw [hA.pentagonDiagram_label_eq_one h c hj, map_one, AlgEquiv.one_apply, one_zpow,
      Units.val_one, one_mul]

include hQ₁ hQ₂ hc₁ hc₂ in
/-- Under the hypotheses of `isPositive_discrete_pentagonDiagram`, the pentagon diagram is a
positive wall representative for the image of `S[Q]`. -/
theorem isPositiveWallRepresentative_pentagonDiagram :
    (hA.pentagonDiagram h c).IsPositiveWallRepresentative ((F).completedBCHAction d ℒ)
      (mapRingHom Q φ).rangeS I.projection :=
  (hA.isPositive_discrete_pentagonDiagram h c Q hQ₁ hQ₂ φ hc₁ hc₂).isPositiveWallRepresentative

end Positive

end Diagram

end IsTypeA₂

end Mei.RankTwoPolynomialInput

/-! ### Consistency, needing the degree lattice in `Type`

The pentagon identity `Mei.binomialLabel_pentagon` is transported through `ℤ × ℤ`, so the
theorems below take `L : Type`. -/

namespace Mei.RankTwoPolynomialInput.IsTypeA₂

open _root_.AddMonoidAlgebra

variable {L : Type} {M ι : Type*} [AddCommGroup L] [AddCommGroup M] {d : PositiveDegrees L}
  {I : RankTwoPolynomialInput d M ι} {j₁ j₂ : ι} {n₁ n₂ : L} (hA : I.IsTypeA₂ j₁ j₂ n₁ n₂)
  {R V : Type*} [CommRing R] [Algebra ℚ R] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {latticeMap : L →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap) (c : I.Variable → R)
include hA

local notation "ρ" => AddMonoidHom.id L
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

/-- The labels of the three nontrivial walls satisfy the pentagon identity
`θ[ν₂, n₂, c₂] θ[ν₁, n₁, c₁] = θ[ν₁, n₁, c₁] θ[ν₁ + ν₂, n₁ + n₂, c₁ c₂] θ[ν₂, n₂, c₂]` of binomial
labels. -/
theorem pentagonDiagram_label_pentagon :
    ((hA.pentagonDiagram h c).wall (.inl hA.sndIndex)).label *
        ((hA.pentagonDiagram h c).wall (.inl hA.fstIndex)).label =
      ((hA.pentagonDiagram h c).wall (.inl hA.fstIndex)).label *
        ((hA.pentagonDiagram h c).wall (.inr ())).label *
        ((hA.pentagonDiagram h c).wall (.inl hA.sndIndex)).label := by
  simp only [pentagonDiagram_wall_inl, pentagonDiagram_wall_inr,
    hA.incomingDiagram_label_fstIndex, hA.incomingDiagram_label_sndIndex, outgoingWall_label]
  exact binomialLabel_pentagon d ρ hA.mem_monoid_fst hA.mem_monoid_snd hA.ne_zero_fst
    hA.ne_zero_snd hA.wallNormal_fst_fst hA.wallNormal_snd_snd hA.wallNormal_fst_snd
    hA.wallNormal_snd_fst _ _

/-- The pentagon diagram is consistent. -/
theorem pentagonDiagram_consistent : (hA.pentagonDiagram h c).Consistent := by
  -- The three nontrivial walls are consistent by the pentagon identity; all other walls are full
  -- hyperplanes with trivial labels.
  refine DirectedDiagram.consistent_of_restrict_of_restrict_compl
    ((hA.isPentagonConfiguration h c).consistent ?_) ?_ fun j _ j' hj' => ?_
  · simpa only [DirectedDiagram.restrict_wall] using hA.pentagonDiagram_label_pentagon h c
  · refine DirectedDiagram.consistent_of_commute_of_full _ (fun j => ?_) fun j j' => ?_
    · obtain ⟨j | u, hj⟩ := j
      · rw [DirectedDiagram.restrict_wall, pentagonDiagram_wall_inl]
        exact I.incomingDiagram_full h c j
      · exact absurd (hA.mem_pentagonIndices.mpr (Or.inr (Or.inr rfl))) hj
    · rw [DirectedDiagram.restrict_wall, hA.pentagonDiagram_label_eq_one h c j.property]
      exact Commute.one_left _
  · rw [hA.pentagonDiagram_label_eq_one h c hj']
    exact Commute.one_right _

/-- The pentagon diagram is an outgoing completion of the input: its walls indexed by the
incoming index are the incoming walls, its remaining wall is outgoing, and it is consistent. -/
theorem isOutgoingCompletion_pentagonDiagram :
    DirectedDiagram.IsOutgoingCompletion (I.incomingDiagram h c).wall (hA.pentagonDiagram h c) where
  wall_inl := hA.pentagonDiagram_wall_inl h c
  outgoing_inr u := by
    rw [pentagonDiagram_wall_inr]
    exact hA.outgoingWall_outgoing h c
  consistent := hA.pentagonDiagram_consistent h c

/-- **The scattering diagram of type `A₂` of a rank-two polynomial input.** For an input of type
`A₂` with arbitrary coefficients `c₁, c₂`, the outgoing scattering class of the incoming diagram
is the class of the pentagon diagram, with the one additional outgoing wall
`{ν₁ + ν₂ = 0, ν₁ ≥ 0}` labelled by the binomial label of `1 + c₁ c₂ z^{n₁ + n₂}`. -/
theorem scat_eq_toClass_pentagonDiagram [Module.Free ℤ L] :
    (I.incomingDiagram h c).Scat (I.incomingDiagram_full h c) =
      (hA.pentagonDiagram h c).toClass :=
  DirectedDiagram.scat_eq_toClass _ _ (hA.isOutgoingCompletion_pentagonDiagram h c)

section Positive

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid L) [Fact (d.monoid ≤ Q)] (hQ₁ : -n₁ ∈ Q) (hQ₂ : -n₂ ∈ Q)
  [Module.Free ℤ M] [Module.Finite ℤ M] {S : Type*} [Semiring S] (φ : S →+* R)
  (hc₁ : c hA.fstVariable ∈ φ.rangeS) (hc₂ : c hA.sndVariable ∈ φ.rangeS)

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q

include hQ₁ hQ₂ hc₁ hc₂ in
/-- **Positivity of rank-two polynomial inputs of type `A₂`.** For a rank-two polynomial input of
type `A₂` whose coefficients `c₁, c₂` lie in the image of a semiring map `φ : S →+* R`, and a
coefficient monoid `Q` containing `-n₁` and `-n₂`, the outgoing scattering class of the incoming
diagram has a consistent outgoing representative, the pentagon diagram, whose grouped wall
functions `1 + c₁ z^{n₁}`, `1 + c₂ z^{n₂}`, `1 + c₁ c₂ z^{n₁ + n₂}` (and `1` on the remaining ray
walls) are positive for the image of `S[Q]`. -/
theorem exists_isPositiveWallRepresentative_scat [Module.Free ℤ L] :
    ∃ (κ : Type) (E : DirectedDiagram (d := d) h H (I.IncomingIndex ⊕ κ)),
      DirectedDiagram.IsOutgoingCompletion (I.incomingDiagram h c).wall E ∧
      E.toClass = (I.incomingDiagram h c).Scat (I.incomingDiagram_full h c) ∧
      E.IsPositiveWallRepresentative ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS
        I.projection :=
  ⟨Unit, hA.pentagonDiagram h c, hA.isOutgoingCompletion_pentagonDiagram h c,
    (hA.scat_eq_toClass_pentagonDiagram h c).symm,
    hA.isPositiveWallRepresentative_pentagonDiagram h c Q hQ₁ hQ₂ φ hc₁ hc₂⟩

end Positive

end Mei.RankTwoPolynomialInput.IsTypeA₂
