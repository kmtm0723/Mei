/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.RayFactor
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic
public import Mei.RingTheory.FilteredAlgebra.Positive.Basic

/-!
# Incoming diagrams of rank-two polynomial inputs

Let `I` be a rank-two polynomial input on positive degree data `(L, P, δ)`, with projection
`π : L → M`, and fix coefficients `c_{j,n}` in a commutative `ℚ`-algebra `R`. The wall function
`f_j = 1 + ∑_n c_{j,n} z^n` of the line `j` is tangent to the cylinder normal `ν_j ∘ π`, so its
logarithm is a completed tangent field and `exp(log(f_j) ∂_{ν_j ∘ π})` is a completed label
(`RankTwoPolynomialInput.initialLabel`). It acts on `z^p` by multiplication by
`f_j^{⟨ν_j, π(p)⟩}` (`RankTwoPolynomialInput.completedBCHAction_initialLabel`).

The logarithm generally has terms on many supported rays of `L`. Its ray presentation has the
commuting labels `exp((log f_j)_w ∂_{ν_j ∘ π})`, the ray factors on the supported primitive rays
`w` of `L` tangent to the cylinder. We place them on the cylinder `{x ∈ L_ℝ | ν_j(π x) = c_j}`
over the affine line, an incoming full affine hyperplane
(`DirectedWall.ofAffineHyperplane`), and obtain the incoming diagram
(`RankTwoPolynomialInput.incomingDiagram`). All logarithmic degrees lie in the monoid generated
by the exponents of `f_j`; hence a ray factor surviving the cutoff `k` lies on a ray of order at
most `k` and belongs to a line with a term of degree at most `k`. Since only finitely many lines
and rays qualify, the diagram is finitely active at every order. The nontrivial ray labels of a
line have generators projecting to positive multiples of its tangent `m_j`, and at each order
the ray labels of a line reassemble the projection of its unsplit label.

The constructions use `PositiveDegrees.rayFactor`,
`logComponent_completedBCHExp_completedTropicalTangentField_completedLog_eq_zero`,
`exists_mem_rayDegrees_of_projection_rayFactor_ne_one` and
`projection_completedBCHExp_completedTropicalTangentField_eq_noncommProd_rayFactor`, as for the
BLM inputs of `Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Incoming`. The rank-two
polynomial inputs and their ray presentations follow Burcroff–Lee–Mou, *Positivity of
generalized cluster scattering diagrams*, Definition 2.1, §9.2 and Theorem 9.9
(arXiv:2503.03719v1), and the function-wall convention of Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2).
-/

public noncomputable section

namespace Mei.RankTwoPolynomialInput

open _root_.AddMonoidAlgebra

variable {L M ι R V : Type*} [AddCommGroup L] [AddCommGroup M] {d : PositiveDegrees L}
  (I : RankTwoPolynomialInput d M ι) [CommRing R]

local notation "ρ" => AddMonoidHom.id L
local notation "χ" j => AddMonoidHom.comp (Int.castAddHom R) (I.wallNormal j)
local notation "T" j => tropicalTangentMonoid d ρ (χ j)
local notation "F" j => TropicalVertexCoefficientAction.filtration (R := R) d (T j)

/-- An exponent of the wall function of `j`, as a tangent degree of its cylinder. -/
def tangentExponent (j : ι) (n : I.exponents j) : T j :=
  ⟨n, (mem_tropicalTangentMonoid _ _ _ _).mpr ⟨I.mem_monoid_of_mem_exponents n.property, by
    simp [I.wallNormal_eq_zero_of_mem_exponents n.property]⟩⟩

/-- A tangent exponent is the original exponent. -/
@[simp]
theorem coe_tangentExponent (j : ι) (n : I.exponents j) :
    (I.tangentExponent (R := R) j n : L) = n := (rfl)

/-- The wall function `f_j = 1 + ∑_n c_{j,n} z^n` in its tangent coefficient algebra. -/
def tangentInitialFunction (c : I.Variable → R) (j : ι) : R[T j] :=
  1 + ∑ n : I.exponents j, single (I.tangentExponent j n) (c ⟨j, n⟩)

/-- The wall function is one modulo the first tangent filtration ideal, since its exponents are
nonzero allowed degrees. -/
theorem tangentInitialFunction_sub_one_mem (c : I.Variable → R) (j : ι) :
    I.tangentInitialFunction c j - 1 ∈ (F j).ideal 1 := by
  rw [tangentInitialFunction, add_sub_cancel_left]
  refine Ideal.sum_mem _ fun n _ => ?_
  rw [TropicalVertexCoefficientAction.filtration_ideal,
    AddSubmonoid.single_mem_monoidAlgebraIdeal_iff]
  refine Or.inr ⟨I.tangentExponent j n, I.mem_monoid_of_mem_exponents n.property, ?_, 0,
    by simp⟩
  have := d.degree_pos (I.mem_monoid_of_mem_exponents n.property)
    (I.ne_zero_of_mem_exponents n.property)
  simp only [AddMonoidHom.coe_comp, AddSubmonoid.coe_subtype, Function.comp_apply,
    coe_tangentExponent, Nat.cast_one]
  omega

/-- The completed wall function is congruent to one. -/
theorem toCompletion_tangentInitialFunction_sub_one_mem (c : I.Variable → R) (j : ι) :
    (F j).toCompletion (I.tangentInitialFunction c j) - 1 ∈ (F j).completionIdeal 1 := by
  rw [← map_one (F j).toCompletion, ← map_sub,
    AlgFiltration.toCompletion_mem_completionIdeal_iff]
  exact I.tangentInitialFunction_sub_one_mem c j

/-- The degrees generated by the exponents of the wall function of `j`. -/
def initialMonoid (j : ι) : AddSubmonoid (T j) :=
  AddSubmonoid.closure (Set.range (I.tangentExponent (R := R) j))

/-- The wall function, lifted to the monoid generated by its exponents. -/
private def initialMonoidFunction (c : I.Variable → R) (j : ι) : R[I.initialMonoid (R := R) j] :=
  1 + ∑ n : I.exponents j,
    single ⟨I.tangentExponent j n, AddSubmonoid.subset_closure ⟨n, rfl⟩⟩ (c ⟨j, n⟩)

/-- The lifted wall function maps to the tangent wall function. -/
private theorem mapDomainRingHom_initialMonoidFunction (c : I.Variable → R) (j : ι) :
    mapDomainRingHom R (I.initialMonoid j).subtype (I.initialMonoidFunction c j) =
      I.tangentInitialFunction c j := by
  simp only [initialMonoidFunction, tangentInitialFunction, map_add, map_one, map_sum,
    mapDomainRingHom_apply, mapDomain_single, AddSubmonoid.subtype_apply]

/-- A nonzero degree generated by the exponents of `j` projects to a positive multiple of the
tangent `m_j`, and its degree bounds that of some exponent. -/
theorem initialMonoid_property (j : ι) {q : T j} (hq : q ∈ I.initialMonoid (R := R) j) :
    q = 0 ∨ (∃ k : ℕ, 0 < k ∧ I.projection q = k • I.tangent j) ∧
      ∃ n ∈ I.exponents j, d.degree n ≤ d.degree (q : L) := by
  induction hq using AddSubmonoid.closure_induction with
  | mem q hq =>
    obtain ⟨n, rfl⟩ := hq
    exact Or.inr ⟨I.exists_projection_eq_of_mem_exponents n.property, n, n.property, le_rfl⟩
  | zero => exact Or.inl rfl
  | add q r _ _ hq hr =>
    rcases hq with rfl | ⟨⟨a, ha, hqa⟩, n, hn, hnq⟩
    · simpa using hr
    have hr0 : 0 ≤ d.degree (r : L) := d.degree_nonneg (tropicalTangentMonoid_le _ _ _ r.property)
    refine Or.inr ⟨?_, n, hn, by simp only [AddSubmonoid.coe_add, map_add]; omega⟩
    rcases hr with rfl | ⟨⟨b, hb, hrb⟩, -⟩
    · exact ⟨a, ha, by simpa using hqa⟩
    exact ⟨a + b, by omega, by simp only [AddSubmonoid.coe_add, map_add, hqa, hrb, add_nsmul]⟩

variable [DecidableEq L] [Algebra ℚ R]

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

/-- The unsplit function-wall label `exp(log(f_j) ∂_{ν_j ∘ π})` in the completed tropical
vertex group. -/
def initialLabel (c : I.Variable → R) (j : ι) : d.completedBCHGroup ℒ :=
  d.completedBCHExp ℒ (completedTropicalTangentField d ρ (χ j)
    ((F j).completedLog ⟨(F j).toCompletion (I.tangentInitialFunction c j),
      I.toCompletion_tangentInitialFunction_sub_one_mem c j⟩))

/-- The defining logarithmic tangent field of the unsplit label. -/
theorem initialLabel_def (c : I.Variable → R) (j : ι) :
    I.initialLabel c j = d.completedBCHExp ℒ (completedTropicalTangentField d ρ (χ j)
      ((F j).completedLog ⟨(F j).toCompletion (I.tangentInitialFunction c j),
        I.toCompletion_tangentInitialFunction_sub_one_mem c j⟩)) := (rfl)

/-- The logarithm of the unsplit label has no monomials outside the monoid generated by the
exponents. -/
theorem logComponent_initialLabel_eq_zero (c : I.Variable → R) (j : ι) {q : L}
    (hq : ∀ t : I.initialMonoid (R := R) j, ((t : T j) : L) ≠ q) :
    d.logComponent ℒ (I.initialLabel c j) q = 0 :=
  logComponent_completedBCHExp_completedTropicalTangentField_completedLog_eq_zero d ρ
    (I.wallNormal j) (I.initialMonoid j) (I.initialMonoidFunction c j)
    (I.mapDomainRingHom_initialMonoidFunction c j)
    (I.toCompletion_tangentInitialFunction_sub_one_mem c j) hq

/-- Each ray factor is a wall-group label with the cylinder normal. -/
@[simp high]
theorem rayFactor_initialLabel_mem_wallGroup (c : I.Variable → R) (j : ι) (w : SupportedRay d) :
    d.rayFactor ℒ (I.initialLabel c j) w ∈ (H).wallGroup w (I.wallNormal j) :=
  rayFactor_completedBCHExp_completedTropicalTangentField_mem_wallGroup _ _ _ _ _

/-- Nontangent rays have identity labels. -/
@[simp]
theorem rayFactor_initialLabel_eq_one (c : I.Variable → R) (j : ι) {w : SupportedRay d}
    (hw : I.wallNormal j w.generator ≠ 0) : d.rayFactor ℒ (I.initialLabel c j) w = 1 :=
  rayFactor_completedBCHExp_completedTropicalTangentField_eq_one _ _ _ _ hw

/-- The ray factors of a fixed line commute. -/
theorem commute_rayFactor_initialLabel (c : I.Variable → R) (j : ι) (v w : SupportedRay d) :
    Commute (d.rayFactor ℒ (I.initialLabel c j) v) (d.rayFactor ℒ (I.initialLabel c j) w) :=
  (H).commute_of_mem_wallGroup (I.rayFactor_initialLabel_mem_wallGroup c j v)
    (I.rayFactor_initialLabel_mem_wallGroup c j w) one_ne_zero one_ne_zero rfl

/-- A ray factor surviving the cutoff `k` lies on a ray of order at most `k`, and the line has
a term of degree at most `k`. -/
theorem exists_mem_exponents_of_projection_rayFactor_ne_one (c : I.Variable → R) (j : ι)
    {w : SupportedRay d} {k : ℕ}
    (hw : CompletedGroup.projection k (d.rayFactor ℒ (I.initialLabel c j) w) ≠ 1) :
    w ∈ d.raysAtOrder k ∧ ∃ n ∈ I.exponents j, d.degree n ≤ k := by
  obtain ⟨t, htw, htk⟩ := exists_mem_rayDegrees_of_projection_rayFactor_ne_one d ρ
    (I.wallNormal j) (I.initialMonoid j) (I.initialMonoidFunction c j)
    (I.mapDomainRingHom_initialMonoidFunction c j)
    (I.toCompletion_tangentInitialFunction_sub_one_mem c j) hw
  refine ⟨d.mem_raysAtOrder.mpr ⟨_, htw, htk⟩, ?_⟩
  rcases I.initialMonoid_property j t.property with ht0 | ⟨-, n, hn, hnt⟩
  · exact (SupportedRay.ne_zero_of_mem_rayDegrees htw (by rw [ht0]; rfl)).elim
  · exact ⟨n, hn, hnt.trans htk⟩

/-- A nontrivial ray label of the line `j` has a generator projecting to a positive rational
multiple of the tangent `m_j`. Identity labels carry no direction constraint. -/
theorem rayFactor_initialLabel_projectedDirection (c : I.Variable → R) (j : ι)
    {w : SupportedRay d} (hw : d.rayFactor ℒ (I.initialLabel c j) w ≠ 1) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a • I.projection w.generator = b • I.tangent j := by
  obtain ⟨k, hk⟩ : ∃ k, CompletedGroup.projection k (d.rayFactor ℒ (I.initialLabel c j) w) ≠ 1 := by
    by_contra! h
    exact hw (CompletedGroup.ext fun k => (h k).trans (map_one _).symm)
  obtain ⟨t, htw, -⟩ := exists_mem_rayDegrees_of_projection_rayFactor_ne_one d ρ
    (I.wallNormal j) (I.initialMonoid j) (I.initialMonoidFunction c j)
    (I.mapDomainRingHom_initialMonoidFunction c j)
    (I.toCompletion_tangentInitialFunction_sub_one_mem c j) hk
  obtain ⟨_, a, ha, hta⟩ := SupportedRay.mem_rayDegrees.mp htw
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha.le
  rw [natCast_zsmul] at hta
  rcases I.initialMonoid_property j t.property with ht0 | ⟨⟨b, hb, htb⟩, -⟩
  · exact (SupportedRay.ne_zero_of_mem_rayDegrees htw (by rw [ht0]; rfl)).elim
  · exact ⟨a, b, by exact_mod_cast ha, hb, by rw [← map_nsmul, ← hta, htb]⟩

/-- At every order, the unsplit label is the product of its ray factors over any finite set of
rays containing those meeting the cutoff. -/
private theorem projection_initialLabel_eq_noncommProd [Module.Free ℤ L] (c : I.Variable → R)
    (j : ι) (k : ℕ) (s : Finset (SupportedRay d)) (hs : d.raysAtOrder k ⊆ s) :
    CompletedGroup.projection k (I.initialLabel c j) =
      s.noncommProd (fun w => CompletedGroup.projection k (d.rayFactor ℒ (I.initialLabel c j) w))
        (fun v _ w _ _ => (I.commute_rayFactor_initialLabel c j v w).map _) :=
  projection_completedBCHExp_completedTropicalTangentField_eq_noncommProd_rayFactor
    d ρ (I.wallNormal j) _ k s hs

/-- The walls are indexed by a line and a supported ray tangent to its cylinder. Coincident
supports from different lines remain distinct. -/
abbrev IncomingIndex : Type _ :=
  Σ j : ι, {w : SupportedRay d // I.wallNormal j w.generator = 0}

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {latticeMap : L →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- The incoming diagram of a rank-two polynomial input: the ray factors of the wall function
of each line on the cylinder `{x | ν_j(π x) = c_j}` over it. -/
def incomingDiagram (c : I.Variable → R) : DirectedDiagram (d := d) h (H) I.IncomingIndex where
  wall j := DirectedWall.ofAffineHyperplane h (H) (I.wallNormal j.1)
    (I.wallNormal_ne_zero j.1) (I.offset j.1) j.2.val j.2.property
    ⟨d.rayFactor ℒ (I.initialLabel c j.1) j.2.val,
      I.rayFactor_initialLabel_mem_wallGroup c j.1 j.2.val⟩
  finite_active k := by
    let := h.free
    let : HasUniqueDiv L := .of_isTorsionFree ℤ _
    let f : I.IncomingIndex → ι × SupportedRay d := fun j => (j.1, j.2.val)
    have hf : Function.Injective f := by
      rintro ⟨i, v⟩ ⟨j, w⟩ he
      obtain ⟨rfl, he⟩ := Prod.mk.inj he
      exact congrArg (Sigma.mk i) (Subtype.ext he)
    apply (((I.finite_nontrivial k).prod (d.finite_raysAtOrder k)).preimage hf.injOn).subset
    intro j hj
    obtain ⟨hw, hn⟩ := I.exists_mem_exponents_of_projection_rayFactor_ne_one c j.1
      (by simpa only [Function.mem_mulSupport, DirectedWall.ofAffineHyperplane_label] using hj)
    exact ⟨hn, hw⟩

variable (c : I.Variable → R)

/-- The wall over a line is cooriented by the cylinder normal `ν_j ∘ π`. -/
@[simp]
theorem incomingDiagram_normal (j : I.IncomingIndex) :
    ((I.incomingDiagram h c).wall j).normal = I.wallNormal j.1 := by
  simp [incomingDiagram]

/-- The wall indexed by a tangent supported ray lies on that ray. -/
@[simp]
theorem incomingDiagram_ray (j : I.IncomingIndex) :
    ((I.incomingDiagram h c).wall j).ray = j.2.val := by
  simp [incomingDiagram]

/-- The wall over the line `j` is supported on the cylinder `{x | ν_j(π x) = c_j}`. -/
@[simp]
theorem incomingDiagram_support (j : I.IncomingIndex) :
    ((I.incomingDiagram h c).wall j).support =
      {x | h.realCharacter (I.wallNormal j.1) x = I.offset j.1} := by
  simp [incomingDiagram]

/-- The wall over the line `j` on the ray `w` carries the ray factor
`exp((log f_j)_w ∂_{ν_j ∘ π})`. -/
@[simp]
theorem incomingDiagram_label (j : I.IncomingIndex) :
    ((I.incomingDiagram h c).wall j).label = d.rayFactor ℒ (I.initialLabel c j.1) j.2.val := by
  simp [incomingDiagram]

/-- Every wall is incoming. -/
@[simp]
theorem incomingDiagram_incoming (j : I.IncomingIndex) :
    ((I.incomingDiagram h c).wall j).Incoming :=
  DirectedWall.ofAffineHyperplane_incoming _ _ _ _ _ _ _ _

/-- The full-hyperplane condition required for outgoing completion. -/
theorem incomingDiagram_full (j : I.IncomingIndex) :
    ∃ a : ℝ, ((I.incomingDiagram h c).wall j).support =
      {x | h.realCharacter ((I.incomingDiagram h c).wall j).normal x = a} :=
  ⟨I.offset j.1, by simp only [incomingDiagram_support, incomingDiagram_normal]⟩

/-- At every cutoff, the labels on the tangent rays of the line `i` reassemble the projection of
its unsplit label. The finite set may contain additional rays, whose surviving factors are
retained automatically. -/
theorem projection_initialLabel_eq_noncommProd_incomingDiagram (i : ι) (k : ℕ)
    (s : Finset {w : SupportedRay d // I.wallNormal i w.generator = 0})
    (hs : ∀ w ∈ d.raysAtOrder k, ∀ hw : I.wallNormal i w.generator = 0, ⟨w, hw⟩ ∈ s) :
    CompletedGroup.projection k (I.initialLabel c i) =
      s.noncommProd (fun w => CompletedGroup.projection k
        ((I.incomingDiagram h c).wall ⟨i, w⟩).label)
        (fun v _ w _ _ => by
          simp only [incomingDiagram_label]
          exact (I.commute_rayFactor_initialLabel c i v.val w.val).map _) := by
  classical
  let := h.free
  let : HasUniqueDiv L := .of_isTorsionFree ℤ _
  let e : {w : SupportedRay d // I.wallNormal i w.generator = 0} ↪ SupportedRay d :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let t := (d.finite_raysAtOrder k).toFinset
  let f (w : SupportedRay d) :=
    CompletedGroup.projection k (d.rayFactor ℒ (I.initialLabel c i) w)
  have comm : (↑(s.map e ∪ t) : Set (SupportedRay d)).Pairwise
      (fun v w => Commute (f v) (f w)) :=
    fun v _ w _ _ => (I.commute_rayFactor_initialLabel c i v w).map _
  rw [I.projection_initialLabel_eq_noncommProd c i k (s.map e ∪ t) (by simp [t])]
  rw [← Finset.noncommProd_subset Finset.subset_union_left f comm (fun w hw hn => ?_),
    Finset.noncommProd_map]
  · exact Finset.noncommProd_congr rfl (fun w _ => by simp [f, e, incomingDiagram_label]) _
  · have hwt : w ∈ d.raysAtOrder k := by
      simpa only [Finset.mem_union, hn, false_or, t, Set.Finite.mem_toFinset] using hw
    have hnormal : I.wallNormal i w.generator ≠ 0 := by
      intro hzero
      exact hn (Finset.mem_map.mpr ⟨⟨w, hzero⟩, hs w hwt hzero, rfl⟩)
    simp only [f, I.rayFactor_initialLabel_eq_one c i hnormal, map_one]

section Action

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid L) [Fact (d.monoid ≤ Q)]

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d Q

/-- The wall function `1 + ∑_n c_{j,n} z^n` in the coefficient algebra `R[Q]`. -/
def initialFunction (j : ι) : R[Q] :=
  1 + ∑ n : I.exponents j, single (⟨n, (Fact.out : d.monoid ≤ Q)
    (I.mem_monoid_of_mem_exponents n.property)⟩ : Q) (c ⟨j, n⟩)

omit [DecidableEq L] [Algebra ℚ R] in
/-- Unfold the wall function in the coefficient algebra. -/
theorem initialFunction_def (j : ι) :
    I.initialFunction c Q j = 1 + ∑ n : I.exponents j, single (⟨n, (Fact.out : d.monoid ≤ Q)
      (I.mem_monoid_of_mem_exponents n.property)⟩ : Q) (c ⟨j, n⟩) := (rfl)

omit [DecidableEq L] [Algebra ℚ R] in
/-- The tangent wall function includes as the wall function of the coefficient algebra. -/
theorem tropicalTangentInclusion_tangentInitialFunction (j : ι) :
    tropicalTangentInclusion d ρ (χ j) Q Fact.out (I.tangentInitialFunction c j) =
      I.initialFunction c Q j := by
  simp only [tangentInitialFunction, initialFunction, map_add, map_one, map_sum,
    tropicalTangentInclusion_single, coe_tangentExponent]

/-- The wall function `f_j` as a unit of the completed coefficient algebra. -/
def completedInitialFunction (j : ι) : (G).completionˣ :=
  (isUnit_completedTropicalTangentInclusion d ρ (χ j) Q
    (I.toCompletion_tangentInitialFunction_sub_one_mem c j)).unit

omit [DecidableEq L] [Algebra ℚ R] in
/-- The completed wall function is the completion of the polynomial wall function. -/
@[simp]
theorem coe_completedInitialFunction (j : ι) :
    (I.completedInitialFunction c Q j : (G).completion) =
      (G).toCompletion (I.initialFunction c Q j) := by
  rw [completedInitialFunction, IsUnit.unit_spec, completedTropicalTangentInclusion_toCompletion,
    I.tropicalTangentInclusion_tangentInitialFunction c Q j]

/-- **Wall-function formula.** The unsplit label of the line `j` acts on `z^p` by
multiplication by `f_j^{⟨ν_j, π(p)⟩}`. Negative pairings use inverse unit powers. -/
theorem completedBCHAction_initialLabel (j : ι) (p : Q) (r : R) :
    (G).completedBCHAction d ℒ (I.initialLabel c j) ((G).toCompletion (single p r)) =
      (I.completedInitialFunction c Q j ^ I.wallNormal j p.val : (G).completionˣ) *
        (G).toCompletion (single p r) := by
  exact completedBCHAction_completedBCHExp_completedTropicalTangentField_completedLog
      d ρ Q (I.wallNormal j) (I.toCompletion_tangentInitialFunction_sub_one_mem c j) p r

end Action

end Mei.RankTwoPolynomialInput
