/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Principal.Cylinder
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall

/-!
# Positive wall representatives of adapted polynomial inputs

Let `B` be an adapted basis of a skew lattice datum, with degenerate and zero forms allowed.
The adapted polynomial input on the principal lattice `L_pr = M° × N_uf` has, at each unfrozen
index `i`, the full hyperplane of the primitive normal `κ(eᵢ)νᵢ` and the label with wall
function `fᵢ = 1 + ∑ₛ aᵢₛ (q^{eᵢ})^s`, where `q^{eᵢ} = z^{r(eᵢ)}` is the principal monomial. The
labels act on the completion of `R[Q]`, for a coefficient monoid `Q ⊇ P_pr`, through the
principal realization.

* If `Q` contains every character `(χ, 0)`, then in the grouping in which every input wall is
  its own function wall (`adaptedPolynomialGrouping`), `fᵢ` is the wall function of the wall at
  `i` (`isWallFunction_adaptedPolynomialGrouping`). As an element of the completion it is the
  polynomial `1 + ∑ₛ aᵢₛ z^{s r(eᵢ)}` (`coe_completedPolynomialWallFunction`).
* If moreover every `aᵢₛ` lies in the image of a semiring map `φ : S →+* R`, the input is a
  positive wall representative for the image of `S[Q]`, for every form
  (`isPositiveWallRepresentative_adaptedPolynomialInput`).
* If the form vanishes on `N_uf`, for instance for the zero form, the input is consistent. Then
  its outgoing scattering class is its own class
  (`scat_adaptedPolynomialInput_of_forall_form_eq_zero`), so that class has a representative
  whose grouped wall functions are positive
  (`exists_isPositiveWallRepresentative_of_forall_form_eq_zero`). For the variables
  `aᵢₛ ∈ ℚ[a]` and `φ = MvPolynomial.map (Nat.castRingHom ℚ)`, the grouped wall functions have
  monomial coefficients in `ℕ[a]`.

If the form does not vanish on `N_uf`, the outgoing completion has further walls, whose
positivity is not formalized here.

The adapted polynomial inputs, their principal realization and the positivity statement are
those of Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Theorem 1.13 (arXiv:1411.1394v2), and of Burcroff–Lee–Mou, *Positivity of generalized cluster
scattering diagrams*, §8 (arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis

open _root_.AddMonoidAlgebra PowerSeries
open scoped Mei.TropicalVertexCoefficientAction

universe u

variable {N R V M : Type*} {ι : Type u} [AddCommGroup N] {D : SkewLatticeDatum N}
  (B : D.AdaptedBasis ι)

local notation "𝒅" => B.unfrozenBasis.positiveDegrees
local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "e" => D.principalPositiveDegrees 𝒅
local notation "ℳ" => tropicalVertexGrading (R := R) e (AddMonoidHom.id Lpr)

/-- An unfrozen basis vector `eᵢ` lies in the positive monoid `P_N`. -/
theorem unfrozenBasis_mem_positiveDegrees_monoid (i : B.unfrozenIndex) :
    B.unfrozenBasis i ∈ (𝒅).monoid := by
  rw [Module.Basis.positiveDegrees_monoid_eq_closure]
  exact AddSubmonoid.subset_closure (Set.mem_range_self i)

/-- The principal exponent `r(eᵢ)` of an unfrozen basis vector is a principal positive
degree. -/
theorem principalEmbedding_unfrozenBasis_mem (i : B.unfrozenIndex) :
    D.principalEmbedding (B.unfrozenBasis i) ∈ (e).monoid := by
  rw [principalEmbedding_apply, PositiveDegrees.mem_graph_monoid]
  exact ⟨B.unfrozenBasis_mem_positiveDegrees_monoid i, by simp⟩

-- The lattices are spelled out: local notations are not expanded hygienically in `variable`
-- binders.
variable (ℓ : B.unfrozenIndex → ℕ) (a : ∀ i, Fin (ℓ i) → R)
  (Q : AddSubmonoid (Module.Dual ℤ D.sublattice × D.unfrozen))
  [Fact ((D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees).monoid ≤ Q)]

/-- The principal exponent `r(eᵢ)` as an element of the coefficient monoid. -/
def principalExponent (i : B.unfrozenIndex) : Q :=
  ⟨D.principalEmbedding (B.unfrozenBasis i),
    (Fact.out : (e).monoid ≤ Q) (B.principalEmbedding_unfrozenBasis_mem i)⟩

/-- The principal exponent is `r(eᵢ)`. -/
@[simp]
theorem coe_principalExponent (i : B.unfrozenIndex) :
    (B.principalExponent Q i : Lpr) = D.principalEmbedding (B.unfrozenBasis i) := (rfl)

variable [CommRing R]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) e Q

/-- The principal monomial `q^{eᵢ} = z^{r(eᵢ)}` in the first ideal of the completed coefficient
algebra. -/
def principalMonomial (i : B.unfrozenIndex) : (F).completionIdeal 1 :=
  ⟨(F).toCompletion (single (B.principalExponent Q i) 1),
    D.toCompletion_single_principalEmbedding_mem_first 𝒅
      (B.unfrozenBasis_mem_positiveDegrees_monoid i) (B.unfrozenBasis.ne_zero i) Q _
      (B.coe_principalExponent Q i)⟩

/-- The principal monomial is the image of `z^{r(eᵢ)}` in the completion. -/
@[simp]
theorem coe_principalMonomial (i : B.unfrozenIndex) :
    (B.principalMonomial (R := R) Q i).val =
      (F).toCompletion (single (B.principalExponent Q i) 1) := (rfl)

/-- The polynomial wall function `fᵢ = 1 + ∑ₛ aᵢₛ (q^{eᵢ})^s` of the input wall at `i`, as a
unit of the completed coefficient algebra. -/
def completedPolynomialWallFunction (i : B.unfrozenIndex) : (F).completionˣ :=
  ((F).isUnit_of_sub_one_mem ((F).completedAeval_sub_one_mem_first (B.principalMonomial Q i)
    (B.polynomialWallFunction ℓ a i) (B.constantCoeff_polynomialWallFunction ℓ a i))).unit

/-- The wall function is the evaluation of the polynomial ray function at `q^{eᵢ}`. -/
theorem coe_completedPolynomialWallFunction_eq_completedAeval (i : B.unfrozenIndex) :
    (B.completedPolynomialWallFunction ℓ a Q i : (F).completion) =
      (F).completedAeval (B.principalMonomial Q i) (B.polynomialWallFunction ℓ a i) :=
  IsUnit.unit_spec _

/-- Evaluating the monomial `c Xⁿ` at `q^{eᵢ}` gives the monomial `c z^{n r(eᵢ)}`. -/
theorem completedAeval_principalMonomial_monomial (i : B.unfrozenIndex) (n : ℕ) (c : R) :
    (F).completedAeval (B.principalMonomial Q i) (monomial n c) =
      (F).toCompletion (single (n • B.principalExponent Q i) c) := by
  have hm : monomial n c = C c * X ^ n := by
    rw [X_pow_eq, ← monomial_zero_eq_C_apply, monomial_mul_monomial, zero_add, mul_one]
  simp only [hm, map_mul, AlgFiltration.completedAeval_C, map_pow, AlgFiltration.completedAeval_X,
    coe_principalMonomial, ← map_pow (F).toCompletion, single_pow, one_pow,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [← AlgFiltration.toCompletionₐ_apply (R := R), ← map_smul, smul_single, smul_eq_mul, mul_one,
    AlgFiltration.toCompletionₐ_apply]

/-- The wall function is the polynomial `1 + ∑ₛ aᵢₛ z^{s r(eᵢ)}`, with `s = 1, …, ℓᵢ`. -/
@[simp]
theorem coe_completedPolynomialWallFunction (i : B.unfrozenIndex) :
    (B.completedPolynomialWallFunction ℓ a Q i : (F).completion) =
      (F).toCompletion (1 + ∑ s : Fin (ℓ i), single ((s.val + 1) • B.principalExponent Q i)
        (a i s)) := by
  rw [coe_completedPolynomialWallFunction_eq_completedAeval, polynomialWallFunction_def]
  simp only [map_add, map_one, map_sum, completedAeval_principalMonomial_monomial]

/-- If every coefficient `aᵢₛ` is the image of an element of `S`, the wall function `fᵢ` is
positive for the image of `S[Q]`. -/
theorem isPositive_completedPolynomialWallFunction {S : Type*} [Semiring S] (φ : S →+* R)
    (ha : ∀ i s, a i s ∈ φ.rangeS) (i : B.unfrozenIndex) :
    (F).IsPositive (mapRingHom Q φ).rangeS
      (B.completedPolynomialWallFunction ℓ a Q i : (F).completion) := by
  rw [coe_completedPolynomialWallFunction]
  refine AlgFiltration.isPositive_toCompletion (add_mem (one_mem _) (sum_mem fun s _ => ?_))
  obtain ⟨b, hb⟩ := ha i s
  exact ⟨single _ b, by rw [mapRingHom_single, hb]⟩

variable [Module.Free ℤ N]

/-- Some character `χ ∈ M°` has principal normal pairing `⟨κ(eᵢ) eᵢ, χ⟩ = 1`. -/
theorem exists_principalNormal_eq_one (i : B.unfrozenIndex) :
    ∃ χ : Module.Dual ℤ D.sublattice, D.principalNormal (B.unfrozenBasis i) (χ, 0) = 1 := by
  let : Module.Free ℤ D.sublattice.toAddSubgroup := Module.Free.of_basis B.sublatticeBasis
  have hn : ((B.unfrozenBasis i : D.unfrozen) : N) ≠ 0 := fun h0 =>
    B.unfrozenBasis.ne_zero i (Subtype.ext h0)
  obtain ⟨χ, hχ⟩ := TauCeti.isPrimitive_def.mp (D.sublattice.toAddSubgroup.isPrimitive_rayVector
    (D.sublattice.toAddSubgroup.rayIndex_pos hn))
  exact ⟨χ, by rw [principalNormal_apply]; exact hχ⟩

variable [Algebra ℚ R] [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]

-- The lattices are spelled out: local notations are not expanded hygienically in `variable`
-- binders.
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : Module.Dual ℤ D.sublattice × D.unfrozen →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap) [AddCommGroup M]
  (π : Module.Dual ℤ D.sublattice × D.unfrozen →+ M)

local notation "𝓗" => D.principalGraphWallSpaces (R := R) 𝒅
local notation "σ" => MonoidHom.comp (AlgFiltration.completedBCHAction (F) e ℳ)
  (GradedLieHom.completedMap (D.principalGraphGradedLieHom (R := R) 𝒅))

/-- The grouping of the adapted polynomial input in which every input wall is its own function
wall. Its groups are indexed by the unfrozen indices. -/
def adaptedPolynomialGrouping :
    (B.adaptedPolynomialInput (V := V) ℓ a h).FunctionWallGrouping π B.unfrozenIndex :=
  DirectedDiagram.FunctionWallGrouping.discrete _
    (B.isPrimitive_adaptedPolynomialInput_normal ℓ a h) π

/-- The input wall at `i` forms the group `i`. -/
@[simp]
theorem adaptedPolynomialGrouping_group (i : B.unfrozenIndex) :
    (B.adaptedPolynomialGrouping ℓ a h π).group i = i :=
  DirectedDiagram.FunctionWallGrouping.discrete_group _ i

/-- The label of the group `i` is the polynomial label of the input wall at `i`. -/
@[simp]
theorem label_adaptedPolynomialGrouping (i : B.unfrozenIndex) :
    (B.adaptedPolynomialGrouping ℓ a h π).label i = B.polynomialWallLabel ℓ a i := by
  rw [adaptedPolynomialGrouping, DirectedDiagram.FunctionWallGrouping.label_discrete,
    adaptedPolynomialInput_label]

/-- The label of the group `i` acts on every monomial by `z^p ↦ fᵢ^(ν(p)) z^p`, where `ν` is
the primitive normal `κ(eᵢ)νᵢ` of the wall at `i`. This holds for every form. -/
theorem completedBCHAction_label_adaptedPolynomialGrouping (i : B.unfrozenIndex) (p : Q)
    (c : R) :
    (σ) ((B.adaptedPolynomialGrouping ℓ a h π).label i) ((F).toCompletion (single p c)) =
      ((B.completedPolynomialWallFunction ℓ a Q i ^
          ((B.adaptedPolynomialInput ℓ a h).wall i).normal p : (F).completionˣ) : (F).completion) *
        (F).toCompletion (single p c) := by
  -- The label and the normal of the wall are transported by `congrArg`: rewriting them with
  -- `rw` in goals containing the completed coefficient algebra times out.
  have hl := congrArg (fun g => (σ) g ((F).toCompletion (single p c)))
    (B.label_adaptedPolynomialGrouping ℓ a h π i)
  have key : (σ) (B.polynomialWallLabel ℓ a i) ((F).toCompletion (single p c)) =
      ((B.completedPolynomialWallFunction ℓ a Q i ^ D.principalNormal (B.unfrozenBasis i) p.val :
        (F).completionˣ) : (F).completion) * (F).toCompletion (single p c) :=
    B.completedBCHAction_polynomialWallLabel ℓ a Q i (B.principalExponent Q i)
      (B.coe_principalExponent Q i) (B.principalMonomial Q i) (B.coe_principalMonomial Q i) _
      (B.coe_completedPolynomialWallFunction_eq_completedAeval ℓ a Q i) p c
  have hpow := congrArg (fun k : ℤ =>
    ((B.completedPolynomialWallFunction ℓ a Q i ^ k : (F).completionˣ) : (F).completion) *
      (F).toCompletion (single p c))
    (congrArg (fun ν : Lpr →+ ℤ => ν p) (B.adaptedPolynomialInput_normal ℓ a h i))
  exact (hl.trans key).trans hpow.symm

/-- If the coefficient monoid contains every character `(χ, 0)`, the polynomial
`fᵢ = 1 + ∑ₛ aᵢₛ (q^{eᵢ})^s` is the wall function of the group `i`: some monomial of normal
weight one is invertible, and the label acts by `z^p ↦ fᵢ^(ν(p)) z^p`. This holds for every
form. -/
theorem isWallFunction_adaptedPolynomialGrouping
    (hQ : ∀ χ : Module.Dual ℤ D.sublattice, ((χ, 0) : Lpr) ∈ Q) (i : B.unfrozenIndex) :
    (B.adaptedPolynomialGrouping ℓ a h π).IsWallFunction σ i
      (B.completedPolynomialWallFunction ℓ a Q i) := by
  obtain ⟨χ, hχ⟩ := B.exists_principalNormal_eq_one i
  refine (DirectedDiagram.FunctionWallGrouping.isWallFunction_iff _ σ i _).mpr fun j hj => ?_
  rw [adaptedPolynomialGrouping_group] at hj
  subst hj
  refine ⟨⟨⟨(χ, 0), hQ χ⟩, (congrArg (fun ν : Lpr →+ ℤ => ν (χ, 0))
    (B.adaptedPolynomialInput_normal ℓ a h j)).trans hχ, ?_⟩,
    B.completedBCHAction_label_adaptedPolynomialGrouping ℓ a Q h π j⟩
  have hmul : (single (⟨(χ, 0), hQ χ⟩ : Q) (1 : R) *
      single ⟨(-χ, 0), hQ (-χ)⟩ 1 : AddMonoidAlgebra R Q) = 1 := by
    rw [single_mul_single, mul_one, one_def]
    exact congrArg (single · 1) (Subtype.ext (by simp))
  exact (isUnit_iff_exists_inv.mpr ⟨_, hmul⟩).map (F).toCompletion

/-- If the coefficient monoid contains every character `(χ, 0)` and every coefficient `aᵢₛ`
is the image of an element of `S`, the grouping of the input walls is positive for the image
of `S[Q]`. This holds for every form. -/
theorem isPositive_adaptedPolynomialGrouping
    (hQ : ∀ χ : Module.Dual ℤ D.sublattice, ((χ, 0) : Lpr) ∈ Q) {S : Type*} [Semiring S]
    (φ : S →+* R) (ha : ∀ i s, a i s ∈ φ.rangeS) :
    (B.adaptedPolynomialGrouping ℓ a h π).IsPositive σ (mapRingHom Q φ).rangeS :=
  (DirectedDiagram.FunctionWallGrouping.isPositive_iff _ _ _).mpr fun i =>
    ⟨_, B.isWallFunction_adaptedPolynomialGrouping ℓ a Q h π hQ i,
      B.isPositive_completedPolynomialWallFunction ℓ a Q φ ha i⟩

/-- Under the hypotheses of `isPositive_adaptedPolynomialGrouping`, the adapted polynomial input
is a positive wall representative, for every form. -/
theorem isPositiveWallRepresentative_adaptedPolynomialInput
    (hQ : ∀ χ : Module.Dual ℤ D.sublattice, ((χ, 0) : Lpr) ∈ Q) {S : Type*} [Semiring S]
    (φ : S →+* R) (ha : ∀ i s, a i s ∈ φ.rangeS) :
    (B.adaptedPolynomialInput ℓ a h).IsPositiveWallRepresentative σ (mapRingHom Q φ).rangeS π :=
  (B.isPositive_adaptedPolynomialGrouping ℓ a Q h π hQ φ ha).isPositiveWallRepresentative

section Abelian

variable [Module.Free ℤ (Module.Dual ℤ D.sublattice × D.unfrozen)]

/-- If the form vanishes on the unfrozen sublattice, for instance for the zero form, the adapted
polynomial input is consistent, so its outgoing scattering class is its own class: the input is
its own outgoing completion. -/
theorem scat_adaptedPolynomialInput_of_forall_form_eq_zero
    (hform : ∀ n m : D.unfrozen, D.form n m = 0) :
    (B.adaptedPolynomialInput ℓ a h).Scat (B.adaptedPolynomialInput_full ℓ a h) =
      (B.adaptedPolynomialInput ℓ a h).toClass :=
  DirectedDiagram.scat_eq_toClass_of_consistent _ _
    (B.adaptedPolynomialInput_consistent_of_forall_form_eq_zero ℓ a hform h)

/-- **Positivity of adapted polynomial walls when the form vanishes on `N_uf`.** If the form
vanishes on the unfrozen sublattice, for instance for the zero form, the coefficient monoid
contains every character `(χ, 0)` and every coefficient `aᵢₛ` is the image of an element of
`S`, then the outgoing scattering class of the adapted polynomial input has a representative
whose grouped wall functions are positive for the image of `S[Q]`: the input itself, with the
wall functions `1 + ∑ₛ aᵢₛ (q^{eᵢ})^s`. -/
theorem exists_isPositiveWallRepresentative_of_forall_form_eq_zero
    (hform : ∀ n m : D.unfrozen, D.form n m = 0)
    (hQ : ∀ χ : Module.Dual ℤ D.sublattice, ((χ, 0) : Lpr) ∈ Q) {S : Type*} [Semiring S]
    (φ : S →+* R) (ha : ∀ i s, a i s ∈ φ.rangeS) :
    ∃ (κ : Type u) (E : DirectedDiagram (d := e) h 𝓗 κ),
      E.toClass = (B.adaptedPolynomialInput ℓ a h).Scat (B.adaptedPolynomialInput_full ℓ a h) ∧
        E.IsPositiveWallRepresentative σ (mapRingHom Q φ).rangeS π :=
  ⟨_, _, (B.scat_adaptedPolynomialInput_of_forall_form_eq_zero ℓ a h hform).symm,
    B.isPositiveWallRepresentative_adaptedPolynomialInput ℓ a Q h π hQ φ ha⟩

end Abelian

end Mei.SkewLatticeDatum.AdaptedBasis
