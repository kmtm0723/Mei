/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.BCH.Ray.LogSum
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.WallFamily
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Hyperplane
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.RayFactor

/-!
# Polynomial function walls on affine hyperplanes

A `HyperplaneTermInput` on positive degree data `(Γ, P, δ)` with projection `ρ : Γ → Λ` to a
tangent lattice consists of affine hyperplanes `{μ_i = a_i}`, `i ∈ ι`, cooriented by nonzero
integral normals `μ_i`, and a family `E` of terms: the term `α` lies on the hyperplane
`wallIndex α` and has a nonzero allowed exponent `n_α` tangent to it. For coefficients
`c : E → R` in a `ℚ`-algebra, the hyperplane `i` carries the polynomial wall function
`f_i = 1 + ∑_{wallIndex α = i} c_α z^{n_α}` and the function-wall label
`exp(log(f_i) ∂_{μ_i})` (`HyperplaneTermInput.label`).

Its logarithm generally has terms on several supported rays, so the label is not a wall label.
Its ray presentation (`HyperplaneTermInput.diagram`) places the ray factors
`exp((log f_i)_w ∂_{μ_i})` on the supported rays `w` tangent to `μ_i` on the whole hyperplane.
With finitely many terms it is finitely active at every order, and the hyperplanes form the
families of `DirectedDiagram.familyLog`: at every order the family logarithm of `i` is the
logarithm of the label of `f_i` (`HyperplaneTermInput.familyLog_diagram`).

These are the cooriented affine walls with finitely many terms `c_α z^{m_α}` of the
finite-alphabet lift of Burcroff–Lee–Mou, *Positivity of generalized cluster scattering
diagrams*, §9.2 (arXiv:2503.03719v1), and the ray presentation of function walls of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2). The construction follows `RankTwoPolynomialInput.incomingDiagram`.
-/

public section

noncomputable section

namespace Mei

/-- Affine hyperplanes `{μ_i = a_i}` in the tangent lattice of `(Γ, P, δ)`, cooriented by
nonzero integral normals, with a family `E` of terms: the term `α` lies on the hyperplane
`wallIndex α` and has a nonzero allowed exponent tangent to it. -/
@[ext]
structure HyperplaneTermInput {Γ Λ : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]
    (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (ι E : Type*) where
  /-- The integral normal `μ_i` of the hyperplane `i`. -/
  normal : ι → Λ →+ ℤ
  /-- The normals are nonzero. -/
  normal_ne_zero (i : ι) : normal i ≠ 0
  /-- The offset `a_i` of the hyperplane `{μ_i = a_i}`. -/
  offset : ι → ℝ
  /-- The hyperplane carrying each term. -/
  wallIndex : E → ι
  /-- The exponent of each term. -/
  exponent : E → Γ
  /-- The exponents are allowed degrees. -/
  exponent_mem (α : E) : exponent α ∈ d.monoid
  /-- The exponents are nonzero. -/
  exponent_ne_zero (α : E) : exponent α ≠ 0
  /-- The exponents are tangent to their hyperplanes. -/
  normal_exponent (α : E) : normal (wallIndex α) (ρ (exponent α)) = 0

namespace HyperplaneTermInput

open _root_.AddMonoidAlgebra

variable {Γ Λ R ι E V : Type*} [AddCommGroup Γ] [AddCommGroup Λ] {d : PositiveDegrees Γ}
  {ρ : Γ →+ Λ} (I : HyperplaneTermInput d ρ ι E) [CommRing R]

local notation "χ" i => AddMonoidHom.comp (Int.castAddHom R) (I.normal i)
local notation "T" i => tropicalTangentMonoid d ρ (χ i)
local notation "F" i => TropicalVertexCoefficientAction.filtration (R := R) d (T i)

/-- The terms on the hyperplane `i`. -/
abbrev Term (i : ι) : Type _ := {α : E // I.wallIndex α = i}

/-- The exponent of a term on the hyperplane `i`, as a degree tangent to its normal. -/
def tangentExponent (i : ι) (α : I.Term i) : T i :=
  ⟨I.exponent α, (mem_tropicalTangentMonoid _ _ _ _).mpr ⟨I.exponent_mem α, by
    simp [← α.property, I.normal_exponent α]⟩⟩

/-- A tangent exponent is the exponent of the term. -/
@[simp]
theorem coe_tangentExponent (i : ι) (α : I.Term i) :
    (I.tangentExponent (R := R) i α : Γ) = I.exponent α := by
  simp [tangentExponent]

variable [Fintype E] [DecidableEq ι]

/-- The completed wall function `f_i = 1 + ∑_{wallIndex α = i} c_α z^{n_α}` of the
hyperplane `i` is congruent to one: its exponents are nonzero allowed degrees. -/
theorem toCompletion_wallFunction_sub_one_mem (c : E → R) (i : ι) :
    (F i).toCompletion (1 + ∑ α : I.Term i, single (I.tangentExponent i α) (c α)) - 1 ∈
      (F i).completionIdeal 1 :=
  toCompletion_one_add_sum_single_sub_one_mem d ρ (I.normal i) (I.tangentExponent i)
    (fun α => c α) fun α => I.exponent_ne_zero α

variable [DecidableEq Γ] [Algebra ℚ R]

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

/-- The function-wall label `exp(log(f_i) ∂_{μ_i})` of the hyperplane `i`, for the wall function
`f_i = 1 + ∑_{wallIndex α = i} c_α z^{n_α}`. -/
def label (c : E → R) (i : ι) : d.completedBCHGroup ℒ :=
  d.completedBCHExp ℒ (completedTropicalTangentField d ρ (χ i) ((F i).completedLog
    ⟨(F i).toCompletion (1 + ∑ α : I.Term i, single (I.tangentExponent i α) (c α)),
      I.toCompletion_wallFunction_sub_one_mem c i⟩))

/-- The label is the exponential of the logarithmic tangent field of the wall function. -/
theorem label_def (c : E → R) (i : ι) :
    I.label c i = d.completedBCHExp ℒ (completedTropicalTangentField d ρ (χ i)
      ((F i).completedLog
        ⟨(F i).toCompletion (1 + ∑ α : I.Term i, single (I.tangentExponent i α) (c α)),
          I.toCompletion_wallFunction_sub_one_mem c i⟩)) := (rfl)

/-- The ray factors of the label are wall labels with the hyperplane normal. -/
@[simp high]
theorem rayFactor_label_mem_wallGroup (c : E → R) (i : ι) (w : SupportedRay d) :
    d.rayFactor ℒ (I.label c i) w ∈ (H).wallGroup w (I.normal i) :=
  rayFactor_completedBCHExp_completedTropicalTangentField_mem_wallGroup _ _ _ _ _

/-- Ray factors on rays not tangent to the hyperplane are trivial. -/
@[simp]
theorem rayFactor_label_eq_one (c : E → R) (i : ι) {w : SupportedRay d}
    (hw : I.normal i (ρ w.generator) ≠ 0) : d.rayFactor ℒ (I.label c i) w = 1 :=
  rayFactor_completedBCHExp_completedTropicalTangentField_eq_one _ _ _ _ hw

/-- The walls are indexed by a hyperplane and a supported ray tangent to it. -/
abbrev Index : Type _ := Σ i : ι, {w : SupportedRay d // I.normal i (ρ w.generator) = 0}

variable [Module.Free ℤ Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {j : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice j)

/-- The ray presentation of the function walls: the ray factor of the label of `f_i` on each
supported ray `w` tangent to `μ_i`, placed on the whole hyperplane `{μ_i = a_i}`. -/
def diagram (c : E → R) : DirectedDiagram (d := d) h (H) I.Index where
  wall x := DirectedWall.ofAffineHyperplane h (H) (I.normal x.1) (I.normal_ne_zero x.1)
    (I.offset x.1) x.2.val x.2.property
    ⟨d.rayFactor ℒ (I.label c x.1) x.2.val, I.rayFactor_label_mem_wallGroup c x.1 x.2.val⟩
  finite_active := by
    let : HasUniqueDiv Γ := .of_isTorsionFree ℤ _
    simpa only [DirectedWall.ofAffineHyperplane_label] using
      hasFiniteSupport_rayFactor_sigma d ρ (P := fun i w => I.normal i (ρ w.generator) = 0)
        (I.label c) fun k => (Set.finite_range I.wallIndex).subset fun i ⟨_, hw⟩ => by
          obtain ⟨-, α, -⟩ :=
            mem_raysAtOrder_and_exists_degree_le_of_projection_rayFactor_ne_one d ρ
              (I.normal i) (I.tangentExponent i) (fun α => c α)
              (I.toCompletion_wallFunction_sub_one_mem c i) hw
          exact ⟨α, α.property⟩

variable (c : E → R)

/-- The wall over the hyperplane `i` is cooriented by `μ_i`. -/
@[simp]
theorem diagram_normal (x : I.Index) : ((I.diagram h c).wall x).normal = I.normal x.1 := by
  simp [diagram]

/-- The wall indexed by a tangent supported ray lies on that ray. -/
@[simp]
theorem diagram_ray (x : I.Index) : ((I.diagram h c).wall x).ray = x.2.val := by
  simp [diagram]

/-- The wall over the hyperplane `i` is supported on the whole hyperplane `{μ_i = a_i}`. -/
@[simp]
theorem diagram_support (x : I.Index) :
    ((I.diagram h c).wall x).support = {y | h.realCharacter (I.normal x.1) y = I.offset x.1} := by
  simp [diagram]

/-- The wall over the hyperplane `i` on the ray `w` carries the ray factor of the label. -/
@[simp]
theorem diagram_label (x : I.Index) :
    ((I.diagram h c).wall x).label = d.rayFactor ℒ (I.label c x.1) x.2.val := by
  simp [diagram]

/-- Every wall is incoming. -/
@[simp]
theorem diagram_incoming (x : I.Index) : ((I.diagram h c).wall x).Incoming :=
  DirectedWall.ofAffineHyperplane_incoming _ _ _ _ _ _ _ _

/-- Every wall is a full affine hyperplane, as required for outgoing completion. -/
theorem diagram_full (x : I.Index) : ∃ a : ℝ, ((I.diagram h c).wall x).support =
    {y | h.realCharacter ((I.diagram h c).wall x).normal y = a} :=
  ⟨I.offset x.1, by simp only [diagram_support, diagram_normal]⟩

/-- At every order, the walls over the hyperplane `i` have the logarithm of the label of `f_i`
as their family logarithm. -/
theorem familyLog_diagram (k : ℕ) (i : ι) :
    (I.diagram h c).familyLog Sigma.fst k i =
      BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k (I.label c i)) := by
  classical
  let : HasUniqueDiv Γ := .of_isTorsionFree ℤ _
  let A := (d.finite_raysAtOrder k).toFinset
  let s : Finset I.Index :=
    (A.subtype fun w => I.normal i (ρ w.generator) = 0).map (Function.Embedding.sigmaMk i)
  have hs (x : I.Index) (hx : x ∈ s) : x.1 = i := by
    obtain ⟨⟨w, hw⟩, -, rfl⟩ := Finset.mem_map.mp hx
    simp
  have hact (x : I.Index) (hx : x ∈ (I.diagram h c).active k) (hxi : x.1 = i) : x ∈ s := by
    obtain ⟨i', w, hw⟩ := x
    obtain rfl : i' = i := hxi
    refine Finset.mem_map.mpr ⟨⟨w, hw⟩, Finset.mem_subtype.mpr ?_, rfl⟩
    refine (d.finite_raysAtOrder k).mem_toFinset.mpr (not_not.mp fun hwk => ?_)
    refine (I.diagram h c).mem_active k _ |>.mp hx ?_
    rw [diagram_label]
    exact d.projection_eq_one_of_notMem_raysAtOrder ℒ
      (d.rayFactor_mem_completedRaySubgroup ℒ _ _) k hwk
  rw [(I.diagram h c).familyLog_eq_sum Sigma.fst k i s hs hact, Finset.sum_map,
    d.log_projection_eq_sum_log_projection_rayFactor ℒ _ k A (by simp [A])]
  simp only [Function.Embedding.sigmaMk_apply, diagram_label]
  rw [Finset.sum_subtype_eq_sum_filter (fun w => BCHGroup.log (L := d.truncatedLie ℒ k)
      (CompletedGroup.projection k (d.rayFactor ℒ (I.label c i) w))),
    Finset.sum_filter_of_ne fun w _ hw => ?_]
  by_contra hn
  rw [I.rayFactor_label_eq_one c i hn] at hw
  exact hw (by rw [map_one]; exact BCHGroup.log_one)

end HyperplaneTermInput

end Mei
