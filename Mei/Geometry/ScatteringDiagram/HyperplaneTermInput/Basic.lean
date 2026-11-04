/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.RayFactor

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
Its ray presentation (`HyperplaneTermInput.diagram`) is the shared construction
`DirectedDiagram.ofHyperplaneRayFactors`, which places the ray factors
`exp((log f_i)_w ∂_{μ_i})` on the supported rays `w` tangent to `μ_i` on the whole hyperplane;
with finitely many terms it is finitely active at every order. Its walls, their incomingness
and its family logarithms are described by the lemmas of that construction.

These are the cooriented affine walls with finitely many terms `c_α z^{m_α}` of the
finite-alphabet lift of Burcroff–Lee–Mou, *Positivity of generalized cluster scattering
diagrams*, §9.2 (arXiv:2503.03719v1), and the ray presentation of function walls of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2).
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
theorem rayFactor_label_mem_wallGroup (c : E → R) (i : ι) (w : SupportedRay d) :
    d.rayFactor ℒ (I.label c i) w ∈ (H).wallGroup w (I.normal i) :=
  rayFactor_completedBCHExp_completedTropicalTangentField_mem_wallGroup _ _ _ _ _

/-- With finitely many terms, only finitely many ray factors of the labels survive each cutoff. -/
theorem hasFiniteSupport_rayFactor_label [Module.Free ℤ Γ] (c : E → R) :
    CompletedGroup.HasFiniteSupport
      fun x : Σ i, {w : SupportedRay d // I.normal i (ρ w.generator) = 0} =>
        d.rayFactor ℒ (I.label c x.1) x.2.val := by
  let : HasUniqueDiv Γ := .of_isTorsionFree ℤ _
  exact hasFiniteSupport_rayFactor_sigma d ρ (I.label c) fun k =>
    (Set.finite_range I.wallIndex).subset fun i ⟨_, hw⟩ => by
      obtain ⟨-, α, -⟩ := mem_raysAtOrder_and_exists_degree_le_of_projection_rayFactor_ne_one d ρ
        (I.normal i) (I.tangentExponent i) (fun α => c α)
        (I.toCompletion_wallFunction_sub_one_mem c i) hw
      exact ⟨α, α.property⟩

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {j : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice j)

/-- The ray presentation of the function walls (`DirectedDiagram.ofHyperplaneRayFactors`): the
ray factor of the label of `f_i` on each supported ray tangent to `μ_i`, placed on the whole
hyperplane `{μ_i = a_i}`. -/
abbrev diagram [Module.Free ℤ Γ] (c : E → R) :
    DirectedDiagram (d := d) h (H) (Σ i, {w : SupportedRay d // I.normal i (ρ w.generator) = 0}) :=
  DirectedDiagram.ofHyperplaneRayFactors h I.normal I.normal_ne_zero I.offset (I.label c)
    (I.rayFactor_label_mem_wallGroup c) (I.hasFiniteSupport_rayFactor_label c)

end HyperplaneTermInput

end Mei
