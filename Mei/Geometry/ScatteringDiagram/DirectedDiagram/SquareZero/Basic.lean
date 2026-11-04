/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Sweep
public import Mei.Geometry.Toric.Algebraic.Lattice

/-!
# Two hyperplanes with square-zero coefficients

Let `x₀ ∈ h_{n₀,m₀}` and `x₁ ∈ h_{n₁,m₁}` be elements of directed wall spaces and let
`t₀, t₁` be scalars with `t₀² = t₁² = 0`; for instance `t₀, t₁` generate
`ℚ[t₀, t₁]/(t₀², t₁²)`, acting on the scalar extension of the wall spaces
(`DirectedWallSpaces.baseChange`). The full affine hyperplanes `{m₀ = m₀(θ₀)}` and
`{m₁ = m₁(θ₀)}` through a point `θ₀`, labelled `exp (t₀ x₀)` and `exp (t₁ x₁)`, form the
incoming diagram `SquareZeroPair.input`.

The bracket `t₀ t₁ ⁅x₀, x₁⁆` lies in the wall space of degree `n₀ + n₁` and normal
`μ = m₀(ρ n₁) m₁ - m₁(ρ n₀) m₀` (`SquareZeroPair.bracketNormal`). For `μ ≠ 0`, the wall
`SquareZeroPair.correction` has normal `μ`, label `exp (t₀ t₁ ⁅x₀, x₁⁆)`, and support the
joint of the two hyperplanes swept by `-i(ρ(n₀ + n₁))`; it is outgoing. In the coordinates
`p_j = m_j - m_j(θ₀)` its support is the ray `-ℝ≥0 (α, β)` with `α = m₀(ρ n₁)` and
`β = m₁(ρ n₀)` (`SquareZeroPair.mem_correction_support_iff`). If `ρ(n₀ + n₁) = 0`, then
`μ = 0` and the bracket vanishes.

For `Γ = Λ = ℤ²`, `ρ = id`, `n₀ = e₁`, `m₀ = e₂*`, `n₁ = e₂`, `m₁ = e₁*` and `θ₀ = 0`, the
bracket normal is `e₁* - e₂*` and the correction wall is the ray `-ℝ≥0 (1, 1)`.

Consistency of the resulting diagram is proved in
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.SquareZero.Consistency`. This is the
first-order scattering of two lines in Gross–Pandharipande–Siebert, *Quivers, curves, and
the tropical vertex*, [arXiv:0902.1260](https://arxiv.org/abs/0902.1260), §1, in the
directed setting of Travis Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, [arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), §2.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (d : PositiveDegrees Γ)
  (H : DirectedWallSpaces ρ ℒ)

/-- The points `-t (α, β)`, `t ≥ 0`, of the plane are the points of the line `α p₁ = β p₀`
on the nonpositive side of `(α, β)`. -/
private theorem exists_eq_neg_mul_iff {α β p₀ p₁ : ℝ} (hαβ : α ≠ 0 ∨ β ≠ 0) :
    (∃ t : ℝ, 0 ≤ t ∧ p₀ = -(t * α) ∧ p₁ = -(t * β)) ↔
      α * p₁ - β * p₀ = 0 ∧ α * p₀ + β * p₁ ≤ 0 := by
  have hpos : 0 < α ^ 2 + β ^ 2 := by
    rcases hαβ with hα | hβ
    · have := pow_pos (abs_pos.mpr hα) 2
      rw [sq_abs] at this
      positivity
    · have := pow_pos (abs_pos.mpr hβ) 2
      rw [sq_abs] at this
      positivity
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩
    refine ⟨by ring, ?_⟩
    nlinarith [mul_nonneg ht hpos.le]
  · rintro ⟨hq, hs⟩
    refine ⟨-(α * p₀ + β * p₁) / (α ^ 2 + β ^ 2), div_nonneg (by linarith) hpos.le, ?_, ?_⟩
    · field_simp
      linear_combination (-β) * hq
    · field_simp
      linear_combination α * hq

/-- Two wall-space coefficients `x₀ ∈ h_{n₀,m₀}` and `x₁ ∈ h_{n₁,m₁}` on supported rays
`w₀, w₁`, with scalars `t₀, t₁` satisfying `t₀² = t₁² = 0`. Together with a point `θ₀`
they determine the incoming hyperplanes `{m₀ = m₀(θ₀)}` and `{m₁ = m₁(θ₀)}` labelled by
`exp (t₀ x₀)` and `exp (t₁ x₁)` (`SquareZeroPair.input`). -/
structure SquareZeroPair where
  /-- The integral normals `m₀, m₁`. -/
  normal : Fin 2 → Λ →+ ℤ
  /-- The normals are nonzero. -/
  normal_ne_zero (j : Fin 2) : normal j ≠ 0
  /-- The supported rays `w₀, w₁`. -/
  ray : Fin 2 → SupportedRay d
  /-- Each normal annihilates the geometric direction of its ray. -/
  normal_ray (j : Fin 2) : normal j (ρ (ray j).generator) = 0
  /-- The degrees `n₀, n₁` of the coefficients. -/
  degree : Fin 2 → Γ
  /-- Each degree is an actual degree of its ray. -/
  degree_mem (j : Fin 2) : degree j ∈ (ray j).rayDegrees
  /-- The coefficients `x₀, x₁`. -/
  coeff : Fin 2 → L
  /-- Each coefficient lies in the wall space of its degree and normal. -/
  coeff_mem (j : Fin 2) : coeff j ∈ H.wall (degree j) (normal j)
  /-- The square-zero scalars `t₀, t₁`. -/
  scalar : Fin 2 → R
  /-- The scalars square to zero. -/
  scalar_mul_self (j : Fin 2) : scalar j * scalar j = 0

namespace SquareZeroPair

variable {d H} (P : SquareZeroPair d H)

/-- The normal of a coefficient annihilates its degree. -/
theorem normal_degree (j : Fin 2) : P.normal j (ρ (P.degree j)) = 0 := by
  obtain ⟨-, a, -, ha⟩ := SupportedRay.mem_rayDegrees.mp (P.degree_mem j)
  rw [ha, map_zsmul, map_zsmul, P.normal_ray j, smul_zero]

/-- The normal `μ = m₀(ρ n₁) m₁ - m₁(ρ n₀) m₀` of the bracket `⁅x₀, x₁⁆`. -/
def bracketNormal : Λ →+ ℤ :=
  wallBracketNormal ρ (P.degree 0) (P.degree 1) (P.normal 0) (P.normal 1)

/-- The correction coefficient `t₀ t₁ ⁅x₀, x₁⁆`. -/
def commutator : L :=
  (P.scalar 0 * P.scalar 1) • ⁅P.coeff 0, P.coeff 1⁆

/-- The correction coefficient lies in the wall space of degree `n₀ + n₁` and normal `μ`. -/
theorem commutator_mem :
    P.commutator ∈ H.wall (P.degree 0 + P.degree 1) P.bracketNormal :=
  Submodule.smul_mem _ _ (H.bracket_mem (P.coeff_mem 0) (P.coeff_mem 1))

/-- The bracket of the two label logarithms is the correction coefficient. -/
theorem lie_smul_coeff :
    ⁅P.scalar 0 • P.coeff 0, P.scalar 1 • P.coeff 1⁆ = P.commutator := by
  rw [smul_lie, lie_smul, smul_smul, commutator]

/-- The correction coefficient commutes with the first label logarithm, as `t₀² = 0`. -/
theorem lie_smul_coeff_zero_commutator :
    ⁅P.scalar 0 • P.coeff 0, P.commutator⁆ = 0 := by
  rw [commutator, smul_lie, lie_smul, smul_smul, ← mul_assoc, P.scalar_mul_self 0, zero_mul,
    zero_smul]

/-- The correction coefficient commutes with the second label logarithm, as `t₁² = 0`. -/
theorem lie_smul_coeff_one_commutator :
    ⁅P.scalar 1 • P.coeff 1, P.commutator⁆ = 0 := by
  rw [commutator, smul_lie, lie_smul, smul_smul, mul_comm (P.scalar 0), ← mul_assoc,
    P.scalar_mul_self 1, zero_mul, zero_smul]

/-- The bracket normal is `m₀(ρ n₁) m₁ - m₁(ρ n₀) m₀`. -/
theorem bracketNormal_eq : P.bracketNormal =
    P.normal 0 (ρ (P.degree 1)) • P.normal 1 - P.normal 1 (ρ (P.degree 0)) • P.normal 0 := by
  ext v
  simp [bracketNormal, wallBracketNormal_apply]

/-- A nonzero bracket normal has a nonzero coefficient `m₀(ρ n₁)` or `m₁(ρ n₀)`. -/
theorem ne_zero_or_ne_zero_of_bracketNormal_ne_zero (hμ : P.bracketNormal ≠ 0) :
    P.normal 0 (ρ (P.degree 1)) ≠ 0 ∨ P.normal 1 (ρ (P.degree 0)) ≠ 0 := by
  by_contra! hαβ
  apply hμ
  rw [bracketNormal_eq, hαβ.1, hαβ.2, zero_smul, zero_smul, sub_zero]

/-- If the bracket normal vanishes, so does the correction coefficient. -/
theorem commutator_eq_zero_of_bracketNormal_eq_zero (hμ : P.bracketNormal = 0) :
    P.commutator = 0 := by
  have hc := P.commutator_mem
  rwa [hμ, H.zero_normal, Submodule.mem_bot] at hc

/-- If the total degree has zero geometric direction, the bracket normal vanishes. -/
theorem bracketNormal_eq_zero_of_direction_eq_zero
    (hρ : ρ (P.degree 0 + P.degree 1) = 0) : P.bracketNormal = 0 := by
  have h₀ := P.normal_degree 0
  have h₁ := P.normal_degree 1
  rw [map_add] at hρ
  have h₀₁ : ρ (P.degree 1) = -ρ (P.degree 0) := eq_neg_of_add_eq_zero_right hρ
  have h₁₀ : P.normal 1 (ρ (P.degree 0)) = 0 := by
    rw [eq_neg_of_add_eq_zero_left hρ, map_neg, h₁, neg_zero]
  have h₀₁' : P.normal 0 (ρ (P.degree 1)) = 0 := by
    rw [h₀₁, map_neg, h₀, neg_zero]
  ext v
  simp [bracketNormal, wallBracketNormal_apply, h₁₀, h₀₁']

/-- If the total degree has zero geometric direction, the correction coefficient vanishes. -/
theorem commutator_eq_zero_of_direction_eq_zero
    (hρ : ρ (P.degree 0 + P.degree 1) = 0) : P.commutator = 0 :=
  P.commutator_eq_zero_of_bracketNormal_eq_zero (P.bracketNormal_eq_zero_of_direction_eq_zero hρ)

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i) (θ₀ : V)

/-- The joint `{m₀ = m₀(θ₀)} ∩ {m₁ = m₁(θ₀)}` of the two hyperplanes. -/
def joint : Set V := {z | h.realCharacter (P.normal 0) z = h.realCharacter (P.normal 0) θ₀ ∧
  h.realCharacter (P.normal 1) z = h.realCharacter (P.normal 1) θ₀}

/-- The base point lies on the joint. -/
theorem self_mem_joint : θ₀ ∈ P.joint h θ₀ := ⟨rfl, rfl⟩

/-- The joint is nonempty. -/
theorem joint_nonempty : (P.joint h θ₀).Nonempty := ⟨θ₀, P.self_mem_joint h θ₀⟩

/-- The joint is the affine subspace through `θ₀` with direction `ker ℓ₀ ⊓ ker ℓ₁`. -/
theorem joint_eq_mk' : P.joint h θ₀ = (AffineSubspace.mk' θ₀
    (LinearMap.ker (h.realCharacter (P.normal 0)) ⊓
      LinearMap.ker (h.realCharacter (P.normal 1))) : Set V) := by
  ext z
  simp [joint, AffineSubspace.mem_mk', sub_eq_zero]

/-- The direction of the joint is `ker ℓ₀ ⊓ ker ℓ₁`. -/
theorem direction_affineSpan_joint : (affineSpan ℝ (P.joint h θ₀)).direction =
    LinearMap.ker (h.realCharacter (P.normal 0)) ⊓
      LinearMap.ker (h.realCharacter (P.normal 1)) := by
  rw [joint_eq_mk', AffineSubspace.affineSpan_coe, AffineSubspace.direction_mk']

/-- The first normal takes the value `α = m₀(ρ n₁)` on the geometric direction
`i(ρ(n₀ + n₁))` of the correction. -/
theorem realCharacter_normal_zero_direction :
    h.realCharacter (P.normal 0) (i (ρ (P.degree 0 + P.degree 1))) =
      (P.normal 0 (ρ (P.degree 1)) : ℝ) := by
  rw [h.realCharacter_apply, map_add, map_add, P.normal_degree 0, zero_add]

/-- The second normal takes the value `β = m₁(ρ n₀)` on the geometric direction
`i(ρ(n₀ + n₁))` of the correction. -/
theorem realCharacter_normal_one_direction :
    h.realCharacter (P.normal 1) (i (ρ (P.degree 0 + P.degree 1))) =
      (P.normal 1 (ρ (P.degree 0)) : ℝ) := by
  rw [h.realCharacter_apply, map_add, map_add, P.normal_degree 1, add_zero]

/-- The real extension of the bracket normal is `α ℓ₁ - β ℓ₀`. -/
theorem realCharacter_bracketNormal (z : V) :
    h.realCharacter P.bracketNormal z =
      (P.normal 0 (ρ (P.degree 1)) : ℝ) * h.realCharacter (P.normal 1) z -
        (P.normal 1 (ρ (P.degree 0)) : ℝ) * h.realCharacter (P.normal 0) z := by
  rw [bracketNormal_eq, map_sub, map_zsmul, map_zsmul, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, zsmul_eq_mul, zsmul_eq_mul]

/-- The bracket normal annihilates the geometric direction of the total degree. -/
theorem realCharacter_bracketNormal_direction :
    h.realCharacter P.bracketNormal (i (ρ (P.degree 0 + P.degree 1))) = 0 := by
  rw [realCharacter_bracketNormal, realCharacter_normal_zero_direction,
    realCharacter_normal_one_direction]
  ring

/-- The kernel of the bracket normal is spanned by the joint direction and `i(ρ(n₀ + n₁))`. -/
theorem ker_realCharacter_bracketNormal (hμ : P.bracketNormal ≠ 0) :
    LinearMap.ker (h.realCharacter P.bracketNormal) =
      (affineSpan ℝ (P.joint h θ₀)).direction ⊔ ℝ ∙ i (ρ (P.degree 0 + P.degree 1)) := by
  set v := i (ρ (P.degree 0 + P.degree 1))
  set α : ℝ := (P.normal 0 (ρ (P.degree 1)) : ℝ)
  set β : ℝ := (P.normal 1 (ρ (P.degree 0)) : ℝ)
  have hv₀ : h.realCharacter (P.normal 0) v = α := P.realCharacter_normal_zero_direction h
  have hv₁ : h.realCharacter (P.normal 1) v = β := P.realCharacter_normal_one_direction h
  rw [direction_affineSpan_joint]
  apply le_antisymm
  · intro z hz
    rw [LinearMap.mem_ker, realCharacter_bracketNormal] at hz
    -- Remove the multiple of `v` that has the same value under a nonzero coefficient.
    rcases P.ne_zero_or_ne_zero_of_bracketNormal_ne_zero hμ with hα | hβ
    · have hα : α ≠ 0 := Int.cast_ne_zero.mpr hα
      refine Submodule.mem_sup.mpr ⟨z - (h.realCharacter (P.normal 0) z / α) • v, ?_,
        (h.realCharacter (P.normal 0) z / α) • v, Submodule.smul_mem _ _
          (Submodule.mem_span_singleton_self v), sub_add_cancel _ _⟩
      refine ⟨?_, ?_⟩ <;> simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul,
        smul_eq_mul, hv₀, hv₁]
      · field_simp
        ring
      · field_simp
        linear_combination hz
    · have hβ : β ≠ 0 := Int.cast_ne_zero.mpr hβ
      refine Submodule.mem_sup.mpr ⟨z - (h.realCharacter (P.normal 1) z / β) • v, ?_,
        (h.realCharacter (P.normal 1) z / β) • v, Submodule.smul_mem _ _
          (Submodule.mem_span_singleton_self v), sub_add_cancel _ _⟩
      refine ⟨?_, ?_⟩ <;> simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul,
        smul_eq_mul, hv₀, hv₁]
      · field_simp
        linear_combination -hz
      · field_simp
        ring
  · refine sup_le (fun z hz => ?_) ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    · obtain ⟨hz₀, hz₁⟩ := hz
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hz₀ hz₁
      rw [LinearMap.mem_ker, realCharacter_bracketNormal, hz₀, hz₁]
      ring
    · exact P.realCharacter_bracketNormal_direction h

/-- The geometric direction of the total degree is transverse to the joint. -/
theorem direction_notMem_joint (hμ : P.bracketNormal ≠ 0) :
    i (ρ (P.degree 0 + P.degree 1)) ∉ (affineSpan ℝ (P.joint h θ₀)).direction := by
  rw [direction_affineSpan_joint]
  rintro ⟨h₀, h₁⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, realCharacter_normal_zero_direction] at h₀
  rw [SetLike.mem_coe, LinearMap.mem_ker, realCharacter_normal_one_direction] at h₁
  rcases P.ne_zero_or_ne_zero_of_bracketNormal_ne_zero hμ with hα | hβ
  · exact hα (Int.cast_eq_zero.mp h₀)
  · exact hβ (Int.cast_eq_zero.mp h₁)

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- The wall-group label `exp (t_j x_j)`. -/
def label (j : Fin 2) : H.wallGroup (P.ray j) (P.normal j) :=
  ⟨d.expToCompletion ℒ (P.scalar j • P.coeff j), H.expToCompletion_mem_wallGroup
    (H.wall_le_raySubmodule _ _ (P.degree_mem j) (Submodule.smul_mem _ _ (P.coeff_mem j)))⟩

/-- The label is the completed exponential of `t_j x_j`. -/
@[simp]
theorem coe_label (j : Fin 2) :
    (P.label j : d.completedBCHGroup ℒ) = d.expToCompletion ℒ (P.scalar j • P.coeff j) :=
  (rfl)

/-- The incoming hyperplane `{m_j = m_j(θ₀)}` labelled by `exp (t_j x_j)`. -/
def hyperplane (j : Fin 2) : DirectedWall (d := d) h H :=
  DirectedWall.ofAffineHyperplane h H (P.normal j) (P.normal_ne_zero j)
    (h.realCharacter (P.normal j) θ₀) (P.ray j) (P.normal_ray j) (P.label j)

/-- The normal of the `j`-th hyperplane is `m_j`. -/
@[simp]
theorem hyperplane_normal (j : Fin 2) : (P.hyperplane h θ₀ j).normal = P.normal j :=
  DirectedWall.ofAffineHyperplane_normal ..

/-- The `j`-th hyperplane is `{m_j = m_j(θ₀)}`. -/
@[simp]
theorem hyperplane_support (j : Fin 2) :
    (P.hyperplane h θ₀ j).support =
      {z | h.realCharacter (P.normal j) z = h.realCharacter (P.normal j) θ₀} :=
  DirectedWall.ofAffineHyperplane_support ..

/-- The `j`-th hyperplane is labelled by `exp (t_j x_j)`. -/
@[simp]
theorem hyperplane_label (j : Fin 2) :
    (P.hyperplane h θ₀ j).label = d.expToCompletion ℒ (P.scalar j • P.coeff j) :=
  DirectedWall.ofAffineHyperplane_label ..

/-- The two incoming hyperplanes through `θ₀`. -/
def input : DirectedDiagram (d := d) h H (Fin 2) :=
  ofFinite (P.hyperplane h θ₀)

/-- The walls of the input are the two hyperplanes. -/
@[simp]
theorem input_wall (j : Fin 2) : (P.input h θ₀).wall j = P.hyperplane h θ₀ j :=
  ofFinite_wall ..

/-- The walls of the input are full affine hyperplanes. -/
theorem input_full (j : Fin 2) : ∃ a : ℝ,
    ((P.input h θ₀).wall j).support =
      {x | h.realCharacter ((P.input h θ₀).wall j).normal x = a} :=
  ⟨_, by rw [input_wall, hyperplane_support, hyperplane_normal]⟩

/-- The joint is the intersection of the two hyperplanes. -/
theorem joint_eq :
    P.joint h θ₀ = (P.hyperplane h θ₀ 0).support ∩ (P.hyperplane h θ₀ 1).support := by
  rw [hyperplane_support, hyperplane_support]
  rfl

/-- The joint is a rational-normal polyhedron. -/
theorem isRationalNormalPolyhedron_joint : IsRationalNormalPolyhedron h (P.joint h θ₀) := by
  rw [joint_eq]
  exact (P.hyperplane h θ₀ 0).rational_support.inter (P.hyperplane h θ₀ 1).rational_support

section Completion

variable {w : SupportedRay d} (hw : P.degree 0 + P.degree 1 ∈ w.rayDegrees)
  (hμ : P.bracketNormal ≠ 0)

/-- The outgoing correction wall: the joint swept along `-i(ρ(n₀ + n₁))`, with normal
`μ` and label `exp (t₀ t₁ ⁅x₀, x₁⁆)`. -/
def correction : DirectedWall (d := d) h H :=
  DirectedWall.ofSweep (P.joint h θ₀) (P.joint_nonempty h θ₀)
    (P.isRationalNormalPolyhedron_joint h θ₀)
    w _ hw P.bracketNormal hμ (P.ker_realCharacter_bracketNormal h θ₀ hμ) (-P.commutator)
    (Submodule.neg_mem _ P.commutator_mem)

/-- The correction wall has normal `μ`. -/
@[simp]
theorem correction_normal : (P.correction h θ₀ hw hμ).normal = P.bracketNormal :=
  DirectedWall.ofSweep_normal ..

/-- The correction wall lies on the given supported ray of `n₀ + n₁`. -/
@[simp]
theorem correction_ray : (P.correction h θ₀ hw hμ).ray = w :=
  DirectedWall.ofSweep_ray ..

/-- The correction wall is the joint swept along `-i(ρ(n₀ + n₁))`. -/
@[simp]
theorem correction_support :
    (P.correction h θ₀ hw hμ).support =
      sweep (P.joint h θ₀) (i (ρ (P.degree 0 + P.degree 1))) :=
  DirectedWall.ofSweep_support ..

/-- The correction wall is labelled by `exp (t₀ t₁ ⁅x₀, x₁⁆)`. -/
@[simp]
theorem correction_label :
    (P.correction h θ₀ hw hμ).label = d.expToCompletion ℒ P.commutator := by
  rw [correction, DirectedWall.ofSweep_label, neg_neg]

/-- The correction wall is outgoing. -/
theorem correction_outgoing : (P.correction h θ₀ hw hμ).Outgoing :=
  DirectedWall.ofSweep_outgoing _ _ _ _ _ _ _ _ _ _ _ (P.direction_notMem_joint h θ₀ hμ)

/-- The two incoming hyperplanes together with the outgoing correction wall. -/
def completion : DirectedDiagram (d := d) h H (Fin 2 ⊕ Unit) :=
  ofFinite (Sum.elim (P.hyperplane h θ₀) fun _ => P.correction h θ₀ hw hμ)

/-- The initial walls of the completed diagram are the two hyperplanes. -/
@[simp]
theorem completion_wall_inl (j : Fin 2) :
    (P.completion h θ₀ hw hμ).wall (.inl j) = P.hyperplane h θ₀ j :=
  ofFinite_wall ..

/-- The additional wall of the completed diagram is the correction wall. -/
@[simp]
theorem completion_wall_inr (u : Unit) :
    (P.completion h θ₀ hw hμ).wall (.inr u) = P.correction h θ₀ hw hμ :=
  ofFinite_wall ..


/-- A point lies on the `j`-th hyperplane exactly when its `j`-th coordinate relative to `θ₀`
vanishes. -/
theorem mem_hyperplane_support_iff (j : Fin 2) (z : V) :
    z ∈ (P.hyperplane h θ₀ j).support ↔
      h.realCharacter (P.normal j) z - h.realCharacter (P.normal j) θ₀ = 0 := by
  rw [hyperplane_support, Set.mem_ofPred_eq, sub_eq_zero]

/-- In the coordinates `p_j = m_j - m_j(θ₀)`, the correction wall is the ray `-t (α, β)`,
`t ≥ 0`, where `α = m₀(ρ n₁)` and `β = m₁(ρ n₀)`: the points with `α p₁ - β p₀ = 0` and
`α p₀ + β p₁ ≤ 0`. -/
theorem mem_correction_support_iff (z : V) :
    z ∈ (P.correction h θ₀ hw hμ).support ↔
      (P.normal 0 (ρ (P.degree 1)) : ℝ) *
          (h.realCharacter (P.normal 1) z - h.realCharacter (P.normal 1) θ₀) -
        (P.normal 1 (ρ (P.degree 0)) : ℝ) *
          (h.realCharacter (P.normal 0) z - h.realCharacter (P.normal 0) θ₀) = 0 ∧
      (P.normal 0 (ρ (P.degree 1)) : ℝ) *
          (h.realCharacter (P.normal 0) z - h.realCharacter (P.normal 0) θ₀) +
        (P.normal 1 (ρ (P.degree 0)) : ℝ) *
          (h.realCharacter (P.normal 1) z - h.realCharacter (P.normal 1) θ₀) ≤ 0 := by
  have hαβ := (P.ne_zero_or_ne_zero_of_bracketNormal_ne_zero hμ).imp
    (Int.cast_ne_zero (α := ℝ)).mpr (Int.cast_ne_zero (α := ℝ)).mpr
  rw [← exists_eq_neg_mul_iff hαβ, correction_support, mem_sweep_iff_exists]
  have hv₀ := P.realCharacter_normal_zero_direction h
  have hv₁ := P.realCharacter_normal_one_direction h
  constructor
  · rintro ⟨x, ⟨hx₀, hx₁⟩, t, ht, rfl⟩
    refine ⟨t, ht, ?_, ?_⟩ <;> simp only [map_sub, map_smul, smul_eq_mul, hv₀, hv₁, hx₀, hx₁] <;>
      ring
  · rintro ⟨t, ht, h₀, h₁⟩
    refine ⟨z + t • i (ρ (P.degree 0 + P.degree 1)), ⟨?_, ?_⟩, t, ht, by abel⟩
    · rw [LinearMap.map_add, LinearMap.map_smul, smul_eq_mul, hv₀]
      linarith
    · rw [LinearMap.map_add, LinearMap.map_smul, smul_eq_mul, hv₁]
      linarith

end Completion

/-- The two hyperplanes with no additional walls. -/
def inputWithoutCorrection : DirectedDiagram (d := d) h H (Fin 2 ⊕ Empty) :=
  ofFinite (Sum.elim (P.hyperplane h θ₀) Empty.elim)

/-- The walls of `inputWithoutCorrection` are the two hyperplanes. -/
@[simp]
theorem inputWithoutCorrection_wall_inl (j : Fin 2) :
    (P.inputWithoutCorrection h θ₀).wall (.inl j) = P.hyperplane h θ₀ j :=
  ofFinite_wall ..

end SquareZeroPair

end Mei.DirectedDiagram

/-! ### The coordinate example

For `Γ = Λ = ℤ²`, `ρ = id`, `n₀ = e₁`, `m₀ = e₂*`, `n₁ = e₂` and `m₁ = e₁*`, the two input
walls are the coordinate axes through the origin, the bracket normal is `e₁* - e₂*`, and the
correction wall is the ray `-ℝ≥0 (1, 1)`. -/

namespace Mei.DirectedDiagram.SquareZeroPair

variable {R L : Type*} [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  {ℒ : ℤ × ℤ → Submodule R L} {d : PositiveDegrees (ℤ × ℤ)}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {H : DirectedWallSpaces (AddMonoidHom.id (ℤ × ℤ)) ℒ}
  (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))
  {P : SquareZeroPair d H} (hn₀ : P.degree 0 = (1, 0)) (hm₀ : P.normal 0 = AddMonoidHom.snd ℤ ℤ)
  (hn₁ : P.degree 1 = (0, 1)) (hm₁ : P.normal 1 = AddMonoidHom.fst ℤ ℤ)

include hn₀ hm₀ hn₁ hm₁

omit [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [GradedLieAlgebra ℒ]
  [IsPositiveGrading d ℒ] in
/-- For `n₀ = e₁`, `m₀ = e₂*`, `n₁ = e₂` and `m₁ = e₁*`, the bracket normal is `e₁* - e₂*`. -/
theorem bracketNormal_eq_fst_sub_snd :
    P.bracketNormal = AddMonoidHom.fst ℤ ℤ - AddMonoidHom.snd ℤ ℤ := by
  rw [bracketNormal_eq, hn₀, hn₁, hm₀, hm₁]
  simp

/-- For `n₀ = e₁`, `m₀ = e₂*`, `n₁ = e₂` and `m₁ = e₁*`, the correction wall through the
origin is the ray `-ℝ≥0 (1, 1)`. -/
theorem correction_support_eq {w : SupportedRay d} (hw : P.degree 0 + P.degree 1 ∈ w.rayDegrees)
    (hμ : P.bracketNormal ≠ 0) :
    (P.correction h 0 hw hμ).support = {z | ∃ t : ℝ, 0 ≤ t ∧ z = -(t • ((1 : ℝ), (1 : ℝ)))} := by
  ext z
  rw [mem_correction_support_iff]
  simp only [hn₀, hn₁, hm₀, hm₁, TauCeti.Toric.IsIntegralLattice.realCharacter_fst,
    TauCeti.Toric.IsIntegralLattice.realCharacter_snd]
  simp only [AddMonoidHom.id_apply, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd,
    LinearMap.coe_fst, LinearMap.coe_snd, Prod.fst_zero, Prod.snd_zero, sub_zero, Int.cast_one,
    one_mul, Prod.smul_mk, smul_eq_mul, mul_one, Prod.neg_mk]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨-z.1, by linarith, Prod.ext (by simp) (by simp; linarith)⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by ring, by linarith⟩

end Mei.DirectedDiagram.SquareZeroPair
