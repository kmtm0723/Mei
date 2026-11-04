/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.SquareZero.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalProduct
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat
public import Mei.Algebra.Lie.BCH.Conjugation
public import Mei.Algebra.Order.Sign

/-!
# Consistency of local scattering with square-zero coefficients

The two incoming hyperplanes of a `SquareZeroPair`, labelled `exp (t₀ x₀)` and
`exp (t₁ x₁)` with `t₀² = t₁² = 0`, together with the outgoing correction wall
`exp (t₀ t₁ ⁅x₀, x₁⁆)` with normal `μ ≠ 0`, form a consistent diagram
(`SquareZeroPair.consistent_completion`). It is therefore an outgoing completion of the two
hyperplanes and represents their scattering class
(`SquareZeroPair.scat_input_eq_toClass_completion`). If `μ = 0`, in particular if the total
degree has zero geometric direction, the labels commute and the two hyperplanes alone
represent the scattering class (`SquareZeroPair.scat_input_eq_toClass_of_bracketNormal_eq_zero`).

At a finite order, write `a`, `b` and `c = ⁅a, b⁆` for the truncated logarithms of the three
labels. As `t₀² = t₁² = 0`, `c` commutes with `a` and `b`. The transport is then given by a
potential: with `s` and `r` the sides of the two hyperplanes and `u` the signed indicator of
an open sector bounded by the correction ray and half of the first hyperplane, every path
from `x` to `y` has transport `F y * (F x)⁻¹` for
`F = exp (-r • b) * exp (-s • a) * exp (-u • c)`. By
`DirectedDiagram.levelConsistent_of_local`, this reduces to the jumps of `F` at regular wall
germs, which are identities between integer-valued functions of the signs of the coordinates
and of the crossing velocity.

This is the first-order scattering of two lines in Gross–Pandharipande–Siebert, *Quivers,
curves, and the tropical vertex*, [arXiv:0902.1260](https://arxiv.org/abs/0902.1260), §1,
and an instance of the existence and uniqueness of outgoing completions in Travis Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), Theorem 2.6.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (d : PositiveDegrees Γ)
  (H : DirectedWallSpaces ρ ℒ)

section LocalPotential

/-! ### Local potentials

The transport of the completed diagram is the quotient of values of the product
`exp (-r • b) * exp (-s • a) * exp (-u • c)` (`potential`), where `s` and `r` are the sides of
the two hyperplanes (`side`) and `u` is the signed indicator of an open sector bounded by the
correction ray (`corner`). These integers are determined by the signs of the coordinates at a
point and at its small perturbations. -/

open SignType

/-- `1` on the positive side of zero and `0` elsewhere. -/
private def side (x : ℝ) : ℤ := if 0 < x then 1 else 0

/-- The exponent of a label crossed with normal velocity `x`: positive crossings invert it. -/
private def crossSign (x : ℝ) : ℤ := if 0 < x then -1 else 1

/-- The correction exponent of the local potential at a point with coordinates `p` (first
hyperplane) and `q` (bracket normal), for the ray direction with first coordinate `α`. -/
private def corner (α p q : ℝ) : ℤ :=
  if 0 ≤ α then side (-p) * side q else -(side p * side (-q))

private theorem side_eq (x : ℝ) : side x = if sign x = 1 then 1 else 0 := by
  simp only [side, sign_eq_one_iff]

private theorem crossSign_eq (x : ℝ) : crossSign x = if sign x = 1 then -1 else 1 := by
  simp only [crossSign, sign_eq_one_iff]

private theorem corner_eq (α p q : ℝ) : corner α p q =
    if sign α = -1 then -((if sign p = 1 then 1 else 0) * (if -sign q = 1 then 1 else 0))
    else (if -sign p = 1 then 1 else 0) * (if sign q = 1 then 1 else 0) := by
  simp only [corner, side_eq, ← Left.sign_neg, sign_eq_neg_one_iff, ← not_le]
  split_ifs <;> simp_all

private theorem crossSign_mul {σ x : ℝ} (hσ : 0 < σ) : crossSign (σ * x) = crossSign x := by
  simp only [crossSign, mul_pos_iff_of_pos_left hσ]

/-- The jump of a side across a hyperplane, for a small transverse perturbation. -/
private theorem side_sub_sub_side {P e : ℝ} (h : P ≠ 0 → |e| < |P|) (he : P = 0 → e ≠ 0) :
    side (P - e) - side (P + e) = if P = 0 then crossSign e else 0 := by
  rcases eq_or_ne P 0 with rfl | hP
  · rw [ite_eq_left rfl, zero_sub, zero_add, side_eq, side_eq, Left.sign_neg, crossSign_eq]
    have he := sign_ne_zero.mpr (he rfl)
    generalize sign e = x at *
    revert x
    decide
  · rw [ite_eq_right hP, side_eq, side_eq, sign_sub_of_abs_lt (h hP), sign_add_of_abs_lt (h hP),
      sub_self]

/-- On the line `α p₁ = β p₀`, the sign of `α p₀ + β p₁` is that of `α p₀`. -/
private theorem sign_add_eq_of_eq_zero {α β p₀ p₁ : ℝ} (hα : α ≠ 0)
    (hq : α * p₁ - β * p₀ = 0) : sign (α * p₀ + β * p₁) = sign α * sign p₀ := by
  have hk : α * (α * p₀ + β * p₁) = (α ^ 2 + β ^ 2) * p₀ := by
    linear_combination β * hq
  have hpos : 0 < α ^ 2 + β ^ 2 := by
    have := pow_pos (abs_pos.mpr hα) 2
    rw [sq_abs] at this
    positivity
  have h := congrArg sign hk
  rw [sign_mul, sign_mul, sign_pos hpos, one_mul] at h
  rw [← sign_ne_zero] at hα
  generalize sign α = x at *
  generalize sign p₀ = y at *
  generalize sign (α * p₀ + β * p₁) = z at *
  revert x y z
  decide

/-- The jump of the correction exponent along a small transverse perturbation `(a, b)` of a
point `(P₀, P₁)`, corrected by the commutator of the two hyperplane labels. Here `Q` and `e`
are the values of `α p₁ - β p₀` at the point and on the perturbation, and the right side is
the exponent of the correction label when the point lies on the correction ray. -/
private theorem corner_jump (α β P0 P1 Q a b e : ℝ) (hαβ : α ≠ 0 ∨ β ≠ 0)
    (hQ : Q = α * P1 - β * P0) (he : e = α * b - β * a)
    (h0 : P0 ≠ 0 → |a| < |P0|) (h1 : P1 ≠ 0 → |b| < |P1|) (hq : Q ≠ 0 → |e| < |Q|)
    (hreg : P0 = 0 → P1 ≠ 0) (ha : P0 = 0 → a ≠ 0)
    (hdq : Q = 0 → α * P0 + β * P1 ≤ 0 → e ≠ 0) :
    side (P1 + b) * (side (P0 - a) - side (P0 + a)) +
      (corner α (P0 - a) (Q - e) - corner α (P0 + a) (Q + e)) =
      if Q = 0 ∧ α * P0 + β * P1 ≤ 0 then crossSign e else 0 := by
  have hW : (Q = 0 ∧ α * P0 + β * P1 ≤ 0) ↔ (sign Q = 0 ∧ sign (α * P0 + β * P1) ≠ 1) := by
    rw [sign_eq_zero_iff, Ne, sign_eq_one_iff, not_lt]
  simp only [corner_eq, side_eq, crossSign_eq, hW]
  clear hW
  rcases eq_or_ne P0 0 with hP0 | hP0
  · subst hP0
    have hP1 := hreg rfl
    have ha := ha rfl
    rw [sign_add_of_abs_lt (h1 hP1)]
    simp only [zero_sub, zero_add, Left.sign_neg, mul_zero, sub_zero, sign_mul] at hQ ⊢
    rcases eq_or_ne α 0 with hα | hα
    · -- The correction ray lies in the first hyperplane.
      subst hα
      simp only [zero_mul, zero_sub] at hQ he ⊢
      subst hQ he
      have hβ : β ≠ 0 := hαβ.resolve_left (by norm_num)
      simp only [neg_neg, Left.sign_neg, sign_mul, sign_zero, sub_neg_eq_add, zero_add]
      rw [← sign_ne_zero] at hβ hP1 ha
      generalize sign β = x at *
      generalize sign P1 = y at *
      generalize sign a = z at *
      revert x y z
      decide
    · subst hQ
      rw [sign_sub_of_abs_lt (hq (mul_ne_zero hα hP1)),
        sign_add_of_abs_lt (hq (mul_ne_zero hα hP1))]
      simp only [sign_mul]
      rw [← sign_ne_zero] at hα hP1 ha
      generalize sign α = x at *
      generalize sign P1 = y at *
      generalize sign a = z at *
      generalize sign β = w at *
      generalize sign e = u at *
      revert x y z w u
      decide
  · rw [sign_sub_of_abs_lt (h0 hP0), sign_add_of_abs_lt (h0 hP0)]
    rcases eq_or_ne Q 0 with hQ0 | hQ0
    · -- The correction ray crosses the line `{q = 0}` transversally.
      have hα : α ≠ 0 := by
        rintro rfl
        have hβ : β ≠ 0 := hαβ.resolve_left (by norm_num)
        rw [hQ0, zero_mul, zero_sub, eq_comm, neg_eq_zero] at hQ
        exact mul_ne_zero hβ hP0 hQ
      have hS := sign_add_eq_of_eq_zero hα (hQ ▸ hQ0)
      have hdq' : sign (α * P0 + β * P1) ≠ 1 → sign e ≠ 0 := by
        rw [Ne, sign_eq_one_iff, not_lt, Ne, sign_eq_zero_iff]
        exact hdq hQ0
      rw [hQ0, zero_sub, zero_add, Left.sign_neg, sign_zero] at *
      rw [hS] at hdq' ⊢
      rw [← sign_ne_zero] at hα hP0
      clear hS hQ he hdq h0 h1 hq hreg ha
      generalize sign α = x at *
      generalize sign P0 = y at *
      generalize sign e = z at *
      generalize sign (P1 + b) = w at *
      revert x y z w
      decide
    · rw [sign_sub_of_abs_lt (hq hQ0), sign_add_of_abs_lt (hq hQ0)]
      rw [← sign_ne_zero] at hQ0
      clear hQ he hdq h0 h1 hq hreg ha
      generalize sign α = x at *
      generalize sign P0 = y at *
      generalize sign e = z at *
      generalize sign (P1 + b) = w at *
      generalize sign Q = u at *
      generalize sign (α * P0 + β * P1) = v at *
      revert x y z w u v
      decide

/-- Off the correction ray, the correction exponent depends only on the strict signs of
`p` and, when it is nonzero, of `q`. -/
private theorem corner_eq_of_sign_eq {α β P0 P1 P0' Q' : ℝ} (hαβ : α ≠ 0 ∨ β ≠ 0)
    (hP0 : P0 ≠ 0) (hW : ¬(α * P1 - β * P0 = 0 ∧ α * P0 + β * P1 ≤ 0))
    (hs : sign P0' = sign P0) (hq : α * P1 - β * P0 ≠ 0 → sign Q' = sign (α * P1 - β * P0)) :
    corner α P0' Q' = corner α P0 (α * P1 - β * P0) := by
  rw [corner_eq, corner_eq, hs]
  rcases eq_or_ne (α * P1 - β * P0) 0 with hQ0 | hQ0
  · have hα : α ≠ 0 := by
      rintro rfl
      have hβ : β ≠ 0 := hαβ.resolve_left (by norm_num)
      rw [zero_mul, zero_sub, neg_eq_zero] at hQ0
      exact mul_ne_zero hβ hP0 hQ0
    have hS := sign_add_eq_of_eq_zero hα hQ0
    have hpos : sign (α * P0 + β * P1) = 1 :=
      sign_eq_one_iff.mpr (lt_of_not_ge fun hle => hW ⟨hQ0, hle⟩)
    rw [hS] at hpos
    rw [hQ0, sign_zero]
    rw [← sign_ne_zero] at hα hP0
    clear hS hW hq hs
    generalize sign α = x at *
    generalize sign P0 = y at *
    generalize sign Q' = z at *
    revert x y z
    decide
  · rw [hq hQ0]

variable {M : Type*} [LieRing M] [LieAlgebra ℚ M] [LieRing.IsNilpotent M]

/-- The normal form `exp (-r • b) * exp (-s • a) * exp (-u • c)`. -/
private def potential (a b c : M) (s r u : ℤ) : BCHGroup M :=
  BCHGroup.exp (-(r • b)) * BCHGroup.exp (-(s • a)) * BCHGroup.exp (-(u • c))

/-- If `⁅a, b⁆ = c` is central for `a` and `b`, two normal forms differing in only one of the
first two exponents have quotient `exp ((s₂ - s₁) a + (r₂ - r₁) b + (r₁ (s₂ - s₁) + u₂ - u₁) c)`.
The extra multiple of `c` is the commutator of `b ^ r₁` with `a ^ (s₂ - s₁)`. -/
private theorem potential_mul_inv {a b c : M} (hab : ⁅a, b⁆ = c) (hac : ⁅a, c⁆ = 0)
    (hbc : ⁅b, c⁆ = 0) {s₁ r₁ u₁ s₂ r₂ u₂ : ℤ} (h : s₁ = s₂ ∨ r₁ = r₂) :
    potential a b c s₁ r₁ u₁ * (potential a b c s₂ r₂ u₂)⁻¹ =
      BCHGroup.exp ((s₂ - s₁) • a + (r₂ - r₁) • b + (r₁ * (s₂ - s₁) + (u₂ - u₁)) • c) := by
  have hca : ⁅c, a⁆ = 0 := by rw [← lie_skew, hac, neg_zero]
  have hcb : ⁅c, b⁆ = 0 := by rw [← lie_skew, hbc, neg_zero]
  have hba : ⁅b, a⁆ = -c := by rw [← lie_skew, hab]
  simp only [potential, mul_inv_rev, ← BCHGroup.exp_neg, neg_neg]
  -- Merge the two central factors and move them past `exp (s₂ a)`.
  have hcc : BCHGroup.exp (-(u₁ • c)) * BCHGroup.exp (u₂ • c) =
      BCHGroup.exp ((u₂ - u₁) • c) := by
    rw [← BCHGroup.exp_add_of_lie_eq_zero _ _ (by simp [lie_self]), sub_smul]
    congr 1
    abel
  have hcomm : Commute (BCHGroup.exp ((u₂ - u₁) • c)) (BCHGroup.exp (s₂ • a)) :=
    BCHGroup.commute_exp_of_lie_eq_zero _ _ (by simp [hca])
  have haa : BCHGroup.exp (-(s₁ • a)) * BCHGroup.exp (s₂ • a) =
      BCHGroup.exp ((s₂ - s₁) • a) := by
    rw [← BCHGroup.exp_add_of_lie_eq_zero _ _ (by simp [lie_self]), sub_smul]
    congr 1
    abel
  have hac' : BCHGroup.exp ((s₂ - s₁) • a) * BCHGroup.exp ((u₂ - u₁) • c) =
      BCHGroup.exp ((s₂ - s₁) • a + (u₂ - u₁) • c) :=
    (BCHGroup.exp_add_of_lie_eq_zero _ _ (by simp [hac])).symm
  calc BCHGroup.exp (-(r₁ • b)) * BCHGroup.exp (-(s₁ • a)) * BCHGroup.exp (-(u₁ • c)) *
        (BCHGroup.exp (u₂ • c) * (BCHGroup.exp (s₂ • a) * BCHGroup.exp (r₂ • b)))
      = BCHGroup.exp (-(r₁ • b)) *
          ((BCHGroup.exp (-(s₁ • a)) * BCHGroup.exp (s₂ • a)) *
            BCHGroup.exp ((u₂ - u₁) • c)) * BCHGroup.exp (r₂ • b) := by
        simp only [mul_assoc]
        rw [← mul_assoc (BCHGroup.exp (-(u₁ • c))), hcc,
          ← mul_assoc (BCHGroup.exp ((u₂ - u₁) • c)), hcomm.eq]
        simp only [mul_assoc]
    _ = BCHGroup.exp (-(r₁ • b)) * BCHGroup.exp ((s₂ - s₁) • a + (u₂ - u₁) • c) *
          BCHGroup.exp (r₂ • b) := by rw [haa, hac']
    _ = _ := by
        rcases h with rfl | rfl
        · -- Only the second exponent changes: everything else is central.
          have hcomm' : Commute (BCHGroup.exp (-(r₁ • b)))
              (BCHGroup.exp ((s₁ - s₁) • a + (u₂ - u₁) • c)) :=
            BCHGroup.commute_exp_of_lie_eq_zero _ _ (by simp [hbc])
          rw [hcomm'.eq, mul_assoc, ← BCHGroup.exp_add_of_lie_eq_zero _ _ (by simp [lie_self]),
            ← BCHGroup.exp_add_of_lie_eq_zero _ _ (by simp [hcb, sub_self])]
          congr 1
          module
        · -- Only the first exponent changes: conjugate by `exp (-(r₁ • b))`.
          have hx : IsNilpotent (LieAlgebra.ad ℚ M (-(r₁ • b))) :=
            LieModule.isNilpotent_toEnd_of_isNilpotent ℚ M M _
          have hlie : ⁅-(r₁ • b), (s₂ - s₁) • a + (u₂ - u₁) • c⁆ = (r₁ * (s₂ - s₁)) • c := by
            simp only [neg_lie, zsmul_lie, lie_add, lie_zsmul, hba, hbc, smul_neg, smul_zero,
              neg_neg]
            module
          rw [show BCHGroup.exp (r₁ • b) = (BCHGroup.exp (-(r₁ • b)))⁻¹ by
              rw [← BCHGroup.exp_neg, neg_neg], ← BCHGroup.exp_expAd _ _ hx,
            TauCeti.expAd_apply_of_lie_lie_eq_zero hx (by rw [hlie]; simp [hbc]), hlie]
          congr 1
          module

end LocalPotential

namespace SquareZeroPair

variable {d H} (P : SquareZeroPair d H)
  [NormedAddCommGroup V] [NormedSpace ℝ V] {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (θ₀ : V) [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

section Completion

variable {w : SupportedRay d} (hw : P.degree 0 + P.degree 1 ∈ w.rayDegrees)
  (hμ : P.bracketNormal ≠ 0)

/-- The completed diagram is consistent at every finite order: every path from `x` to `y` has
transport `F y * (F x)⁻¹`, where `F = exp (-r • t₁ x₁) * exp (-s • t₀ x₀) *
exp (-u • t₀ t₁ ⁅x₀, x₁⁆)` for the sides `s` and `r` of the two hyperplanes and the signed
indicator `u` of a sector bounded by the correction ray. -/
theorem levelConsistent_completion (k : ℕ) :
    (P.completion h θ₀ hw hμ).LevelConsistent k := by
  classical
  let := h.finiteDimensional
  set D := P.completion h θ₀ hw hμ with hD
  -- The truncated label logarithms.
  set a : d.truncatedLie ℒ k := (d.degreeIdeal ℒ k).mkQ (P.scalar 0 • P.coeff 0) with ha_def
  set b : d.truncatedLie ℒ k := (d.degreeIdeal ℒ k).mkQ (P.scalar 1 • P.coeff 1) with hb_def
  set c : d.truncatedLie ℒ k := (d.degreeIdeal ℒ k).mkQ P.commutator with hc_def
  have hlabel₀ : CompletedGroup.projection k (D.wall (.inl 0)).label = BCHGroup.exp a := by
    rw [completion_wall_inl, hyperplane_label, PositiveDegrees.projection_expToCompletion]
  have hlabel₁ : CompletedGroup.projection k (D.wall (.inl 1)).label = BCHGroup.exp b := by
    rw [completion_wall_inl, hyperplane_label, PositiveDegrees.projection_expToCompletion]
  have hlabel₂ (u : Unit) :
      CompletedGroup.projection k (D.wall (.inr u)).label = BCHGroup.exp c := by
    rw [completion_wall_inr, correction_label, PositiveDegrees.projection_expToCompletion]
  have hab : ⁅a, b⁆ = c := by
    rw [ha_def, hb_def, hc_def, ← LieHom.map_lie, P.lie_smul_coeff]
  have hac : ⁅a, c⁆ = 0 := by
    rw [ha_def, hc_def, ← LieHom.map_lie, P.lie_smul_coeff_zero_commutator, map_zero]
  have hbc : ⁅b, c⁆ = 0 := by
    rw [hb_def, hc_def, ← LieHom.map_lie, P.lie_smul_coeff_one_commutator, map_zero]
  by_cases hC : BCHGroup.exp c = 1
  · -- The correction is invisible at this order, and the two hyperplane labels commute.
    have hcomm : Commute (BCHGroup.exp a) (BCHGroup.exp b) := by
      have := BCHGroup.exp_mul_exp_eq_exp_mul_exp_mul hab hac hbc
      rwa [hC, mul_one] at this
    have hinl (j : D.active k) : ∃ l : Fin 2, j.1 = .inl l := by
      obtain ⟨j | u, hj⟩ := j
      · exact ⟨j, rfl⟩
      · exact absurd (by rw [hlabel₂, hC]; exact (d.groupTower_obj_one ℒ k).symm)
          ((D.mem_active k _).mp hj)
    apply D.levelConsistent_of_commute_of_full k
    · intro j
      obtain ⟨l, hl⟩ := hinl j
      rw [hl, completion_wall_inl, hyperplane_support, hyperplane_normal]
      exact ⟨_, rfl⟩
    · intro j j'
      obtain ⟨l, hl⟩ := hinl j
      obtain ⟨l', hl'⟩ := hinl j'
      rw [hl, hl']
      fin_cases l <;> fin_cases l' <;>
        simp only [Fin.zero_eta, Fin.mk_one, hlabel₀, hlabel₁]
      exacts [Commute.refl _, hcomm, hcomm.symm, Commute.refl _]
  · -- Every wall is active at this order.
    have hc0 : c ≠ 0 := fun h0 => hC (by rw [h0, BCHGroup.exp_zero])
    have hexp_ne {x : d.truncatedLie ℒ k} (hx : x ≠ 0) :
        BCHGroup.exp x ≠ (1 : (d.groupTower ℒ).obj (Opposite.op k)) := by
      rw [d.groupTower_obj_one]
      intro h1
      apply hx
      simpa only [BCHGroup.log_exp, BCHGroup.log_one] using congrArg BCHGroup.log h1
    have hall : ∀ j, j ∈ D.active k := by
      rintro (j | u) <;> rw [D.mem_active]
      · fin_cases j
        · rw [Fin.zero_eta, hlabel₀]
          exact hexp_ne fun h0 => hc0 (by rw [← hab, h0, zero_lie])
        · rw [Fin.mk_one, hlabel₁]
          exact hexp_ne fun h0 => hc0 (by rw [← hab, h0, lie_zero])
      · rw [hlabel₂]
        exact hexp_ne hc0
    -- Coordinates relative to `θ₀`, and the coefficients of the correction direction.
    set α : ℝ := (P.normal 0 (ρ (P.degree 1)) : ℝ) with hα_def
    set β : ℝ := (P.normal 1 (ρ (P.degree 0)) : ℝ) with hβ_def
    set ℓ₀ := h.realCharacter (P.normal 0) with hℓ₀_def
    set ℓ₁ := h.realCharacter (P.normal 1) with hℓ₁_def
    have hαβ : α ≠ 0 ∨ β ≠ 0 := (P.ne_zero_or_ne_zero_of_bracketNormal_ne_zero hμ).imp
      (Int.cast_ne_zero (α := ℝ)).mpr (Int.cast_ne_zero (α := ℝ)).mpr
    let p₀ : V → ℝ := fun z => ℓ₀ z - ℓ₀ θ₀
    let p₁ : V → ℝ := fun z => ℓ₁ z - ℓ₁ θ₀
    have hmem₀ (z : V) : z ∈ (D.wall (.inl 0)).support ↔ p₀ z = 0 := by
      rw [hD, completion_wall_inl]
      exact P.mem_hyperplane_support_iff h θ₀ 0 z
    have hmem₁ (z : V) : z ∈ (D.wall (.inl 1)).support ↔ p₁ z = 0 := by
      rw [hD, completion_wall_inl]
      exact P.mem_hyperplane_support_iff h θ₀ 1 z
    have hmem₂ (z : V) (u : Unit) : z ∈ (D.wall (.inr u)).support ↔
        α * p₁ z - β * p₀ z = 0 ∧ α * p₀ z + β * p₁ z ≤ 0 := by
      rw [hD, completion_wall_inr]
      exact P.mem_correction_support_iff h θ₀ hw hμ z
    -- The potential.
    let F : V → d.truncatedGroup ℒ k := fun z =>
      potential a b c (side (p₀ z)) (side (p₁ z)) (corner α (p₀ z) (α * p₁ z - β * p₀ z))
    refine D.levelConsistent_of_local k (F := F) ?_ ?_
    · -- Off the walls, the three exponents are locally constant.
      intro θ hθ
      have h₀ : p₀ θ ≠ 0 := fun h0 => hθ ⟨_, hall (.inl 0)⟩ ((hmem₀ θ).mpr h0)
      have h₁ : p₁ θ ≠ 0 := fun h1 => hθ ⟨_, hall (.inl 1)⟩ ((hmem₁ θ).mpr h1)
      have h₂ : ¬(α * p₁ θ - β * p₀ θ = 0 ∧ α * p₀ θ + β * p₁ θ ≤ 0) := fun h2 =>
        hθ ⟨_, hall (.inr ())⟩ ((hmem₂ θ ()).mpr h2)
      have hcont₀ : Continuous p₀ :=
        (LinearMap.continuous_of_finiteDimensional ℓ₀).sub continuous_const
      have hcont₁ : Continuous p₁ :=
        (LinearMap.continuous_of_finiteDimensional ℓ₁).sub continuous_const
      have ev (f : V → ℝ) (hf : Continuous f) (hne : f θ ≠ 0) :
          ∀ᶠ φ in 𝓝 θ, SignType.sign (f φ) = SignType.sign (f θ) := by
        filter_upwards [(hf.tendsto θ).eventually
          (Metric.ball_mem_nhds (f θ) (abs_pos.mpr hne))] with φ hφ
        rw [Real.dist_eq] at hφ
        simpa only [add_sub_cancel] using sign_add_of_abs_lt hφ
      have evq : ∀ᶠ φ in 𝓝 θ, α * p₁ θ - β * p₀ θ ≠ 0 →
          SignType.sign (α * p₁ φ - β * p₀ φ) = SignType.sign (α * p₁ θ - β * p₀ θ) := by
        by_cases hq : α * p₁ θ - β * p₀ θ = 0
        · exact Eventually.of_forall fun _ hne => absurd hq hne
        · filter_upwards [ev (fun z => α * p₁ z - β * p₀ z)
            ((continuous_const.mul hcont₁).sub (continuous_const.mul hcont₀)) hq]
            with φ hφ _ using hφ
      filter_upwards [ev p₀ hcont₀ h₀, ev p₁ hcont₁ h₁, evq] with φ hφ₀ hφ₁ hφq
      simp only [F]
      rw [side_eq (p₀ φ), side_eq (p₀ θ), hφ₀, side_eq (p₁ φ), side_eq (p₁ θ), hφ₁,
        corner_eq_of_sign_eq hαβ h₀ h₂ hφ₀ hφq]
    · -- At a regular wall germ, the potential jumps by the combined label.
      intro θ hθ v hv
      have hnormal₀ : (D.wall (.inl 0)).normal = P.normal 0 := by
        rw [hD, completion_wall_inl, hyperplane_normal]
      have hnormal₁ : (D.wall (.inl 1)).normal = P.normal 1 := by
        rw [hD, completion_wall_inl, hyperplane_normal]
      have hnormal₂ (u : Unit) : (D.wall (.inr u)).normal = P.bracketNormal := by
        rw [hD, completion_wall_inr, correction_normal]
      -- Walls through a regular point have the same kernel.
      have hker (j j' : Fin 2 ⊕ Unit) (hj : θ ∈ (D.wall j).support)
          (hj' : θ ∈ (D.wall j').support) :
          LinearMap.ker (h.realCharacter (D.wall j).normal) =
            LinearMap.ker (h.realCharacter (D.wall j').normal) := by
        rw [← (D.wall j).direction_support, ← (D.wall j').direction_support]
        exact congrArg AffineSubspace.direction
          (affineSpan_eq_of_notMem_singularSupport (W := fun j : D.active k => (D.wall j).support)
            (i := ⟨j, hall j⟩) (j := ⟨j', hall j'⟩) hθ hj hj')
      have hdir := P.realCharacter_bracketNormal_direction h
      have hα₀ (h0 : p₀ θ = 0) (h2 : α * p₁ θ - β * p₀ θ = 0 ∧ α * p₀ θ + β * p₁ θ ≤ 0) :
          α = 0 := by
        have hk := hker (.inl 0) (.inr ()) ((hmem₀ θ).mpr h0) ((hmem₂ θ ()).mpr h2)
        rw [hnormal₀, hnormal₂] at hk
        have hv₀ : i (ρ (P.degree 0 + P.degree 1)) ∈ LinearMap.ker ℓ₀ := by
          rw [hk]
          exact hdir
        rw [LinearMap.mem_ker, P.realCharacter_normal_zero_direction] at hv₀
        exact hv₀
      have hβ₁ (h1 : p₁ θ = 0) (h2 : α * p₁ θ - β * p₀ θ = 0 ∧ α * p₀ θ + β * p₁ θ ≤ 0) :
          β = 0 := by
        have hk := hker (.inl 1) (.inr ()) ((hmem₁ θ).mpr h1) ((hmem₂ θ ()).mpr h2)
        rw [hnormal₁, hnormal₂] at hk
        have hv₁ : i (ρ (P.degree 0 + P.degree 1)) ∈ LinearMap.ker ℓ₁ := by
          rw [hk]
          exact hdir
        rw [LinearMap.mem_ker, P.realCharacter_normal_one_direction] at hv₁
        exact hv₁
      have hreg (h0 : p₀ θ = 0) : p₁ θ ≠ 0 := by
        intro h1
        have h2 : α * p₁ θ - β * p₀ θ = 0 ∧ α * p₀ θ + β * p₁ θ ≤ 0 := by
          rw [h0, h1]
          constructor <;> simp
        rcases hαβ with hα | hβ
        exacts [hα (hα₀ h0 h2), hβ (hβ₁ h1 h2)]
      -- Transversality of the velocity to the walls through `θ`.
      have ht₀ (h0 : p₀ θ = 0) : ℓ₀ v ≠ 0 := by
        simpa only [hnormal₀] using hv ⟨_, hall (.inl 0)⟩ ((hmem₀ θ).mpr h0)
      have ht₁ (h1 : p₁ θ = 0) : ℓ₁ v ≠ 0 := by
        simpa only [hnormal₁] using hv ⟨_, hall (.inl 1)⟩ ((hmem₁ θ).mpr h1)
      have ht₂ (h2 : α * p₁ θ - β * p₀ θ = 0) (h2' : α * p₀ θ + β * p₁ θ ≤ 0) :
          α * ℓ₁ v - β * ℓ₀ v ≠ 0 := by
        simpa only [hnormal₂, P.realCharacter_bracketNormal] using
          hv ⟨_, hall (.inr ())⟩ ((hmem₂ θ ()).mpr ⟨h2, h2'⟩)
      -- Small perturbations keep every nonzero coordinate on its side.
      have evs (x y : ℝ) : ∀ᶠ σ in 𝓝[>] (0 : ℝ), x ≠ 0 → |σ * y| < |x| := by
        by_cases hx : x = 0
        · exact Eventually.of_forall fun _ hne => absurd hx hne
        · have hlim : Tendsto (fun σ : ℝ => |σ * y|) (𝓝 0) (𝓝 0) := by
            simpa using ((continuous_id.mul continuous_const).abs.tendsto (0 : ℝ) :
              Tendsto (fun σ : ℝ => |σ * y|) (𝓝 0) (𝓝 |0 * y|))
          exact Eventually.mono (nhdsWithin_le_nhds (hlim.eventually_lt_const (abs_pos.mpr hx)))
            fun _ hσ _ => hσ
      filter_upwards [self_mem_nhdsWithin, evs (p₀ θ) (ℓ₀ v), evs (p₁ θ) (ℓ₁ v),
        evs (α * p₁ θ - β * p₀ θ) (α * ℓ₁ v - β * ℓ₀ v)] with σ hσ hs₀ hs₁ hsq
      have hσ : 0 < σ := hσ
      have hp₀ : p₀ (θ + σ • v) = p₀ θ + σ * ℓ₀ v := by
        simp only [p₀, map_add, map_smul, smul_eq_mul]
        ring
      have hp₀' : p₀ (θ - σ • v) = p₀ θ - σ * ℓ₀ v := by
        simp only [p₀, map_sub, map_smul, smul_eq_mul]
        ring
      have hp₁ : p₁ (θ + σ • v) = p₁ θ + σ * ℓ₁ v := by
        simp only [p₁, map_add, map_smul, smul_eq_mul]
        ring
      have hp₁' : p₁ (θ - σ • v) = p₁ θ - σ * ℓ₁ v := by
        simp only [p₁, map_sub, map_smul, smul_eq_mul]
        ring
      have hq : α * (p₁ θ + σ * ℓ₁ v) - β * (p₀ θ + σ * ℓ₀ v) =
          (α * p₁ θ - β * p₀ θ) + σ * (α * ℓ₁ v - β * ℓ₀ v) := by ring
      have hq' : α * (p₁ θ - σ * ℓ₁ v) - β * (p₀ θ - σ * ℓ₀ v) =
          (α * p₁ θ - β * p₀ θ) - σ * (α * ℓ₁ v - β * ℓ₀ v) := by ring
      -- One of the two hyperplane sides is unchanged.
      have hsr : side (p₀ θ + σ * ℓ₀ v) = side (p₀ θ - σ * ℓ₀ v) ∨
          side (p₁ θ + σ * ℓ₁ v) = side (p₁ θ - σ * ℓ₁ v) := by
        rcases eq_or_ne (p₀ θ) 0 with h0 | h0
        · right
          rw [side_eq, side_eq, sign_add_of_abs_lt (hs₁ (hreg h0)),
            sign_sub_of_abs_lt (hs₁ (hreg h0))]
        · left
          rw [side_eq, side_eq, sign_add_of_abs_lt (hs₀ h0), sign_sub_of_abs_lt (hs₀ h0)]
      simp only [F]
      rw [hp₀, hp₀', hp₁, hp₁', hq, hq', potential_mul_inv hab hac hbc hsr]
      -- Compare logarithms with the signed sum of the incident wall logarithms.
      apply BCHGroup.log_injective
      let G : Fin 2 ⊕ Unit → d.truncatedLie ℒ k := fun j =>
        if θ ∈ (D.wall j).support then
          (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ) •
            BCHGroup.log (L := d.truncatedLie ℒ k)
              (CompletedGroup.projection k (D.wall j).label) else 0
      have hsum : BCHGroup.log (D.combinedLabel k θ v hθ) = ∑ j, G j := by
        let := Fintype.ofFinite (D.active k)
        rw [D.log_combinedLabel_eq_sum k θ v hθ]
        exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv hall) _ G (fun _ => rfl)
      rw [BCHGroup.log_exp, hsum, Fintype.sum_sum_type, Fin.sum_univ_two, Fintype.sum_unique]
      simp only [G, hmem₀, hmem₁, hmem₂, hnormal₀, hnormal₁, hnormal₂, hlabel₀, hlabel₁, hlabel₂,
        BCHGroup.log_exp, P.realCharacter_bracketNormal]
      -- The three integer coefficients are the jumps of the potential.
      have hne {x : ℝ} (hx : x ≠ 0) : σ * x ≠ 0 := mul_ne_zero hσ.ne' hx
      rw [corner_jump α β (p₀ θ) (p₁ θ) _ (σ * ℓ₀ v) (σ * ℓ₁ v) (σ * (α * ℓ₁ v - β * ℓ₀ v)) hαβ
          rfl (by ring) hs₀ hs₁ hsq hreg (fun h0 => hne (ht₀ h0)) (fun h2 h2' => hne (ht₂ h2 h2')),
        side_sub_sub_side hs₀ (fun h0 => hne (ht₀ h0)),
        side_sub_sub_side hs₁ (fun h1 => hne (ht₁ h1)),
        crossSign_mul hσ, crossSign_mul hσ, crossSign_mul hσ]
      simp only [crossSign, ite_smul, zero_smul, ← hℓ₀_def, ← hℓ₁_def, ← hα_def, ← hβ_def]

/-- The two hyperplanes together with the correction wall form a consistent diagram. -/
theorem consistent_completion : (P.completion h θ₀ hw hμ).Consistent :=
  (consistent_iff _).mpr (P.levelConsistent_completion h θ₀ hw hμ)

/-- **Local scattering with square-zero coefficients.** For a nonzero bracket normal `μ`, the
outgoing completion of the hyperplanes `{m₀ = m₀(θ₀)}` and `{m₁ = m₁(θ₀)}` labelled by
`exp (t₀ x₀)` and `exp (t₁ x₁)` adds the single wall `exp (t₀ t₁ ⁅x₀, x₁⁆)` with normal `μ`,
supported on the joint swept by `-i(ρ(n₀ + n₁))`. -/
theorem isOutgoingCompletion_completion :
    IsOutgoingCompletion (P.input h θ₀).wall (P.completion h θ₀ hw hμ) where
  wall_inl j := by rw [completion_wall_inl, input_wall]
  outgoing_inr u := by
    rw [completion_wall_inr]
    exact P.correction_outgoing h θ₀ hw hμ
  consistent := P.consistent_completion h θ₀ hw hμ

/-- The scattering class of the two hyperplanes is represented by the diagram with the single
correction wall. -/
theorem scat_input_eq_toClass_completion [Module.Free ℤ Γ] :
    (P.input h θ₀).Scat (P.input_full h θ₀) = (P.completion h θ₀ hw hμ).toClass :=
  scat_eq_toClass _ _ (P.isOutgoingCompletion_completion h θ₀ hw hμ)

end Completion

section Trivial

/-- If the bracket normal vanishes, the two hyperplanes are consistent with no further walls:
their labels commute, since the bracket lies in a wall space with zero normal. -/
theorem isOutgoingCompletion_inputWithoutCorrection (hμ : P.bracketNormal = 0) :
    IsOutgoingCompletion (P.input h θ₀).wall (P.inputWithoutCorrection h θ₀) where
  wall_inl j := by rw [inputWithoutCorrection_wall_inl, input_wall]
  outgoing_inr u := u.elim
  consistent := by
    have hcomm : Commute (d.expToCompletion ℒ (P.scalar 0 • P.coeff 0))
        (d.expToCompletion ℒ (P.scalar 1 • P.coeff 1)) :=
      d.commute_expToCompletion_of_lie_eq_zero ℒ
        (by rw [P.lie_smul_coeff, P.commutator_eq_zero_of_bracketNormal_eq_zero hμ])
    apply consistent_of_commute_of_full
    · rintro (j | u)
      · rw [inputWithoutCorrection_wall_inl, hyperplane_support, hyperplane_normal]
        exact ⟨_, rfl⟩
      · exact u.elim
    · rintro (j | u) (j' | u')
      · rw [inputWithoutCorrection_wall_inl, inputWithoutCorrection_wall_inl, hyperplane_label,
          hyperplane_label]
        fin_cases j <;> fin_cases j'
        exacts [Commute.refl _, hcomm, hcomm.symm, Commute.refl _]
      all_goals first | exact u.elim | exact u'.elim

/-- If the bracket normal vanishes, the scattering class of the two hyperplanes is that of the
hyperplanes alone. -/
theorem scat_input_eq_toClass_of_bracketNormal_eq_zero [Module.Free ℤ Γ]
    (hμ : P.bracketNormal = 0) :
    (P.input h θ₀).Scat (P.input_full h θ₀) = (P.inputWithoutCorrection h θ₀).toClass :=
  scat_eq_toClass _ _ (P.isOutgoingCompletion_inputWithoutCorrection h θ₀ hμ)

/-- If the total degree has zero geometric direction, the bracket normal vanishes, and the
scattering class of the two hyperplanes is that of the hyperplanes alone. -/
theorem scat_input_eq_toClass_of_direction_eq_zero [Module.Free ℤ Γ]
    (hρ : ρ (P.degree 0 + P.degree 1) = 0) :
    (P.input h θ₀).Scat (P.input_full h θ₀) = (P.inputWithoutCorrection h θ₀).toClass :=
  P.scat_input_eq_toClass_of_bracketNormal_eq_zero h θ₀
    (P.bracketNormal_eq_zero_of_direction_eq_zero hρ)

end Trivial

end SquareZeroPair

end Mei.DirectedDiagram
