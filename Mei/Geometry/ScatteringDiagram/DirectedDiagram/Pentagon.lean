/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalProduct
public import Mei.Topology.Order.Sign

/-!
# Consistency of the pentagon configuration

Let `ℓ₁, ℓ₂` be the real extensions of two integral normals `μ₁, μ₂`, neither of whose kernels
contains the other. A directed diagram is in *pentagon configuration*
(`DirectedDiagram.IsPentagonConfiguration`) when it has exactly three walls: the hyperplanes
`{ℓ₁ = 0}` and `{ℓ₂ = 0}`, cooriented by `μ₁` and `μ₂`, and the half-hyperplane
`{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}`, cooriented by `μ₁ + μ₂`. Write `A`, `B` and `C` for their labels. If
they satisfy the pentagon relation `B A = A C B`, the diagram is consistent
(`DirectedDiagram.IsPentagonConfiguration.consistent`).

The chamber function `pentagonTransport A B C a b` is the product
`A^[a > 0] C^[a > 0, a + b > 0] B^[b > 0]`, where `X^[P]` is `X` if `P` holds and `1` otherwise
(`DirectedDiagram.pentagonTransport_def`); in the five chambers of the configuration it takes the
values `1`, `B`, `A`, `A C` and `A C B` at `(a, b) = (ℓ₁ x, ℓ₂ x)`
(`DirectedDiagram.pentagonTransport_of_neg_of_neg` and its four companions). At every order,
for the projected labels, it is locally constant off the active walls
(`DirectedDiagram.IsPentagonConfiguration.eventually_pentagonTransport_eq`), and crossing a wall
changes it by the signed combined label of the crossing
(`DirectedDiagram.IsPentagonConfiguration.eventually_inv_mul_eq_combinedLabel`). Walls whose
labels vanish at an order are allowed.

For dilogarithm labels the relation is the pentagon identity, and the configuration is the
consistent scattering diagram of type `A₂` (Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1.1, arXiv:1411.1394v2); see
`Mei.Geometry.ScatteringDiagram.Skew.Principal.Pentagon`.
`DirectedDiagram.IsPentagonConfiguration.consistent` is derived from the local criterion
`DirectedDiagram.levelConsistent_of_local` applied to the chamber function.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.DirectedDiagram

section Transport

variable {G : Type*} [Group G] (A B C : G)

/-- The chamber function of the pentagon configuration in the coordinates `(a, b)`: the product
`A^[a > 0] C^[a > 0, a + b > 0] B^[b > 0]`, where `X^[P]` is `X` if `P` holds and `1`
otherwise. -/
def pentagonTransport (a b : ℝ) : G :=
  (if 0 < a then A else 1) * (if 0 < a ∧ 0 < a + b then C else 1) * (if 0 < b then B else 1)

/-- The defining formula of `pentagonTransport`. -/
theorem pentagonTransport_def (a b : ℝ) :
    pentagonTransport A B C a b =
      (if 0 < a then A else 1) * (if 0 < a ∧ 0 < a + b then C else 1) *
        (if 0 < b then B else 1) := (rfl)

variable {A B C}

/-- The chamber function takes equal values at two points when each of its three factors is
the identity or has the same indicator at both points. -/
theorem pentagonTransport_congr {a b a' b' : ℝ} (hA : A = 1 ∨ (0 < a ↔ 0 < a'))
    (hB : B = 1 ∨ (0 < b ↔ 0 < b'))
    (hC : C = 1 ∨ (0 < a ∧ 0 < a + b ↔ 0 < a' ∧ 0 < a' + b')) :
    pentagonTransport A B C a b = pentagonTransport A B C a' b' := by
  have key : ∀ {X : G} {P Q : Prop} [Decidable P] [Decidable Q], (X = 1 ∨ (P ↔ Q)) →
      (if P then X else 1) = if Q then X else 1 := by
    rintro X P Q _ _ (rfl | hPQ)
    · simp
    · exact if_congr hPQ rfl rfl
  rw [pentagonTransport_def, pentagonTransport_def, key hA, key hB, key hC]

/-- In the chamber `{a < 0, b < 0}` the chamber function is `1`. -/
theorem pentagonTransport_of_neg_of_neg {a b : ℝ} (ha : a < 0) (hb : b < 0) :
    pentagonTransport A B C a b = 1 := by
  simp [pentagonTransport_def, not_lt.mpr ha.le, not_lt.mpr hb.le]

/-- In the chamber `{a < 0, b > 0}` the chamber function is `B`. -/
theorem pentagonTransport_of_neg_of_pos {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    pentagonTransport A B C a b = B := by
  simp [pentagonTransport_def, not_lt.mpr ha.le, hb]

/-- In the chamber `{a > 0, b > 0}` the chamber function is `A C B`. -/
theorem pentagonTransport_of_pos_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    pentagonTransport A B C a b = A * C * B := by
  simp [pentagonTransport_def, ha, hb, add_pos ha hb]

/-- In the chamber `{a > 0, a + b < 0}` the chamber function is `A`. -/
theorem pentagonTransport_of_pos_of_add_neg {a b : ℝ} (ha : 0 < a) (hab : a + b < 0) :
    pentagonTransport A B C a b = A := by
  have hb : b ≤ 0 := by linarith
  simp [pentagonTransport_def, ha, not_lt.mpr hab.le, not_lt.mpr hb]

/-- In the chamber `{a > 0, b < 0, a + b > 0}` the chamber function is `A C`. -/
theorem pentagonTransport_of_pos_of_neg_of_add_pos {a b : ℝ} (ha : 0 < a) (hb : b < 0)
    (hab : 0 < a + b) : pentagonTransport A B C a b = A * C := by
  simp [pentagonTransport_def, ha, hab, not_lt.mpr hb.le]

/-- If `B` and `C` are the identity, the chamber function is `A^[a > 0]`. -/
theorem pentagonTransport_one_one (a b : ℝ) :
    pentagonTransport A 1 1 a b = if 0 < a then A else 1 := by
  simp [pentagonTransport_def]

/-- If `A` and `C` are the identity, the chamber function is `B^[b > 0]`. -/
theorem pentagonTransport_one_left_one (a b : ℝ) :
    pentagonTransport 1 B 1 a b = if 0 < b then B else 1 := by
  simp [pentagonTransport_def]

/-- Crossing `{a = 0}` in a direction with `a' > 0`, at a point with `b ≠ 0` or where `B` is the
identity, multiplies the chamber function on the right by `A`, provided `B A = A C B`. -/
theorem eventually_pentagonTransport_fst (hpent : B * A = A * C * B) {a b a' b' : ℝ}
    (ha : a = 0) (hb : b ≠ 0 ∨ B = 1) (ha' : 0 < a') :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), pentagonTransport A B C (a + s * a') (b + s * b') =
      pentagonTransport A B C (a - s * a') (b - s * b') * A := by
  subst ha
  have hs : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s * a' :=
    Eventually.mono (self_mem_nhdsWithin : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s) fun _ hs =>
      mul_pos hs ha'
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  rcases hb with hb | rfl
  · rcases hb.lt_or_gt with hb | hb
    · filter_upwards [hs, hle (eventually_add_mul_neg hb b'), hle (eventually_add_mul_neg hb (-b')),
        hle (eventually_add_mul_neg hb (a' + b'))] with s hs h₁ h₂ h₃
      rw [pentagonTransport_of_pos_of_add_neg (by linarith) (by linarith),
        pentagonTransport_of_neg_of_neg (by linarith) (by linarith), one_mul]
    · filter_upwards [hs, hle (eventually_pos_add_mul hb b'), hle (eventually_pos_add_mul hb (-b'))]
        with s hs h₁ h₂
      rw [pentagonTransport_of_pos_of_pos (by linarith) h₁,
        pentagonTransport_of_neg_of_pos (by linarith) (by linarith), hpent]
  · obtain rfl : C = 1 := by simpa using hpent
    filter_upwards [hs] with s hs
    rw [pentagonTransport_one_one, pentagonTransport_one_one, ite_eq_left (by linarith),
      ite_eq_right (by linarith), one_mul]

/-- Crossing `{b = 0}` in a direction with `b' > 0`, at a point with `a ≠ 0` or where `A` is the
identity, multiplies the chamber function on the right by `B`, provided `B A = A C B`. -/
theorem eventually_pentagonTransport_snd (hpent : B * A = A * C * B) {a b a' b' : ℝ}
    (hb : b = 0) (ha : a ≠ 0 ∨ A = 1) (hb' : 0 < b') :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), pentagonTransport A B C (a + s * a') (b + s * b') =
      pentagonTransport A B C (a - s * a') (b - s * b') * B := by
  subst hb
  have hs : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s * b' :=
    Eventually.mono (self_mem_nhdsWithin : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s) fun _ hs =>
      mul_pos hs hb'
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  rcases ha with ha | rfl
  · rcases ha.lt_or_gt with ha | ha
    · filter_upwards [hs, hle (eventually_add_mul_neg ha a'), hle (eventually_add_mul_neg ha (-a'))]
        with s hs h₁ h₂
      rw [pentagonTransport_of_neg_of_pos (by linarith) (by linarith),
        pentagonTransport_of_neg_of_neg (by linarith) (by linarith), one_mul]
    · filter_upwards [hs, hle (eventually_pos_add_mul ha a'), hle (eventually_pos_add_mul ha (-a')),
        hle (eventually_pos_add_mul ha (-a' - b'))] with s hs h₁ h₂ h₃
      rw [pentagonTransport_of_pos_of_pos h₁ (by linarith),
        pentagonTransport_of_pos_of_neg_of_add_pos (by linarith) (by linarith) (by linarith)]
  · obtain rfl : C = 1 := by simpa using hpent
    filter_upwards [hs] with s hs
    rw [pentagonTransport_one_left_one, pentagonTransport_one_left_one, ite_eq_left (by linarith),
      ite_eq_right (by linarith), one_mul]

/-- Crossing `{a + b = 0}` in a direction with `a' + b' > 0`, at a point with `a > 0`,
multiplies the chamber function on the right by `C`. -/
theorem eventually_pentagonTransport_add {a b a' b' : ℝ} (hab : a + b = 0) (ha : 0 < a)
    (hab' : 0 < a' + b') :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), pentagonTransport A B C (a + s * a') (b + s * b') =
      pentagonTransport A B C (a - s * a') (b - s * b') * C := by
  have hb : b < 0 := by linarith
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hle (eventually_pos_add_mul ha a'),
    hle (eventually_pos_add_mul ha (-a')), hle (eventually_add_mul_neg hb b'),
    hle (eventually_add_mul_neg hb (-b'))] with s (hs : 0 < s) h₁ h₂ h₃ h₄
  have hsab : 0 < s * (a' + b') := mul_pos hs hab'
  rw [pentagonTransport_of_pos_of_neg_of_add_pos h₁ h₃ (by linarith),
    pentagonTransport_of_pos_of_add_neg (by linarith) (by linarith)]

end Transport

section Crossing

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℝ V]

/-- Let `T` be a function on `V` such that, near `θ`, crossing in every direction `w` with
`ℓ w > 0` multiplies `T` on the right by `X`. Then crossing in any direction `v` with
`ℓ v ≠ 0` gives `T (θ + s • v)⁻¹ * T (θ - s • v) = X⁻¹` if `ℓ v > 0` and `X` if `ℓ v < 0`,
for all small `s > 0`. -/
theorem eventually_inv_mul_eq_zpow {T : V → G} {θ v : V} {ℓ : V →ₗ[ℝ] ℝ} {X : G}
    (hT : ∀ w, 0 < ℓ w → ∀ᶠ s in 𝓝[>] (0 : ℝ), T (θ + s • w) = T (θ - s • w) * X)
    (hv : ℓ v ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (T (θ + s • v))⁻¹ * T (θ - s • v) =
      X ^ (if 0 < ℓ v then -1 else 1 : ℤ) := by
  rcases hv.lt_or_gt with hv | hv
  · filter_upwards [hT (-v) (by simpa using hv)] with s hs
    rw [smul_neg, ← sub_eq_add_neg, sub_neg_eq_add] at hs
    rw [hs, ite_eq_right (not_lt.mpr hv.le)]
    group
  · filter_upwards [hT v hv] with s hs
    rw [hs, ite_eq_left hv]
    group

end Crossing


section Diagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- A directed diagram is in *pentagon configuration* with walls `j₁, j₂, j₃` and integral
normals `μ₁, μ₂`, with real extensions `ℓ₁, ℓ₂`, when `j₁, j₂, j₃` are all its walls, the walls
`j₁` and `j₂` are the hyperplanes `{ℓ₁ = 0}` and `{ℓ₂ = 0}` cooriented by `μ₁` and `μ₂`, the
wall `j₃` is the half-hyperplane `{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}` cooriented by `μ₁ + μ₂`, and each of
the kernels of `ℓ₁` and `ℓ₂` contains a vector outside the other. -/
structure IsPentagonConfiguration (j₁ j₂ j₃ : ι) (μ₁ μ₂ : Λ →+ ℤ) : Prop where
  /-- Every wall is one of the three. -/
  eq_or_eq_or_eq (j : ι) : j = j₁ ∨ j = j₂ ∨ j = j₃
  /-- The first wall is cooriented by `μ₁`. -/
  normal_fst : (D.wall j₁).normal = μ₁
  /-- The second wall is cooriented by `μ₂`. -/
  normal_snd : (D.wall j₂).normal = μ₂
  /-- The half-hyperplane wall is cooriented by `μ₁ + μ₂`. -/
  normal_half : (D.wall j₃).normal = μ₁ + μ₂
  /-- The first wall is the hyperplane `{ℓ₁ = 0}`. -/
  support_fst : (D.wall j₁).support = {x | h.realCharacter μ₁ x = 0}
  /-- The second wall is the hyperplane `{ℓ₂ = 0}`. -/
  support_snd : (D.wall j₂).support = {x | h.realCharacter μ₂ x = 0}
  /-- The third wall is the half-hyperplane `{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}`. -/
  support_half : (D.wall j₃).support =
    {x | h.realCharacter μ₁ x + h.realCharacter μ₂ x = 0 ∧ 0 ≤ h.realCharacter μ₁ x}
  /-- The kernel of `ℓ₁` is not contained in that of `ℓ₂`. -/
  exists_fst : ∃ x, h.realCharacter μ₁ x = 0 ∧ h.realCharacter μ₂ x ≠ 0
  /-- The kernel of `ℓ₂` is not contained in that of `ℓ₁`. -/
  exists_snd : ∃ x, h.realCharacter μ₂ x = 0 ∧ h.realCharacter μ₁ x ≠ 0

namespace IsPentagonConfiguration

variable {D} {j₁ j₂ j₃ : ι} {μ₁ μ₂ : Λ →+ ℤ} (hD : D.IsPentagonConfiguration j₁ j₂ j₃ μ₁ μ₂)
include hD

/-- The kernels of the normals of the two hyperplane walls differ. -/
theorem ker_fst_ne_snd : LinearMap.ker (h.realCharacter (D.wall j₁).normal) ≠
    LinearMap.ker (h.realCharacter (D.wall j₂).normal) := by
  obtain ⟨x, hx₁, hx₂⟩ := hD.exists_fst
  intro he
  have hx : x ∈ LinearMap.ker (h.realCharacter (D.wall j₂).normal) := by
    rw [← he, LinearMap.mem_ker, hD.normal_fst, hx₁]
  rw [LinearMap.mem_ker, hD.normal_snd] at hx
  exact hx₂ hx

/-- The kernels of the normals of the first wall and of the half-hyperplane wall differ. -/
theorem ker_fst_ne_half : LinearMap.ker (h.realCharacter (D.wall j₁).normal) ≠
    LinearMap.ker (h.realCharacter (D.wall j₃).normal) := by
  obtain ⟨x, hx₁, hx₂⟩ := hD.exists_fst
  intro he
  have hx : x ∈ LinearMap.ker (h.realCharacter (D.wall j₃).normal) := by
    rw [← he, LinearMap.mem_ker, hD.normal_fst, hx₁]
  rw [LinearMap.mem_ker, hD.normal_half, map_add, LinearMap.add_apply, hx₁, zero_add] at hx
  exact hx₂ hx

/-- The kernels of the normals of the second wall and of the half-hyperplane wall differ. -/
theorem ker_snd_ne_half : LinearMap.ker (h.realCharacter (D.wall j₂).normal) ≠
    LinearMap.ker (h.realCharacter (D.wall j₃).normal) := by
  obtain ⟨x, hx₂, hx₁⟩ := hD.exists_snd
  intro he
  have hx : x ∈ LinearMap.ker (h.realCharacter (D.wall j₃).normal) := by
    rw [← he, LinearMap.mem_ker, hD.normal_snd, hx₂]
  rw [LinearMap.mem_ker, hD.normal_half, map_add, LinearMap.add_apply, hx₂, add_zero] at hx
  exact hx₁ hx

variable (hpent : (D.wall j₂).label * (D.wall j₁).label =
  (D.wall j₁).label * (D.wall j₃).label * (D.wall j₂).label) (k : ℕ)

local notation "𝒜" => CompletedGroup.projection k (DirectedWall.label (DirectedDiagram.wall D j₁))
local notation "ℬ" => CompletedGroup.projection k (DirectedWall.label (DirectedDiagram.wall D j₂))
local notation "𝒞" => CompletedGroup.projection k (DirectedWall.label (DirectedDiagram.wall D j₃))
local notation "ℓ₁" => h.realCharacter μ₁
local notation "ℓ₂" => h.realCharacter μ₂

include hpent

omit hD in
/-- The pentagon relation of the order-`k` projections of the labels. -/
theorem projection_pentagon : ℬ * 𝒜 = 𝒜 * 𝒞 * ℬ := by
  simpa only [map_mul] using congrArg (CompletedGroup.projection k) hpent

omit hD in
/-- If the label of the first wall vanishes at order `k`, so does that of the half-hyperplane
wall. -/
theorem projection_half_eq_one_of_fst (hA : 𝒜 = 1) : 𝒞 = 1 := by
  simpa [hA] using projection_pentagon hpent k

omit hD in
/-- If the label of the second wall vanishes at order `k`, so does that of the half-hyperplane
wall. -/
theorem projection_half_eq_one_of_snd (hB : ℬ = 1) : 𝒞 = 1 := by
  simpa [hB] using projection_pentagon hpent k

/-- Off the active walls, the chamber function of the order-`k` labels is locally constant. -/
theorem eventually_pentagonTransport_eq {θ : V} (hθ : ∀ j : D.active k, θ ∉ (D.wall j).support) :
    ∀ᶠ φ in 𝓝 θ, pentagonTransport 𝒜 ℬ 𝒞 (ℓ₁ φ) (ℓ₂ φ) = pentagonTransport 𝒜 ℬ 𝒞 (ℓ₁ θ) (ℓ₂ θ) := by
  let := h.finiteDimensional
  have hsign : ∀ {f : V →ₗ[ℝ] ℝ}, f θ ≠ 0 → ∀ᶠ φ in 𝓝 θ, (0 < f φ ↔ 0 < f θ) := by
    intro f hf
    have hc : ContinuousAt f θ := (LinearMap.continuous_of_finiteDimensional f).continuousAt
    rcases hf.lt_or_gt with hf | hf
    · filter_upwards [hc.eventually_lt continuousAt_const hf] with φ hφ
      exact iff_of_false (not_lt.mpr hφ.le) (not_lt.mpr hf.le)
    · filter_upwards [continuousAt_const.eventually_lt hc hf] with φ hφ
      exact iff_of_true hφ hf
  -- A wall with a nonvanishing projected label does not contain `θ`.
  have hoff : ∀ j, CompletedGroup.projection k (D.wall j).label ≠ 1 → θ ∉ (D.wall j).support :=
    fun j hj => hθ ⟨j, (D.mem_active k j).mpr hj⟩
  have h₁ : 𝒜 = 1 ∨ ℓ₁ θ ≠ 0 := by
    refine or_iff_not_imp_left.mpr fun hA hz => hoff j₁ hA ?_
    rw [hD.support_fst]
    exact hz
  have h₂ : ℬ = 1 ∨ ℓ₂ θ ≠ 0 := by
    refine or_iff_not_imp_left.mpr fun hB hz => hoff j₂ hB ?_
    rw [hD.support_snd]
    exact hz
  have e₁ : ∀ᶠ φ in 𝓝 θ, 𝒜 = 1 ∨ (0 < ℓ₁ φ ↔ 0 < ℓ₁ θ) := by
    rcases h₁ with hA | hA
    · exact Eventually.of_forall fun _ => Or.inl hA
    · exact (hsign hA).mono fun _ hφ => Or.inr hφ
  have e₂ : ∀ᶠ φ in 𝓝 θ, ℬ = 1 ∨ (0 < ℓ₂ φ ↔ 0 < ℓ₂ θ) := by
    rcases h₂ with hB | hB
    · exact Eventually.of_forall fun _ => Or.inl hB
    · exact (hsign hB).mono fun _ hφ => Or.inr hφ
  have e₃ : ∀ᶠ φ in 𝓝 θ, 𝒞 = 1 ∨
      (0 < ℓ₁ φ ∧ 0 < ℓ₁ φ + ℓ₂ φ ↔ 0 < ℓ₁ θ ∧ 0 < ℓ₁ θ + ℓ₂ θ) := by
    by_cases hC : 𝒞 = 1
    · exact Eventually.of_forall fun _ => Or.inl hC
    have hA : ℓ₁ θ ≠ 0 :=
      h₁.resolve_left fun hA => hC (projection_half_eq_one_of_fst hpent k hA)
    rcases hA.lt_or_gt with hA | hA
    · filter_upwards [hsign hA.ne] with φ hφ
      exact Or.inr (iff_of_false (fun h' => (not_lt.mpr hA.le) (hφ.mp h'.1))
        fun h' => (not_lt.mpr hA.le) h'.1)
    · have hs : ℓ₁ θ + ℓ₂ θ ≠ 0 := fun hz => hoff j₃ hC (by
        rw [hD.support_half]
        exact ⟨hz, hA.le⟩)
      have hs' : (ℓ₁ + ℓ₂) θ ≠ 0 := by simpa using hs
      filter_upwards [hsign hA.ne', hsign hs'] with φ hφ hφ'
      simp only [LinearMap.add_apply] at hφ'
      exact Or.inr (and_congr hφ hφ')
  filter_upwards [e₁, e₂, e₃] with φ hφ₁ hφ₂ hφ₃
  exact pentagonTransport_congr hφ₁ hφ₂ hφ₃

omit hpent in
/-- A point outside the singular support of the walls active at order `k` lies on at most one
of them. -/
theorem eq_of_mem_support {θ : V}
    (hθ : θ ∉ singularSupport fun j : D.active k => (D.wall j).support) {a b : ι}
    (ha : a ∈ D.active k) (hb : b ∈ D.active k) (hθa : θ ∈ (D.wall a).support)
    (hθb : θ ∈ (D.wall b).support) : a = b := by
  have hker : LinearMap.ker (h.realCharacter (D.wall a).normal) =
      LinearMap.ker (h.realCharacter (D.wall b).normal) := by
    rw [← (D.wall a).direction_support, ← (D.wall b).direction_support]
    exact congrArg AffineSubspace.direction (affineSpan_eq_of_notMem_singularSupport
      (W := fun j : D.active k => (D.wall j).support) (i := ⟨a, ha⟩) (j := ⟨b, hb⟩) hθ hθa hθb)
  rcases hD.eq_or_eq_or_eq a with rfl | rfl | rfl <;>
    rcases hD.eq_or_eq_or_eq b with rfl | rfl | rfl
  all_goals first
    | rfl
    | exact absurd hker hD.ker_fst_ne_snd
    | exact absurd hker.symm hD.ker_fst_ne_snd
    | exact absurd hker hD.ker_fst_ne_half
    | exact absurd hker.symm hD.ker_fst_ne_half
    | exact absurd hker hD.ker_snd_ne_half
    | exact absurd hker.symm hD.ker_snd_ne_half

omit hD in
/-- Crossing the first wall at a point `θ` with `ℓ₂ θ ≠ 0`, or where the second label vanishes
at order `k`, in a direction `v` with `ℓ₁ v ≠ 0`, the chamber function changes by the signed
projected label of the first wall. -/
theorem eventually_inv_mul_fst {θ v : V} (hθ₁ : ℓ₁ θ = 0) (hθ₂ : ℓ₂ θ ≠ 0 ∨ ℬ = 1)
    (hv : ℓ₁ v ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (pentagonTransport 𝒜 ℬ 𝒞 (ℓ₁ (θ + s • v)) (ℓ₂ (θ + s • v)))⁻¹ *
      pentagonTransport 𝒜 ℬ 𝒞 (ℓ₁ (θ - s • v)) (ℓ₂ (θ - s • v)) =
        𝒜 ^ (if 0 < ℓ₁ v then -1 else 1 : ℤ) :=
  eventually_inv_mul_eq_zpow (T := fun x => pentagonTransport 𝒜 ℬ 𝒞 (ℓ₁ x) (ℓ₂ x))
    (fun w hw => by
      simpa only [map_add, map_sub, map_smul, smul_eq_mul] using
        eventually_pentagonTransport_fst (projection_pentagon hpent k) hθ₁ hθ₂ hw) hv

omit hD in
/-- Crossing the second wall at a point `θ` with `ℓ₁ θ ≠ 0`, or where the first label vanishes
at order `k`, in a direction `v` with `ℓ₂ v ≠ 0`, the chamber function changes by the signed
projected label of the second wall. -/
theorem eventually_inv_mul_snd {θ v : V} (hθ₂ : ℓ₂ θ = 0) (hθ₁ : ℓ₁ θ ≠ 0 ∨ 𝒜 = 1)
    (hv : ℓ₂ v ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (pentagonTransport 𝒜 ℬ 𝒞 (ℓ₁ (θ + s • v)) (ℓ₂ (θ + s • v)))⁻¹ *
      pentagonTransport 𝒜 ℬ 𝒞 (ℓ₁ (θ - s • v)) (ℓ₂ (θ - s • v)) =
        ℬ ^ (if 0 < ℓ₂ v then -1 else 1 : ℤ) :=
  eventually_inv_mul_eq_zpow (T := fun x => pentagonTransport 𝒜 ℬ 𝒞 (ℓ₁ x) (ℓ₂ x))
    (fun w hw => by
      simpa only [map_add, map_sub, map_smul, smul_eq_mul] using
        eventually_pentagonTransport_snd (projection_pentagon hpent k) hθ₂ hθ₁ hw) hv

omit hD hpent in
/-- Crossing the half-hyperplane wall at a point `θ` with `ℓ₁ θ > 0`, in a direction `v` with
`ℓ₁ v + ℓ₂ v ≠ 0`, the chamber function changes by the signed projected label of that wall. -/
theorem eventually_inv_mul_half {θ v : V} (hθ : ℓ₁ θ + ℓ₂ θ = 0) (hθ₁ : 0 < ℓ₁ θ)
    (hv : h.realCharacter (μ₁ + μ₂) v ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (pentagonTransport 𝒜 ℬ 𝒞 (ℓ₁ (θ + s • v)) (ℓ₂ (θ + s • v)))⁻¹ *
      pentagonTransport 𝒜 ℬ 𝒞 (ℓ₁ (θ - s • v)) (ℓ₂ (θ - s • v)) =
        𝒞 ^ (if 0 < h.realCharacter (μ₁ + μ₂) v then -1 else 1 : ℤ) :=
  eventually_inv_mul_eq_zpow (T := fun x => pentagonTransport 𝒜 ℬ 𝒞 (ℓ₁ x) (ℓ₂ x))
    (fun w hw => by
      rw [map_add, LinearMap.add_apply] at hw
      simpa only [map_add, map_sub, map_smul, smul_eq_mul] using
        eventually_pentagonTransport_add hθ hθ₁ hw) hv

/-- At a point `θ` outside the singular support of the walls active at order `k`, crossing in a
direction transverse to these walls changes the chamber function by the combined label. -/
theorem eventually_inv_mul_eq_combinedLabel {θ : V}
    (hθ : θ ∉ singularSupport fun j : D.active k => (D.wall j).support) {v : V}
    (hv : ∀ j : D.active k, θ ∈ (D.wall j).support → h.realCharacter (D.wall j).normal v ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (pentagonTransport 𝒜 ℬ 𝒞 (ℓ₁ (θ + s • v)) (ℓ₂ (θ + s • v)))⁻¹ *
      pentagonTransport 𝒜 ℬ 𝒞 (ℓ₁ (θ - s • v)) (ℓ₂ (θ - s • v)) =
        D.combinedLabel k θ v hθ := by
  by_cases hoff : ∀ j : D.active k, θ ∉ (D.wall j).support
  · -- Off the walls, the chamber function is constant near `θ`.
    rw [D.combinedLabel_eq_one_of_forall_notMem k θ v hθ hoff]
    have ht : ∀ w : V, Tendsto (fun s : ℝ => θ + s • w) (𝓝[>] 0) (𝓝 θ) := fun w =>
      tendsto_nhdsWithin_of_tendsto_nhds (by
        simpa using (show Continuous fun s : ℝ => θ + s • w by fun_prop).tendsto 0)
    have he := hD.eventually_pentagonTransport_eq hpent k hoff
    filter_upwards [ht v he, ht (-v) he] with s h₁ h₂
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, smul_neg, ← sub_eq_add_neg] at h₁ h₂
    rw [h₁, h₂]
    exact inv_mul_cancel _
  simp only [not_forall, not_not] at hoff
  obtain ⟨⟨j, hj⟩, hθj⟩ := hoff
  rw [D.combinedLabel_eq_prod k θ v hθ [⟨j, hj⟩] (List.nodup_singleton _) fun b =>
    ⟨fun hb => List.eq_of_mem_singleton hb ▸ hθj, fun hb => List.mem_singleton.mpr
      (Subtype.ext (hD.eq_of_mem_support k hθ b.2 hj hb hθj))⟩]
  simp only [List.map_cons, List.map_nil, List.prod_singleton]
  have hvj := hv ⟨j, hj⟩ hθj
  rcases hD.eq_or_eq_or_eq j with rfl | rfl | rfl
  · rw [hD.normal_fst] at hvj ⊢
    refine eventually_inv_mul_fst hpent k (by simpa [hD.support_fst] using hθj) ?_ hvj
    refine or_iff_not_imp_right.mpr fun hB hz => hD.ker_fst_ne_snd ?_
    rw [hD.eq_of_mem_support k hθ hj ((D.mem_active k _).mpr hB) hθj
      (by simpa [hD.support_snd] using hz)]
  · rw [hD.normal_snd] at hvj ⊢
    refine eventually_inv_mul_snd hpent k (by simpa [hD.support_snd] using hθj) ?_ hvj
    refine or_iff_not_imp_right.mpr fun hA hz => hD.ker_fst_ne_snd ?_
    rw [hD.eq_of_mem_support k hθ ((D.mem_active k _).mpr hA) hj
      (by simpa [hD.support_fst] using hz) hθj]
  · rw [hD.normal_half] at hvj ⊢
    rw [hD.support_half] at hθj
    refine eventually_inv_mul_half k hθj.1 (hθj.2.lt_of_ne fun hz => hD.ker_fst_ne_half ?_) hvj
    have hA : 𝒜 ≠ 1 := fun hA =>
      (D.mem_active k _).mp hj (projection_half_eq_one_of_fst hpent k hA)
    rw [hD.eq_of_mem_support k hθ ((D.mem_active k _).mpr hA) hj
      (by simpa [hD.support_fst] using hz.symm) (by rw [hD.support_half]; exact hθj)]

/-- **Consistency of the pentagon configuration.** A directed diagram in pentagon configuration
whose labels `A, B, C` of the walls `{ℓ₁ = 0}`, `{ℓ₂ = 0}` and `{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}` satisfy
`B A = A C B` is consistent. -/
theorem consistent : D.Consistent := D.consistent_iff.mpr fun l =>
  D.levelConsistent_of_local l
    (F := fun x => (pentagonTransport (CompletedGroup.projection l (D.wall j₁).label)
      (CompletedGroup.projection l (D.wall j₂).label)
      (CompletedGroup.projection l (D.wall j₃).label) (ℓ₁ x) (ℓ₂ x))⁻¹)
    (fun _ hθ => (hD.eventually_pentagonTransport_eq hpent l hθ).mono fun _ hφ =>
      congrArg (·⁻¹) hφ)
    (fun _ hθ _ hv => (hD.eventually_inv_mul_eq_combinedLabel hpent l hθ hv).mono
      fun _ hs => by
        rw [inv_inv]
        exact hs)

end IsPentagonConfiguration

end Diagram

end Mei.DirectedDiagram
