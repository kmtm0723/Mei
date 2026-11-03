/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Grouping
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Uniqueness
public import Mei.Algebra.PositiveDegrees.Examples

/-!
# A horizontal rank-two polynomial input

Take `L = M = ℤ²`, `π = id`, the even quadrant `P = 2ℕe₁ + ℕe₂` with `δ(a, b) = a + b`
(`Mei.PositiveDegrees.Examples.evenOrthant`), and the horizontal incoming line `{y = 0}` with
wall function `1 + c z^{2e₁}` (`RankTwoPolynomialInput.Examples.horizontalInput`). The primitive
generator `e₁` of the horizontal ray is not an allowed degree, but its ray is supported by
`2e₁`, and it is the only supported ray tangent to the line
(`RankTwoPolynomialInput.Examples.eq_evenHorizontalRay`). Hence the incoming diagram has a single
wall, on the supported primitive ray `e₁`, and the logarithm of `1 + c z^{2e₁}` is supported on
`2ℕ_{>0}e₁` (`RankTwoPolynomialInput.Examples.exists_eq_of_logComponent_initialLabel_ne_zero`).
Being a single full hyperplane, the diagram is consistent, so with no further walls it is its
own outgoing completion (`RankTwoPolynomialInput.Examples.isOutgoingCompletion`), and for the
independent variable `c` it is a positive wall representative
(`RankTwoPolynomialInput.Examples.isPositiveWallRepresentative`).

This is the first check of §7.4 of the scattering-diagram roadmap, for Burcroff–Lee–Mou,
*Positivity of generalized cluster scattering diagrams*, Theorem 9.9 (arXiv:2503.03719v1). The
consistency uses `DirectedDiagram.consistent_of_support_eq`.
-/

public section

noncomputable section

namespace Mei.RankTwoPolynomialInput.Examples

open PositiveDegrees.Examples

/-- The horizontal line `{y = 0}` of `ℤ²` with the wall function `1 + c z^{2e₁}`, on the even
quadrant with the coordinate-sum degree. -/
def horizontalInput : RankTwoPolynomialInput evenOrthant (ℤ × ℤ) Unit where
  projection := AddMonoidHom.id _
  projection_surjective := Function.surjective_id
  finrank_eq_two := by simp
  tangent _ := (1, 0)
  isPrimitive_tangent _ := TauCeti.isPrimitive_def.mpr ⟨LinearMap.fst ℤ ℤ ℤ, rfl⟩
  normal _ := LinearMap.snd ℤ ℤ ℤ
  isPrimitive_normal _ := TauCeti.isPrimitive_def.mpr ⟨Module.Dual.eval ℤ _ (0, 1), rfl⟩
  normal_tangent _ := rfl
  offset _ := 0
  exponents _ := {(2, 0)}
  mem_monoid_of_mem_exponents {_ n} hn := by
    rw [Finset.mem_singleton] at hn
    subst hn
    simp
  ne_zero_of_mem_exponents {_ n} hn := by
    rw [Finset.mem_singleton] at hn
    subst hn
    simp
  exists_projection_eq_of_mem_exponents {_ n} hn := by
    rw [Finset.mem_singleton] at hn
    subst hn
    exact ⟨2, two_pos, by simp⟩
  finite_nontrivial _ := Set.toFinite _

/-- The cylinder normal of the horizontal line is the second coordinate. -/
@[simp]
theorem wallNormal_horizontalInput (j : Unit) (q : ℤ × ℤ) :
    horizontalInput.wallNormal j q = q.2 :=
  horizontalInput.wallNormal_apply j q

/-- The only supported ray tangent to the horizontal line is the horizontal ray, with
primitive generator `e₁`. -/
theorem eq_evenHorizontalRay (w : SupportedRay evenOrthant)
    (hw : horizontalInput.wallNormal () w.generator = 0) : w = evenHorizontalRay := by
  obtain ⟨⟨x, y⟩, hprim, a, ha, hmem⟩ := w
  simp only [wallNormal_horizontalInput] at hw
  subst hw
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hprim
  have hx : x * f (1, 0) = 1 := by
    have he : ((x, 0) : ℤ × ℤ) = x • ((1, 0) : ℤ × ℤ) := by simp
    rwa [he, map_zsmul, smul_eq_mul] at hf
  rw [evenOrthant_monoid] at hmem
  have hax : 0 ≤ a * x := by simpa using (mem_evenOrthantMonoid.mp hmem).1
  have hx0 : 0 ≤ x := nonneg_of_mul_nonneg_right (by linarith [mul_comm a x]) ha
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hx with rfl | rfl
  · exact SupportedRay.ext evenHorizontalRay_generator.symm
  · omega

/-- The incoming walls of the horizontal input are indexed by the horizontal ray alone. -/
instance : Unique horizontalInput.IncomingIndex where
  default := ⟨(), evenHorizontalRay, by simp⟩
  uniq := by
    rintro ⟨⟨⟩, w, hw⟩
    obtain rfl := eq_evenHorizontalRay w hw
    rfl

variable {R : Type*} [CommRing R] [Algebra ℚ R] (c : horizontalInput.Variable → R)

local notation "ρ" => AddMonoidHom.id (ℤ × ℤ)
local notation "ℒ" => tropicalVertexGrading (R := R) evenOrthant ρ

/-- The logarithm of `1 + c z^{2e₁}` is supported on `2ℕ_{>0}e₁`. -/
theorem exists_eq_of_logComponent_initialLabel_ne_zero {q : ℤ × ℤ}
    (hq : evenOrthant.logComponent ℒ (horizontalInput.initialLabel c ()) q ≠ 0) :
    ∃ a : ℤ, 0 < a ∧ q = (2 * a, 0) := by
  obtain ⟨hqP, hq0⟩ := evenOrthant.mem_monoid_and_ne_zero_of_logComponent_ne_zero ℒ hq
  obtain ⟨t, rfl⟩ : ∃ t : horizontalInput.initialMonoid (R := R) (), ((t : _) : ℤ × ℤ) = q := by
    by_contra! h
    exact hq (horizontalInput.logComponent_initialLabel_eq_zero c () h)
  rcases horizontalInput.initialMonoid_property () t.property with ht | ⟨⟨k, hk, hkt⟩, -⟩
  · exact (hq0 (by rw [ht]; rfl)).elim
  · rw [evenOrthant_monoid] at hqP
    obtain ⟨-, -, b, hb⟩ := mem_evenOrthantMonoid.mp hqP
    change ((t : _) : ℤ × ℤ) = k • ((1, 0) : ℤ × ℤ) at hkt
    simp only [hkt, Prod.smul_mk, nsmul_eq_mul, mul_one, smul_zero] at hb ⊢
    exact ⟨b, by omega, by simp only [Prod.mk.injEq, and_true]; omega⟩

variable {latticeMap : ℤ × ℤ →+ ℝ × ℝ} (h : TauCeti.Toric.IsIntegralLattice latticeMap)

local notation "H" => tropicalVertexWallSpaces (R := R) evenOrthant ρ

/-- The single wall of the horizontal input lies on the supported primitive ray `e₁`. -/
theorem incomingDiagram_ray_eq (j : horizontalInput.IncomingIndex) :
    ((horizontalInput.incomingDiagram h c).wall j).ray = evenHorizontalRay := by
  rw [incomingDiagram_ray]
  exact eq_evenHorizontalRay _ j.2.property

/-- The incoming diagram of the horizontal input, with no additional walls. -/
def completionDiagram :
    DirectedDiagram (d := evenOrthant) h (H) (horizontalInput.IncomingIndex ⊕ PEmpty) where
  wall := Sum.elim (horizontalInput.incomingDiagram h c).wall PEmpty.elim
  finite_active k := by
    apply (((horizontalInput.incomingDiagram h c).finite_active k).image Sum.inl).subset
    rintro (j | j) hj
    · exact ⟨j, hj, rfl⟩
    · exact j.elim

/-- The single-wall incoming diagram of the horizontal input is its own outgoing completion:
it is consistent, being a single full hyperplane, and has no further walls. -/
theorem isOutgoingCompletion :
    DirectedDiagram.IsOutgoingCompletion (horizontalInput.incomingDiagram h c).wall
      (completionDiagram c h) where
  wall_inl _ := rfl
  outgoing_inr j := j.elim
  consistent := by
    let : Unique (horizontalInput.IncomingIndex ⊕ PEmpty) := (Equiv.sumEmpty _ _).unique
    refine DirectedDiagram.consistent_of_support_eq (W := (horizontalInput.incomingDiagram h c).wall
      default) ?_ 0 ?_
    · rintro (j | j)
      · exact congrArg _ (Subsingleton.elim j default)
      · exact j.elim
    · simp only [incomingDiagram_support, incomingDiagram_normal]
      rfl

open scoped Mei.TropicalVertexCoefficientAction

local instance : Fact (evenOrthant.monoid ≤ (⊤ : AddSubmonoid (ℤ × ℤ))) := ⟨le_top⟩

/-- For the independent variable `c`, the incoming diagram of the horizontal input is a
positive wall representative: its wall function `1 + c z^{2e₁}` has coefficients in `ℕ[c]`. -/
theorem isPositiveWallRepresentative :
    (horizontalInput.incomingDiagram h MvPolynomial.X).IsPositiveWallRepresentative
      ((TropicalVertexCoefficientAction.filtration
        (R := MvPolynomial horizontalInput.Variable ℚ) evenOrthant ⊤).completedBCHAction
          evenOrthant (tropicalVertexGrading (R := MvPolynomial horizontalInput.Variable ℚ)
            evenOrthant ρ))
      (AddMonoidAlgebra.mapRingHom (⊤ : AddSubmonoid (ℤ × ℤ))
        (MvPolynomial.map (σ := horizontalInput.Variable) (Nat.castRingHom ℚ))).rangeS
      horizontalInput.projection :=
  horizontalInput.isPositiveWallRepresentative_incomingDiagram_variables h

end Mei.RankTwoPolynomialInput.Examples
