/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency
public import Mei.Geometry.Convex.Polyhedron.Path.Subdivision

/-!
# Directed transport from local crossing formulas

Fix a cutoff `k` and a function `F` on the ambient space with values in the order-`k`
BCH group. Suppose that `F` is locally constant off the active supports and that at every
regular point `θ` and every velocity `v` transverse to the walls through `θ`,
`F (θ + s • v) * (F (θ - s • v))⁻¹` is the combined label of the wall germ at `θ` for all
small `s > 0`. Then every admissible path from `x` to `y` has order-`k` product
`F y * (F x)⁻¹`; in particular the diagram is consistent at order `k`.

Thus consistency of an explicit diagram reduces to its wall germs, in the same way as for
finite wall diagrams (`FiniteWallDiagram.consistent_of_local`). Coincident and repeated
supports are allowed: the germ condition concerns the combined label of all active walls
through `θ`.

The proof subdivides a path into segments with at most one crossing time
(`Quiver.Path.exists_subdivision_subsingleton_crossingTimes`), which does not change the
ordered signed crossing events. Such a segment computes the combined label at its crossing
point (`DirectedDiagram.levelPathProduct_toPath_eq_combinedLabel`), and `F` is constant on
the two wall-free pieces on either side of it.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- Subdividing a polygonal path by allowed interior vertices preserves its order-`k`
transport. -/
theorem levelPathProduct_eq_of_isSubdivision (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    {p q : AdmissiblePLPath x y} (hpq : p.IsSubdivision q) :
    D.levelPathProduct k q = D.levelPathProduct k p := by
  rw [D.levelPathProduct_eq_wallPathProduct k q (D.activeLabels_commute k),
    D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k)]
  exact Quiver.Path.wallPathProduct_eq_of_signedCrossingEvents_eq _ _
    (D.activeLabels_commute k) q p (hpq.signedCrossingEvents_eq _)

variable (k : ℕ) {F : V → d.truncatedGroup ℒ k}

/-- A segment with at most one crossing time has transport `F y * (F x)⁻¹` when `F` satisfies
the local crossing formulas. -/
theorem levelPathProduct_toPath_eq_mul_inv_of_local
    (hF : ∀ θ, (∀ j : D.active k, θ ∉ (D.wall j).support) → ∀ᶠ φ in 𝓝 θ, F φ = F θ)
    (hcross : ∀ θ (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
      (v : V), (∀ j : D.active k, θ ∈ (D.wall j).support →
        h.realCharacter (D.wall j).normal v ≠ 0) →
      ∀ᶠ s in 𝓝[>] (0 : ℝ), F (θ + s • v) * (F (θ - s • v))⁻¹ = D.combinedLabel k θ v hθ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)} (e : x ⟶ y)
    (he : (Prod.snd '' WallComplement.crossings x y).Subsingleton) :
    D.levelPathProduct k e.toPath = F y.val * (F x.val)⁻¹ := by
  rcases (WallComplement.crossings x y).eq_empty_or_nonempty with hempty | ⟨⟨j₀, t⟩, ht⟩
  · rw [D.levelPathProduct_eq_one_of_crossings_eq_empty k e hempty,
      WallComplement.apply_eq_of_crossings_eq_empty hF hempty, mul_inv_cancel]
  -- All crossings occur at the single parameter `t`, at the point `θ`.
  have htime {j : D.active k} {r : ℝ} (hr : (j, r) ∈ WallComplement.crossings x y) :
      r = t := he ⟨_, hr, rfl⟩ ⟨_, ht, rfl⟩
  have htI := ((WallComplement.mem_crossings _ _ _ _).mp ht).1
  have htIoo := WallComplement.mem_Ioo_of_mem_crossings ht
  set θ := AffineMap.lineMap x.val y.val t with hθ_def
  have hθ := e.down.regular t htI
  have hcr : ∀ j r, (j, r) ∈ WallComplement.crossings x y ↔
      θ ∈ (D.wall j).support ∧ r = t := by
    intro j r
    constructor
    · intro hr
      obtain rfl := htime hr
      exact ⟨((WallComplement.mem_crossings _ _ _ _).mp hr).2, rfl⟩
    · rintro ⟨hj, rfl⟩
      exact (WallComplement.mem_crossings _ _ _ _).mpr ⟨htI, hj⟩
  rw [D.levelPathProduct_toPath_eq_combinedLabel k e θ hθ t hcr]
  have hv : ∀ j : D.active k, θ ∈ (D.wall j).support →
      h.realCharacter (D.wall j).normal (y.val - x.val) ≠ 0 := by
    intro j hj hzero
    apply e.down.transverse j ⟨t, htI, hj⟩
    rw [(D.wall j).direction_support]
    exact hzero
  -- Choose a small parameter `s` with `t ± s` inside the segment.
  obtain ⟨s, hs, hspos, hst⟩ : ∃ s : ℝ,
      F (θ + s • (y.val - x.val)) * (F (θ - s • (y.val - x.val)))⁻¹ =
        D.combinedLabel k θ (y.val - x.val) hθ ∧ 0 < s ∧ s < min t (1 - t) :=
    ((hcross θ hθ _ hv).and (Ioo_mem_nhdsGT (lt_min htIoo.1 (by linarith [htIoo.2])))).exists
      |>.imp fun s hs => ⟨hs.1, hs.2.1, hs.2.2⟩
  have hs₁ : s < t := hst.trans_le (min_le_left _ _)
  have hs₂ : s < 1 - t := hst.trans_le (min_le_right _ _)
  have hline (r : ℝ) : AffineMap.lineMap x.val y.val (t + r) = θ + r • (y.val - x.val) := by
    simp only [hθ_def, AffineMap.lineMap_apply_module']
    module
  -- Points of the segment other than `θ` lie off every wall.
  have hoff {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hrt : r ≠ t) (j : D.active k) :
      AffineMap.lineMap x.val y.val r ∉ (D.wall j).support := fun hj =>
    hrt (htime ((WallComplement.mem_crossings _ _ _ _).mpr ⟨hr, hj⟩))
  let a₁ : WallComplement (fun j : D.active k => (D.wall j).support) :=
    ⟨AffineMap.lineMap x.val y.val (t - s),
      hoff ⟨by linarith, by linarith⟩ (by linarith)⟩
  let a₂ : WallComplement (fun j : D.active k => (D.wall j).support) :=
    ⟨AffineMap.lineMap x.val y.val (t + s),
      hoff ⟨by linarith, by linarith⟩ (by linarith)⟩
  have hI₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hI₁ : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hx₁ : F x.val = F a₁.val := by
    refine WallComplement.apply_eq_of_crossings_eq_empty hF
      (eq_empty_iff_forall_notMem.mpr fun ⟨j, r⟩ hr => ?_)
    obtain ⟨⟨hr₀, hr₁⟩, hjr⟩ := (WallComplement.mem_crossings_subsegment hI₀
      (⟨by linarith, by linarith⟩ : t - s ∈ Icc (0 : ℝ) 1)
      (AffineMap.lineMap_apply_zero _ _).symm rfl j r).mp hr
    have := htime hjr
    nlinarith
  have hy₂ : F a₂.val = F y.val := by
    refine WallComplement.apply_eq_of_crossings_eq_empty hF
      (eq_empty_iff_forall_notMem.mpr fun ⟨j, r⟩ hr => ?_)
    obtain ⟨⟨hr₀, hr₁⟩, hjr⟩ := (WallComplement.mem_crossings_subsegment
      (⟨by linarith, by linarith⟩ : t + s ∈ Icc (0 : ℝ) 1) hI₁ rfl
      (AffineMap.lineMap_apply_one _ _).symm j r).mp hr
    have := htime hjr
    nlinarith
  have ha₁ : a₁.val = θ - s • (y.val - x.val) := by
    rw [sub_eq_add_neg, ← neg_smul, ← hline (-s), ← sub_eq_add_neg]
  have ha₂ : a₂.val = θ + s • (y.val - x.val) := hline s
  rw [hx₁, ← hy₂, ha₁, ha₂, hs]

/-- If `F` is locally constant off the active supports and satisfies the local crossing
formulas at every regular wall germ, then every admissible path from `x` to `y` has
order-`k` transport `F y * (F x)⁻¹`. -/
theorem levelPathProduct_eq_mul_inv_of_local
    (hF : ∀ θ, (∀ j : D.active k, θ ∉ (D.wall j).support) → ∀ᶠ φ in 𝓝 θ, F φ = F θ)
    (hcross : ∀ θ (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
      (v : V), (∀ j : D.active k, θ ∈ (D.wall j).support →
        h.realCharacter (D.wall j).normal v ≠ 0) →
      ∀ᶠ s in 𝓝[>] (0 : ℝ), F (θ + s • v) * (F (θ - s • v))⁻¹ = D.combinedLabel k θ v hθ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    D.levelPathProduct k p = F y.val * (F x.val)⁻¹ := by
  obtain ⟨q, hq, hsmall⟩ := p.exists_subdivision_subsingleton_crossingTimes
  rw [← D.levelPathProduct_eq_of_isSubdivision k hq]
  clear hq p
  induction q with
  | nil => simp
  | @cons y z q f ih =>
    rw [← Quiver.Path.comp_toPath_eq_cons, Quiver.Path.isChain_vertices_comp] at hsmall
    have hf : (Prod.snd '' WallComplement.crossings y z).Subsingleton := by
      simpa only [Quiver.Path.vertices_toPath, List.isChain_pair] using hsmall.2
    rw [D.levelPathProduct_cons, ih hsmall.1,
      D.levelPathProduct_toPath_eq_mul_inv_of_local k hF hcross f hf]
    group

/-- Local crossing formulas for a function `F` at every regular wall germ imply consistency
at order `k`. -/
theorem levelConsistent_of_local
    (hF : ∀ θ, (∀ j : D.active k, θ ∉ (D.wall j).support) → ∀ᶠ φ in 𝓝 θ, F φ = F θ)
    (hcross : ∀ θ (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
      (v : V), (∀ j : D.active k, θ ∈ (D.wall j).support →
        h.realCharacter (D.wall j).normal v ≠ 0) →
      ∀ᶠ s in 𝓝[>] (0 : ℝ), F (θ + s • v) * (F (θ - s • v))⁻¹ = D.combinedLabel k θ v hθ) :
    D.LevelConsistent k :=
  (D.levelConsistent_iff_loops k).mpr fun _ p => by
    rw [D.levelPathProduct_eq_mul_inv_of_local k hF hcross p, mul_inv_cancel]

end Mei.DirectedDiagram
