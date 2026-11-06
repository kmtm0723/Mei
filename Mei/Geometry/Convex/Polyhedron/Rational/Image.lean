/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Analysis.Convex.Intrinsic
public import Mei.Geometry.Convex.Polyhedron.Rational.Cone
public import Mei.Geometry.Convex.Polyhedron.Rational.Direction
public import Mei.Geometry.Convex.Polyhedron.Rational.LocallyClosed
public import Mei.Geometry.Toric.Algebraic.RationalLinearMap

/-!
# Images of locally closed polyhedra under affine embeddings

Let `g : V → W` be an affine map with rational linear part between real vector spaces with
integral lattices, and let `S ⊆ V` be a locally closed rational-normal polyhedron on which `g` is
injective. Then `g '' S` is a locally closed rational-normal polyhedron in `W`
(`IsLocallyClosedPolyhedron.image_of_injOn`). The map need not be injective on `V`, and `S` may
be lower-dimensional; offsets stay real.

`Mei.Geometry.Convex.Polyhedron.Rational.Map` treats images under integral affine equivalences.
-/

public section

open Filter Set Topology

namespace Mei.IsLocallyClosedPolyhedron

variable {N V N' W : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup N'] [NormedAddCommGroup W] [NormedSpace ℝ W] {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}

/-- An affine map injective on a locally closed polyhedron `S` has linear part injective on the
direction of the affine span of `S`. -/
theorem linear_eq_zero_of_injOn {S : Set V} (hS : IsLocallyClosedPolyhedron h S)
    (g : V →ᵃ[ℝ] W) (hinj : InjOn g S) {v : V} (hv : v ∈ (affineSpan ℝ S).direction)
    (hgv : g.linear v = 0) : v = 0 := by
  let := h.finiteDimensional
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simpa using hv
  obtain ⟨x, hx⟩ := hne.intrinsicInterior hS.convex
  -- Points `x + t • v` of the affine span close to the relative interior point `x` lie in `S`.
  have hev : ∀ᶠ t : ℝ in 𝓝 0, x + t • v ∈ S := by
    refine (tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun t => ?_⟩).eventually_mem
      (mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior hx)
    · have hc : Continuous fun t : ℝ => x + t • v := by fun_prop
      simpa using hc.tendsto 0
    · rw [add_comm, ← vadd_eq_add]
      exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t hv)
        (mem_affineSpan ℝ (intrinsicInterior_subset hx))
  obtain ⟨t, hts, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : {0}ᶜ ∈ 𝓝[≠] (0 : ℝ))).exists
  have hgx : g (x + t • v) = g x := by
    rw [add_comm, ← vadd_eq_add, AffineMap.map_vadd, map_smul, hgv, smul_zero, zero_vadd]
  have hxt : t = 0 ∨ v = 0 := by simpa using hinj hts (intrinsicInterior_subset hx) hgx
  exact hxt.resolve_left ht

/-- An affine map with rational linear part that is injective on a nonempty locally closed
polyhedron `S` has a rational linear left inverse on the direction of the affine span of `S`. -/
theorem exists_leftInverseOn_direction {S : Set V} (hS : IsLocallyClosedPolyhedron h S)
    (hne : S.Nonempty) (g : V →ᵃ[ℝ] W) (hg : Toric.IsRationalLinearMap h h' g.linear)
    (hinj : InjOn g S) :
    ∃ B : W →ₗ[ℝ] V, Toric.IsRationalLinearMap h' h B ∧
      ∀ v ∈ (affineSpan ℝ S).direction, B (g.linear v) = v := by
  let := h.finiteDimensional
  -- The direction of the affine span is cut out by integral characters.
  have hspan : affineSpan ℝ (closure S) = affineSpan ℝ S := by
    rw [← intrinsicClosure_eq_closure ℝ, affineSpan_intrinsicClosure]
  have hdim := Submodule.finrank_le (affineSpan ℝ (closure S)).direction
  obtain ⟨m, -, hdir⟩ := hS.isRationalNormalPolyhedron_closure.exists_direction_eq_iInf_ker
    (hne.mono subset_closure) (Nat.add_sub_of_le hdim)
  have hU (v : V) : (∀ j, h.realCharacter (m j).toAddMonoidHom v = 0) ↔
      v ∈ (affineSpan ℝ S).direction := by
    simp [← hspan, hdir, Submodule.mem_iInf]
  obtain ⟨B, hB, hBg⟩ := hg.exists_leftInverseOn m fun v hv hgv =>
    hS.linear_eq_zero_of_injOn g hinj ((hU v).mp hv) hgv
  exact ⟨B, hB, fun v hv => hBg v ((hU v).mpr hv)⟩

/-- The image of a locally closed polyhedron under an affine map with rational linear part that
is injective on it is a locally closed polyhedron. -/
theorem image_of_injOn {S : Set V} (hS : IsLocallyClosedPolyhedron h S) (g : V →ᵃ[ℝ] W)
    (hg : Toric.IsRationalLinearMap h h' g.linear) (hinj : InjOn g S) :
    IsLocallyClosedPolyhedron h' (g '' S) := by
  let := h'.finiteDimensional
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp [IsLocallyClosedPolyhedron.empty h']
  obtain ⟨B, hB, hBg⟩ := hS.exists_leftInverseOn_direction ⟨x₀, hx₀⟩ g hg hinj
  -- `g '' S` is cut out by `φ w ∈ S` and `g (φ w) = w` for `φ w = x₀ + B (w - g x₀)`.
  let φa : W →ᵃ[ℝ] V := B.toAffineMap + AffineMap.const ℝ W (x₀ - B (g x₀))
  let φ : W →ᴬ[ℝ] V := ⟨φa, φa.continuous_of_finiteDimensional⟩
  let ψa : W →ᵃ[ℝ] W := g.comp φa - AffineMap.id ℝ W
  let ψ : W →ᴬ[ℝ] W := ⟨ψa, ψa.continuous_of_finiteDimensional⟩
  have hφ : Toric.IsRationalLinearMap h' h φ.toAffineMap.linear := by
    simpa [φ, φa] using hB
  have hψ : Toric.IsRationalLinearMap h' h' ψ.toAffineMap.linear := by
    simpa [ψ, ψa, φa] using (hg.comp hB).sub (Toric.IsRationalLinearMap.id h')
  have himage : g '' S = φ ⁻¹' S ∩ ψ ⁻¹' {0} := by
    ext w
    simp only [mem_image, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hφx : φa (g x) = x := by
        have hB := hBg (x - x₀)
          (AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hx) (mem_affineSpan ℝ hx₀))
        have hg : g.linear (x - x₀) = g x - g x₀ := by simpa using g.linear_apply_vsub x x₀
        rw [hg, map_sub] at hB
        simp only [φa, AffineMap.coe_add, Pi.add_apply, LinearMap.coe_toAffineMap,
          AffineMap.const_apply]
        linear_combination (norm := module) hB
      simp [φ, hφx, hx, ψ, ψa]
    · rintro ⟨hw, hψw⟩
      exact ⟨φ w, hw, sub_eq_zero.mp (by simpa [φ, ψ, ψa] using hψw)⟩
  rw [himage]
  exact (hS.preimage φ hφ).inter
    ((isRationalNormalPolyhedron_singleton (h := h') 0).isLocallyClosedPolyhedron.preimage ψ hψ)

end Mei.IsLocallyClosedPolyhedron
