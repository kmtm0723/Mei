/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing.Completed
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Basic

/-!
# Germ labels under pushforward

Let `P` be `DirectedWall.Pushforward` data, with spatial affine equivalence `A`, and let `D` be a
directed diagram. The singular support of the walls of `D.pushforward P` active at order `k` is
the image under `A` of the singular support of a subfamily of the walls of `D` active at the
cutoff modulus of `k`. Hence regular points and generic points of an affine subspace `B` are
carried to regular points and generic points of the image of `B`
(`DirectedDiagram.IsRegular.pushforward`, `DirectedDiagram.IsGenericPoint.pushforward`).

The normal map of `P` sends each normal to one whose real extension, composed with the linear
part of `A`, is a positive multiple of the original real extension. So crossing signs are kept,
and the combined crossing label of the pushforward at order `k`, the point `A θ` and the
direction `A v` is the truncated image of the combined label of `D` at any source order covering
the cutoff modulus (`DirectedDiagram.combinedLabel_pushforward`). The germ label of the
pushforward is the image of the germ label under the completed Lie map
(`DirectedDiagram.germLabel_pushforward`). Hence every diagram equivalent to the pushforward has
this germ label at every image of a generic point that is generic for it
(`DirectedDiagram.Equivalent.germLabel_eq_pushforward`).

This is the germ-level form of `DirectedDiagram.pathProduct_pushforward`: no function-wall
grouping of the source or of the target is involved. It compares the wall functions on a ray of
two completions related by a change of lattice, as in Burcroff–Lee–Mou, *Positivity of generalized
cluster scattering diagrams*, Theorem 9.5 (arXiv:2503.03719v1).
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe u

variable {Γ Γ' Λ Λ' R V V' ι κ : Type*} {L L' : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Λ] [AddCommGroup Λ']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'}
  [DecidableEq Γ] [DecidableEq Γ']
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {i : Λ →+ V} {i' : Λ' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  (D : DirectedDiagram (d := d) h H ι)
  (P : DirectedWall.Pushforward d d' h h' H H')

/-- The singular support of the pushed walls active at order `k` is the spatial image of the
singular support of the same walls of `D`. -/
theorem singularSupport_pushforward (k : ℕ) :
    singularSupport (fun j : (D.pushforward P).active k => ((D.pushforward P).wall j).support) =
      P.spatialMap ''
        singularSupport (fun j : (D.pushforward P).active k => (D.wall j).support) := by
  simp only [pushforward_wall_support]
  exact singularSupport_image _ _

/-- A point outside the singular support of the walls of `D` active at a source order covering
the cutoff modulus of `k` has image outside the singular support of the pushed walls active at
order `k`. -/
theorem notMem_singularSupport_pushforward (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    {θ : V} (hθ : θ ∉ singularSupport (fun j : D.active a => (D.wall j).support)) :
    P.spatialMap θ ∉ singularSupport
      (fun j : (D.pushforward P).active k => ((D.pushforward P).wall j).support) := by
  rw [singularSupport_pushforward, P.spatialMap.injective.mem_set_image]
  exact fun hs => hθ (singularSupport_comp_subset _
    (Set.inclusion (D.active_pushforward_subset P k ha)) hs)

variable {D} in
/-- Regular points are carried to regular points of the pushforward. -/
theorem IsRegular.pushforward {θ : V} (hθ : D.IsRegular θ) :
    (D.pushforward P).IsRegular (P.spatialMap θ) :=
  ((D.pushforward P).isRegular_iff _).mpr fun k =>
    D.notMem_singularSupport_pushforward P k le_rfl (hθ.notMem_singularSupport _)

/-- The affine span of a pushed wall is the image of the affine span of the wall. -/
theorem affineSpan_pushforward_wall_support (j : ι) :
    affineSpan ℝ ((D.pushforward P).wall j).support =
      (affineSpan ℝ (D.wall j).support).map P.spatialMap.toAffineEquiv.toAffineMap := by
  rw [AffineSubspace.map_span, pushforward_wall_support, AffineEquiv.coe_toAffineMap,
    ContinuousAffineEquiv.coe_coe]

variable {D} in
/-- Generic points of an affine subspace `B` are carried to generic points of its image. -/
theorem IsGenericPoint.pushforward {B : AffineSubspace ℝ V} {θ : V}
    (hθ : D.IsGenericPoint B θ) :
    (D.pushforward P).IsGenericPoint (B.map P.spatialMap.toAffineEquiv.toAffineMap)
      (P.spatialMap θ) where
  mem := AffineSubspace.mem_map_of_mem _ hθ.mem
  isRegular := hθ.isRegular.pushforward P
  affineSpan_eq {k} j hj := by
    rw [pushforward_wall_support, P.spatialMap.injective.mem_set_image] at hj
    rw [affineSpan_pushforward_wall_support,
      hθ.affineSpan_eq (Set.inclusion (D.active_pushforward_subset P k le_rfl) j) hj]

/-- Pushing forward keeps the crossing sign of every wall: the pushed normal pairs with the image
of a direction as a positive multiple of the original pairing. -/
theorem pos_realCharacter_pushforward_normal_iff (j : ι) (v : V) :
    0 < h'.realCharacter ((D.pushforward P).wall j).normal (P.spatialMap.toAffineEquiv.linear v) ↔
      0 < h.realCharacter (D.wall j).normal v := by
  obtain ⟨r, hr, he⟩ := P.exists_realCharacter_normalMap_apply (D.wall j).normal
  rw [pushforward_wall, DirectedWall.pushforward_normal, he,
    mul_pos_iff_of_pos_left (by exact_mod_cast hr)]

/-- **Combined labels under pushforward.** At target order `k` and any source order `a` covering
the cutoff modulus of `k`, the combined crossing label of the pushforward at the image `A θ` of
a regular point and the image `A v` of a direction is the truncated image of the combined label
of `D` at `θ` and `v`. -/
theorem combinedLabel_pushforward (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) (θ v : V)
    (hθ : θ ∉ singularSupport (fun j : D.active a => (D.wall j).support)) :
    (D.pushforward P).combinedLabel k (P.spatialMap θ) (P.spatialMap.toAffineEquiv.linear v)
        (D.notMem_singularSupport_pushforward P k ha hθ) =
      (P.lieHom.truncatedMap k ha).bchGroupMap (D.combinedLabel a θ v hθ) := by
  classical
  let S := (Set.toFinite {j : D.active a | θ ∈ (D.wall j).support}).toFinset
  let T := (Set.toFinite {j : (D.pushforward P).active k |
    P.spatialMap θ ∈ ((D.pushforward P).wall j).support}).toFinset
  let emb : (D.pushforward P).active k ↪ D.active a :=
    ⟨Set.inclusion (D.active_pushforward_subset P k ha), Set.inclusion_injective _⟩
  have hmem (j : ι) : P.spatialMap θ ∈ ((D.pushforward P).wall j).support ↔
      θ ∈ (D.wall j).support := by
    rw [pushforward_wall_support, P.spatialMap.injective.mem_set_image]
  have hs : T.map emb ⊆ S := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hb
    simpa [S, T, emb, hmem] using hc
  let f (j : D.active a) :=
    CompletedGroup.projection a (D.wall j).label ^
      (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ)
  let f' (j : (D.pushforward P).active k) :=
    CompletedGroup.projection k ((D.pushforward P).wall j).label ^
      (if 0 < h'.realCharacter ((D.pushforward P).wall j).normal
        (P.spatialMap.toAffineEquiv.linear v) then -1 else 1 : ℤ)
  -- The original crossing sign, which the pushforward keeps.
  let g (j : D.active a) :=
    CompletedGroup.projection k ((D.pushforward P).wall j).label ^
      (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ)
  have hcS : (S : Set (D.active a)).Pairwise fun x y => Commute (f x) (f y) := by
    intro x hx y hy _
    have hx : θ ∈ (D.wall x).support := by simpa [S] using hx
    have hy : θ ∈ (D.wall y).support := by simpa [S] using hy
    exact (D.activeLabels_commute a x y (affineSpan_eq_of_notMem_singularSupport
      (W := fun j : D.active a => (D.wall j).support) hθ hx hy)).zpow_zpow _ _
  have hcT : (T : Set ((D.pushforward P).active k)).Pairwise
      fun x y => Commute (f' x) (f' y) := by
    intro x hx y hy _
    have hx : P.spatialMap θ ∈ ((D.pushforward P).wall x).support := by simpa [T] using hx
    have hy : P.spatialMap θ ∈ ((D.pushforward P).wall y).support := by simpa [T] using hy
    exact ((D.pushforward P).activeLabels_commute k x y (affineSpan_eq_of_notMem_singularSupport
      (W := fun j : (D.pushforward P).active k => ((D.pushforward P).wall j).support)
      (D.notMem_singularSupport_pushforward P k ha hθ) hx hy)).zpow_zpow _ _
  have hz : ∀ b ∈ S, b ∉ T.map emb → g b = 1 := by
    intro b hb hnot
    have hinactive : b.val ∉ (D.pushforward P).active k := fun hbk =>
      hnot (Finset.mem_map.mpr ⟨⟨b.val, hbk⟩, by simpa [S, T, hmem] using hb, rfl⟩)
    have hone : CompletedGroup.projection k ((D.pushforward P).wall b).label = 1 := by
      simpa only [mem_active, not_not] using hinactive
    simp only [g, hone, one_zpow]
  -- The truncated BCH map of the pushforward, between the objects of the two group towers.
  let F : (d.groupTower ℒ).obj (Opposite.op a) →* (d'.groupTower ℳ).obj (Opposite.op k) :=
    (P.lieHom.truncatedMap k ha).bchGroupMap
  have hproj (b : D.active a) : F (CompletedGroup.projection a (D.wall b).label) =
      CompletedGroup.projection k ((D.pushforward P).wall b).label :=
    (D.projection_pushforward_wall_label P k ha b).symm
  have hF (b : D.active a) : F (f b) = g b := by
    simp only [f, g, map_zpow, hproj]
  rw [D.combinedLabel_eq_noncommProd a θ v hθ S (fun j => by simp [S]) hcS,
    (D.pushforward P).combinedLabel_eq_noncommProd k _ _ _ T (fun j => by simp [T]) hcT]
  -- Read the truncated BCH map as the map `F` between the objects of the group towers.
  change T.noncommProd f' hcT = F (S.noncommProd f hcS)
  rw [Finset.map_noncommProd]
  simp only [hF]
  generalize_proofs hcg
  refine Eq.trans ?_ ((Finset.noncommProd_map T emb g
    (hcg.mono (Finset.coe_subset.mpr hs))).symm.trans (Finset.noncommProd_subset hs g hcg hz))
  exact Finset.noncommProd_congr rfl (fun j _ => by
    simp only [f', g, emb, Function.Embedding.coeFn_mk,
      pos_realCharacter_pushforward_normal_iff]) _

/-- **Germ labels under pushforward.** The germ label of the pushforward at the image `A θ` of a
regular point and the image `A v` of a direction is the image of the germ label of `D` under the
completed Lie map. -/
theorem germLabel_pushforward {θ : V} (v : V) (hθ : D.IsRegular θ) :
    (D.pushforward P).germLabel (P.spatialMap θ) (P.spatialMap.toAffineEquiv.linear v)
        (hθ.pushforward P) =
      P.lieHom.completedMap (D.germLabel θ v hθ) :=
  CompletedGroup.ext fun k => by
    rw [projection_germLabel, P.lieHom.projection_completedMap, projection_germLabel,
      ← combinedLabel_pushforward]

variable {D} {E : DirectedDiagram (d := d') h' H' κ}

/-- **Germ labels of diagrams equivalent to a pushforward.** Let `θ` be a generic point of an
affine subspace `B` for `D`, and `E` a diagram equivalent to `D.pushforward P` for which the image
`A θ` is a generic point of the image of `B`. Then for every direction `v ∉ B.direction`, the
germ label of `E` at `A θ` in the direction `A v` is the image of the germ label of `D` at `θ` in
the direction `v` under the completed Lie map. -/
theorem Equivalent.germLabel_eq_pushforward (hDE : (D.pushforward P).Equivalent E)
    {B : AffineSubspace ℝ V} {θ v : V} (hD : D.IsGenericPoint B θ)
    (hE : E.IsGenericPoint (B.map P.spatialMap.toAffineEquiv.toAffineMap) (P.spatialMap θ))
    (hv : v ∉ B.direction) :
    E.germLabel (P.spatialMap θ) (P.spatialMap.toAffineEquiv.linear v) hE.isRegular =
      P.lieHom.completedMap (D.germLabel θ v hD.isRegular) := by
  have hv' : P.spatialMap.toAffineEquiv.linear v ∉
      (B.map P.spatialMap.toAffineEquiv.toAffineMap).direction := by
    rwa [AffineSubspace.map_direction, AffineEquiv.linear_toAffineMap, Submodule.mem_map_equiv,
      LinearEquiv.symm_apply_apply]
  rw [← (hDE.germLabel_eq (hD.pushforward P) hE hv'), germLabel_pushforward]

end Mei.DirectedDiagram
