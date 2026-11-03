/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Pushforward
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.AffineTransport.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Map.Basic
import Mei.Geometry.Convex.Polyhedron.Path.Restriction

/-!
# Pushing directed diagrams forward along degree-changing maps

A `DirectedWall.Pushforward` pushes every indexed wall of a directed diagram forward,
preserving finite activity through the cutoff modulus of the positive degree map. At
target order `k`, paths are pushed forward from any source cutoff `a` covering the
modulus: first the walls whose labels die at order `k` are forgotten, then the path is
moved by the spatial affine equivalence. The finite path product is carried by the
truncated BCH homomorphism, and common all-order paths give naturality of completed
path products.

Image normals are only positive rational multiples of the inverse-dual normals, as for
tropical pairings of finite-index lattices. Positive rescaling of normals preserves all
signed crossing events, so it does not change path products
(`Quiver.Path.wallPathProduct_smul_normal`).

The fixed-degree coefficient maps `DirectedDiagram.map` and the coordinate changes
`DirectedDiagram.image` are special cases. The proofs follow
`DirectedDiagram.levelPathProduct_image`, combining
`Quiver.Path.wallPathProduct_restrict`, `Quiver.Path.wallPathProduct_wallComplementMap`
and `Quiver.Path.signedCrossingEvents_smul`. The setting is Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), Example 2.1(i).
-/

public section

noncomputable section

open Set Mei.Convex

namespace Quiver.Path

variable {V ι G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι] [Group G]
  {W : ι → Set V} {x y : WallComplement W}

/-- Positive rescaling of the coorientations does not change a wall product. -/
theorem wallPathProduct_smul_normal (p : AdmissiblePLPath x y) (ν : ι → V →ₗ[ℝ] ℝ)
    (r : ι → ℝ) (hr : ∀ j, 0 < r j) (label : ι → G)
    (comm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j)) :
    p.wallPathProduct (fun j => r j • ν j) label comm = p.wallPathProduct ν label comm := by
  rw [wallPathProduct_eq_prod_signedCrossingEvents,
    wallPathProduct_eq_prod_signedCrossingEvents, signedCrossingEvents_smul ν r hr]

end Quiver.Path

namespace Mei.DirectedDiagram

universe u

variable {Γ Γ' Λ Λ' R V V' ι : Type*} {L L' : Type u}
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

/-- Push every indexed wall forward. Finite activity is preserved through the cutoff
modulus of the degree map. -/
def pushforward : DirectedDiagram (d := d') h' H' ι where
  wall j := (D.wall j).pushforward P
  finite_active := by
    simpa only [DirectedWall.pushforward_label] using
      P.lieHom.hasFiniteSupport_completedMap D.finite_active

/-- Diagram pushforward pushes every indexed wall forward. -/
@[simp]
theorem pushforward_wall (j : ι) : (D.pushforward P).wall j = (D.wall j).pushforward P :=
  (rfl)

/-- A target-active label was active at any source order covering the modulus. -/
theorem active_pushforward_subset (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) :
    (D.pushforward P).active k ⊆ D.active a := by
  simpa only [Set.subset_def, mem_active, Function.mem_mulSupport, pushforward_wall,
    DirectedWall.pushforward_label] using
    P.lieHom.mulSupport_projection_completedMap_subset (fun j => (D.wall j).label) k ha

/-- Restrict a source path to the target-active indices and then apply the spatial
affine equivalence. The source cutoff can be any bound for the prescribed modulus. -/
def levelPathPushforward (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) :
    WallComplement (fun j : D.active a => (D.wall j).support) ⥤q
      WallComplement (fun j : (D.pushforward P).active k =>
        ((D.pushforward P).wall j).support) :=
  WallComplement.restrictPrefunctor (fun j : D.active a => (D.wall j).support)
      (Set.inclusion (D.active_pushforward_subset P k ha)) ⋙q
    P.spatialMap.wallComplementMap (Equiv.refl _) (fun _ => by
      rw [Equiv.refl_apply, pushforward_wall, DirectedWall.pushforward_support]
      rfl)

/-- The finite path map sends each vertex to its spatial image. -/
@[simp]
theorem levelPathPushforward_obj_val (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    (x : WallComplement (fun j : D.active a => (D.wall j).support)) :
    ((D.levelPathPushforward P k ha).obj x).val = P.spatialMap x.val := by
  simp [levelPathPushforward]

/-- Finite path pushforward preserves reversal of segments and polygonal paths. -/
instance (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) :
    (D.levelPathPushforward P k ha).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Finite directed transport is natural under pushforward, using the truncated BCH map
at any source cutoff covering the target modulus. Walls whose labels die are forgotten,
and image normals may be positive multiples of the inverse-dual normals. -/
@[simp]
theorem levelPathProduct_pushforward (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    {x y : WallComplement (fun j : D.active a => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    (D.pushforward P).levelPathProduct k ((D.levelPathPushforward P k ha).mapPath p) =
      (P.lieHom.truncatedMap k ha).bchGroupMap (D.levelPathProduct a p) := by
  let f := Set.inclusion (D.active_pushforward_subset P k ha)
  let q := (WallComplement.restrictPrefunctor
    (fun j : D.active a => (D.wall j).support) f).mapPath p
  let F := (P.lieHom.truncatedMap k ha).bchGroupMap
  let r : (D.pushforward P).active k → ℝ :=
    fun j => ((P.realCharacter_normalMap (D.wall j).normal).choose : ℝ)
  have hlabel (j : ι) : CompletedGroup.projection k ((D.pushforward P).wall j).label =
      F (CompletedGroup.projection a (D.wall j).label) := by
    simp only [pushforward_wall, DirectedWall.pushforward_label]
    exact P.lieHom.projection_completedMap_of_le k ha _
  -- First delete exactly the labels killed at the target cutoff.
  have hzero (j : D.active a) (hj : j ∉ range f) :
      F (CompletedGroup.projection a (D.wall j).label) = 1 := by
    rw [← hlabel]
    by_contra hne
    exact hj ⟨⟨j.val, ((D.pushforward P).mem_active k j.val).mpr hne⟩, Subtype.ext rfl⟩
  have hr := p.wallPathProduct_restrict
    (fun j : D.active a => h.realCharacter (D.wall j).normal)
    (fun j => F (CompletedGroup.projection a (D.wall j).label))
    (fun j l h => (D.activeLabels_commute a j l h).map F) f (Set.inclusion_injective _) hzero
  -- Affine covariance applies to the surviving family with rescaled source normals.
  have hi := q.wallPathProduct_wallComplementMap P.spatialMap (Equiv.refl _)
    (W' := fun j : (D.pushforward P).active k => ((D.pushforward P).wall j).support)
    (fun _ => by
      rw [Equiv.refl_apply, pushforward_wall, DirectedWall.pushforward_support]
      rfl)
    (fun j => r j • h.realCharacter (D.wall (f j)).normal)
    (fun j => h'.realCharacter ((D.pushforward P).wall j).normal)
    (fun j => by
      rw [Equiv.refl_apply, pushforward_wall, DirectedWall.pushforward_normal]
      exact (P.realCharacter_normalMap (D.wall j).normal).choose_spec.2)
    (fun j => CompletedGroup.projection a (D.wall (f j)).label)
    (fun j => CompletedGroup.projection k ((D.pushforward P).wall j).label)
    (fun j l h => D.activeLabels_commute a (f j) (f l) h)
    ((D.pushforward P).activeLabels_commute k) F (fun j => hlabel j)
  have hs := q.wallPathProduct_smul_normal
    (fun j => h.realCharacter (D.wall (f j)).normal) r
    (fun j => Rat.cast_pos.mpr (P.realCharacter_normalMap (D.wall j).normal).choose_spec.1)
    (fun j => CompletedGroup.projection a (D.wall (f j)).label)
    (fun j l h => D.activeLabels_commute a (f j) (f l) h)
  -- Move coefficient change through both products and recombine the comparisons.
  have hm := q.map_wallPathProduct
    (fun j => h.realCharacter (D.wall (f j)).normal)
    (fun j => CompletedGroup.projection a (D.wall (f j)).label)
    (fun j l h => D.activeLabels_commute a (f j) (f l) h) F
  have he := hi.trans ((congrArg F hs).trans (hm.trans hr))
  have hm' := p.map_wallPathProduct
    (fun j : D.active a => h.realCharacter (D.wall j).normal)
    (fun j => CompletedGroup.projection a (D.wall j).label)
    (D.activeLabels_commute a) F
  calc
    _ = _ := (D.pushforward P).levelPathProduct_eq_wallPathProduct k _
      ((D.pushforward P).activeLabels_commute k)
    _ = _ := by
      -- The prefunctor composition and its two successive path maps coincide.
      convert he.trans hm'.symm using 1
      simp only [levelPathPushforward, Prefunctor.mapPath_comp_apply, q, f]
      rfl
    _ = _ := congrArg F (D.levelPathProduct_eq_wallPathProduct a p
      (D.activeLabels_commute a)).symm

/-- Push a common all-order path forward. Each target admissibility condition uses the
source condition at its prescribed cutoff modulus. -/
def pathPushforward : D.Point ⥤q (D.pushforward P).Point where
  obj x := ⟨P.spatialMap x.val, fun k j => by
    have hx := ((D.levelPathPushforward P k le_rfl).obj
      (CommonWallComplement.projection (P.degreeMap.modulus k) x)).notMem j
    simpa only [levelPathPushforward_obj_val, CommonWallComplement.projection_val] using hx⟩
  map {x y} a := ⟨fun k => by
    let b := (D.levelPathPushforward P k le_rfl).map
      ((CommonWallComplement.projectionPrefunctor (P.degreeMap.modulus k)).map a)
    have hb := b.down
    -- The projected endpoints and the finite affine images have the same ambient values.
    convert hb using 1 <;> apply WallComplement.ext <;>
      simp only [levelPathPushforward_obj_val, CommonWallComplement.projection_val,
        CommonWallComplement.projectionPrefunctor_obj]⟩

/-- All-order allowed points move by the spatial affine equivalence. -/
@[simp]
theorem pathPushforward_obj_val (x : D.Point) :
    ((D.pathPushforward P).obj x).val = P.spatialMap x.val := (rfl)

/-- All-order path pushforward preserves reversal. -/
instance : (D.pathPushforward P).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Projecting a pushed common path agrees with pushing its projection from the source
cutoff selected by the modulus. -/
theorem pathPushforward_comp_projection (k : ℕ) :
    D.pathPushforward P ⋙q CommonWallComplement.projectionPrefunctor k =
      CommonWallComplement.projectionPrefunctor (P.degreeMap.modulus k) ⋙q
        D.levelPathPushforward P k le_rfl := by
  refine Prefunctor.ext (fun x => ?_) (fun _ _ _ => PLift.ext (Subsingleton.elim _ _))
  apply WallComplement.ext
  simp

/-- Pushforward carries completed directed path products through the completed BCH
group homomorphism of the graded Lie map. -/
@[simp]
theorem pathProduct_pushforward {x y : D.Point} (p : Quiver.Path x y) :
    (D.pushforward P).pathProduct ((D.pathPushforward P).mapPath p) =
      P.lieHom.completedMap (D.pathProduct p) := by
  apply CompletedGroup.ext
  intro k
  have hp := congrArg
    (fun F : D.Point ⥤q WallComplement
        (fun j : (D.pushforward P).active k => ((D.pushforward P).wall j).support) =>
      (D.pushforward P).levelPathProduct k (F.mapPath p))
    (D.pathPushforward_comp_projection P k)
  simp only [Prefunctor.mapPath_comp_apply] at hp
  rw [projection_pathProduct, P.lieHom.projection_completedMap, projection_pathProduct]
  exact hp.trans (D.levelPathProduct_pushforward P k le_rfl
    ((CommonWallComplement.projectionPrefunctor (P.degreeMap.modulus k)).mapPath p))

section SpecialCases

variable {L'' : Type u} [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L'']
  [IsScalarTower ℚ R L''] {ℋ : Γ → Submodule R L''} [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℋ] {H'' : DirectedWallSpaces ρ ℋ}

/-- Fixed-degree coefficient maps of diagrams are pushforwards. -/
@[simp]
theorem pushforward_ofFixedDegree (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℋ)
    (hf : ∀ n m, ∀ x ∈ H.wall n m, f x ∈ H''.wall n m) :
    D.pushforward (DirectedWall.Pushforward.ofFixedDegree f hf) = D.map f hf := by
  apply DirectedDiagram.ext
  funext j
  simp

/-- Coordinate changes of diagrams are pushforwards. -/
@[simp]
theorem pushforward_ofCoordinateChange (e : Toric.IntegralAffineEquiv h h')
    (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
    (hE : E.tangentEquiv = e.latticeEquiv) :
    D.pushforward (DirectedWall.Pushforward.ofCoordinateChange e E hE) = D.image e E hE := by
  apply DirectedDiagram.ext
  funext j
  simp

end SpecialCases

/-- The identity pushforward fixes every directed diagram. -/
@[simp]
theorem pushforward_id : D.pushforward DirectedWall.Pushforward.id = D := by
  apply DirectedDiagram.ext
  funext j
  simp

section Composition

variable {Γ'' Λ'' V'' : Type*} {L'' : Type u} [AddCommGroup Γ''] [AddCommGroup Λ'']
  [NormedAddCommGroup V''] [NormedSpace ℝ V'']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq Γ''] {ρ'' : Γ'' →+ Λ''} {ℋ : Γ'' → Submodule R L''}
  {d'' : PositiveDegrees Γ''} [GradedLieAlgebra ℋ] [IsPositiveGrading d'' ℋ]
  {i'' : Λ'' →+ V''} {h'' : TauCeti.Toric.IsIntegralLattice i''}
  {H'' : DirectedWallSpaces ρ'' ℋ}

/-- Successive diagram pushforwards agree with the pushforward along the composite. -/
@[simp]
theorem pushforward_pushforward (Q : DirectedWall.Pushforward d' d'' h' h'' H' H'') :
    (D.pushforward P).pushforward Q = D.pushforward (Q.comp P) := by
  apply DirectedDiagram.ext
  funext j
  simp

end Composition

end Mei.DirectedDiagram
