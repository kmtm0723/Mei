/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Product

/-!
# Projection of paths through cylinder walls

Adding unrestricted spatial coordinates to each wall preserves singular support
and signed crossings. Projection onto the original coordinates carries admissible
polygonal paths and their wall products to the original wall family.
-/

public section
noncomputable section

open Set Mei.Convex

namespace Mei.Convex

variable {V E ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The relative boundary of a cylinder is the cylinder over the relative boundary. -/
theorem intrinsicFrontier_prod_univ (P : Set V) :
    intrinsicFrontier ℝ (P ×ˢ (univ : Set E)) = intrinsicFrontier ℝ P ×ˢ univ := by
  rw [← intrinsicClosure_sdiff_intrinsicInterior, intrinsicInterior_prod_eq,
    intrinsicClosure_eq_closure_inter_affineSpan, closure_prod_eq, affineSpan_prod_eq,
    ← intrinsicClosure_sdiff_intrinsicInterior, intrinsicClosure_eq_closure_inter_affineSpan]
  ext x
  simp

private theorem direction_prod_univ {P : Set V} (hP : P.Nonempty) :
    (affineSpan ℝ (P ×ˢ (univ : Set E))).direction =
      (affineSpan ℝ P).direction.prod ⊤ := by
  rw [direction_affineSpan, vectorSpan_prod_eq hP Set.univ_nonempty]
  rw [← direction_affineSpan, ← direction_affineSpan,
    AffineSubspace.span_univ, AffineSubspace.direction_top]

/-- A cylinder family has precisely the singularities of the original family. -/
theorem singularSupport_prod_univ (W : ι → Set V) (hW : ∀ j, (W j).Nonempty) :
    singularSupport (fun j => W j ×ˢ (univ : Set E)) = singularSupport W ×ˢ univ := by
  have hd (i j : ι) :
      (affineSpan ℝ (W i ×ˢ (univ : Set E))).direction =
        (affineSpan ℝ (W j ×ˢ (univ : Set E))).direction ↔
      (affineSpan ℝ (W i)).direction = (affineSpan ℝ (W j)).direction := by
    rw [direction_prod_univ (hW i), direction_prod_univ (hW j)]
    constructor
    · intro he
      ext v
      have := congrArg (fun S : Submodule ℝ (V × E) => (v, 0) ∈ S) he
      simpa using this
    · exact fun he => congrArg (fun S : Submodule ℝ V => S.prod (⊤ : Submodule ℝ E)) he
  ext x
  simp only [mem_singularSupport, intrinsicFrontier_prod_univ, mem_prod, mem_univ,
    and_true, ne_eq, hd]

namespace WallComplement

variable (W : ι → Set V) (hW : ∀ j, (W j).Nonempty)

/-- Forget the unrestricted coordinates of a path through cylinder walls. -/
def cylinderProjection : WallComplement (fun j => W j ×ˢ (univ : Set E)) ⥤q
    WallComplement W where
  obj x := ⟨x.val.1, fun j hj => x.notMem j ⟨hj, mem_univ _⟩⟩
  map {x y} a := ⟨{
    transverse := fun j hj hm => by
      apply a.down.transverse j
      · obtain ⟨t, ht, hm⟩ := hj
        exact ⟨t, ht, hm, mem_univ _⟩
      · rw [direction_prod_univ (hW j)]
        exact ⟨hm, Submodule.mem_top⟩
    regular := fun t ht hm => by
      apply a.down.regular t ht
      rw [singularSupport_prod_univ W hW]
      exact ⟨hm, mem_univ _⟩ }⟩

@[simp]
theorem cylinderProjection_obj_val
    (x : WallComplement (fun j => W j ×ˢ (univ : Set E))) :
    ((cylinderProjection W hW).obj x).val = x.val.1 := by rfl

instance : (cylinderProjection (E := E) W hW).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

theorem mem_crossings_cylinderProjection
    (x y : WallComplement (fun j => W j ×ˢ (univ : Set E))) (j : ι) (t : ℝ) :
    (j, t) ∈ crossings ((cylinderProjection W hW).obj x)
      ((cylinderProjection W hW).obj y) ↔ (j, t) ∈ crossings x y := by
  simp [mem_crossings, AffineMap.lineMap_apply]

variable [Finite ι]
  {x y : WallComplement (fun j => W j ×ˢ (univ : Set E))}

@[simp]
theorem orderedCrossingTimes_cylinderProjection (a : x ⟶ y) :
    orderedCrossingTimes ((cylinderProjection W hW).map a) = orderedCrossingTimes a := by
  apply (pairwise_orderedCrossingTimes _).eq_of_mem_iff (pairwise_orderedCrossingTimes _)
  intro t
  simp

@[simp]
theorem signedCrossingEvent_cylinderProjection (ν : ι → V →ₗ[ℝ] ℝ) (t : ℝ) :
    signedCrossingEvent ν ((cylinderProjection W hW).obj x)
      ((cylinderProjection W hW).obj y) t =
    signedCrossingEvent (fun j => (ν j).comp (LinearMap.fst ℝ V E)) x y t := by
  ext ⟨j, s⟩
  simp

@[simp]
theorem segmentCrossingEvents_cylinderProjection (ν : ι → V →ₗ[ℝ] ℝ) (a : x ⟶ y) :
    segmentCrossingEvents ν ((cylinderProjection W hW).map a) =
      segmentCrossingEvents (fun j => (ν j).comp (LinearMap.fst ℝ V E)) a := by
  simp only [segmentCrossingEvents_def, orderedCrossingTimes_cylinderProjection]
  apply List.map_congr_left
  intro t _
  exact signedCrossingEvent_cylinderProjection W hW ν t

end WallComplement
end Mei.Convex

namespace Quiver.Path

open Mei.Convex.WallComplement

variable {V E ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (W : ι → Set V) (hW : ∀ j, (W j).Nonempty) [Finite ι]
  {x y : WallComplement (fun j => W j ×ˢ (univ : Set E))}

@[simp]
theorem signedCrossingEvents_cylinderProjection (ν : ι → V →ₗ[ℝ] ℝ)
    (p : AdmissiblePLPath x y) :
    ((cylinderProjection W hW).mapPath p).signedCrossingEvents ν =
      p.signedCrossingEvents (fun j => (ν j).comp (LinearMap.fst ℝ V E)) := by
  induction p with
  | nil => simp
  | cons p a ih => simp [ih]

/-- The product along a cylinder path is the product along its spatial projection. -/
theorem wallPathProduct_cylinderProjection {G : Type*} [Group G]
    (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
    (comm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
    (comm' : ∀ i j, affineSpan ℝ (W i ×ˢ (univ : Set E)) =
      affineSpan ℝ (W j ×ˢ univ) → Commute (label i) (label j))
    (p : AdmissiblePLPath x y) :
    ((cylinderProjection W hW).mapPath p).wallPathProduct ν label comm =
      p.wallPathProduct (fun j => (ν j).comp (LinearMap.fst ℝ V E)) label comm' := by
  rw [wallPathProduct_eq_prod_signedCrossingEvents,
    wallPathProduct_eq_prod_signedCrossingEvents, signedCrossingEvents_cylinderProjection]

end Quiver.Path
