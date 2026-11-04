/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Cylinder
public import Mei.Geometry.Convex.Polyhedron.Path.AffineTransport

/-!
# Paths through preimages of walls under linear surjections

A surjective linear map `A : V → V'` from a finite-dimensional real space is the first
coordinate of a continuous linear equivalence `V ≃ V' × ker A`. Under this equivalence the
preimage `A⁻¹(W)` of a wall becomes the cylinder `W × ker A`. Hence `A` carries allowed
points and admissible segments for a pulled-back wall family to allowed points and admissible
segments for the original family, and the supporting direction of a preimage is the preimage
of the supporting direction. Every polygonal wall product through the preimages is the product
along the image path, for the pulled-back normals `ν ∘ A`. A linear section of
`A` lifts admissible paths back, so `A` induces a retraction of path quivers. Coincident and
repeated walls retain separate factors, and the wall indices may be reindexed.

This combines `ContinuousAffineEquiv.wallComplementMap` with
`WallComplement.cylinderProjection` and `WallComplement.cylinderLift`. The splitting uses
Mathlib's `LinearMap.equivProdOfSurjectiveOfIsCompl` and `Submodule.projectionOnto`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace LinearMap

variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V]
  (A : V →ₗ[ℝ] V') (hA : Function.Surjective A)

/-- A surjective linear map is the first coordinate of a continuous linear equivalence
with the product of its target and its kernel. The kernel coordinate is the projection
along a chosen complement. -/
def prodKerEquiv : V ≃L[ℝ] V' × LinearMap.ker A :=
  (A.equivProdOfSurjectiveOfIsCompl
    (Submodule.projectionOnto (LinearMap.ker A)
      (Submodule.exists_isCompl (LinearMap.ker A)).choose
      (Submodule.exists_isCompl (LinearMap.ker A)).choose_spec)
    (LinearMap.range_eq_top.mpr hA) (Submodule.range_projectionOnto _)
    (by
      rw [Submodule.ker_projectionOnto]
      exact (Submodule.exists_isCompl (LinearMap.ker A)).choose_spec)).toContinuousLinearEquiv

/-- The first coordinate of the splitting is the surjection itself. -/
@[simp]
theorem prodKerEquiv_apply_fst (x : V) : (A.prodKerEquiv hA x).1 = A x := (rfl)

/-- The splitting carries the preimage of a set to the cylinder over that set. -/
theorem image_prodKerEquiv_preimage (S : Set V') :
    A.prodKerEquiv hA '' (A ⁻¹' S) = S ×ˢ (univ : Set (LinearMap.ker A)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by simpa using hx, mem_univ _⟩
  · intro hz
    refine ⟨(A.prodKerEquiv hA).symm z, ?_, (A.prodKerEquiv hA).apply_symm_apply z⟩
    have he := congrArg Prod.fst ((A.prodKerEquiv hA).apply_symm_apply z)
    rw [prodKerEquiv_apply_fst] at he
    simpa [he] using hz.1

/-- The inverse splitting carries the cylinder over a set to its preimage. -/
theorem image_prodKerEquiv_symm_prod_univ (S : Set V') :
    (A.prodKerEquiv hA).symm '' (S ×ˢ (univ : Set (LinearMap.ker A))) = A ⁻¹' S := by
  rw [← A.image_prodKerEquiv_preimage hA S, ContinuousLinearEquiv.symm_image_image]

include hA in
/-- The supporting direction of a preimage of a nonempty set under a linear surjection is
the preimage of the original supporting direction. -/
theorem direction_affineSpan_preimage {S : Set V'} (hS : S.Nonempty) :
    (affineSpan ℝ (A ⁻¹' S)).direction = (affineSpan ℝ S).direction.comap A := by
  -- The image under the affine map of the inverse splitting is its image as an equivalence.
  have he : (affineSpan ℝ ((A.prodKerEquiv hA).symm ''
        (S ×ˢ (univ : Set (LinearMap.ker A))))).direction =
      (affineSpan ℝ (S ×ˢ (univ : Set (LinearMap.ker A)))).direction.map
        (A.prodKerEquiv hA).symm.toLinearEquiv.toLinearMap :=
    AffineMap.direction_affineSpan_image
      (A.prodKerEquiv hA).symm.toLinearEquiv.toLinearMap.toAffineMap _
  rw [A.image_prodKerEquiv_symm_prod_univ hA, Mei.direction_affineSpan_prod_univ hS] at he
  rw [he]
  ext v
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mem_prod, Submodule.mem_top,
    and_true]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hf := congrArg Prod.fst ((A.prodKerEquiv hA).apply_symm_apply z)
    rw [prodKerEquiv_apply_fst] at hf
    simpa [hf] using hz
  · intro hv
    exact ⟨A.prodKerEquiv hA v, by simpa using hv, by simp⟩

end LinearMap

namespace Mei.Convex.WallComplement

variable {V V' ι ι' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V]
  (A : V →ₗ[ℝ] V') (hA : Function.Surjective A) (W : ι → Set V') {W' : ι' → Set V}
  (r : ι' ≃ ι) (hW : ∀ j, W' j = A ⁻¹' W (r j))

include hW in
/-- Under the splitting, each preimage wall is the cylinder over the original wall. -/
theorem prod_univ_eq_image_prodKerEquiv (j : ι') :
    W (r j) ×ˢ (univ : Set (LinearMap.ker A)) =
      (A.prodKerEquiv hA).toContinuousAffineEquiv '' W' j := by
  rw [hW, ContinuousLinearEquiv.coe_toContinuousAffineEquiv, A.image_prodKerEquiv_preimage hA]

include hW in
/-- The inverse splitting carries each cylinder wall back to the preimage wall. -/
theorem eq_image_prodKerEquiv_symm (j : ι) :
    W' (r.symm j) = (A.prodKerEquiv hA).symm.toContinuousAffineEquiv ''
      (W j ×ˢ (univ : Set (LinearMap.ker A))) := by
  rw [hW, r.apply_symm_apply, ContinuousLinearEquiv.coe_toContinuousAffineEquiv,
    A.image_prodKerEquiv_symm_prod_univ hA]

/-- Push allowed points and admissible segments for the preimage walls `A⁻¹(W (r j))`
forward along a linear surjection `A`. Use `Prefunctor.mapPath` for polygonal paths. -/
def preimageProjection : WallComplement W' ⥤q WallComplement W :=
  (A.prodKerEquiv hA).toContinuousAffineEquiv.wallComplementMap r
      (prod_univ_eq_image_prodKerEquiv A hA W r hW) ⋙q
    cylinderProjection (E := LinearMap.ker A) W

/-- The projection applies the surjection to the actual spatial point. -/
@[simp]
theorem preimageProjection_obj_val (x : WallComplement W') :
    ((preimageProjection A hA W r hW).obj x).val = A x.val := by
  rw [preimageProjection, Prefunctor.comp_obj, cylinderProjection_obj_val,
    ContinuousAffineEquiv.wallComplementMap_obj_val,
    ContinuousLinearEquiv.coe_toContinuousAffineEquiv, LinearMap.prodKerEquiv_apply_fst]

instance : (preimageProjection A hA W r hW).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Lift allowed points and admissible segments along the linear section of `A` given by
the splitting of `V` with zero kernel coordinate. -/
def preimageLift : WallComplement W ⥤q WallComplement W' :=
  cylinderLift W (0 : LinearMap.ker A) ⋙q
    (A.prodKerEquiv hA).symm.toContinuousAffineEquiv.wallComplementMap r.symm
      (eq_image_prodKerEquiv_symm A hA W r hW)

/-- The lift of a point is a preimage of it. -/
@[simp]
theorem apply_preimageLift_obj_val (x : WallComplement W) :
    A ((preimageLift A hA W r hW).obj x).val = x.val := by
  have he := congrArg Prod.fst
    ((A.prodKerEquiv hA).apply_symm_apply (x.val, (0 : LinearMap.ker A)))
  rw [LinearMap.prodKerEquiv_apply_fst] at he
  rw [preimageLift, Prefunctor.comp_obj, ContinuousAffineEquiv.wallComplementMap_obj_val,
    cylinderLift_obj_val, ContinuousLinearEquiv.coe_toContinuousAffineEquiv]
  exact he

instance : (preimageLift A hA W r hW).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Projection is a retraction of the lift. -/
@[simp]
theorem preimageLift_comp_preimageProjection :
    preimageLift A hA W r hW ⋙q preimageProjection A hA W r hW = Prefunctor.id _ := by
  refine Prefunctor.ext (fun x => WallComplement.ext ?_) ?_
  · simp
  · intros
    exact PLift.ext (Subsingleton.elim _ _)

end Mei.Convex.WallComplement

namespace Quiver.Path

open WallComplement

variable {V V' ι ι' G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V] [Finite ι] [Finite ι']
  [Group G] (A : V →ₗ[ℝ] V') (hA : Function.Surjective A) {W : ι → Set V'} {W' : ι' → Set V}
  (r : ι' ≃ ι) (hW : ∀ j, W' j = A ⁻¹' W (r j))
  {x y : WallComplement W'}

/-- The product along the image of a path through preimage walls is the product along the
original path for the pulled-back normals. Simultaneous and repeated crossings are retained. -/
theorem wallPathProduct_preimageProjection (ν : ι → V' →ₗ[ℝ] ℝ) (label : ι → G)
    (comm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
    (comm' : ∀ i j, affineSpan ℝ (W' i) = affineSpan ℝ (W' j) →
      Commute (label (r i)) (label (r j)))
    (p : AdmissiblePLPath x y) :
    ((preimageProjection A hA W r hW).mapPath p).wallPathProduct ν label comm =
      p.wallPathProduct (fun j => (ν (r j)).comp A) (fun j => label (r j)) comm' := by
  let e := (A.prodKerEquiv hA).toContinuousAffineEquiv
  have hp := p.wallPathProduct_wallComplementMap e r
    (prod_univ_eq_image_prodKerEquiv A hA W r hW)
    (fun j => (ν (r j)).comp A) (fun j => (ν j).comp (LinearMap.fst ℝ V' (LinearMap.ker A)))
    (fun j => LinearMap.ext fun v => (rfl))
    (fun j => label (r j)) label comm' (fun i j h => comm i j
      ((Mei.affineSpan_prod_univ_eq_iff (W i) (W j)).mp h))
    (MonoidHom.id G) (fun _ => rfl)
  rw [preimageProjection, Prefunctor.mapPath_comp_apply]
  exact (wallPathProduct_cylinderProjection W ν label comm _).trans hp

end Quiver.Path
