/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Graph
public import Mei.Algebra.Lie.BCH.Completion

/-!
# Completed BCH groups under graph regrading

Graph inclusion and projection, acting as identity on the Lie algebra, induce
inverse maps on completed BCH groups. This comparison retains each finite cutoff
and commutes with exponentiation of original Lie elements. At every cutoff the same
two maps are inverse isomorphisms of the finite BCH groups, and the completed
comparison projects to them. It uses `GradedLieHom.completedMap` and its independence
of the choice of degree map.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {N M R L : Type*} [AddCommMonoid N] [AddCommMonoid M]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N] [DecidableEq M]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L) (f : N →+ M)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Graph reindexing gives a canonical isomorphism of completed BCH groups.
Both directions are induced by identity on the original Lie algebra. -/
def graphBCHGroupEquiv :
    d.completedBCHGroup ℒ ≃* (d.graph f).completedBCHGroup (graphGrading ℒ f) :=
  MonoidHom.toMulEquiv (graphGradedLieHom ℒ f d).completedMap
    (graphProjectionGradedLieHom ℒ f d).completedMap
    (by
      rw [← GradedLieHom.completedMap_comp]
      exact (GradedLieHom.completedMap_eq_of_toLieHom_eq _ (GradedLieHom.id ℒ)
        (by simp)).trans GradedLieHom.completedMap_id)
    (by
      rw [← GradedLieHom.completedMap_comp]
      exact (GradedLieHom.completedMap_eq_of_toLieHom_eq _
        (GradedLieHom.id (graphGrading ℒ f)) (by simp)).trans GradedLieHom.completedMap_id)

/-- The forward comparison is the completed map of graph inclusion. -/
theorem graphBCHGroupEquiv_apply (x : d.completedBCHGroup ℒ) :
    d.graphBCHGroupEquiv ℒ f x = (graphGradedLieHom ℒ f d).completedMap x := (rfl)

/-- The inverse comparison is the completed map of graph projection. -/
theorem graphBCHGroupEquiv_symm_apply
    (x : (d.graph f).completedBCHGroup (graphGrading ℒ f)) :
    (d.graphBCHGroupEquiv ℒ f).symm x =
      (graphProjectionGradedLieHom ℒ f d).completedMap x := (rfl)

/-- Reindexing preserves exponentials of original Lie elements. -/
@[simp]
theorem graphBCHGroupEquiv_expToCompletion (x : L) :
    d.graphBCHGroupEquiv ℒ f (d.expToCompletion ℒ x) =
      (d.graph f).expToCompletion (graphGrading ℒ f) x := by
  rw [graphBCHGroupEquiv_apply, GradedLieHom.completedMap_expToCompletion,
    graphGradedLieHom_apply]

/-- At each cutoff, graph reindexing is an isomorphism of finite BCH groups. Both
directions are induced by identity on the original Lie algebra. -/
def graphTruncatedGroupEquiv (k : ℕ) :
    d.truncatedGroup ℒ k ≃* (d.graph f).truncatedGroup (graphGrading ℒ f) k :=
  MonoidHom.toMulEquiv
    ((graphGradedLieHom ℒ f d).truncatedMap k (d.graphMap_modulus f k).le).bchGroupMap
    ((graphProjectionGradedLieHom ℒ f d).truncatedMap k
      (d.graphProjection_modulus f k).le).bchGroupMap
    (by
      refine MonoidHom.ext fun y => ?_
      obtain ⟨x, rfl⟩ := CompletedGroup.projection_surjective (d.groupTower ℒ)
        (fun n => d.groupTower_map_surjective ℒ (CategoryTheory.homOfLE (Nat.le_succ n)).op) k y
      have hf := (graphGradedLieHom ℒ f d).projection_completedMap_of_le k
        (d.graphMap_modulus f k).le x
      have hg := (graphProjectionGradedLieHom ℒ f d).projection_completedMap_of_le k
        (d.graphProjection_modulus f k).le ((graphGradedLieHom ℒ f d).completedMap x)
      rw [← graphBCHGroupEquiv_apply, ← graphBCHGroupEquiv_symm_apply,
        MulEquiv.symm_apply_apply] at hg
      -- Both sides are applications of the composite and identity homomorphisms.
      exact (congrArg _ hf.symm).trans hg.symm)
    (by
      refine MonoidHom.ext fun y => ?_
      obtain ⟨x, rfl⟩ := CompletedGroup.projection_surjective ((d.graph f).groupTower _)
        (fun n => (d.graph f).groupTower_map_surjective _
          (CategoryTheory.homOfLE (Nat.le_succ n)).op) k y
      have hg := (graphProjectionGradedLieHom ℒ f d).projection_completedMap_of_le k
        (d.graphProjection_modulus f k).le x
      have hf := (graphGradedLieHom ℒ f d).projection_completedMap_of_le k
        (d.graphMap_modulus f k).le ((graphProjectionGradedLieHom ℒ f d).completedMap x)
      rw [← graphBCHGroupEquiv_symm_apply, ← graphBCHGroupEquiv_apply,
        MulEquiv.apply_symm_apply] at hf
      -- Both sides are applications of the composite and identity homomorphisms.
      exact (congrArg _ hg.symm).trans hf.symm)

/-- The completed graph comparison projects to the finite graph comparison at every cutoff. -/
@[simp]
theorem projection_graphBCHGroupEquiv (k : ℕ) (x : d.completedBCHGroup ℒ) :
    CompletedGroup.projection k (d.graphBCHGroupEquiv ℒ f x) =
      d.graphTruncatedGroupEquiv ℒ f k (CompletedGroup.projection k x) :=
  (graphGradedLieHom ℒ f d).projection_completedMap_of_le k (d.graphMap_modulus f k).le x

end Mei.PositiveDegrees
