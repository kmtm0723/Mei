/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedCorrespondence.Basic
public import TauCeti.Algebra.Module.GradedModule.Trivial

/-!
# Graph correspondences of trivially graded modules

Give two modules Tau Ceti's `trivialGrading`, concentrated in degree `0 : ℤ`. For the graph
correspondence of a linear equivalence `e`, each forward transfer is `e` in degree zero and
zero in every other degree; each backward transfer is the same statement for `e.symm`. The
admissible input degree is arbitrary, because a homogeneous input of nonzero degree is zero.

For doubling on `ℚ`, this computes `B^{0,0}(1) = 2` and `B^{0,η}(1) = 0` for `η ≠ 0`.
The proofs reduce to `graph_transfer_apply`, `graph_symm_transfer_apply` and Tau Ceti's
`TauCeti.proj_trivialGrading`.
-/

public section

open TauCeti

namespace Mei.GradedCorrespondence

variable {R U V : Type*} [Semiring R] [AddCommMonoid U] [Module R U]
  [AddCommMonoid V] [Module R V]

/-- Between trivially graded modules, a forward graph transfer is the equivalence in degree
zero and vanishes in every other degree. -/
theorem graph_trivialGrading_transfer_apply (e : U ≃ₗ[R] V) (i : (Set.univ : Set ℤ))
    (j : ℤ) (a : trivialGrading R U i) :
    ((graph (trivialGrading R U) (trivialGrading R V) e).transfer i j a : V) =
      if j = 0 then e a else 0 := by
  rw [graph_transfer_apply, proj_trivialGrading]

/-- Between trivially graded modules, a backward graph transfer is the inverse equivalence
in degree zero and vanishes in every other degree. -/
theorem graph_trivialGrading_symm_transfer_apply (e : U ≃ₗ[R] V) (j : (Set.univ : Set ℤ))
    (i : ℤ) (a : trivialGrading R V j) :
    ((graph (trivialGrading R U) (trivialGrading R V) e).symm.transfer j i a : U) =
      if i = 0 then e.symm a else 0 := by
  rw [graph_symm_transfer_apply, proj_trivialGrading]

namespace Examples

/-- Multiplication by `2` on `ℚ`. -/
noncomputable def double : ℚ ≃ₗ[ℚ] ℚ :=
  LinearEquiv.smulOfNeZero ℚ ℚ 2 two_ne_zero

/-- Doubling sends `a` to `2 * a`. -/
@[simp]
theorem double_apply (a : ℚ) : double a = 2 * a := (rfl)

/-- The graph of doubling, with `ℚ` concentrated in degree zero on both sides. -/
noncomputable def doubleGraph :
    GradedCorrespondence (B := ℚ) (trivialGrading ℚ ℚ) (trivialGrading ℚ ℚ)
      Set.univ Set.univ :=
  graph (trivialGrading ℚ ℚ) (trivialGrading ℚ ℚ) double

/-- The unit in degree zero, as an admissible homogeneous input. -/
def unitInput : trivialGrading ℚ ℚ ((⟨0, Set.mem_univ 0⟩ : (Set.univ : Set ℤ)) : ℤ) :=
  ⟨1, by simp⟩

/-- The degree-zero transfer of the doubling graph sends `1` to `2`. -/
theorem doubleGraph_transfer_zero :
    (doubleGraph.transfer ⟨0, Set.mem_univ 0⟩ 0 unitInput : ℚ) = 2 := by
  rw [doubleGraph, graph_trivialGrading_transfer_apply]
  simp [unitInput]

/-- Every transfer of the doubling graph to a nonzero degree vanishes on `1`. -/
theorem doubleGraph_transfer_of_ne_zero {η : ℤ} (hη : η ≠ 0) :
    (doubleGraph.transfer ⟨0, Set.mem_univ 0⟩ η unitInput : ℚ) = 0 := by
  rw [doubleGraph, graph_trivialGrading_transfer_apply]
  simp [hη]

end Examples

end Mei.GradedCorrespondence
