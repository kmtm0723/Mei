/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.RegularLocus
public import Mathlib.Topology.Baire.Lemmas

/-!
# Coefficient points avoiding finitely many exceptional arrangements

On the regular locus of a finite polyhedral complex, off-wall coefficient points
remain dense after imposing any finite family of exceptional-arrangement
conditions. Only finite intersections of open dense sets are used; no Baire-space
or completeness hypothesis is required. This supplies a dense domain for
extending geometrically defined coefficients to an ambient transport sheaf.
-/

public noncomputable section

open Set Mei.Convex TopologicalSpace

namespace Mei.FinitePolyhedralComplex

variable {N V J : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h)

/-- Off-wall coefficient points satisfying every arrangement condition. -/
abbrev arrangementCoefficientPoints (A : J → ExceptionalArrangement V) :=
  {x : C.coefficientPoints // ∀ j, (A j).IsGeneric x.val.val}

/-- Simultaneous genericity for a finite family of arrangements preserves density
in the full regular locus, including its regular wall points. -/
theorem denseRange_arrangementCoefficientPoints [Finite J]
    (A : J → ExceptionalArrangement V) :
    DenseRange (fun x : C.arrangementCoefficientPoints A => x.val.val) := by
  let := h.finiteDimensional
  let s (j : J) : Set C.regularSpace := {x | (A j).IsGeneric x.val}
  have ho (j : J) : IsOpen (s j) :=
    (A j).isOpen_isGeneric.preimage continuous_subtype_val
  have hd (j : J) : Dense (s j) :=
    (A j).dense_isGeneric.preimage C.isOpen_regularLocus.isOpenMap_subtype_val
  have hdAll : Dense {x : C.regularSpace | ∀ j, (A j).IsGeneric x.val} := by
    have hd' := (finite_range s).dense_sInter
      (fun _ ⟨j, hj⟩ => hj ▸ ho j) (fun _ ⟨j, hj⟩ => hj ▸ hd j)
    simpa only [sInter_range, mem_iInter, mem_ofPred_eq, ofPred_forall, s] using hd'
  have hoAll : IsOpen {x : C.regularSpace | ∀ j, (A j).IsGeneric x.val} := by
    simpa only [ofPred_forall] using isOpen_iInter_of_finite ho
  have hdPoints := C.dense_coefficientPoints.inter_of_isOpen_right hdAll hoAll
  unfold DenseRange
  apply hdPoints.mono
  rintro x ⟨hx, hA⟩
  exact ⟨⟨⟨x, hx⟩, hA⟩, rfl⟩

end Mei.FinitePolyhedralComplex
