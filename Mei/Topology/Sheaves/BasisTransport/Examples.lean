/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.BasisTransport
public import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.NormNum

/-!
# A Boolean local system across a wall

On the real line, choose Boolean coordinates which change by the nontrivial
permutation at zero. Their relative changes give coherent basis transport.
The resulting sheaf is locally constant in the restriction sense, even though
its sections as Boolean-valued functions can jump at the wall. Evaluation
reconstructs the jump, whereas constant false values cannot give a section
on an interval crossing zero.
-/

open CategoryTheory TopologicalSpace Opposite Set TopCat

public noncomputable section

namespace Mei.BasisTransport.Examples

/-- An open metric ball in the real line. -/
abbrev ballOpen (c r : ℝ) : Opens (TopCat.of ℝ) := ⟨Metric.ball c r, Metric.isOpen_ball⟩

/-- The basis of real metric balls, allowing arbitrary centers and radii. -/
abbrev balls : Set (Opens (TopCat.of ℝ)) := Set.range (fun p : ℝ × ℝ => ballOpen p.1 p.2)

/-- Metric balls form an open basis. -/
theorem balls_isBasis : Opens.IsBasis balls := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  exact ⟨ballOpen x ε, ⟨(x, ε), rfl⟩, Metric.mem_ball_self hε, hsub⟩

/-- The Boolean coordinate chart changes by the nontrivial permutation at zero. -/
def twist (x : ℝ) : Bool ≃ Bool :=
  if 0 < x then Equiv.swap false true else Equiv.refl Bool

/-- Coherent transport across a single wall at zero, with Boolean fibers. -/
def wallTransport : BasisTransport (fun _ : TopCat.of ℝ => Bool) where
  basis := balls
  isBasis := balls_isBasis
  transport _ _ x y := (twist x).symm.trans (twist y)
  transport_trans := by intro U hU x y z; ext a; simp
  transport_restrict _ _ _ _ _ := rfl

/-- Each chart is preconnected, including the empty balls. -/
theorem balls_preconnected (U : Opens (TopCat.of ℝ)) (hU : U ∈ wallTransport.basis) :
    _root_.IsPreconnected (U : Set ℝ) := by
  obtain ⟨⟨c, r⟩, rfl⟩ := hU
  exact (convex_ball c r).isPreconnected

/-- The Boolean wall transport gives a concrete locally constant sheaf. -/
instance wallTransport_sheaf_hasLocallyBijectivePreconnectedRestrictions :
    wallTransport.sheaf.HasLocallyBijectivePreconnectedRestrictions :=
  wallTransport.hasLocallyBijectivePreconnectedRestrictions (fun x =>
    ⟨ballOpen x 1, ⟨(x, 1), rfl⟩, ballOpen x 1, Metric.mem_ball_self zero_lt_one, le_rfl,
      balls_preconnected _ ⟨(x, 1), rfl⟩⟩)

/-- A parallel global section whose Boolean values change across the wall. -/
def jump (b : Bool) : wallTransport.sheaf.presheaf.obj (op ⊤) :=
  wallTransport.sectionOfParallel (fun x => twist x b) (by
    rw [BasisTransport.prelocal_pred_iff]
    intro V hV hVtop x y
    simp [wallTransport])

/-- The distinguished section has value false on the negative side. -/
theorem value_jump_neg_one : wallTransport.value (jump false) ⟨-1, mem_univ _⟩ = false := by
  norm_num [jump, twist]

/-- The same section has value true on the positive side. -/
theorem value_jump_one : wallTransport.value (jump false) ⟨1, mem_univ _⟩ = true := by
  norm_num [jump, twist]

/-- The radius-two interval is one of the transport charts. -/
theorem ball02_mem : ballOpen 0 2 ∈ wallTransport.basis := ⟨(0, 2), rfl⟩

instance : PreconnectedSpace (ballOpen 0 2) :=
  isPreconnected_iff_preconnectedSpace.mp (balls_preconnected _ ball02_mem)

/-- A point to the left of the wall in the radius-two chart. -/
abbrev leftPoint : ballOpen 0 2 := ⟨-1, by norm_num [ballOpen, Metric.mem_ball, Real.dist_eq]⟩
/-- A point to the right of the wall in the radius-two chart. -/
abbrev rightPoint : ballOpen 0 2 := ⟨1, by norm_num [ballOpen, Metric.mem_ball, Real.dist_eq]⟩

/-- Inverse evaluation reconstructs the nontrivial change across the wall. -/
theorem value_evaluationEquiv_symm : wallTransport.value
    ((wallTransport.evaluationEquiv ball02_mem le_rfl leftPoint).symm false) rightPoint = true := by
  rw [BasisTransport.evaluationEquiv_symm_apply]
  norm_num [wallTransport, twist, leftPoint, rightPoint]

/-- Constant false values across this chart violate the transport equation. -/
theorem not_exists_const_false : ¬ ∃ s : wallTransport.sheaf.presheaf.obj (op (ballOpen 0 2)),
    ∀ x, wallTransport.value s x = false := by
  rintro ⟨s, hs⟩
  have hp := wallTransport.parallel_of_le ball02_mem le_rfl s leftPoint rightPoint
  rw [hs leftPoint, hs rightPoint] at hp
  norm_num [wallTransport, twist, leftPoint, rightPoint] at hp

/-- Restriction to the radius-one interval retains exactly the section data. -/
theorem restriction_bijective : Function.Bijective (wallTransport.sheaf.presheaf.map
    (homOfLE (Metric.ball_subset_ball (by norm_num)) :
      ballOpen 0 1 ⟶ ballOpen 0 2).op) := by
  apply wallTransport.restriction_bijective ball02_mem le_rfl
  · exact balls_preconnected _ ball02_mem
  · exact ⟨0, by norm_num [ballOpen, Metric.mem_ball]⟩
  · exact (convex_ball (0 : ℝ) 1).isPreconnected

end Mei.BasisTransport.Examples
