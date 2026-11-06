/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Avoidance
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Compact

/-!
# Actual decorated rays at regular limits

With closed selected supports and a rational-normal polyhedral incoming source,
a closed type path is admissible when its endpoint misses the walls and its
entire negative half-line avoids both wall singular support and the prescribed
singular sets. Regularity excludes collapsed encounter intervals and new wall
contacts; closedness retains selected incidences and incoming-source admission.
Thus failure of admissibility at a limiting endpoint forces a terminal wall
contact or a singular contact, under these hypotheses.

The recovered ray retains its complete type, whole decoration, encounter history
and global path. Compact endpoint sequences whose possible closed type limits
satisfy these regularity conditions therefore have subsequences converging to
actual rays. No admissibility is asserted for singular limits or nonclosed
selected supports. The endpoint reconstruction follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei

variable {R M Γ V J K O Λ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ}
  (c : J → ℝ) (P : J → Set V) (W : O → Set V) (S : K → Set V) (C : Set V)
  [AddCommGroup Λ] {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

namespace CutoffDecoratedType

variable (t : CutoffDecoratedType d ℳ T a v f ε k)

local notation "F" => fun j => f (t.itinerary.val.get j)
local notation "b" => fun j => c (t.itinerary.val.get j)
local notation "u" => fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j)
local notation "τ" => backwardParameter F b
  (fun j : Fin t.itinerary.val.length => u (Fin.castSucc j))

/-- A regular closed type path lies in its original full admissible domain.
Both kinds of singular avoidance concern the entire negative half-line, not
only the recorded encounters. Selected supports must be closed. -/
theorem mem_domain_of_mem_closure_of_regular
    (hPclosed : ∀ j, IsClosed (P j)) (wall : J → O)
    (hWclosed : ∀ j, IsClosed (W j)) (hP : ∀ j, P j ⊆ W (wall j))
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (ν : O → V →L[ℝ] ℝ) (z : O → ℝ)
    (hspan : ∀ j, (affineSpan ℝ (W j) : Set V) = {x | ν j x = z j})
    (hC : IsRationalNormalPolyhedron h C)
    {Q : V} (hQ : Q ∈ closure (domain c P W S C t))
    (hoff : ∀ j, Q ∉ W j)
    (hregular : ∀ s ≤ 0, t.path c Q s ∉ singularSupport W)
    (havoid : ∀ j s, s ≤ 0 → t.path c Q s ∉ S j) :
    Q ∈ domain c P W S C t := by
  have h0 := t.backwardTime_nonneg c P W S C hQ
  have hτ (j : Fin (t.itinerary.val.length + 1)) : τ j Q ≤ 0 := by
    simpa using antitone_backwardParameter F b (fun j => u j.castSucc) Q h0 (Fin.zero_le j)
  have hpos := t.backwardTime_pos_of_notMem_singularSupport c P W S C W wall
    hWclosed hP hheight hQ hoff (fun j => by
      simpa only [Fin.snoc_castSucc] using hregular (τ j.succ Q) (hτ _))
  have he : t.path c Q = (backwardRay F b u Q hpos).toContinuousMap := by
    rw [path_def, backwardPath_eq_backwardRay F b u Q hpos]
  apply (t.mem_domain c P W S C Q).mpr
  apply (mem_admissibleBackwardDomain_iff F b u
    (fun j => P (t.itinerary.val.get j)) W S C Q hpos).mpr
  refine ⟨?_, ?_, ?_, ?_, hoff⟩
  · intro j
    simpa only [he, FiniteAffineRay.toContinuousMap_apply] using
      t.path_parameter_mem c P W S C hPclosed hQ j
  · simpa only [he, FiniteAffineRay.toContinuousMap_apply] using
      t.path_avoids_walls_of_regular c P W S C wall hWclosed hP hheight
        ν z hspan hQ hoff hregular
  · simpa only [he, FiniteAffineRay.toContinuousMap_apply] using
      t.path_eventually_mem c P W S C hC hQ
  · simpa only [he, FiniteAffineRay.toContinuousMap_apply] using havoid

/-- If a closed type endpoint is not admitted, some wall contains the endpoint
or its limiting negative half-line meets wall singular support or a prescribed
singular set. This classifies loss of admissibility, not every domain frontier. -/
theorem not_mem_domain_imp_terminal_or_singular
    (hPclosed : ∀ j, IsClosed (P j)) (wall : J → O)
    (hWclosed : ∀ j, IsClosed (W j)) (hP : ∀ j, P j ⊆ W (wall j))
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (ν : O → V →L[ℝ] ℝ) (z : O → ℝ)
    (hspan : ∀ j, (affineSpan ℝ (W j) : Set V) = {x | ν j x = z j})
    (hC : IsRationalNormalPolyhedron h C)
    {Q : V} (hQ : Q ∈ closure (domain c P W S C t))
    (hnot : Q ∉ domain c P W S C t) :
    (∃ j, Q ∈ W j) ∨ (∃ s ≤ 0, t.path c Q s ∈ singularSupport W) ∨
      ∃ j s, s ≤ 0 ∧ t.path c Q s ∈ S j := by
  by_contra hn
  push Not at hn
  exact hnot (t.mem_domain_of_mem_closure_of_regular c P W S C hPclosed wall
    hWclosed hP hheight ν z hspan hC hQ hn.1 hn.2.1 hn.2.2)

end CutoffDecoratedType

section ActualRay

variable [Finite J] (W : J → Set V)

/-- A regular closed type limit is realized by an actual ray with the same
complete decorated type, whole final decoration and compact-open path. -/
theorem CutoffDecoratedType.exists_ray_of_mem_closure_of_regular
    (t : CutoffDecoratedType d ℳ T a v f ε k)
    (hPclosed : ∀ j, IsClosed (P j)) (wall : J → J)
    (hWclosed : ∀ j, IsClosed (W j)) (hP : ∀ j, P j ⊆ W (wall j))
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (ν : J → V →L[ℝ] ℝ) (z : J → ℝ)
    (hspan : ∀ j, (affineSpan ℝ (W j) : Set V) = {x | ν j x = z j})
    (hC : IsRationalNormalPolyhedron h C)
    {Q : V} (hQ : Q ∈ closure (CutoffDecoratedType.domain c P W S C t))
    (hoff : ∀ j, Q ∉ W j)
    (hregular : ∀ s ≤ 0, t.path c Q s ∉ singularSupport W)
    (havoid : ∀ j s, s ≤ 0 → t.path c Q s ∉ S j) :
    ∃ r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q,
      (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q r).val = t ∧
      r.realization.2.ray.toContinuousMap = t.path c Q ∧ r.decoration = t.decoration := by
  have hmem := t.mem_domain_of_mem_closure_of_regular c P W S C hPclosed wall
    hWclosed hP hheight ν z hspan hC hQ hoff hregular havoid
  let r := (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q).symm ⟨t, hmem⟩
  have ht : (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q r).val = t :=
    congrArg Subtype.val (Equiv.apply_symm_apply _ _)
  refine ⟨r, ht, ?_, ?_⟩
  · rw [r.toContinuousMap_eq_typePath c P W S C, ht]
  · rw [← cutoffDecoratedRayFiberEquiv_decoration d ℳ T a v f c ε P W S C, ht]

/-- If every possible closed type limit over a compact endpoint set is regular,
any sequence of actual rays has an actual limiting ray. The extracted subsequence
retains the limit ray's entire type and whole final decoration. -/
theorem CutoffDecoratedRay.exists_actual_tendsto_subseq_of_regular
    (hPclosed : ∀ j, IsClosed (P j)) (wall : J → J)
    (hWclosed : ∀ j, IsClosed (W j)) (hP : ∀ j, P j ⊆ W (wall j))
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (ν : J → V →L[ℝ] ℝ) (z : J → ℝ)
    (hspan : ∀ j, (affineSpan ℝ (W j) : Set V) = {x | ν j x = z j})
    (hC : IsRationalNormalPolyhedron h C)
    {B : Set V} (hB : IsCompact B) (hoff : ∀ Q ∈ B, ∀ j, Q ∉ W j)
    (hregular : ∀ (t : CutoffDecoratedType d ℳ T a v f ε k) Q,
      Q ∈ B ∩ closure (CutoffDecoratedType.domain c P W S C t) →
        (∀ s ≤ 0, t.path c Q s ∉ singularSupport W) ∧
        ∀ j s, s ≤ 0 → t.path c Q s ∉ S j)
    {Q : ℕ → V} (hQ : ∀ n, Q n ∈ B)
    (r : ∀ n, CutoffDecoratedRay d ℳ T a v f c ε P W S C k (Q n)) :
    ∃ (q : V) (_ : q ∈ B) (r₀ : CutoffDecoratedRay d ℳ T a v f c ε P W S C k q)
      (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ n, (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k
        (Q (φ n)) (r (φ n))).val =
        (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k q r₀).val) ∧
      (∀ n, (r (φ n)).decoration = r₀.decoration) ∧
      Tendsto (Q ∘ φ) atTop (𝓝 q) ∧
      Tendsto (fun n => (r (φ n)).realization.2.ray.toContinuousMap)
        atTop (𝓝 r₀.realization.2.ray.toContinuousMap) := by
  obtain ⟨t, q, φ, hq, hφ, ht, hd, hend, hp⟩ :=
    CutoffDecoratedRay.exists_type_tendsto_subseq c P W S C hB hQ r
  obtain ⟨hr, hs⟩ := hregular t q hq
  obtain ⟨r₀, ht₀, hp₀, hd₀⟩ := t.exists_ray_of_mem_closure_of_regular c P S C W
    hPclosed wall hWclosed hP hheight ν z hspan hC hq.2 (hoff q hq.1) hr hs
  refine ⟨q, hq.1, r₀, φ, hφ, ?_, ?_, hend, ?_⟩
  · exact fun n => (ht n).trans ht₀.symm
  · exact fun n => (hd n).trans hd₀.symm
  · rwa [← hp₀] at hp

end ActualRay

end Mei
