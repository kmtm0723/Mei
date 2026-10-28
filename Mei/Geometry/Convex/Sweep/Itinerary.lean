/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Topology
public import TauCeti.Analysis.Convex.Polyhedron.Basic

/-!
# Backward affine propagation along a fixed transverse itinerary

Starting at an endpoint, successively meet specified hyperplanes along specified
vectors. The encounter points and elapsed times are continuous affine functions
of the endpoint, obtained by composing the existing `sweepProjection` maps.
Transversality gives uniqueness, without a genericity assumption.

The vectors point backwards along the itinerary. For a broken line with forward
velocity `-ρ(p)`, use `ρ(p)` here; positive elapsed times impose the correct order.
The sign of the normal applied to the velocity may be negative. Incidence with
the selected supports does not assert that a segment avoids other walls or meets
a selected wall for the first time.
-/

public section

noncomputable section

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (v : Fin n → V)

/-- The encounter points, as affine functions of the final endpoint. Index zero
is the endpoint; each successor is the preceding encounter in backward order. -/
def backwardPoint : Fin (n + 1) → (V →ᴬ[ℝ] V) :=
  Fin.induction (ContinuousAffineMap.id ℝ V)
    (fun i X => (sweepProjection (f i) (c i) ((f i (v i))⁻¹ • v i)).comp X)

/-- The starting point of backward propagation is the endpoint. -/
@[simp]
theorem backwardPoint_zero : backwardPoint f c v 0 = ContinuousAffineMap.id ℝ V := by
  simp only [backwardPoint, Fin.induction_zero]

/-- Each encounter is obtained by the normalized transverse sweep projection. -/
theorem backwardPoint_succ (i : Fin n) :
    backwardPoint f c v i.succ =
      (sweepProjection (f i) (c i) ((f i (v i))⁻¹ • v i)).comp
        (backwardPoint f c v i.castSucc) := by
  simp only [backwardPoint, Fin.induction_succ]

/-- Elapsed backward time to the next selected hyperplane. Its positivity, rather
than the sign of the unnormalized height difference, orders the encounters. -/
def backwardTime (i : Fin n) : V →ᴬ[ℝ] ℝ :=
  (f i (v i))⁻¹ • (ContinuousAffineMap.const ℝ V (c i) -
    (f i).toContinuousAffineMap.comp (backwardPoint f c v i.castSucc))

/-- The affine backward-time formula. -/
@[simp]
theorem backwardTime_apply (i : Fin n) (Q : V) :
    backwardTime f c v i Q =
      (c i - f i (backwardPoint f c v i.castSucc Q)) / f i (v i) := by
  simp only [backwardTime, ContinuousAffineMap.smul_apply, ContinuousAffineMap.sub_apply,
    ContinuousAffineMap.coe_const, Function.const_apply, ContinuousAffineMap.comp_apply,
    ContinuousLinearMap.coe_toContinuousAffineMap, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Successive encounter points are separated by the elapsed time times the
specified backward velocity. -/
@[simp]
theorem backwardPoint_succ_apply (i : Fin n) (Q : V) :
    backwardPoint f c v i.succ Q = backwardPoint f c v i.castSucc Q +
      backwardTime f c v i Q • v i := by
  rw [backwardPoint_succ, ContinuousAffineMap.comp_apply, sweepProjection_apply,
    backwardTime_apply, smul_smul, div_eq_mul_inv]

/-- A transverse step lies on its selected hyperplane. -/
theorem backwardPoint_height (i : Fin n) (hi : f i (v i) ≠ 0) (Q : V) :
    f i (backwardPoint f c v i.succ Q) = c i := by
  rw [backwardPoint_succ, ContinuousAffineMap.comp_apply]
  apply sweepProjection_height
  simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hi]

/-- Endpoint, velocities and transverse hyperplanes uniquely determine every
encounter and elapsed time. Positivity is unnecessary for this uniqueness law. -/
theorem backward_unique (hf : ∀ i, f i (v i) ≠ 0) (Q : V)
    (X : Fin (n + 1) → V) (t : Fin n → ℝ) (hX : X 0 = Q)
    (hstep : ∀ i, X i.succ = X i.castSucc + t i • v i)
    (hheight : ∀ i, f i (X i.succ) = c i) :
    (∀ i, X i = backwardPoint f c v i Q) ∧
      ∀ i, t i = backwardTime f c v i Q := by
  have htime (i : Fin n) : t i = (c i - f i (X i.castSucc)) / f i (v i) := by
    apply (eq_div_iff (hf i)).mpr
    have h := hheight i
    rw [hstep i, map_add, map_smul, smul_eq_mul] at h
    linarith
  have hp : ∀ i, X i = backwardPoint f c v i Q := by
    intro i
    induction i using Fin.induction with
    | zero => simpa only [backwardPoint_zero, ContinuousAffineMap.coe_id, id_eq] using hX
    | succ i ih =>
      rw [hstep, backwardPoint_succ_apply, htime, ih, backwardTime_apply]
  exact ⟨hp, fun i => by rw [htime, backwardTime_apply, hp]⟩

/-- Rescaling each normal and its level by the same nonzero scalar preserves
all encounter points and physical backward times, including negative scalars. -/
theorem backward_rescale (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) (Q : V) :
    (∀ i, backwardPoint (fun j => a j • f j) (fun j => a j * c j) v i Q =
      backwardPoint f c v i Q) ∧
    ∀ i, backwardTime (fun j => a j • f j) (fun j => a j * c j) v i Q =
      backwardTime f c v i Q := by
  have ht (i : Fin n)
      (hi : backwardPoint (fun j => a j • f j) (fun j => a j * c j) v i.castSucc Q =
        backwardPoint f c v i.castSucc Q) :
      backwardTime (fun j => a j • f j) (fun j => a j * c j) v i Q =
        backwardTime f c v i Q := by
    rw [backwardTime_apply, backwardTime_apply, hi]
    simp only [smul_apply, smul_eq_mul, ← mul_sub]
    exact mul_div_mul_left _ _ (ha i)
  have hp : ∀ i, backwardPoint (fun j => a j • f j) (fun j => a j * c j) v i Q =
      backwardPoint f c v i Q := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ i ih => rw [backwardPoint_succ_apply, backwardPoint_succ_apply, ht i ih, ih]
  exact ⟨hp, fun i => ht i (hp i.castSucc)⟩


/-- Endpoints satisfying the selected support incidences and strictly positive
backward elapsed times. -/
def backwardDomain (P : Fin n → Set V) : Set V :=
  {Q | ∀ i, 0 < backwardTime f c v i Q ∧ backwardPoint f c v i.succ Q ∈ P i}

/-- The weakened endpoint constraints, allowing zero elapsed times. -/
def weakBackwardDomain (P : Fin n → Set V) : Set V :=
  {Q | ∀ i, 0 ≤ backwardTime f c v i Q ∧ backwardPoint f c v i.succ Q ∈ P i}

/-- Membership in the strict endpoint domain. -/
@[simp]
theorem mem_backwardDomain (P : Fin n → Set V) (Q : V) :
    Q ∈ backwardDomain f c v P ↔
      ∀ i, 0 < backwardTime f c v i Q ∧ backwardPoint f c v i.succ Q ∈ P i := Iff.rfl

/-- Membership in the weak endpoint domain. -/
@[simp]
theorem mem_weakBackwardDomain (P : Fin n → Set V) (Q : V) :
    Q ∈ weakBackwardDomain f c v P ↔
      ∀ i, 0 ≤ backwardTime f c v i Q ∧ backwardPoint f c v i.succ Q ∈ P i := Iff.rfl

/-- Strict endpoint constraints imply the weakened ones. -/
theorem backwardDomain_subset_weakBackwardDomain (P : Fin n → Set V) :
    backwardDomain f c v P ⊆ weakBackwardDomain f c v P :=
  fun _ h i => ⟨(h i).1.le, (h i).2⟩

/-- Convex support constraints give a convex strict endpoint domain. -/
theorem convex_backwardDomain {P : Fin n → Set V} (hP : ∀ i, Convex ℝ (P i)) :
    Convex ℝ (backwardDomain f c v P) := by
  have he : backwardDomain f c v P = ⋂ i,
      (backwardTime f c v i) ⁻¹' Set.Ioi 0 ∩
        (backwardPoint f c v i.succ) ⁻¹' P i := by
    ext Q
    simp only [mem_backwardDomain, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Ioi]
  rw [he]
  exact convex_iInter fun i =>
    ((convex_Ioi (0 : ℝ)).affine_preimage (backwardTime f c v i).toAffineMap).inter
      ((hP i).affine_preimage (backwardPoint f c v i.succ).toAffineMap)

/-- Closed support constraints give a closed weak endpoint domain. -/
theorem isClosed_weakBackwardDomain {P : Fin n → Set V} (hP : ∀ i, IsClosed (P i)) :
    IsClosed (weakBackwardDomain f c v P) := by
  have he : weakBackwardDomain f c v P = ⋂ i,
      (backwardTime f c v i) ⁻¹' Set.Ici 0 ∩
        (backwardPoint f c v i.succ) ⁻¹' P i := by
    ext Q
    simp only [mem_weakBackwardDomain, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Ici]
  rw [he]
  exact isClosed_iInter fun i =>
    (isClosed_Ici.preimage (backwardTime f c v i).continuous).inter
      ((hP i).preimage (backwardPoint f c v i.succ).continuous)

/-- Strict times define an open condition inside the closed support-incidence
locus, so the strict endpoint domain is locally closed. -/
theorem isLocallyClosed_backwardDomain {P : Fin n → Set V}
    (hP : ∀ i, IsClosed (P i)) : IsLocallyClosed (backwardDomain f c v P) := by
  have he : backwardDomain f c v P =
      (⋂ i, (backwardTime f c v i) ⁻¹' Set.Ioi 0) ∩
      (⋂ i, (backwardPoint f c v i.succ) ⁻¹' P i) := by
    ext Q
    simp only [mem_backwardDomain, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, Set.mem_Ioi, forall_and]
  rw [he]
  exact (isOpen_iInter_of_finite fun i =>
    isOpen_Ioi.preimage (backwardTime f c v i).continuous).isLocallyClosed.inter
      (isClosed_iInter fun i => (hP i).preimage
        (backwardPoint f c v i.succ).continuous).isLocallyClosed

/-- Polyhedral support constraints pull back to a polyhedron when zero elapsed
times are admitted. No boundedness or finite-dimensionality is assumed. -/
theorem isConvexPolyhedron_weakBackwardDomain {P : Fin n → Set V}
    (hP : ∀ i, TauCeti.IsConvexPolyhedron (P i)) :
    TauCeti.IsConvexPolyhedron (weakBackwardDomain f c v P) := by
  choose m g hg using fun i => TauCeti.isConvexPolyhedron_iff.mp (hP i)
  let rows : Fin n ⊕ (Σ i, Fin (m i)) → V →ᴬ[ℝ] ℝ := Sum.elim
    (fun i => -backwardTime f c v i)
    (fun a => (g a.1 a.2).comp (backwardPoint f c v a.1.succ))
  have he : weakBackwardDomain f c v P = {Q | ∀ j, rows j Q ≤ 0} := by
    ext Q
    simp only [mem_weakBackwardDomain, hg, Set.mem_ofPred_eq, rows, Sum.forall,
      Sum.elim_inl, Sum.elim_inr,
      Sigma.forall, ContinuousAffineMap.neg_apply, neg_nonpos,
      ContinuousAffineMap.comp_apply, forall_and]
  rw [he]
  exact TauCeti.isConvexPolyhedron_setOf_forall rows

/-- If one strict realization exists, every weak realization is its limit along
a segment inside the support constraints. The nonemptiness hypothesis is essential. -/
theorem closure_backwardDomain {P : Fin n → Set V}
    (hclosed : ∀ i, IsClosed (P i)) (hconvex : ∀ i, Convex ℝ (P i))
    (hne : (backwardDomain f c v P).Nonempty) :
    closure (backwardDomain f c v P) = weakBackwardDomain f c v P := by
  apply Set.Subset.antisymm
  · exact closure_minimal (backwardDomain_subset_weakBackwardDomain f c v P)
      (isClosed_weakBackwardDomain f c v hclosed)
  · obtain ⟨p, hp⟩ := hne
    intro x hx
    have hs : openSegment ℝ x p ⊆ backwardDomain f c v P := by
      rintro y ⟨a, b, ha, hb, hab, rfl⟩ i
      constructor
      · have he : backwardTime f c v i (a • x + b • p) =
            a * backwardTime f c v i x + b * backwardTime f c v i p :=
          Convex.combo_affine_apply (f := (backwardTime f c v i).toAffineMap) hab
        rw [he]
        exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (hx i).1) (mul_pos hb (hp i).1)
      · have he : backwardPoint f c v i.succ (a • x + b • p) =
            a • backwardPoint f c v i.succ x + b • backwardPoint f c v i.succ p :=
          Convex.combo_affine_apply (f := (backwardPoint f c v i.succ).toAffineMap) hab
        rw [he]
        exact hconvex i (hx i).2 (hp i).2 ha.le hb.le hab
    exact closure_mono hs
      (segment_subset_closure_openSegment (left_mem_segment ℝ x p))

end Mei.Convex
