/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Comparison.Stable
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Comparison.Completion

/-!
# Intrinsic stable endpoints for completed weighted ray sums

The finite stable locus consists of allowed endpoints at which the actual total
weighted ray evaluation is locally constant. It depends on the actual sum, not
on a chosen exceptional arrangement, and includes type-domain frontier points
whenever cancellations make the sum locally constant. Each finite locus is open
and dense. Their all-order intersection is therefore a dense Gδ locus, which
need not be open. On this intrinsic locus the actual sums determine a unique
completed value and obey completed transport.

We use the finite endpoint extension from `Comparison.Stable`, the independent
finite comparison, and the existing completed probe field. Finite-comparison
arrangements are used only to prove density, never to define the public locus.
The incoming coefficient is fixed before taking the countable intersection.
No boundary admissibility or coefficient-uniform exceptional set is claimed.
The geometric interpretation follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Λ V E ι κ κ' : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D₀ : DirectedDiagram (d := d) h H ι) (a : ℳ p)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) ((ι ⊕ Unit) ⊕ κ))
  (B : DirectedDiagram (d := d) h H κ')


/-- Allowed endpoints where the actual weighted ray sum is locally constant.
This locus is intrinsic to the total evaluation, so cancellations can include
points on individual type-domain frontiers. -/
def stableWallEventLocus (K : ℕ) (b : (d.shiftedQuotientGrading ℳ p K).piece 0) : Set V :=
  {Q | (∀ c : B.active K, Q ∉ (B.wall c).support) ∧
    ∀ᶠ Q' in 𝓝 Q,
      cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl K) b univ Q' =
        cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl K) b univ Q}

omit [IsWallAnnihilating H ℳ] in
/-- The finite intrinsic stable locus is open, with no consistency or probe
hypotheses needed. -/
theorem isOpen_stableWallEventLocus (K : ℕ)
    (b : (d.shiftedQuotientGrading ℳ p K).piece 0) :
    IsOpen (stableWallEventLocus d ℳ p ℒ H h B K b) := by
  have hU : IsOpen {Q | ∀ c : B.active K, Q ∉ (B.wall c).support} := by
    simpa only [ofPred_forall, compl_def] using isOpen_iInter_of_finite
      (fun c : B.active K => (B.wall c).isConvexPolyhedron.isClosed.isOpen_compl)
  apply isOpen_iff_eventually.mpr
  intro Q hQ
  filter_upwards [hU.mem_nhds hQ.1, hQ.2, eventually_eventually_nhds.mpr hQ.2]
    with Q' hallow heq hnear
  exact ⟨hallow, hnear.mono fun Q'' h => h.trans heq.symm⟩


omit [IsWallAnnihilating H ℳ] in
/-- Among open sets of allowed endpoints, the intrinsic stable locus is maximal
for local constancy of the actual evaluation. This criterion includes stable
total sums even when individual decorated types change. -/
theorem subset_stableWallEventLocus_iff (K : ℕ)
    (b : (d.shiftedQuotientGrading ℳ p K).piece 0) (U : Set V) (hU : IsOpen U) :
    U ⊆ stableWallEventLocus d ℳ p ℒ H h B K b ↔
      (∀ Q ∈ U, ∀ c : B.active K, Q ∉ (B.wall c).support) ∧
      IsLocallyConstant (fun Q : U =>
        cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl K) b univ Q.val) := by
  constructor
  · intro hsub
    refine ⟨fun Q hQ => (hsub hQ).1, (IsLocallyConstant.iff_eventually_eq _).mpr ?_⟩
    intro Q
    exact (continuous_subtype_val.tendsto Q).eventually (hsub Q.property).2
  · rintro ⟨hallow, hlocal⟩ Q hQ
    refine ⟨hallow Q hQ, ?_⟩
    have heq := hlocal.eventually_eq (⟨Q, hQ⟩ : U)
    exact (hU.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨Q, hQ⟩).ge heq

variable
  (hinitial : ∀ c, D.wall (.inl c) =
    (initialDiagram d ℳ p ℒ H h h' D₀ a).wall c)
  (K : ℕ) (hBc : B.LevelConsistent K)
  (hD : D.LevelConsistent (K + 1))
  (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
    (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
    (cylinderDiagram d ℳ p ℒ H h h' B) K)
  (hout : ∀ n : d.cutoff K, ∀ c, Sum.inr c ∈ D.active (K + 1) →
    (p + n.val, 1) ∈ (D.wall (.inr c)).ray.rayDegrees →
      (D.wall (.inr c)).Outgoing)
  (b : (d.shiftedQuotientGrading ℳ p K).piece 0)

include hinitial hBc hD hB hout in
/-- The finite stable locus is dense. On the open finite-comparison generic
locus, equality with the locally constant probe field gives actual ambient
local constancy of the sum. -/
theorem dense_stableWallEventLocus
    (hb : d.shiftedQuotientComponent ℳ p p K (by simp) b = a) :
    Dense (stableWallEventLocus d ℳ p ℒ H h B K b) := by
  let := h.finiteDimensional
  obtain ⟨A, hA⟩ := exists_extendedCoefficientField_eq_cutoffWallEventEvaluation
    d ℳ p ℒ H h h' D₀ a D B hinitial K hBc hD hB hout b hb
  let G : Set V := {Q | ∀ n, (A n).IsGeneric Q}
  have hG : IsOpen G := by
    simpa only [G, ofPred_forall] using isOpen_iInter_of_finite
      (fun n => (A n).isOpen_isGeneric)
  apply (ExceptionalArrangement.dense_iInter_isGeneric A).mono
  intro Q hQ
  obtain ⟨hallow, heq⟩ := hA Q hQ
  refine ⟨hallow, ?_⟩
  let f : G → {Q // ∀ c : B.active K, Q ∉ (B.wall c).support} :=
    fun x => ⟨x.val, (hA x.val x.property).choose⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hlocal := (isLocallyConstant_extendedCoefficientField
    d ℳ p ℒ H h h' D B K hBc).eventually_eq (f ⟨Q, hQ⟩)
  have hp := (hf.tendsto ⟨Q, hQ⟩).eventually hlocal
  have hr : ∀ᶠ x : G in 𝓝 (⟨Q, hQ⟩ : G),
      cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl K) b univ x.val =
        cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl K) b univ Q := by
    filter_upwards [hp] with x hx
    exact (hA x.val x.property).choose_spec.symm.trans (hx.trans heq)
  exact (hG.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨Q, hQ⟩).ge hr


/-- The common intrinsic stable locus for a family of incoming coefficients.
Only actual allowedness and actual finite evaluation germs occur in this set. -/
def stableWallEventLocusAll
    (b : (k : ℕ) → (d.shiftedQuotientGrading ℳ p k).piece 0) : Set V :=
  ⋂ k, stableWallEventLocus d ℳ p ℒ H h B k (b k)

omit [IsWallAnnihilating H ℳ] in
/-- The intrinsic all-order locus is Gδ; it need not be open. -/
theorem isGδ_stableWallEventLocusAll
    (b : (k : ℕ) → (d.shiftedQuotientGrading ℳ p k).piece 0) :
    IsGδ (stableWallEventLocusAll d ℳ p ℒ H h B b) :=
  IsGδ.iInter fun k => (isOpen_stableWallEventLocus d ℳ p ℒ H h B k (b k)).isGδ

local notation "F" => d.shiftedFiltration ℳ p
local notation "action" => d.shiftedLieFiltration ℒ ℳ p

include hinitial in
/-- Every intrinsically stable all-order endpoint has a unique completed actual
ray value. The locus is dense Gδ independently of the auxiliary arrangements,
and completed transport holds between any two of its points. Coherence across
changing geometric inventories is a conclusion, not a hypothesis. -/
theorem exists_completedWallEventEvaluation_on_stableLocus
    (hBc : B.Consistent) (hD : D.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B))
    (hout : ∀ K, ∀ n : d.cutoff K, ∀ c, Sum.inr c ∈ D.active (K + 1) →
      (p + n.val, 1) ∈ (D.wall (.inr c)).ray.rayDegrees → (D.wall (.inr c)).Outgoing)
    (b : (k : ℕ) → (d.shiftedQuotientGrading ℳ p k).piece 0)
    (hb : ∀ k, d.shiftedQuotientComponent ℳ p p k (by simp) (b k) = a) :
    Dense (stableWallEventLocusAll d ℳ p ℒ H h B b) ∧
    ∃ (point : stableWallEventLocusAll d ℳ p ℒ H h B b → B.Point)
      (Θ : stableWallEventLocusAll d ℳ p ℒ H h B b → (F).completion),
      (∀ Q, (point Q).val = Q.val) ∧
      (∀ Q k, (F).projection k (Θ Q) =
        cutoffWallEventEvaluation d ℳ p ℒ H h B k k (Nat.le_refl k) (b k) univ Q.val) ∧
      (∀ Q Ψ, (∀ k, (F).projection k Ψ =
        cutoffWallEventEvaluation d ℳ p ℒ H h B k k (Nat.le_refl k) (b k) univ Q.val) →
        Ψ = Θ Q) ∧
      (∀ Q, Θ Q = completedExtendedCoefficientField d ℳ p ℒ H h h' D B
        hD hBc hB (point Q)) ∧
      (∀ Q Q', Θ Q' = (action).completedBCHAction d ℒ
        (B.transport hBc (point Q) (point Q')) (Θ Q)) := by
  let := h.finiteDimensional
  have hBk (k : ℕ) := (B.consistent_iff.mp hBc) k
  have hDk (k : ℕ) := (D.consistent_iff.mp hD) (k + 1)
  have hBk' (k : ℕ) := (DirectedDiagram.equivalent_iff _ _).mp hB k
  refine ⟨dense_iInter_of_isOpen
    (fun k => isOpen_stableWallEventLocus d ℳ p ℒ H h B k (b k))
    (fun k => dense_stableWallEventLocus d ℳ p ℒ H h h' D₀ a D B hinitial
      k (hBk k) (hDk k) (hBk' k) (hout k) (b k) (hb k)), ?_⟩
  let Ω := stableWallEventLocusAll d ℳ p ℒ H h B b
  have hstable (Q : Ω) (k : ℕ) := Set.mem_iInter.mp Q.property k
  let point (Q : Ω) : B.Point := ⟨Q.val, fun k => (hstable Q k).1⟩
  have hvalue (Q : Ω) (k : ℕ) :
      extendedCoefficientField d ℳ p ℒ H h h' D B k (hBk k)
        (CommonWallComplement.projection k (point Q)) =
      cutoffWallEventEvaluation d ℳ p ℒ H h B k k (Nat.le_refl k) (b k) univ Q.val :=
    extendedCoefficientField_eq_cutoffWallEventEvaluation_of_eventually_eq
      d ℳ p ℒ H h h' D₀ a D B hinitial k (hBk k) (hDk k) (hBk' k)
      (hout k) (b k) (hb k) (CommonWallComplement.projection k (point Q)) (hstable Q k).2
  obtain ⟨Θ, _, hprojection, hunique, hcompleted, htransport⟩ :=
    exists_completedWallEventEvaluation_of_eq d ℳ p ℒ H h h' D B b hBc hD hB point hvalue
  exact ⟨point, Θ, fun _ => rfl, hprojection, hunique, hcompleted, htransport⟩

end Mei.ModuleProbe
