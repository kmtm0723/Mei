/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Group
public import Mei.Algebra.Lie.Logarithmic.WallFunction

/-!
# Supported-ray factors of tropical function walls

Fix an integral normal `n` and a completed coefficient `u` on the allowed degrees tangent
to `n`. The completed tropical vertex label `exp(u ∂_n)` is not a wall label in general:
its logarithm `u ∂_n` has terms `u_q z^q ∂_n` in tangent degrees `q` on many different
supported rays. Every such term lies in the tropical vertex wall space of `q` and `n`.
Hence the ray factors of the label (`Mei.PositiveDegrees.rayFactor`) are wall labels on
their supported rays with normal `n`, all of them commute, and at every order the label is
the unordered product of its ray factors. For `u = log f`, these are the supported-ray
walls `exp((log f)_w ∂_n)` presenting the function wall of `f`, whose action multiplies
`z^p` by `f^{n(ρ p)}`
(`Mei.completedBCHAction_completedBCHExp_completedTropicalTangentField_completedLog`).
If `f` is a polynomial supported on a submonoid `S` of the tangent degrees, then so is every
truncation of `log f`; hence the label has no logarithmic coefficient outside `S`
(`Mei.logComponent_completedBCHExp_completedTropicalTangentField_completedLog_eq_zero`), and a
ray factor surviving the cutoff `k` has a degree of `S` of order at most `k` on its ray
(`Mei.exists_mem_rayDegrees_of_projection_rayFactor_ne_one`). These control the directions
and the finite activity of the ray walls of polynomial function walls.

No condition on the coefficient ring beyond being a `ℚ`-algebra is imposed, and degrees of
zero spatial direction are allowed. The splitting of wall functions into supported-ray
factors follows Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
§1.1, arXiv:1411.1394v2, and Burcroff–Lee–Mou, *Positivity of generalized cluster
scattering diagrams*, §9.2, arXiv:2503.03719v1.
-/

public section

noncomputable section

namespace Mei

open _root_.AddMonoidAlgebra

variable {R Γ Λ : Type*} [CommRing R] [Algebra ℚ R] [AddCommMonoid Λ]

section Monoid

variable [AddCommMonoid Γ]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (n : Λ →+ ℤ)

local notation "χ" => AddMonoidHom.comp (Int.castAddHom R) n
local notation "T" => tropicalTangentMonoid d ρ χ
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d T
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

/-- The tangent field of a tangent monomial `c z^q` lies in the wall space of `q` and `n`. -/
theorem tropicalTangentField_single_mem_wall (q : T) (c : R) :
    tropicalTangentField d ρ χ (single q c) ∈ (H).wall q n := by
  by_cases hq : (q : Γ) = 0
  · rw [show q = 0 from Subtype.ext hq, tropicalTangentField_single_zero]
    exact zero_mem _
  rw [mem_tropicalVertexWallSpaces_iff, coe_tropicalTangentField_single d ρ χ hq, map_smul]
  by_cases hn : n (ρ q) = 0
  · exact (LogarithmicVectorField.mem_wallSubmodule_iff ρ _ n hn _).mpr ⟨c, rfl⟩
  -- A nonzero integer vanishes in `R` only when the `ℚ`-algebra `R` is trivial.
  have hcast : ((n (ρ q) : ℤ) : R) = 0 := ((mem_tropicalTangentMonoid d ρ χ q).mp q.2).2
  have h10 : (1 : R) = 0 := by
    have h := congrArg (algebraMap ℚ R ((n (ρ q) : ℚ)⁻¹) * ·) hcast
    rwa [mul_zero, ← map_intCast (algebraMap ℚ R), ← map_mul,
      inv_mul_cancel₀ (by exact_mod_cast hn), map_one] at h
  have : Subsingleton R := subsingleton_of_zero_eq_one h10.symm
  have := Module.subsingleton R (LogarithmicVectorField R Γ Λ ρ)
  rw [Subsingleton.elim (c • LogarithmicVectorField.single ρ (q : Γ) χ) 0]
  exact zero_mem _

/-- Every homogeneous component of a tangent field lies in the wall space of its degree. -/
theorem decompose_tropicalTangentField_mem_wall (v : R[T]) (q : Γ) :
    (DirectSum.decompose ℒ (tropicalTangentField d ρ χ v) q : tropicalVertexLieAlgebra d ρ) ∈
      (H).wall q n := by
  induction v using induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
    exact add_mem ha hb
  | single t c =>
    have ht := tropicalTangentField_single_mem_wall d ρ n t c
    by_cases htq : (t : Γ) = q
    · subst htq
      rw [DirectSum.decompose_of_mem_same ℒ (((H).wall_le_piece _ _) ht)]
      exact ht
    · rw [DirectSum.decompose_of_mem_ne ℒ (((H).wall_le_piece _ _) ht) htq]
      exact zero_mem _

/-- The homogeneous component of a tangent field in a tangent degree `q` is the tangent field of
the coefficient of `q`. -/
theorem decompose_tropicalTangentField_apply (v : R[T]) (q : T) :
    (DirectSum.decompose ℒ (tropicalTangentField d ρ χ v) (q : Γ) :
      tropicalVertexLieAlgebra d ρ) = tropicalTangentField d ρ χ (single q (v.coeff q)) := by
  induction v using induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, ha, hb,
      coeff_add, Finsupp.add_apply, single_add]
  | single t c =>
    have ht := ((H).wall_le_piece _ _) (tropicalTangentField_single_mem_wall d ρ n t c)
    by_cases htq : t = q
    · subst htq
      rw [DirectSum.decompose_of_mem_same ℒ ht, coeff_single, Finsupp.single_eq_same]
    · rw [DirectSum.decompose_of_mem_ne ℒ ht (fun h => htq (Subtype.ext h)), coeff_single,
        Finsupp.single_eq_of_ne' htq, single_zero, map_zero]

/-- In a degree of order at most `k`, the logarithmic coefficient of a completed tangent label
`exp(u ∂_n)` is the homogeneous component of the tangent field of any representative `v` of the
order-`k` truncation of `u`. -/
theorem logComponent_completedBCHExp_completedTropicalTangentField_eq_decompose
    (u : (G).completion) {k : ℕ} {v : R[T]} (hv : (G).projection k u = Ideal.Quotient.mk _ v)
    {q : Γ} (hq : d.degree q ≤ k) :
    d.logComponent ℒ (d.completedBCHExp ℒ (completedTropicalTangentField d ρ χ u)) q =
      DirectSum.decompose ℒ (tropicalTangentField d ρ χ v) q :=
  d.logComponent_eq_decompose ℒ _ hq (x := tropicalTangentField d ρ χ v) (by
    rw [PositiveDegrees.projection_completedBCHExp, BCHGroup.log_exp,
      completionProjection_completedTropicalTangentField d ρ χ _ u v hv])

/-- The logarithmic coefficients of a completed tangent label `exp(u ∂_n)` lie in the
wall spaces of their degrees and the normal `n`. -/
theorem logComponent_completedBCHExp_completedTropicalTangentField_mem_wall
    (u : (G).completion) (q : Γ) :
    (d.logComponent ℒ (d.completedBCHExp ℒ (completedTropicalTangentField d ρ χ u)) q :
      tropicalVertexLieAlgebra d ρ) ∈ (H).wall q n := by
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective ((G).projection (d.degree q).toNat u)
  rw [logComponent_completedBCHExp_completedTropicalTangentField_eq_decompose d ρ n u hv.symm
    (Int.self_le_toNat _)]
  exact decompose_tropicalTangentField_mem_wall d ρ n v q

/-- If the completed coefficient is the completion of a polynomial `g` supported on a
submonoid `S` of the tangent degrees, the label `exp(log(g) ∂_n)` has no logarithmic
coefficient outside `S`: at every order the logarithm of `g` is a polynomial in `g - 1`. -/
theorem logComponent_completedBCHExp_completedTropicalTangentField_completedLog_eq_zero
    (S : AddSubmonoid T) {g : R[T]} (f : R[S]) (hfg : mapDomainRingHom R S.subtype f = g)
    (hg : (G).toCompletion g - 1 ∈ (G).completionIdeal 1) {q : Γ}
    (hq : ∀ t : S, ((t : T) : Γ) ≠ q) :
    d.logComponent ℒ (d.completedBCHExp ℒ (completedTropicalTangentField d ρ χ
      ((G).completedLog ⟨(G).toCompletion g, hg⟩))) q = 0 := by
  classical
  let inc := mapDomainRingHom R S.subtype
  let k := (d.degree q).toNat
  obtain ⟨m, hm⟩ := (G).isNilpotent_projection hg k
  let v : R[S] := ∑ a ∈ Finset.range m, ((-1 : ℚ) ^ (a + 1) / a) • (f - 1) ^ a
  have hv : (G).projection k ((G).completedLog ⟨(G).toCompletion g, hg⟩) =
      Ideal.Quotient.mk _ (inc v) := by
    rw [AlgFiltration.projection_completedLog, IsNilpotent.log_eq_sum (by
      simpa only [map_sub, map_one] using hm)]
    simp only [v, inc, map_sum, map_rat_smul, map_pow, map_sub, map_one, hfg,
      AlgFiltration.projection_toCompletion]
  rw [logComponent_completedBCHExp_completedTropicalTangentField_eq_decompose d ρ n _ hv
    (Int.self_le_toNat _)]
  have hzero (v : R[S]) :
      (DirectSum.decompose ℒ (tropicalTangentField d ρ χ (inc v)) q :
        tropicalVertexLieAlgebra (R := R) d ρ) = 0 := by
    induction v using induction_linear with
    | zero => simp
    | add a b ha hb => simp [map_add, ha, hb]
    | single t c =>
      simp only [inc, mapDomainRingHom_apply, mapDomain_single, AddSubmonoid.subtype_apply]
      exact DirectSum.decompose_of_mem_ne ℒ
        ((H).wall_le_piece _ _ (tropicalTangentField_single_mem_wall d ρ n t.val c)) (hq t)
  exact Subtype.ext (hzero v)

end Monoid

section Group

variable [AddCommGroup Γ] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (n : Λ →+ ℤ)

local notation "χ" => AddMonoidHom.comp (Int.castAddHom R) n
local notation "T" => tropicalTangentMonoid d ρ χ
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d T
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

/-- The ray factors of a completed tangent label `exp(u ∂_n)` are wall labels with
normal `n`. For nontangent rays these wall groups are trivial. -/
@[simp high]
theorem rayFactor_completedBCHExp_completedTropicalTangentField_mem_wallGroup
    (u : (G).completion) (w : SupportedRay d) :
    d.rayFactor ℒ (d.completedBCHExp ℒ (completedTropicalTangentField d ρ χ u)) w ∈
      (H).wallGroup w n :=
  (H).rayFactor_mem_wallGroup fun q _ =>
    logComponent_completedBCHExp_completedTropicalTangentField_mem_wall d ρ n u q

/-- A completed tangent label `exp(u ∂_n)` has trivial ray factors on the supported rays
whose geometric direction is not annihilated by `n`. -/
@[simp]
theorem rayFactor_completedBCHExp_completedTropicalTangentField_eq_one
    (u : (G).completion) {w : SupportedRay d} (hw : n (ρ w.generator) ≠ 0) :
    d.rayFactor ℒ (d.completedBCHExp ℒ (completedTropicalTangentField d ρ χ u)) w = 1 := by
  have h := rayFactor_completedBCHExp_completedTropicalTangentField_mem_wallGroup d ρ n u w
  rwa [(H).wallGroup_eq_bot_of_normal_ne_zero hw, Subgroup.mem_bot] at h

/-- At every order, a completed tangent label `exp(u ∂_n)` is the unordered product of
its ray factors over any finite set of supported rays containing those meeting the
cutoff. -/
theorem projection_completedBCHExp_completedTropicalTangentField_eq_noncommProd_rayFactor
    [Module.Free ℤ Γ] (u : (G).completion) (k : ℕ) (s : Finset (SupportedRay d))
    (hs : d.raysAtOrder k ⊆ s) :
    CompletedGroup.projection k (d.completedBCHExp ℒ (completedTropicalTangentField d ρ χ u)) =
      s.noncommProd (fun w => CompletedGroup.projection k
        (d.rayFactor ℒ (d.completedBCHExp ℒ (completedTropicalTangentField d ρ χ u)) w))
        (fun v _ w _ _ => (d.commute_rayFactor (fun q q' => (H).lie_eq_zero_of_same_normal
          (logComponent_completedBCHExp_completedTropicalTangentField_mem_wall d ρ n u q)
          (logComponent_completedBCHExp_completedTropicalTangentField_mem_wall d ρ n u q'))
            v w).map _) :=
  d.projection_eq_noncommProd_rayFactor (fun q q' => (H).lie_eq_zero_of_same_normal
    (logComponent_completedBCHExp_completedTropicalTangentField_mem_wall d ρ n u q)
    (logComponent_completedBCHExp_completedTropicalTangentField_mem_wall d ρ n u q')) k s hs

/-- A completed label with a nontrivial order-`k` projection has a nonzero logarithmic
coefficient in some degree of order at most `k`. -/
private theorem exists_logComponent_ne_zero_of_projection_ne_one
    {g : d.completedBCHGroup ℒ} {k : ℕ} (hg : CompletedGroup.projection k g ≠ 1) :
    ∃ q, d.degree q ≤ k ∧ d.logComponent ℒ g q ≠ 0 := by
  by_contra! h0
  apply hg
  rw [← BCHGroup.exp_log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g),
    d.log_projection_eq_mkQ_sum ℒ g k, Finset.sum_eq_zero fun q hq => by
      rw [h0 q (d.mem_cutoff.mp ((d.finite_cutoff k).mem_toFinset.mp hq)).2,
        ZeroMemClass.coe_zero], map_zero]
  exact BCHGroup.exp_zero

/-- If the completed coefficient is the completion of a polynomial supported on a submonoid
`S` of the tangent degrees, a ray factor of `exp(log(g) ∂_n)` that survives the cutoff `k`
has a degree of `S` on its ray of order at most `k`. -/
theorem exists_mem_rayDegrees_of_projection_rayFactor_ne_one
    (S : AddSubmonoid T) {g : R[T]} (f : R[S]) (hfg : mapDomainRingHom R S.subtype f = g)
    (hg : (G).toCompletion g - 1 ∈ (G).completionIdeal 1) {w : SupportedRay d} {k : ℕ}
    (hw : CompletedGroup.projection k (d.rayFactor ℒ (d.completedBCHExp ℒ
      (completedTropicalTangentField d ρ χ ((G).completedLog ⟨(G).toCompletion g, hg⟩))) w) ≠
        1) :
    ∃ t : S, ((t : T) : Γ) ∈ w.rayDegrees ∧ d.degree ((t : T) : Γ) ≤ k := by
  obtain ⟨q, hqk, hq⟩ := exists_logComponent_ne_zero_of_projection_ne_one d ρ hw
  have hqw : q ∈ w.rayDegrees := by
    by_contra h
    exact hq (d.logComponent_rayFactor_of_notMem ℒ _ h)
  rw [d.logComponent_rayFactor_of_mem ℒ _ hqw] at hq
  obtain ⟨t, rfl⟩ : ∃ t : S, ((t : T) : Γ) = q := by
    by_contra! h
    exact hq (logComponent_completedBCHExp_completedTropicalTangentField_completedLog_eq_zero
      d ρ n S f hfg hg h)
  exact ⟨t, hqw, hqk⟩

end Group

end Mei
