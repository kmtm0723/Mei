/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Linear
public import Mei.Geometry.ScatteringDiagram.Coefficient.Linear.LocallyConstant

/-!
# Generic cutoff ray evaluations as coefficient sections

`cutoffDecoratedEvaluationLinearMap` is locally constant away from one
finite exceptional arrangement, uniformly over incoming coefficients. On any
off-wall open consisting of generic points, it therefore defines a linear map
into `coefficientLocalSystem`. Its values are `cutoffDecoratedEvaluation`, summed over
actual decorated rays, with their incoming tails and endpoint admission retained.

These are top-stratum section maps for facet descent. No extension across the
exceptional arrangement or coefficient faces is asserted here: such an extension
requires the corresponding resolution identities and common face lifts.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite Topology Set TopCat Mei.Convex

namespace Mei.FiniteWallDiagram

variable {N V G Γ R M E J K : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {i : N →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i} {C : FinitePolyhedralComplex h}
  [Group G] (D : FiniteWallDiagram C G) [Semiring R] [AddCommMonoid M]
  [DistribMulAction G M] [Module R M] [SMulCommClass G R M]
  [AddCommMonoid E] [Module R E] [AddCommGroup Γ] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (T : J → Module.End R M) (w : Γ → N) [Finite J] [Finite K]
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P W : J → Set V) (S : K → Set V) (A : Set V)
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hA : IsRationalNormalPolyhedron h A)

include hf hP hW hS hA in
/-- One exceptional arrangement supplies actual coefficient-section maps for
every generic off-wall open and every incoming linear parameter map. The
arrangement is independent of the input and of the open. Values are
`cutoffDecoratedEvaluation`, including rays that bend outside the open. -/
theorem exists_cutoffDecoratedEvaluation_sections (k : ℕ) :
    ∃ 𝒜 : ExceptionalArrangement V, ∀ (U : Opens C.regularSpace)
      (_ : (U : Set C.regularSpace) ⊆ C.coefficientPoints),
      (∀ x ∈ U, 𝒜.IsGeneric x.val) → ∀ α : E →ₗ[R] ℳ 0,
      ∃! t : E →ₗ[R] (D.coefficientLocalSystem M).presheaf.obj (op U),
        ∀ a (x : C.coefficientPoints) (hx : x.val ∈ U),
          (D.coefficientTransport M).value (t a) x hx =
            cutoffDecoratedEvaluation d ℳ T (α a) (fun q => i (w q))
              f c ε P W S A k x.val.val := by
  obtain ⟨𝒜, h𝒜⟩ := exists_cutoffDecoratedEvaluationLinearMap_eventually_eq
    d ℳ T f c ε P W S A h w hf hP hW hS hA k
  refine ⟨𝒜, fun U hoff hgen α => ?_⟩
  let F (Q : V) : E →ₗ[R] M :=
    (cutoffDecoratedEvaluationLinearMap d ℳ T (fun q => i (w q)) f c ε P W S A k Q).comp α
  have hval : Continuous (fun x : U => x.val.val : U → V) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hF (x : U) : ∀ᶠ y in nhds x, F y.val.val = F x.val.val :=
    (hval.tendsto x).eventually ((h𝒜 x.val.val (hgen x.val x.property)).mono
      fun Q he => congrArg (fun l : ℳ 0 →ₗ[R] M => l.comp α) he)
  let g : LocallyConstant U (E →ₗ[R] M) :=
    ⟨fun x => F x.val.val, (IsLocallyConstant.iff_eventually_eq _).mpr hF⟩
  refine ⟨D.locallyConstantCoefficientSections hoff g, ?_, ?_⟩
  · intro a x hx
    exact (D.value_locallyConstantCoefficientSections hoff g a x hx).trans
      (cutoffDecoratedEvaluationLinearMap_apply d ℳ T (fun q => i (w q))
        f c ε P W S A k x.val.val (α a))
  · intro t ht
    apply LinearMap.ext
    intro a
    apply (D.coefficientTransport M).section_ext
    intro x hx
    calc
      (D.coefficientTransport M).value (t a) x hx =
          cutoffDecoratedEvaluation d ℳ T (α a) (fun q => i (w q))
            f c ε P W S A k x.val.val := ht a x hx
      _ = g ⟨x.val, hx⟩ a :=
        (cutoffDecoratedEvaluationLinearMap_apply d ℳ T (fun q => i (w q))
          f c ε P W S A k x.val.val (α a)).symm
      _ = (D.coefficientTransport M).value
          (D.locallyConstantCoefficientSections hoff g a) x hx :=
        (D.value_locallyConstantCoefficientSections hoff g a x hx).symm

end Mei.FiniteWallDiagram
