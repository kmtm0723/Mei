/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Manifold.IntegralAffine.ExponentSystem
public import Mei.Geometry.ScatteringDiagram.FocusFocus.LocalSystem

/-!
# The exponent system of the focus-focus puncture

The integral-affine atlas of the punctured plane (`Mei.FocusFocus.chartedSpace`) has two
charts, indexed by `atlasIndex`: `false` for the cut chart and `true` for the upper chart. On
the left half of their overlap the chart change is the shear `(u, v) ↦ (u, v - u)`, and on the
right half it is the identity. Hence the tangent frame changes of the atlas are the
`upperTangent` transitions of `tangentLatticeBundleCore`
(`tangentLatticeChange_eq_latticeTransition`): the tangent lattice local system specified for
the focus-focus model is the canonical one of its integral-affine structure.

The rank-three exponent lattice with the `upperExponent` transitions and the projection
`exponentProjection` forgetting the smoothing exponent is therefore an exponent system on the
punctured plane (`Mei.FocusFocus.exponentSystem`), whose frame changes are those of
`exponentBundleCore`.

The geometry is the focus-focus local model of Gross–Siebert, *An Invitation to Toric
Degenerations*, §2.2–2.3 (arXiv:0808.2749v2).
-/

public section

open Set Topology Manifold

namespace Mei.FocusFocus

attribute [local instance] chartedSpace hasGroupoid

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The cut chart and the upper chart are different charts. -/
theorem cutChart_ne_upperChart : cutChart ≠ upperChart := by
  intro he
  have hp : (⟨(1, 0), by simp⟩ : regularLocus) ∈ upperChart.source := by
    rw [← he, mem_cutChart_source]
    norm_num
  rw [mem_upperChart_source] at hp
  exact lt_irrefl _ hp

/-- A point in the domains of both charts lies off the vertical axis. -/
theorem fst_ne_zero_of_mem_source {p : regularLocus} (hc : p ∈ cutChart.source)
    (hu : p ∈ upperChart.source) : p.val.1 ≠ 0 :=
  ((mem_cutChart_source p).mp hc).resolve_right
    (not_lt.mpr ((mem_upperChart_source p).mp hu).le)

/-- The index of a chart of the focus-focus atlas in the frames of the lattice local systems:
`true` for the upper chart and `false` for the cut chart. -/
noncomputable def atlasIndex (e : atlas (ℝ × ℝ) regularLocus) : Bool :=
  @decide (e.1 = upperChart) (Classical.propDecidable _)

/-- The upper chart has index `true`. -/
theorem atlasIndex_eq_true_iff (e : atlas (ℝ × ℝ) regularLocus) :
    atlasIndex e = true ↔ e.1 = upperChart :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

/-- The cut chart has index `false`. -/
theorem atlasIndex_eq_false_iff (e : atlas (ℝ × ℝ) regularLocus) :
    atlasIndex e = false ↔ e.1 = cutChart := by
  rw [← Bool.not_eq_true, atlasIndex_eq_true_iff]
  rcases (mem_atlas_iff e.1).mp e.2 with he | he <;> rw [he]
  · exact iff_of_true cutChart_ne_upperChart rfl
  · exact iff_of_false (not_not.mpr rfl) cutChart_ne_upperChart.symm

/-- The chart of the focus-focus atlas with a given index. -/
theorem eq_of_atlasIndex (e : atlas (ℝ × ℝ) regularLocus) :
    e.1 = if atlasIndex e then upperChart else cutChart := by
  cases he : atlasIndex e
  · exact (atlasIndex_eq_false_iff e).mp he
  · exact (atlasIndex_eq_true_iff e).mp he

/-- Charts of the focus-focus atlas are determined by their index. -/
theorem atlasIndex_injective : Function.Injective atlasIndex := by
  intro e e' he
  exact Subtype.ext ((eq_of_atlasIndex e).trans (he ▸ (eq_of_atlasIndex e').symm))

/-- A point in the domains of two charts with different indices lies off the vertical axis. -/
theorem fst_ne_zero_of_atlasIndex_ne {e e' : atlas (ℝ × ℝ) regularLocus}
    (hee : atlasIndex e ≠ atlasIndex e') {p : regularLocus}
    (hp : p ∈ e.1.source ∩ e'.1.source) : p.val.1 ≠ 0 := by
  cases he : atlasIndex e <;> cases he' : atlasIndex e' <;> rw [he, he'] at hee
  · exact absurd rfl hee
  · rw [(atlasIndex_eq_false_iff e).mp he, (atlasIndex_eq_true_iff e').mp he'] at hp
    exact fst_ne_zero_of_mem_source hp.1 hp.2
  · rw [(atlasIndex_eq_true_iff e).mp he, (atlasIndex_eq_false_iff e').mp he'] at hp
    exact fst_ne_zero_of_mem_source hp.2 hp.1
  · exact absurd rfl hee

/-- On the overlap of two charts, the change of lattice frames is locally constant. -/
theorem eventually_latticeTransition_eq {F : Type*} [AddCommGroup F] (σ : F ≃+ F)
    {e e' : atlas (ℝ × ℝ) regularLocus} {p : regularLocus}
    (hp : p ∈ e.1.source ∩ e'.1.source) :
    ∀ᶠ q in 𝓝 p, latticeTransition σ (atlasIndex e) (atlasIndex e') q =
      latticeTransition σ (atlasIndex e) (atlasIndex e') p := by
  by_cases hee : atlasIndex e = atlasIndex e'
  · simp only [hee, latticeTransition_self, Filter.eventually_true]
  have hc : Continuous fun q : regularLocus => q.val.1 :=
    continuous_fst.comp continuous_subtype_val
  rcases lt_or_gt_of_ne (fst_ne_zero_of_atlasIndex_ne hee hp) with hx | hx
  · filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hx] with q hq
    have hq' : q.val.1 < 0 := hq
    simp only [latticeTransition, hee, ↓reduceIte, hq', hx]
  · filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hx] with q hq
    have hq' : 0 < q.val.1 := hq
    simp only [latticeTransition, hee, ↓reduceIte, not_lt.mpr hq'.le, not_lt.mpr hx.le]

/-- On the overlap, the tangent frame changes of the focus-focus atlas are the transitions
of `tangentLatticeBundleCore`: the upper shear `upperTangent` on the left half and the
identity on the right half. -/
theorem tangentLatticeChange_eq_latticeTransition {e e' : atlas (ℝ × ℝ) regularLocus}
    {p : regularLocus} (hp : p ∈ e.1.source ∩ e'.1.source) :
    Toric.tangentLatticeChange h e e' p =
      latticeTransition upperTangent.toAddEquiv (atlasIndex e) (atlasIndex e') p := by
  -- The change from the cut chart to the upper chart.
  have hcu {e e' : atlas (ℝ × ℝ) regularLocus} (he : e.1 = cutChart) (he' : e'.1 = upperChart)
      {p : regularLocus} (hp : p ∈ e.1.source ∩ e'.1.source) :
      Toric.tangentLatticeChange h e e' p =
        latticeTransition upperTangent.toAddEquiv false true p := by
    have hx := fst_ne_zero_of_mem_source (he ▸ hp.1) (he' ▸ hp.2)
    rcases lt_or_gt_of_ne hx with hx | hx
    · rw [Toric.tangentLatticeChange_eq hp (isOpen_lt continuous_fst continuous_const)
        (by rw [he, cutChart_apply]; exact hx)
        (by simpa only [he, he'] using eqOn_cutChart_symm_trans_upperChart_upperAffine h),
        upperAffine_latticeEquiv]
      simp only [latticeTransition, hx, Bool.false_eq_true, ↓reduceIte]
    · rw [Toric.tangentLatticeChange_eq hp (isOpen_lt continuous_const continuous_fst)
        (by rw [he, cutChart_apply]; exact hx)
        (by simpa only [he, he'] using eqOn_cutChart_symm_trans_upperChart_refl h),
        Toric.IntegralAffineEquiv.refl_latticeEquiv]
      simp only [latticeTransition, not_lt.mpr hx.le, Bool.false_eq_true, ↓reduceIte]
  cases he : atlasIndex e <;> cases he' : atlasIndex e'
  · rw [atlasIndex_injective (he.trans he'.symm), Toric.tangentLatticeChange_self hp.2,
      latticeTransition_self]
  · exact hcu ((atlasIndex_eq_false_iff e).mp he) ((atlasIndex_eq_true_iff e').mp he') hp
  · rw [Toric.tangentLatticeChange_symm ⟨hp.2, hp.1⟩,
      hcu ((atlasIndex_eq_false_iff e').mp he') ((atlasIndex_eq_true_iff e).mp he) ⟨hp.2, hp.1⟩,
      latticeTransition_symm]
  · rw [atlasIndex_injective (he.trans he'.symm), Toric.tangentLatticeChange_self hp.2,
      latticeTransition_self]

/-- The tangent frame changes of the focus-focus atlas are the coordinate changes of
`tangentLatticeBundleCore`. -/
theorem tangentLatticeChange_apply {e e' : atlas (ℝ × ℝ) regularLocus} {p : regularLocus}
    (hp : p ∈ e.1.source ∩ e'.1.source) (q : ℤ × ℤ) :
    Toric.tangentLatticeChange h e e' p q =
      tangentLatticeBundleCore.coordChange (atlasIndex e) (atlasIndex e') p q := by
  rw [tangentLatticeChange_eq_latticeTransition h hp,
    tangentLatticeBundleCore_coordChange_eq_latticeTransition]

/-- The exponent system of the focus-focus puncture: the rank-three exponent lattice with the
`upperExponent` frame changes, projected to the integral tangent lattice by
`exponentProjection`. -/
noncomputable def exponentSystem : Toric.ExponentSystem h regularLocus (ℤ × ℤ × ℤ) where
  coordChange e e' := latticeTransition upperExponent.toAddEquiv (atlasIndex e) (atlasIndex e')
  coordChange_trans _ := AddEquiv.ext fun q => latticeTransition_comp _ _ _ _ _ q
  eventually_coordChange_eq hp := eventually_latticeTransition_eq _ hp
  projection _ := exponentProjection.toAddMonoidHom
  projection_coordChange {e e' p} hp q := by
    rw [LinearMap.toAddMonoidHom_coe, tangentLatticeChange_apply h hp,
      ← exponentBundleCore_coordChange_eq_latticeTransition]
    exact exponentProjection_coordChange _ _ _ _

/-- The frame changes of the focus-focus exponent system are the `upperExponent`
transitions. -/
@[simp]
theorem exponentSystem_coordChange (e e' : atlas (ℝ × ℝ) regularLocus) :
    (exponentSystem h).coordChange e e' =
      latticeTransition upperExponent.toAddEquiv (atlasIndex e) (atlasIndex e') := (rfl)

/-- The focus-focus exponent system projects by forgetting the smoothing exponent. -/
@[simp]
theorem exponentSystem_projection (e : atlas (ℝ × ℝ) regularLocus) :
    (exponentSystem h).projection e = exponentProjection.toAddMonoidHom := (rfl)

/-- The frame changes of the focus-focus exponent system are the coordinate changes of
`exponentBundleCore`. -/
theorem exponentSystem_coordChange_apply (e e' : atlas (ℝ × ℝ) regularLocus) (p : regularLocus)
    (q : ℤ × ℤ × ℤ) :
    (exponentSystem h).coordChange e e' p q =
      exponentBundleCore.coordChange (atlasIndex e) (atlasIndex e') p q := by
  rw [exponentSystem_coordChange, exponentBundleCore_coordChange_eq_latticeTransition]

end Mei.FocusFocus
