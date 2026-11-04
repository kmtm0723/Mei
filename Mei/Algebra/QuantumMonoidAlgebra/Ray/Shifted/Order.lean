/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.Basic
public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Order

/-!
# Shifted quantum ray actions raise relative order

On every translate of the positive monoid, subtracting the identity from a ray
action increases relative order by at least one. The origin may have negative
degree, and the acting unit series need not have constant coefficient one.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)

private local instance : Ring (positiveSubalgebra q β d.monoid) := inferInstance
private local instance : Algebra R (positiveSubalgebra q β d.monoid) := inferInstance
private local instance : Ring (F).completion := inferInstance
private local instance : AddCommGroup (F).completion :=
  (inferInstance : Ring (F).completion).toAddCommGroup
private local instance : Sub (F).completion := ⟨(inferInstance : Ring (F).completion).sub⟩
private local instance : Algebra R (F).completion := inferInstance
private local instance : Module R (F).completion := inferInstance
private local instance (p : Γ) : AddCommGroup (d.ShiftedCoefficients (grade q β) p) := inferInstance
private local instance (p : Γ) : Module R (d.ShiftedCoefficients (grade q β) p) := inferInstance

private theorem shiftedRayAction_sub_mem_coordinates (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) (k : ℕ)
    {b : (F).completion} (hb : b ∈ (F).completionIdeal k) :
    shiftedRayAction q β d n hn p H (positiveCompletionShiftEquiv q β d p b) -
        positiveCompletionShiftEquiv q β d p b ∈
      (d.shiftedFiltration (grade q β) p).completedFiltration.submodule (k + 1) := by
  let e := positiveCompletionShiftEquiv q β d p
  let x := completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn
  let c : R := ((q ^ (β n p - β p n) : Rˣ) : R)
  have hd := (F).completedTwistedSeriesAction_sub_mem x c H k hb
  have hmap := (positiveCompletionShiftEquiv_mem_iff q β d p (k + 1)
    ((F).completedTwistedSeriesAction x c H b - b)).mpr hd
  have hc : shiftedRayAction q β d n hn p H (e b) =
      e ((F).completedTwistedSeriesAction x c H b) := by
    simpa only [AlgFiltration.completedTwistedSeriesAction_apply] using
      shiftedRayAction_coordinates_skew q β d n hn p H b
  have heq : e ((F).completedTwistedSeriesAction x c H b - b) =
      shiftedRayAction q β d n hn p H (e b) - e b :=
    (e.map_sub _ _).trans (congrArg (fun u => u - e b) hc.symm)
  change e ((F).completedTwistedSeriesAction x c H b - b) ∈
    (d.shiftedFiltration (grade q β) p).completedFiltration.submodule (k + 1) at hmap
  rwa [heq] at hmap

/-- A ray action on an arbitrary translate is the identity modulo the next relative order. -/
theorem shiftedRayAction_sub_mem (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) (k : ℕ)
    {a : d.ShiftedCoefficients (grade q β) p}
    (ha : a ∈ (d.shiftedFiltration (grade q β) p).completedFiltration.submodule k) :
    shiftedRayAction q β d n hn p H a - a ∈
      (d.shiftedFiltration (grade q β) p).completedFiltration.submodule (k + 1) := by
  let e := positiveCompletionShiftEquiv q β d p
  have he : e (e.symm a) = a := e.apply_symm_apply a
  have ha' : e (e.symm a) ∈
      (d.shiftedFiltration (grade q β) p).completedFiltration.submodule k := by
    simpa only [he] using ha
  have hb := (positiveCompletionShiftEquiv_mem_iff q β d p k (e.symm a)).mp ha'
  simpa only [e, LinearEquiv.apply_symm_apply] using
    shiftedRayAction_sub_mem_coordinates q β d n hn p H k hb

/-- The inverse shifted action raises relative order by the same amount. -/
theorem shiftedRayAction_symm_sub_mem (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) (k : ℕ)
    {a : d.ShiftedCoefficients (grade q β) p}
    (ha : a ∈ (d.shiftedFiltration (grade q β) p).completedFiltration.submodule k) :
    (shiftedRayAction q β d n hn p H).symm a - a ∈
      (d.shiftedFiltration (grade q β) p).completedFiltration.submodule (k + 1) := by
  simpa only [shiftedRayAction_inv] using
    shiftedRayAction_sub_mem q β d n hn p (H⁻¹) k ha

end Mei.QuantumMonoidAlgebra
