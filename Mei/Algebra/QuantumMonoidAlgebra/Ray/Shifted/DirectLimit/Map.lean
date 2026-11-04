/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Map
public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.DirectLimit
public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.Map

/-!
# Naturality of global quantum ray actions

Compatible scalar and positive degree maps intertwine the global ray actions.
The result descends the existing arbitrary-bilinear-form local naturality law and
uses independence of containing charts. Exponent maps may merge distinct positive
rays, and the coefficient homomorphism need not be injective.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R S Γ Γ' : Type*} [CommRing R] [CommRing S]
  [AddCommGroup Γ] [AddCommGroup Γ'] [DecidableEq Γ] [DecidableEq Γ']
  {q : Rˣ} {q' : Sˣ} {β : LinearMap.BilinForm ℤ Γ} {β' : LinearMap.BilinForm ℤ Γ'}
  (d : PositiveDegrees Γ) (e : PositiveDegrees Γ') (T : PositiveDegreeMap d e)
  (φ : R →+* S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))

private local instance : Ring (QuantumMonoidAlgebra q β) := inferInstance
private local instance : Algebra R (QuantumMonoidAlgebra q β) := inferInstance
private local instance : AddCommGroup (QuantumMonoidAlgebra q β) := inferInstance
private local instance : Module R (QuantumMonoidAlgebra q β) := inferInstance
private local instance : DirectSum.Decomposition (grade q β) := inferInstance
private local instance : Ring (QuantumMonoidAlgebra q' β') := inferInstance
private local instance : Algebra S (QuantumMonoidAlgebra q' β') := inferInstance
private local instance : AddCommGroup (QuantumMonoidAlgebra q' β') := inferInstance
private local instance : Module S (QuantumMonoidAlgebra q' β') := inferInstance
private local instance : DirectSum.Decomposition (grade q' β') := inferInstance
private local instance (p : Γ) : AddCommGroup (d.ShiftedCoefficients (grade q β) p) := inferInstance
private local instance (p : Γ) : Module R (d.ShiftedCoefficients (grade q β) p) := inferInstance
private local instance (p : Γ') : AddCommGroup (e.ShiftedCoefficients (grade q' β') p) :=
  inferInstance
private local instance (p : Γ') : Module S (e.ShiftedCoefficients (grade q' β') p) :=
  inferInstance
private local instance : AddCommMonoid (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : Module R (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : AddCommMonoid (e.ShiftedDirectLimit (grade q' β')) := inferInstance
private local instance : Module S (e.ShiftedDirectLimit (grade q' β')) := inferInstance

/-- Global scalar and exponent transport intertwines quantum ray actions. -/
theorem mapShiftedDirectLimit_directLimitRayAction
    (n : d.monoid) (hn : 0 < d.degree n) (H : (PowerSeries R)ˣ)
    (x : d.ShiftedDirectLimit (grade q β)) :
    mapShiftedDirectLimit d e T φ h (directLimitRayAction q β d n hn H x) =
      directLimitRayAction q' β' e ⟨T n, T.map_mem n.property⟩
        (mappedRay_degree_pos d e T n hn) (Units.map (PowerSeries.map φ).toMonoidHom H)
        (mapShiftedDirectLimit d e T φ h x) := by
  let hx := d.exists_toShiftedDirectLimit (grade q β) x
  let s := Classical.choose hx
  let z := Classical.choose (Classical.choose_spec hx)
  have hz := Classical.choose_spec (Classical.choose_spec hx)
  let t : Multiset e.monoid := {⟨T (s.sum : Γ), T.map_mem s.sum.property⟩}
  have ht : T (d.coefficientOrigin s) - e.coefficientOrigin t ∈ e.monoid := by
    simp only [PositiveDegrees.coefficientOrigin_eq_neg_sum, t, Multiset.sum_singleton,
      map_neg, sub_self, zero_mem]
  let E := e.toShiftedDirectLimitOfChart (grade q' β') (T (d.coefficientOrigin s)) t ht
  let K := Units.map (PowerSeries.map φ).toMonoidHom H
  let N : e.monoid := ⟨T n, T.map_mem n.property⟩
  let hn' := mappedRay_degree_pos d e T n hn
  have h₁ := congrArg (mapShiftedDirectLimit d e T φ h)
    (directLimitRayAction_toShiftedDirectLimit q β d n hn H s z)
  have h₂ := mapShiftedDirectLimit_toShiftedDirectLimit d e T φ h s t ht
    (shiftedRayAction q β d n hn (d.coefficientOrigin s) H z)
  have h₃ := congrArg E
    (mapShiftedCompletion_shiftedRayAction d e T φ h n hn (d.coefficientOrigin s) H z)
  have h₄ := directLimitRayAction_toShiftedDirectLimitOfChart q' β' e N hn' K
    (T (d.coefficientOrigin s)) t ht
    (mapShiftedCompletion d e T φ h (d.coefficientOrigin s) z)
  have h₅ := congrArg (directLimitRayAction q' β' e N hn' K)
    (mapShiftedDirectLimit_toShiftedDirectLimit d e T φ h s t ht z)
  have hchart := h₁.trans (h₂.trans (h₃.trans (h₄.symm.trans h₅.symm)))
  exact (congrArg (fun y => mapShiftedDirectLimit d e T φ h
      (directLimitRayAction q β d n hn H y)) hz).symm.trans
    (hchart.trans (congrArg (fun y => directLimitRayAction q' β' e N hn' K
      (mapShiftedDirectLimit d e T φ h y)) hz))

end Mei.QuantumMonoidAlgebra
