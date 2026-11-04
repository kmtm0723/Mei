/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.DirectLimit.Semilinear
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Inclusion
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Inclusion

/-!
# Scalar and exponent transport of global quantum coefficients

Compatible scalar and positive degree maps descend from the existing shifted
completion maps to the module of global coefficients. The descent uses Mathlib's
module direct-limit universal property after restriction of scalars. No injectivity
or alternation hypothesis is needed. Chart independence removes any dependence on
the auxiliary choice of a containing target chart.
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

private def targetChart (s : Multiset d.monoid) : Multiset e.monoid :=
  {⟨T (s.sum : Γ), T.map_mem s.sum.property⟩}

omit [DecidableEq Γ] [DecidableEq Γ'] in
private theorem targetChart_origin (s : Multiset d.monoid) :
    T (d.coefficientOrigin s) = e.coefficientOrigin (targetChart d e T s) := by
  simp only [PositiveDegrees.coefficientOrigin_eq_neg_sum, targetChart,
    Multiset.sum_singleton, map_neg]

omit [DecidableEq Γ] [DecidableEq Γ'] in
private theorem targetChart_mem (s : Multiset d.monoid) :
    T (d.coefficientOrigin s) - e.coefficientOrigin (targetChart d e T s) ∈ e.monoid := by
  rw [targetChart_origin, sub_self]
  exact e.monoid.zero_mem

private def mapGlobalChart (s : Multiset d.monoid) :
    d.ShiftedCoefficients (grade q β) (d.coefficientOrigin s) →ₛₗ[φ]
      e.ShiftedDirectLimit (grade q' β') :=
  (e.toShiftedDirectLimitOfChart (grade q' β') (T (d.coefficientOrigin s))
    (targetChart d e T s) (targetChart_mem d e T s)).comp
      (mapShiftedCompletion d e T φ h (d.coefficientOrigin s))

omit [DecidableEq Γ] in
private theorem mapGlobalChart_apply (s : Multiset d.monoid)
    (x : d.ShiftedCoefficients (grade q β) (d.coefficientOrigin s)) :
    mapGlobalChart d e T φ h s x =
      e.toShiftedDirectLimitOfChart (grade q' β') (T (d.coefficientOrigin s))
        (targetChart d e T s) (targetChart_mem d e T s)
        (mapShiftedCompletion d e T φ h (d.coefficientOrigin s) x) := by
  -- Applying the composition exposes the defining chart map.
  rfl

omit [DecidableEq Γ] in
private theorem mapGlobalChart_inclusion (s t : Multiset d.monoid) (hst : s ≤ t)
    (x : d.ShiftedCoefficients (grade q β) (d.coefficientOrigin s)) :
    mapGlobalChart d e T φ h t (d.coefficientInclusion (grade q β) s t hst x) =
      mapGlobalChart d e T φ h s x := by
  simp only [mapGlobalChart, LinearMap.comp_apply, PositiveDegrees.coefficientInclusion_eq,
    mapShiftedCompletion_shiftedCompletedInclusion]
  exact e.toShiftedDirectLimitOfChart_inclusion (grade q' β')
    (T (d.coefficientOrigin s)) (T (d.coefficientOrigin t))
    (by simpa only [map_sub] using T.map_mem (d.coefficientOrigin_sub_mem hst))
    (targetChart d e T s) (targetChart d e T t)
    (targetChart_mem d e T s) (targetChart_mem d e T t) _

/-- Transport global coefficients along compatible scalar and positive degree maps. -/
def mapShiftedDirectLimit :
    d.ShiftedDirectLimit (grade q β) →ₛₗ[φ] e.ShiftedDirectLimit (grade q' β') :=
  Module.DirectLimit.liftSemilinear
    (fun s t hst => d.coefficientInclusion (grade q β) s t hst) φ
    (mapGlobalChart d e T φ h) (mapGlobalChart_inclusion d e T φ h)

private theorem mapShiftedDirectLimit_chart (s : Multiset d.monoid)
    (x : d.ShiftedCoefficients (grade q β) (d.coefficientOrigin s)) :
    mapShiftedDirectLimit d e T φ h (d.toShiftedDirectLimit (grade q β) s x) =
      mapGlobalChart d e T φ h s x := by
  exact (congrArg (mapShiftedDirectLimit d e T φ h)
    (d.toShiftedDirectLimit_apply (grade q β) s x)).trans
      (Module.DirectLimit.liftSemilinear_of
        (fun s t hst => d.coefficientInclusion (grade q β) s t hst) φ
        (mapGlobalChart d e T φ h) (mapGlobalChart_inclusion d e T φ h) s x)

/-- Transport in a chart can use any target chart containing the mapped origin. -/
theorem mapShiftedDirectLimit_toShiftedDirectLimit (s : Multiset d.monoid)
    (t : Multiset e.monoid) (ht : T (d.coefficientOrigin s) - e.coefficientOrigin t ∈ e.monoid)
    (x : d.ShiftedCoefficients (grade q β) (d.coefficientOrigin s)) :
    mapShiftedDirectLimit d e T φ h (d.toShiftedDirectLimit (grade q β) s x) =
      e.toShiftedDirectLimitOfChart (grade q' β') (T (d.coefficientOrigin s)) t ht
        (mapShiftedCompletion d e T φ h (d.coefficientOrigin s) x) := by
  rw [mapShiftedDirectLimit_chart, mapGlobalChart_apply]
  simpa only [PositiveDegrees.shiftedCompletedInclusion_refl] using
    e.toShiftedDirectLimitOfChart_inclusion (grade q' β')
      (T (d.coefficientOrigin s)) (T (d.coefficientOrigin s)) (by simp)
      t (targetChart d e T s) ht (targetChart_mem d e T s)
      (mapShiftedCompletion d e T φ h (d.coefficientOrigin s) x)

/-- Arbitrary-origin chart embeddings commute with global scalar and exponent transport. -/
theorem mapShiftedDirectLimit_toShiftedDirectLimitOfChart (p : Γ)
    (s : Multiset d.monoid) (hs : p - d.coefficientOrigin s ∈ d.monoid)
    (t : Multiset e.monoid) (ht : T p - e.coefficientOrigin t ∈ e.monoid)
    (x : d.ShiftedCoefficients (grade q β) p) :
    mapShiftedDirectLimit d e T φ h (d.toShiftedDirectLimitOfChart (grade q β) p s hs x) =
      e.toShiftedDirectLimitOfChart (grade q' β') (T p) t ht
        (mapShiftedCompletion d e T φ h p x) := by
  let E := e.toShiftedDirectLimitOfChart (grade q' β') (T (d.coefficientOrigin s))
    (targetChart d e T s) (targetChart_mem d e T s)
  have h₁ := congrArg (mapShiftedDirectLimit d e T φ h)
    (d.toShiftedDirectLimitOfChart_apply (grade q β) p s hs x)
  have h₂ := mapShiftedDirectLimit_chart d e T φ h s
    (d.shiftedCompletedInclusion (grade q β) p (d.coefficientOrigin s) hs x)
  have h₃ := mapGlobalChart_apply d e T φ h s
    (d.shiftedCompletedInclusion (grade q β) p (d.coefficientOrigin s) hs x)
  have h₄ := congrArg E (mapShiftedCompletion_shiftedCompletedInclusion q β d e T φ h
    p (d.coefficientOrigin s) hs x)
  have h₅ := e.toShiftedDirectLimitOfChart_inclusion (grade q' β') (T p)
    (T (d.coefficientOrigin s)) (by simpa only [map_sub] using T.map_mem hs)
    t (targetChart d e T s) ht (targetChart_mem d e T s)
    (mapShiftedCompletion d e T φ h p x)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

private theorem toShiftedDirectLimitOfChart_cast {p r : Γ} (hpr : p = r)
    (s : Multiset d.monoid) (hr : r - d.coefficientOrigin s ∈ d.monoid)
    (x : d.ShiftedCoefficients (grade q β) p) :
    d.toShiftedDirectLimitOfChart (grade q β) r s hr
        (cast (congrArg (d.ShiftedCoefficients (grade q β)) hpr) x) =
      d.toShiftedDirectLimitOfChart (grade q β) p s (by rwa [hpr]) x := by
  subst r
  rfl

/-- Identity scalar and degree transport fixes every global coefficient. -/
@[simp]
theorem mapShiftedDirectLimit_id (x : d.ShiftedDirectLimit (grade q β)) :
    mapShiftedDirectLimit (q' := q) (β' := β) d d (PositiveDegreeMap.id d)
      (RingHom.id R) (fun u v => by simp) x = x := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit (grade q β) x
  have hm := mapShiftedDirectLimit_toShiftedDirectLimit (q' := q) (β' := β)
    d d (PositiveDegreeMap.id d) (RingHom.id R) (fun u v => by simp) s s (by simp) a
  have hi := mapShiftedCompletion_id (q := q) (β := β) d (d.coefficientOrigin s) a
  have hc := toShiftedDirectLimitOfChart_cast d
    (PositiveDegreeMap.id_apply (d := d) (d.coefficientOrigin s)) s (by simp)
    (mapShiftedCompletion (q' := q) (β' := β) d d (PositiveDegreeMap.id d) (RingHom.id R)
      (fun u v => by simp) (d.coefficientOrigin s) a)
  exact hm.trans (hc.symm.trans ((congrArg
    (d.toShiftedDirectLimitOfChart (grade q β) (d.coefficientOrigin s) s (by simp)) hi).trans
      ((d.toShiftedDirectLimitOfChart_apply (grade q β) (d.coefficientOrigin s) s
        (by simp) a).trans
          (congrArg (d.toShiftedDirectLimit (grade q β) s)
            (d.shiftedCompletedInclusion_refl (grade q β) (d.coefficientOrigin s) a)))))

variable {U Γ'' : Type*} [CommRing U] [AddCommGroup Γ''] [DecidableEq Γ'']
  {q'' : Uˣ} {β'' : LinearMap.BilinForm ℤ Γ''}
  (a : PositiveDegrees Γ'') (T' : PositiveDegreeMap e a) (ψ : S →+* U)
  (h' : ∀ u v, Units.map ψ.toMonoidHom (q' ^ β' u v) = q'' ^ β'' (T' u) (T' v))

private local instance : Ring (QuantumMonoidAlgebra q'' β'') := inferInstance
private local instance : Algebra U (QuantumMonoidAlgebra q'' β'') := inferInstance
private local instance : AddCommGroup (QuantumMonoidAlgebra q'' β'') := inferInstance
private local instance : Module U (QuantumMonoidAlgebra q'' β'') := inferInstance
private local instance : DirectSum.Decomposition (grade q'' β'') := inferInstance
private local instance (p : Γ'') : AddCommGroup (a.ShiftedCoefficients (grade q'' β'') p) :=
  inferInstance
private local instance (p : Γ'') : Module U (a.ShiftedCoefficients (grade q'' β'') p) :=
  inferInstance
private local instance : AddCommMonoid (a.ShiftedDirectLimit (grade q'' β'')) := inferInstance
private local instance : Module U (a.ShiftedDirectLimit (grade q'' β'')) := inferInstance

/-- Scalar and exponent transport compose on all global coefficients. -/
theorem mapShiftedDirectLimit_comp (x : d.ShiftedDirectLimit (grade q β)) :
    mapShiftedDirectLimit (q' := q'') (β' := β'') d a (T'.comp T) (ψ.comp φ)
      (fun u v => by
        rw [PositiveDegreeMap.comp_apply, PositiveDegreeMap.comp_apply, ← h', ← h]; rfl) x =
      mapShiftedDirectLimit e a T' ψ h' (mapShiftedDirectLimit d e T φ h x) := by
  let hx := d.exists_toShiftedDirectLimit (grade q β) x
  let s := Classical.choose hx
  let z := Classical.choose (Classical.choose_spec hx)
  have hz := Classical.choose_spec (Classical.choose_spec hx)
  let r := targetChart d a (T'.comp T) s
  have hrc := targetChart_mem d a (T'.comp T) s
  have hr : T' (T (d.coefficientOrigin s)) - a.coefficientOrigin r ∈ a.monoid := by
    simpa only [PositiveDegreeMap.comp_apply] using hrc
  let hc : ∀ u v, Units.map (ψ.comp φ).toMonoidHom (q ^ β u v) =
      q'' ^ β'' ((T'.comp T) u) ((T'.comp T) v) := fun u v => by
    rw [PositiveDegreeMap.comp_apply, PositiveDegreeMap.comp_apply, ← h', ← h]
    rfl
  have h₁ := mapShiftedDirectLimit_toShiftedDirectLimit d a (T'.comp T) (ψ.comp φ) hc
    s r hrc z
  have h₂ := mapShiftedCompletion_comp d e T φ h (d.coefficientOrigin s) a T' ψ h' z
  have h₃ := congrArg (mapShiftedDirectLimit e a T' ψ h')
    (mapShiftedDirectLimit_toShiftedDirectLimit d e T φ h s (targetChart d e T s)
      (targetChart_mem d e T s) z)
  have h₄ := mapShiftedDirectLimit_toShiftedDirectLimitOfChart e a T' ψ h'
    (T (d.coefficientOrigin s)) (targetChart d e T s) (targetChart_mem d e T s) r hr
    (mapShiftedCompletion d e T φ h (d.coefficientOrigin s) z)
  have hcast := toShiftedDirectLimitOfChart_cast a
    (PositiveDegreeMap.comp_apply T' T (d.coefficientOrigin s)) r hr
    (mapShiftedCompletion d a (T'.comp T) (ψ.comp φ) hc (d.coefficientOrigin s) z)
  have hc' := h₁.trans (hcast.symm.trans ((congrArg
    (a.toShiftedDirectLimitOfChart (grade q'' β'') (T' (T (d.coefficientOrigin s))) r hr)
      h₂).trans (h₄.symm.trans h₃.symm)))
  exact (congrArg (mapShiftedDirectLimit d a (T'.comp T) (ψ.comp φ) hc) hz).symm.trans
    (hc'.trans (congrArg (fun y =>
      mapShiftedDirectLimit e a T' ψ h' (mapShiftedDirectLimit d e T φ h y)) hz))

end Mei.QuantumMonoidAlgebra
