/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.CommonLift
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Common-lift certificates for finite linear resolutions

Two finite families of linear maps share a common lift of their sums along a
span. The index sets are independent of the input, and only the totals must
lift. Individual summands need not lift, and their sums may cancel. A diagonal
span encodes an equality of the two finite sums; a general span retains a common
face value. Joint injectivity determines the certificate uniquely.

The construction uses the existing common-lift characterization. It records
linear coefficient data; realization and exhaustiveness of geometric histories
are separate requirements.
-/

public noncomputable section

namespace LinearMap

variable {R E N U V ι κ : Type*} [Semiring R]
  [AddCommMonoid E] [Module R E] [AddCommMonoid N] [Module R N]
  [AddCommMonoid U] [Module R U] [AddCommMonoid V] [Module R V]
  [Fintype ι] [Fintype κ]

/-- A common linear lift of the sums of two finite families along a span.
The finite index sets do not depend on the input. Only the sums are required to
lift; no lifts of the individual terms are part of the data. -/
structure LocalResolutionCertificate (f : N →ₗ[R] U) (g : N →ₗ[R] V)
    (left : ι → E →ₗ[R] U) (right : κ → E →ₗ[R] V) where
  /-- The common value in the middle module. -/
  lift : E →ₗ[R] N
  /-- Its first image is the complete left sum. -/
  fst_comp : f.comp lift = ∑ j, left j
  /-- Its second image is the complete right sum. -/
  snd_comp : g.comp lift = ∑ j, right j

namespace LocalResolutionCertificate

variable {f : N →ₗ[R] U} {g : N →ₗ[R] V}
  {left : ι → E →ₗ[R] U} {right : κ → E →ₗ[R] V}

/-- The common lift determines the certificate. -/
@[ext]
theorem ext {c d : LocalResolutionCertificate f g left right} (h : c.lift = d.lift) :
    c = d := by
  cases c
  cases d
  cases h
  rfl

/-- A jointly injective span admits at most one certificate for the fixed sums. -/
theorem subsingleton (hfg : Function.Injective (f.prod g)) :
    Subsingleton (LocalResolutionCertificate f g left right) := by
  refine ⟨fun c d => ext ?_⟩
  apply (LinearMap.cancel_left hfg).mp
  simp only [prod_comp, c.fst_comp, c.snd_comp, d.fst_comp, d.snd_comp]

/-- For a jointly injective span, a certificate exists exactly when the two
summed values have a common preimage for each input. No linear choice of those
preimages is assumed. -/
theorem nonempty_iff (hfg : Function.Injective (f.prod g)) :
    Nonempty (LocalResolutionCertificate f g left right) ↔
      ∀ a : E, ((∑ j, left j) a, (∑ j, right j) a) ∈ LinearMap.range (f.prod g) := by
  constructor
  · rintro ⟨c⟩ a
    refine ⟨c.lift a, ?_⟩
    exact Prod.ext (LinearMap.congr_fun c.fst_comp a) (LinearMap.congr_fun c.snd_comp a)
  · intro h
    obtain ⟨ℓ, hℓ, -⟩ := (existsUnique_comp_eq_and_comp_eq_iff hfg).mpr h
    exact ⟨⟨ℓ, hℓ.1, hℓ.2⟩⟩

/-- Equal finite sums give a certificate along the diagonal span. The two
families may have different index sets and cardinalities. -/
def ofSumEq {M : Type*} [AddCommMonoid M] [Module R M]
    (left : ι → E →ₗ[R] M) (right : κ → E →ₗ[R] M)
    (h : ∑ j, left j = ∑ j, right j) :
    LocalResolutionCertificate LinearMap.id LinearMap.id left right where
  lift := ∑ j, left j
  fst_comp := LinearMap.id_comp _
  snd_comp := (LinearMap.id_comp _).trans h

/-- Precomposing every input map preserves a common-lift certificate. -/
def precomp {H : Type*} [AddCommMonoid H] [Module R H]
    (c : LocalResolutionCertificate f g left right) (a : H →ₗ[R] E) :
    LocalResolutionCertificate f g (fun j => (left j).comp a)
      (fun j => (right j).comp a) where
  lift := c.lift.comp a
  fst_comp := by
    rw [← LinearMap.comp_assoc, c.fst_comp]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  snd_comp := by
    rw [← LinearMap.comp_assoc, c.snd_comp]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]

/-- A commuting morphism of spans transports the entire certificate, retaining
its common lift and mapping each branch weight. -/
def map {N' U' V' : Type*} [AddCommMonoid N'] [Module R N']
    [AddCommMonoid U'] [Module R U'] [AddCommMonoid V'] [Module R V']
    {f' : N' →ₗ[R] U'} {g' : N' →ₗ[R] V'}
    (c : LocalResolutionCertificate f g left right)
    (n : N →ₗ[R] N') (u : U →ₗ[R] U') (v : V →ₗ[R] V')
    (hf : f'.comp n = u.comp f) (hg : g'.comp n = v.comp g) :
    LocalResolutionCertificate f' g' (fun j => u.comp (left j))
      (fun j => v.comp (right j)) where
  lift := n.comp c.lift
  fst_comp := by
    rw [← LinearMap.comp_assoc, hf, LinearMap.comp_assoc, c.fst_comp]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  snd_comp := by
    rw [← LinearMap.comp_assoc, hg, LinearMap.comp_assoc, c.snd_comp]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]

/-- The common value after a morphism of spans is the image of the original value. -/
@[simp]
theorem map_lift {N' U' V' : Type*} [AddCommMonoid N'] [Module R N']
    [AddCommMonoid U'] [Module R U'] [AddCommMonoid V'] [Module R V']
    {f' : N' →ₗ[R] U'} {g' : N' →ₗ[R] V'}
    (c : LocalResolutionCertificate f g left right)
    (n : N →ₗ[R] N') (u : U →ₗ[R] U') (v : V →ₗ[R] V')
    (hf : f'.comp n = u.comp f) (hg : g'.comp n = v.comp g) :
    (c.map n u v hf hg).lift = n.comp c.lift := by rfl

/-- A certificate reflects through injective chamber maps when its face value
has a source preimage for each input. The preimages need not be supplied
linearly. No separate injectivity hypothesis on the face coefficient map is
needed. The source certificate maps to the prescribed target common value. -/
theorem exists_of_coeffEmbedding {N' U' V' : Type*} [AddCommMonoid N'] [Module R N']
    [AddCommMonoid U'] [Module R U'] [AddCommMonoid V'] [Module R V']
    {f' : N' →ₗ[R] U'} {g' : N' →ₗ[R] V'}
    (n : N →ₗ[R] N') (u : U →ₗ[R] U') (v : V →ₗ[R] V')
    (hf : f'.comp n = u.comp f) (hg : g'.comp n = v.comp g)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hfg : Function.Injective (f.prod g))
    (c' : LocalResolutionCertificate f' g' (fun j => u.comp (left j))
      (fun j => v.comp (right j)))
    (hpre : ∀ a, ∃ z, n z = c'.lift a) :
    ∃ c : LocalResolutionCertificate f g left right, n.comp c.lift = c'.lift := by
  have hpre' (a : E) : ∃ z, n z = c'.lift a ∧
      f z = (∑ j, left j) a ∧ g z = (∑ j, right j) a := by
    obtain ⟨z, hz⟩ := hpre a
    refine ⟨z, hz, hu ?_, hv ?_⟩
    · calc
        u (f z) = f' (n z) := (LinearMap.congr_fun hf z).symm
        _ = f' (c'.lift a) := congrArg f' hz
        _ = u ((∑ j, left j) a) := by
          simpa only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum] using
            LinearMap.congr_fun c'.fst_comp a
    · calc
        v (g z) = g' (n z) := (LinearMap.congr_fun hg z).symm
        _ = g' (c'.lift a) := congrArg g' hz
        _ = v ((∑ j, right j) a) := by
          simpa only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum] using
            LinearMap.congr_fun c'.snd_comp a
  obtain ⟨c⟩ := (nonempty_iff hfg).mpr (fun a => by
    obtain ⟨z, -, hz⟩ := hpre' a
    exact ⟨z, Prod.ext hz.1 hz.2⟩)
  refine ⟨c, ?_⟩
  ext a
  obtain ⟨z, hn, hfz, hgz⟩ := hpre' a
  have hc : c.lift a = z := hfg (Prod.ext
    ((LinearMap.congr_fun c.fst_comp a).trans hfz.symm)
    ((LinearMap.congr_fun c.snd_comp a).trans hgz.symm))
  simpa only [LinearMap.comp_apply, hc] using hn

/-- Reindexing the two finite branch families retains the common lift. -/
def reindex {ι' κ' : Type*} [Fintype ι'] [Fintype κ']
    (c : LocalResolutionCertificate f g left right) (e : ι' ≃ ι) (e' : κ' ≃ κ) :
    LocalResolutionCertificate f g (fun j => left (e j)) (fun j => right (e' j)) where
  lift := c.lift
  fst_comp := c.fst_comp.trans (e.sum_comp left).symm
  snd_comp := c.snd_comp.trans (e'.sum_comp right).symm

/-- The diagonal certificate uses the complete left sum as its common value. -/
@[simp]
theorem ofSumEq_lift {M : Type*} [AddCommMonoid M] [Module R M]
    (left : ι → E →ₗ[R] M) (right : κ → E →ₗ[R] M)
    (h : ∑ j, left j = ∑ j, right j) : (ofSumEq left right h).lift = ∑ j, left j := by rfl

/-- Input substitution precomposes the common value. -/
@[simp]
theorem precomp_lift {H : Type*} [AddCommMonoid H] [Module R H]
    (c : LocalResolutionCertificate f g left right) (a : H →ₗ[R] E) :
    (c.precomp a).lift = c.lift.comp a := by rfl

/-- Relabeling histories retains the common value. -/
@[simp]
theorem reindex_lift {ι' κ' : Type*} [Fintype ι'] [Fintype κ']
    (c : LocalResolutionCertificate f g left right) (e : ι' ≃ ι) (e' : κ' ≃ κ) :
    (c.reindex e e').lift = c.lift := by rfl

end LocalResolutionCertificate

end LinearMap
