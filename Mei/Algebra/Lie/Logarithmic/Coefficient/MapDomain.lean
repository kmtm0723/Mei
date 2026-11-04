/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Logarithmic.Coefficient
public import Mei.RingTheory.FilteredAlgebra.Exp.Map

/-!
# Monomial maps of completed coefficient algebras

Let `U` be a positive degree map and `φ : Q → Q'` an additive map of coefficient monoids lifting
`U`. The monomial map `z^q ↦ z^{φ q}` carries the positive-increment coefficient filtration with
the cutoff modulus of `U`
(`TropicalVertexCoefficientAction.filtration_ideal_le_comap_mapDomainAlgHom_of_coe`) and
preserves the first filtration ideal, since nonzero allowed degrees have nonzero images
(`TropicalVertexCoefficientAction.filtration_ideal_one_le_comap_mapDomainAlgHom_of_coe`). Hence
it extends to the completions (`TropicalVertexCoefficientAction.completedMapDomain`), where it
commutes with completed logarithms
(`TropicalVertexCoefficientAction.completedMapDomain_completedLog`). This generalizes
`TropicalVertexCoefficientAction.filtration_ideal_le_comap_mapDomainAlgHom`, in which `φ` is the
restriction of `U`.
-/

public section

noncomputable section

namespace Mei

open _root_.AddMonoidAlgebra

namespace TropicalVertexCoefficientAction

variable {R Γ Γ' : Type*} [CommRing R] [AddCommMonoid Γ] [AddCommMonoid Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {Q : AddSubmonoid Γ} {Q' : AddSubmonoid Γ'}
  (U : PositiveDegreeMap d e) (φ : Q →+ Q') (hφ : ∀ q, (φ q : Γ') = U q)

include hφ in
/-- A monomial map `z^q ↦ z^{φ q}` lifting a positive degree map `U` carries the coefficient
filtration with the cutoff modulus of `U`. -/
theorem filtration_ideal_le_comap_mapDomainAlgHom_of_coe (k : ℕ) :
    (filtration (R := R) d Q).ideal (U.modulus k + 1) ≤
      ((filtration e Q').ideal (k + 1)).comap (mapDomainAlgHom R R φ) := by
  have hQ : Q.map U.toAddMonoidHom ≤ Q' := by
    rintro _ ⟨q, hq, rfl⟩
    simpa only [hφ] using (φ ⟨q, hq⟩).property
  have he : φ = (AddSubmonoid.inclusion hQ).comp (U.toAddMonoidHom.addSubmonoidMap Q) :=
    AddMonoidHom.ext fun q => Subtype.ext (hφ q)
  rw [he]
  exact filtration_ideal_le_comap_mapDomainAlgHom U hQ k

include hφ in
/-- A monomial map `z^q ↦ z^{φ q}` lifting a positive degree map preserves the first
filtration ideal: nonzero allowed degrees have nonzero images. -/
theorem filtration_ideal_one_le_comap_mapDomainAlgHom_of_coe :
    (filtration (R := R) d Q).ideal 1 ≤
      ((filtration e Q').ideal 1).comap (mapDomainAlgHom R R φ) := by
  intro a ha
  rw [filtration_ideal] at ha
  rw [Ideal.mem_comap, filtration_ideal]
  refine AddSubmonoid.monoidAlgebraIdeal_le_comap_mapDomainRingHom (d.monoid.comap Q.subtype)
    _ _ _ _ (fun n hn => ?_) (fun n hn hd => ?_) ha
  · simpa only [AddSubmonoid.mem_comap, AddSubmonoid.coe_subtype, hφ] using
      U.map_mem (AddSubmonoid.mem_comap.mp hn)
  · have hn0 : (n : Γ) ≠ 0 := fun h0 => by
      simp only [AddMonoidHom.comp_apply, AddSubmonoid.subtype_apply, h0, map_zero] at hd
      omega
    have h := e.degree_pos (U.map_mem (AddSubmonoid.mem_comap.mp hn))
      (U.map_ne_zero (AddSubmonoid.mem_comap.mp hn) hn0)
    simp only [AddMonoidHom.comp_apply, AddSubmonoid.coe_subtype, Nat.cast_one, hφ] at h ⊢
    omega

/-- The completed monomial map `z^q ↦ z^{φ q}`, with the cutoff modulus of `U`. -/
def completedMapDomain :
    (filtration (R := R) d Q).completion →+* (filtration (R := R) e Q').completion :=
  (filtration (R := R) d Q).mapCompletion (filtration (R := R) e Q')
    (mapDomainAlgHom R R φ : _ →+* _) U.modulus U.monotone_modulus
    (filtration_ideal_le_comap_mapDomainAlgHom_of_coe U φ hφ)

/-- At order `k`, the completed monomial map is the finite one at the order of the cutoff
modulus. -/
theorem projection_completedMapDomain (k : ℕ) (u : (filtration (R := R) d Q).completion) :
    (filtration (R := R) e Q').projection k (completedMapDomain U φ hφ u) =
      Ideal.quotientMap _ (mapDomainAlgHom R R φ : _ →+* _)
        (filtration_ideal_le_comap_mapDomainAlgHom_of_coe U φ hφ k)
        ((filtration (R := R) d Q).projection (U.modulus k) u) :=
  AlgFiltration.projection_mapCompletion _ _ _ _ _ _ k u

/-- The completed monomial map extends the finite one. -/
@[simp]
theorem completedMapDomain_toCompletion (v : R[Q]) :
    completedMapDomain U φ hφ ((filtration (R := R) d Q).toCompletion v) =
      (filtration (R := R) e Q').toCompletion (mapDomainAlgHom R R φ v) :=
  AlgFiltration.mapCompletion_toCompletion _ _ _ _ _ _ v

/-- The completed monomial map preserves the first completion ideal. -/
theorem completedMapDomain_mem_completionIdeal_one {u : (filtration (R := R) d Q).completion}
    (hu : u ∈ (filtration (R := R) d Q).completionIdeal 1) :
    completedMapDomain U φ hφ u ∈ (filtration (R := R) e Q').completionIdeal 1 :=
  (filtration (R := R) d Q).mapCompletion_mem_first (filtration (R := R) e Q') _ _ _ _
    (filtration_ideal_one_le_comap_mapDomainAlgHom_of_coe U φ hφ) hu

/-- The completed monomial map commutes with completed logarithms. -/
theorem completedMapDomain_completedLog [Algebra ℚ R]
    {g : (filtration (R := R) d Q).completion}
    (hg : g - 1 ∈ (filtration (R := R) d Q).completionIdeal 1) :
    completedMapDomain U φ hφ ((filtration (R := R) d Q).completedLog ⟨g, hg⟩) =
      (filtration (R := R) e Q').completedLog ⟨completedMapDomain U φ hφ g, by
        simpa only [map_sub, map_one] using
          completedMapDomain_mem_completionIdeal_one U φ hφ hg⟩ :=
  AlgFiltration.mapCompletion_completedLog _ _ _ _ _ _
    (filtration_ideal_one_le_comap_mapDomainAlgHom_of_coe U φ hφ) ⟨g, hg⟩

end TropicalVertexCoefficientAction

end Mei
