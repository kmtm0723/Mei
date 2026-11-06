/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.MonoidAlgebra.Twisted.Hom

/-!
# Coefficients under injective twisted exponent transport

When an exponent map is injective on a set containing the source support, its
transport does not combine distinct coefficients there. The scalar map can be
arbitrary, including maps which annihilate nonzero coefficients.
-/

public section
noncomputable section

namespace Mei.TwistedMonoidAlgebra

open TauCeti TauCeti.TwistedMonoidAlgebra

variable {R S G H : Type*} [CommSemiring R] [CommSemiring S] [Monoid G] [Monoid H]
  {α : G → G → Rˣ} {β : H → H → Sˣ} [IsFactorSet α] [IsFactorSet β]
  (φ : R →+* S) (f : G →* H)
  (h : ∀ g j, Units.map φ.toMonoidHom (α g j) = β (f g) (f j))

/-- Transport at an exponent in a set where the exponent map is injective reads
the original coefficient through the scalar map. -/
theorem repr_map_of_injOn (P : Set G) (hf : Set.InjOn f P)
    (x : twistedMonoidAlgebra R G α)
    (hx : ∀ g, (basis R G α).repr x g ≠ 0 → g ∈ P) (g : G) (hg : g ∈ P) :
    (basis S H β).repr (map φ f h x) (f g) = φ ((basis R G α).repr x g) := by
  classical
  conv_lhs => rw [← (basis R G α).linearCombination_repr x, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, map_smul, basis_apply, map_of]
  simp only [← basis_apply, _root_.map_smul, Module.Basis.repr_self,
    Finset.sum_apply', Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single g]
  · simp only [ite_true]
  · intro j hj hjg
    have hjP := hx j (Finsupp.mem_support_iff.mp hj)
    have hne : f j ≠ f g := fun he => hjg (hf hjP hg he)
    simp only [hne, ite_false]
  · intro hg'
    have hz : (basis R G α).repr x g = 0 := by
      simpa only [Finsupp.mem_support_iff, not_not] using hg'
    simp only [hz, map_zero, ite_true]

end Mei.TwistedMonoidAlgebra
