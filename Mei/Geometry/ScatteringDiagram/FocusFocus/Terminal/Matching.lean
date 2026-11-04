/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Terminal.FiniteInput
public import Mei.Algebra.Category.SemimoduleCat.Multispan.FiniteInput

/-!
# Matching coefficients of finite terminal slab evaluations

The actual finite weighted evaluations near a regular slab point assemble into
one matching coefficient family on the slab span. We apply the general
finite-input criterion and the existing multispan reconstruction to the uniform
terminal common lifts. The resulting face value is the sum of theta monomials
with their original incoming parameter maps.

This is matching at one coefficient face. It does not supply the closed global
broken-line family, its singular-degeneration certificate or sheaf descent.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Mei.FocusFocus

open AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial

variable {R : Type*} [CommRing R]

/-- The full-exponent slab correspondence as a multispan of semimodules.
The false and true chamber indices denote its negative and positive sides. -/
abbrev slabTerminalMultispan (t : R) :
    MultispanIndex (MultispanShape.ofLinearOrder Bool) (SemimoduleCat R) where
  left _ := SemimoduleCat.of R (TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1)))
  right _ := SemimoduleCat.of R (R[ℤ × ℤ])
  fst _ := SemimoduleCat.ofHom (exponentLeftMap (C t * (1 + T 1))).toLinearMap
  snd _ := SemimoduleCat.ofHom (exponentRightMap (C t * (1 + T 1))).toLinearMap

/-- Both maps together are injective, even for nilpotent smoothing parameters. -/
theorem slabTerminalMultispan_jointly_injective (t : R)
    (c : (MultispanShape.ofLinearOrder Bool).L) :
    Function.Injective (((slabTerminalMultispan t).fst c).hom.prod
      ((slabTerminalMultispan t).snd c).hom) :=
  exponentMaps_jointly_injective (C t * (1 + T 1))

variable {ι H : Type*} [AddCommMonoid H] [Module R H]
  (s : Finset ι) (n b : ι → ℤ) (t : R) (α : ι → H →ₗ[R] R)
  {v : ℝ} {L U : ℝ × ℝ}

private def terminalChamberMap (side : Bool) : H →ₗ[R] R[ℤ × ℤ] :=
  (if side then (exponentRightMap (C t * (1 + T 1))).toLinearMap else
    (exponentLeftMap (C t * (1 + T 1))).toLinearMap).comp
      (slabTerminalFiniteLift s n b t α)

private theorem terminalChamberMap_eq
    (hL : L ∈ slabTerminalFiniteDomain s n b v)
    (hU : U ∈ slabTerminalFiniteDomain s n b v) (hLs : L.1 < 0) (hUs : 0 < U.1)
    (a : H) (side : Bool) :
    terminalChamberMap s n b t α side a =
      ∑ i ∈ s, slabThetaEvaluation t (α i a) (n i) (b i) (if side then U else L) := by
  cases side
  · exact exponentLeftMap_slabTerminalFiniteLift s n b t α hL hLs a
  · exact exponentRightMap_slabTerminalFiniteLift s n b t α hU hUs a

/-- Actual finite weighted evaluations at any two opposite-side endpoints in
the common terminal neighborhood extend uniquely to a linear matching family. -/
theorem existsUnique_slabTerminalFinite_matchingFamily
    (hL : L ∈ slabTerminalFiniteDomain s n b v)
    (hU : U ∈ slabTerminalFiniteDomain s n b v) (hLs : L.1 < 0) (hUs : 0 < U.1) :
    ∃! ℓ : H →ₗ[R] SemimoduleCat.sectionsSubmodule (slabTerminalMultispan t).multispan,
      ∀ a (side : Bool), (ℓ a).val (.right side) =
        ∑ i ∈ s, slabThetaEvaluation t (α i a) (n i) (b i) (if side then U else L) := by
  have htest : ∃! ℓ : H →ₗ[R]
      SemimoduleCat.sectionsSubmodule (slabTerminalMultispan t).multispan,
      ∀ a side, (ℓ a).val (.right side) = terminalChamberMap s n b t α side a := by
    apply ((slabTerminalMultispan t).existsUnique_sections_lift_iff_finiteInput
      (terminalChamberMap s n b t α) (slabTerminalMultispan_jointly_injective t)).mpr
    intro m a c
    have hc : c = default := Subsingleton.elim _ _
    subst c
    exact ⟨(slabTerminalFiniteLift s n b t α).comp a, rfl, rfl⟩
  obtain ⟨ℓ, hℓ, huniq⟩ := htest
  refine ⟨ℓ, fun a side => (hℓ a side).trans
    (terminalChamberMap_eq s n b t α hL hU hLs hUs a side), ?_⟩
  intro l hl
  apply huniq l
  intro a side
  exact (hl a side).trans (terminalChamberMap_eq s n b t α hL hU hLs hUs a side).symm

/-- The face coefficient of any matching extension of the actual evaluations
is the common total theta lift, with complete incoming records still indexed by `s`. -/
theorem slabTerminalFinite_matchingFamily_face
    (hL : L ∈ slabTerminalFiniteDomain s n b v)
    (hU : U ∈ slabTerminalFiniteDomain s n b v) (hLs : L.1 < 0) (hUs : 0 < U.1)
    (ℓ : H →ₗ[R] SemimoduleCat.sectionsSubmodule (slabTerminalMultispan t).multispan)
    (hℓ : ∀ a (side : Bool), (ℓ a).val (.right side) =
      ∑ i ∈ s, slabThetaEvaluation t (α i a) (n i) (b i) (if side then U else L))
    (a : H) (c : (MultispanShape.ofLinearOrder Bool).L) :
    (ℓ a).val (.left c) = slabTerminalFiniteLift s n b t α a := by
  have hc : c = default := Subsingleton.elim _ _
  subst c
  have hface := (slabTerminalMultispan t).mem_sectionsSubmodule_multispan.mp (ℓ a).property
  apply exponentMaps_jointly_injective (C t * (1 + T 1))
  exact Prod.ext
    (((hface.1 default).trans (hℓ a false)).trans
      (exponentLeftMap_slabTerminalFiniteLift s n b t α hL hLs a).symm)
    (((hface.2 default).trans (hℓ a true)).trans
      (exponentRightMap_slabTerminalFiniteLift s n b t α hU hUs a).symm)

end Mei.FocusFocus
