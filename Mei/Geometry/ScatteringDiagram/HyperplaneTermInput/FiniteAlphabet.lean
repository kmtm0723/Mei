/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.Pushforward

/-!
# Finite alphabet lifts of polynomial function walls

Fix cooriented affine hyperplanes in a lattice `M` and a finite family `E` of terms
`c_α z^{m_α}`, the term `α` lying on the hyperplane `wallIndex α` with `m_α` tangent to it. The
alphabet input (`HyperplaneTermInput.finiteAlphabet`) has the letters `v_α = (m_α, e_α)` of
`PositiveDegrees.finiteAlphabet` as exponents, so that the hyperplane `i` carries the alphabet
wall function `1 + ∑_{wallIndex α = i} c_α z^{v_α}`.

Given positive degree data `(L, P, δ)`, a projection `π : L → M` and an additive map `τ` with
`τ v_α = n_α ∈ P ∖ {0}` and `π n_α = m_α`, an input on the alphabet is lifted along `τ`
(`HyperplaneTermInput.liftFiniteAlphabet`); the lift of the alphabet input has exponents `n_α`
(`HyperplaneTermInput.liftFiniteAlphabet_finiteAlphabet_exponent`). The pushforward of the ray
presentation of the alphabet wall functions along
`DirectedWall.Pushforward.ofFiniteAlphabetLift` is equivalent to the ray presentation of
`1 + ∑ c_α z^{n_α}` in `P`
(`HyperplaneTermInput.diagram_pushforward_ofFiniteAlphabetLift_equivalent`), and the scattering
classes correspond (`HyperplaneTermInput.pushforward_scat_liftFiniteAlphabet`).
Distinct letters lie on distinct rays of the alphabet (`PositiveDegrees.letterRay_injective`),
while their images may lie on one ray of `P`; the equivalence regroups the image rays into the
ray factors of `1 + ∑ c_α z^{n_α}`.

The walls are full affine hyperplanes; walls supported on proper polyhedral subsets of
hyperplanes are not treated. Not formalized here: the maps of shifted modules induced by the
lift, positivity of the lifted wall functions, and the identification
`z^{v_{i,s}} ↦ p_{i,s} z^{s w_i}` for BLM polynomial inputs. The degree inequality of the lift is
`PositiveDegrees.finiteAlphabet_degree_lt`.

The finite alphabet lift follows Burcroff–Lee–Mou, *Positivity of generalized cluster
scattering diagrams*, §9.2 (arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.HyperplaneTermInput

open DirectedWall PositiveDegrees

universe u

variable {R M ι E L : Type u} {V : Type*} [CommRing R] [AddCommGroup M] [Fintype E]
  [DecidableEq E] [AddCommGroup L]

section Alphabet

variable (μ : ι → M →+ ℤ) (hμ : ∀ i, μ i ≠ 0) (a : ι → ℝ) (w : E → ι) (m : E → M)
  (hm : ∀ α, μ (w α) (m α) = 0)

/-- The alphabet input: the hyperplanes `{μ_i = a_i}` of `M`, and the term `α` on the hyperplane
`w α` with the letter `v_α = (m_α, e_α)` as exponent. -/
def finiteAlphabet :
    HyperplaneTermInput (PositiveDegrees.finiteAlphabet m) (AddMonoidHom.fst M (E → ℤ)) ι E where
  normal := μ
  normal_ne_zero := hμ
  offset := a
  wallIndex := w
  exponent := letter m
  exponent_mem := letter_mem m
  exponent_ne_zero := letter_ne_zero m
  normal_exponent α := by simpa using hm α

@[simp]
theorem finiteAlphabet_normal : (finiteAlphabet μ hμ a w m hm).normal = μ := (rfl)

@[simp]
theorem finiteAlphabet_offset : (finiteAlphabet μ hμ a w m hm).offset = a := (rfl)

@[simp]
theorem finiteAlphabet_wallIndex : (finiteAlphabet μ hμ a w m hm).wallIndex = w := (rfl)

@[simp]
theorem finiteAlphabet_exponent : (finiteAlphabet μ hμ a w m hm).exponent = letter m := (rfl)

end Alphabet

variable {m : E → M} {f : PositiveDegrees L} {τ : M × (E → ℤ) →+ L}
  (hτ : ∀ α, τ (letter m α) ∈ f.monoid) (hτ0 : ∀ α, τ (letter m α) ≠ 0)
  {π : L →+ M} (hπ : ∀ α, π (τ (letter m α)) = m α)
  (I : HyperplaneTermInput (PositiveDegrees.finiteAlphabet m) (AddMonoidHom.fst M (E → ℤ)) ι E)

include hπ in
/-- The finite alphabet lift is compatible with the projections to `M`. -/
theorem projection_finiteAlphabetLift {x : M × (E → ℤ)}
    (hx : x ∈ (PositiveDegrees.finiteAlphabet m).monoid) :
    π (PositiveDegrees.finiteAlphabetLift m hτ hτ0 x) = AddMonoidHom.fst M (E → ℤ) x := by
  rw [finiteAlphabetLift_apply]
  exact eq_fst_of_eq_sum m (σ := π.comp τ) hπ ((mem_finiteAlphabet_monoid m).mp hx).2

/-- An input on the finite alphabet lifted along `τ`: the same hyperplanes, with exponents
`τ x_α`. -/
def liftFiniteAlphabet : HyperplaneTermInput f π ι E :=
  I.map (PositiveDegrees.finiteAlphabetLift m hτ hτ0) fun _ hx =>
    projection_finiteAlphabetLift hτ hτ0 hπ hx

@[simp]
theorem liftFiniteAlphabet_normal : (I.liftFiniteAlphabet hτ hτ0 hπ).normal = I.normal := by
  simp [liftFiniteAlphabet]

@[simp]
theorem liftFiniteAlphabet_offset : (I.liftFiniteAlphabet hτ hτ0 hπ).offset = I.offset := by
  simp [liftFiniteAlphabet]

@[simp]
theorem liftFiniteAlphabet_wallIndex :
    (I.liftFiniteAlphabet hτ hτ0 hπ).wallIndex = I.wallIndex := by
  simp [liftFiniteAlphabet]

@[simp]
theorem liftFiniteAlphabet_exponent (α : E) :
    (I.liftFiniteAlphabet hτ hτ0 hπ).exponent α = τ (I.exponent α) := by
  simp [liftFiniteAlphabet]

/-- The lift of the alphabet input has the exponents `n_α = τ v_α`. -/
theorem liftFiniteAlphabet_finiteAlphabet_exponent (μ : ι → M →+ ℤ) (hμ : ∀ i, μ i ≠ 0)
    (a : ι → ℝ) (w : E → ι) (hm : ∀ α, μ (w α) (m α) = 0) (α : E) :
    ((finiteAlphabet μ hμ a w m hm).liftFiniteAlphabet hτ hτ0 hπ).exponent α =
      τ (letter m α) := by
  simp

variable [Algebra ℚ R] [Module.Free ℤ L] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {j : M →+ V} (g : TauCeti.Toric.IsIntegralLattice j)

local notation "Pτ" => Pushforward.ofFiniteAlphabetLift (R := R) (g := g) hτ hτ0 hπ

/-- The lifted input is the input mapped along the degree map of the pushforward data. -/
theorem map_ofFiniteAlphabetLift_degreeMap
    (hPT : ∀ x ∈ (PositiveDegrees.finiteAlphabet m).monoid,
      π ((Pτ).degreeMap x) = AddMonoidHom.fst M (E → ℤ) x) :
    I.map (Pτ).degreeMap hPT = I.liftFiniteAlphabet hτ hτ0 hπ := by
  rw [liftFiniteAlphabet]
  exact map_congr fun α => by rw [Pushforward.ofFiniteAlphabetLift_degreeMap]

variable [Module.Free ℤ M] [DecidableEq M] [DecidableEq ι] [DecidableEq L] (c : E → R)

/-- The pushforward of the ray presentation of an input on the finite alphabet along the finite
alphabet lift is equivalent to the ray presentation of the lifted input. -/
theorem diagram_pushforward_ofFiniteAlphabetLift_equivalent :
    ((I.diagram g c).pushforward (Pτ)).Equivalent
      ((I.liftFiniteAlphabet hτ hτ0 hπ).diagram g c) := by
  have hPT : ∀ x ∈ (PositiveDegrees.finiteAlphabet m).monoid,
      π ((Pτ).degreeMap x) = AddMonoidHom.fst M (E → ℤ) x := fun x hx => by
    rw [Pushforward.ofFiniteAlphabetLift_degreeMap]
    exact projection_finiteAlphabetLift hτ hτ0 hπ hx
  rw [← I.map_ofFiniteAlphabetLift_degreeMap hτ hτ0 hπ g hPT]
  refine I.diagram_pushforward_equivalent (Pτ) (fun y μ hy => ?_) hPT c
    (Pushforward.ofFiniteAlphabetLift_normalMap hτ hτ0 hπ)
    (Pushforward.ofFiniteAlphabetLift_spatialMap hτ hτ0 hπ)
  rw [Pushforward.coe_ofFiniteAlphabetLift_lieHom_of_homogeneous hτ hτ0 hπ y μ hy,
    Pushforward.ofFiniteAlphabetLift_degreeMap, finiteAlphabetLift_apply]

/-- Pushing forward the scattering class of an input on the finite alphabet along the finite
alphabet lift gives the scattering class of the lifted input. -/
theorem pushforward_scat_liftFiniteAlphabet :
    DirectedDiagram.Class.pushforward (Pτ) ((I.diagram g c).Scat (I.diagram_full g c)) =
      ((I.liftFiniteAlphabet hτ hτ0 hπ).diagram g c).Scat
        ((I.liftFiniteAlphabet hτ hτ0 hπ).diagram_full g c) :=
  ((I.diagram g c).pushforward_scat _ _).trans (DirectedDiagram.scat_eq_of_equivalent _ _
    (I.diagram_pushforward_ofFiniteAlphabetLift_equivalent hτ hτ0 hπ g c))

end Mei.HyperplaneTermInput
