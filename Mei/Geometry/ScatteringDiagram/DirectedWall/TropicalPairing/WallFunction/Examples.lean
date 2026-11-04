/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.PositiveDegrees.Basis
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedWall.TropicalPairing.WallFunction
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.RayFactor
public import Mathlib.GroupTheory.IndexNSmul

/-!
# The lattice change for `m₁ = (1, 0)` and `m₂ = (1, 2)`

Let `M = ℤ²`, let `M₀ ⊆ M` be spanned by `m₁ = (1, 0)` and `m₂ = (1, 2)`, of index `ℓ = 2`,
and let `m° = m₁ + m₂ = (2, 2) = 2 • (1, 1)`, so `r = 2`. The coefficient variables are the
exponents `(a, b) ∈ ℕ²` of `x^{a m₁ + b m₂}`. In `M` they have coordinates
`latticeCoord (a, b) = (a + b, 2b)`; in `ℓ⁻¹M₀ = ½M₀`, with basis `½m₁, ½m₂`, they have
coordinates `halfLatticeCoord (a, b) = (2a, 2b)`. The inclusion `M ⊆ ½M₀` is
`latticeChange (x, y) = (2x - y, y)`, of index two, and the degree map is the identity.

The normal map `μ ↦ μ ∘ latticeCoord` satisfies `ν μ ∘ latticeChange = 2 • μ`, which gives the
finite-index pushforward `latticeChangePushforward`. It keeps the normal `n°(x, y) = x - y`
of the diagonal (`latticeChangeNormal_diagonalNormal`); this is primitive for both lattices, and
the comparison scalar is `r = 2`. Hence:

* the function-wall label of `(1 + c z^{(1,1)})²` over `M` is pushed to the function-wall label
  of `1 + c z^{(1,1)}` over `½M₀` (`latticeChangePushforward_completedMap`);
* the wall on the diagonal labelled by the ray factor of the first label is pushed to the wall
  on the same ray labelled by the ray factor of the second
  (`diagonalWall_pushforward_label`).

So the wall function over `M` is the square of the wall function over `½M₀`, as in the lattice
change of Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*,
Theorem 9.5 (arXiv:2503.03719v1). The invariants `ℓ = 2` and `r = 2` of this lattice are
computed in `Mei.DualLatticeIndex.Examples`.
-/

public section

noncomputable section

namespace Mei.DirectedWall.LatticeChange.Examples

open LogarithmicVectorField TauCeti.Toric

/-- The positive quadrant `ℕ²` of `ℤ²`, with coordinate-sum degree. -/
local notation "ℕ²" => Module.Basis.positiveDegrees (Module.Basis.finTwoProd ℤ)

/-- The coordinates `(a + b, 2b)` in `M = ℤ²` of `a m₁ + b m₂`. -/
def latticeCoord : ℤ × ℤ →+ ℤ × ℤ :=
  (AddMonoidHom.fst ℤ ℤ + AddMonoidHom.snd ℤ ℤ).prod ((2 : ℤ) • AddMonoidHom.snd ℤ ℤ)

@[simp]
theorem latticeCoord_apply (x : ℤ × ℤ) : latticeCoord x = (x.1 + x.2, 2 * x.2) := by
  simp [latticeCoord]

/-- The coordinates `(2a, 2b)` of `a m₁ + b m₂` in `½M₀`, with basis `½m₁, ½m₂`. -/
def halfLatticeCoord : ℤ × ℤ →+ ℤ × ℤ :=
  ((2 : ℤ) • AddMonoidHom.fst ℤ ℤ).prod ((2 : ℤ) • AddMonoidHom.snd ℤ ℤ)

@[simp]
theorem halfLatticeCoord_apply (x : ℤ × ℤ) : halfLatticeCoord x = (2 * x.1, 2 * x.2) := by
  simp [halfLatticeCoord]

/-- The inclusion `M ⊆ ½M₀` in coordinates: `(x, y) ↦ (2x - y, y)`. -/
def latticeChange : ℤ × ℤ →+ ℤ × ℤ :=
  ((2 : ℤ) • AddMonoidHom.fst ℤ ℤ - AddMonoidHom.snd ℤ ℤ).prod (AddMonoidHom.snd ℤ ℤ)

@[simp]
theorem latticeChange_apply (x : ℤ × ℤ) : latticeChange x = (2 * x.1 - x.2, x.2) := by
  simp [latticeChange]

theorem latticeChange_injective : Function.Injective latticeChange := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simp only [latticeChange_apply, Prod.mk.injEq] at h
  simp only [Prod.mk.injEq]
  omega

/-- The image of `M` in `½M₀` contains `2 • ½M₀`, so it has finite index. -/
instance : latticeChange.range.FiniteIndex := by
  have : (nsmulAddMonoidHom (α := ℤ × ℤ) 2).range.FiniteIndex :=
    ⟨by rw [AddSubgroup.index_range_nsmul]; norm_num⟩
  refine AddSubgroup.finiteIndex_of_le (H := (nsmulAddMonoidHom (α := ℤ × ℤ) 2).range) ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨(x.1 + x.2, 2 * x.2), ?_⟩
  simp only [Prod.ext_iff, latticeChange_apply, nsmulAddMonoidHom_apply, two_nsmul,
    Prod.fst_add, Prod.snd_add]
  omega

/-- The two coordinate maps are compatible with the inclusion `M ⊆ ½M₀`. -/
theorem halfLatticeCoord_eq_latticeChange (n : ℤ × ℤ) (_ : n ∈ ℕ².monoid) :
    halfLatticeCoord (PositiveDegreeMap.id ℕ² n) = latticeChange (latticeCoord n) := by
  simp only [Prod.ext_iff, PositiveDegreeMap.id_apply, halfLatticeCoord_apply,
    latticeChange_apply, latticeCoord_apply, and_true]
  omega

/-- The normal map `μ ↦ μ ∘ latticeCoord`, where `latticeCoord ∘ latticeChange = 2`. -/
def latticeChangeNormal (μ : ℤ × ℤ →+ ℤ) : ℤ × ℤ →+ ℤ := μ.comp latticeCoord

@[simp]
theorem latticeChangeNormal_apply (μ : ℤ × ℤ →+ ℤ) (x : ℤ × ℤ) :
    latticeChangeNormal μ x = μ (x.1 + x.2, 2 * x.2) := by
  simp [latticeChangeNormal]

/-- The normal map pulls back along `latticeChange` to twice the original normal. -/
theorem latticeChangeNormal_apply_latticeChange (μ : ℤ × ℤ →+ ℤ) (x : ℤ × ℤ) :
    (latticeChangeNormal μ (latticeChange x) : ℚ) = 2 * μ x := by
  have hx : ((2 * x.1 - x.2 + x.2, 2 * x.2) : ℤ × ℤ) = (2 : ℤ) • x := by
    simp only [Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, and_true]
    omega
  rw [latticeChangeNormal_apply, latticeChange_apply, hx, map_zsmul, smul_eq_mul, Int.cast_mul,
    Int.cast_ofNat]

/-- The normal `n°(x, y) = x - y` of the diagonal. -/
def diagonalNormal : ℤ × ℤ →+ ℤ := AddMonoidHom.fst ℤ ℤ - AddMonoidHom.snd ℤ ℤ

@[simp]
theorem diagonalNormal_apply (x : ℤ × ℤ) : diagonalNormal x = x.1 - x.2 := by
  simp [diagonalNormal]

/-- The normal of the diagonal is kept: `n°` is primitive both in the dual of `M` and in the
dual of `½M₀`, and `n° ∘ latticeChange = 2 • n°` with `r = 2`. -/
@[simp]
theorem latticeChangeNormal_diagonalNormal : latticeChangeNormal diagonalNormal = diagonalNormal :=
  AddMonoidHom.ext fun x => by
    simp only [latticeChangeNormal_apply, diagonalNormal_apply]
    omega

variable (h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The finite-index pushforward along `M ⊆ ½M₀` over `ℚ`, with identity degree map, normal map
`μ ↦ μ ∘ latticeCoord` and comparison scalar `2`. -/
def latticeChangePushforward :
    Pushforward ℕ² ℕ² h h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord)
      (tropicalVertexWallSpaces ℕ² halfLatticeCoord) :=
  Pushforward.ofFiniteIndex (PositiveDegreeMap.id ℕ²) latticeChange latticeChange_injective
    halfLatticeCoord_eq_latticeChange latticeChangeNormal (fun _ => 2) (fun _ => two_pos)
    latticeChangeNormal_apply_latticeChange

/-- The diagonal degree `(1, 1)` is an allowed degree. -/
theorem one_one_mem : ((1 : ℤ), (1 : ℤ)) ∈ ℕ².monoid := by
  simp [Fin.forall_fin_two]

/-- The diagonal degree `(1, 1)` is tangent to `n°` in both coordinates. -/
theorem one_one_mem_tropicalTangentMonoid {ρ₀ : ℤ × ℤ →+ ℤ × ℤ}
    (hρ₀ : diagonalNormal (ρ₀ (1, 1)) = 0) :
    ((1 : ℤ), (1 : ℤ)) ∈
      tropicalTangentMonoid ℕ² ρ₀ ((Int.castAddHom ℚ).comp diagonalNormal) := by
  rw [mem_tropicalTangentMonoid]
  exact ⟨one_one_mem, by simp [hρ₀]⟩

local notation "G" ρ₀ => TropicalVertexCoefficientAction.filtration (R := ℚ) ℕ²
  (tropicalTangentMonoid ℕ² ρ₀ (AddMonoidHom.comp (Int.castAddHom ℚ) diagonalNormal))

/-- The completed tangent series `1 + c z^{(1,1)}`, congruent to one. -/
def diagonalFunction (ρ₀ : ℤ × ℤ →+ ℤ × ℤ) (hρ₀ : diagonalNormal (ρ₀ (1, 1)) = 0) (c : ℚ) :
    {u : (G ρ₀).completion // u - 1 ∈ (G ρ₀).completionIdeal 1} :=
  ⟨(G ρ₀).toCompletion
      (1 + AddMonoidAlgebra.single ⟨(1, 1), one_one_mem_tropicalTangentMonoid hρ₀⟩ c), by
    rw [← map_one (G ρ₀).toCompletion, ← map_sub,
      AlgFiltration.toCompletion_mem_completionIdeal_iff,
      add_sub_cancel_left, TropicalVertexCoefficientAction.filtration_ideal,
      AddSubmonoid.single_mem_monoidAlgebraIdeal_iff]
    exact Or.inr ⟨⟨(1, 1), one_one_mem_tropicalTangentMonoid hρ₀⟩,
      AddSubmonoid.mem_comap.mpr one_one_mem, by simp, 0, by simp⟩⟩

@[simp]
theorem coe_diagonalFunction (ρ₀ : ℤ × ℤ →+ ℤ × ℤ) (hρ₀ : diagonalNormal (ρ₀ (1, 1)) = 0)
    (c : ℚ) :
    (diagonalFunction ρ₀ hρ₀ c : (G ρ₀).completion) =
      (G ρ₀).toCompletion (1 + AddMonoidAlgebra.single
        ⟨(1, 1), one_one_mem_tropicalTangentMonoid hρ₀⟩ c) := by
  simp only [diagonalFunction]

theorem diagonalNormal_latticeCoord : diagonalNormal (latticeCoord (1, 1)) = 0 := by simp

theorem diagonalNormal_halfLatticeCoord : diagonalNormal (halfLatticeCoord (1, 1)) = 0 := by simp

/-- The square of `1 + c z^{(1,1)}` over `M`. -/
def squaredDiagonalFunction (c : ℚ) :
    {u : (G latticeCoord).completion // u - 1 ∈ (G latticeCoord).completionIdeal 1} :=
  ⟨(diagonalFunction latticeCoord diagonalNormal_latticeCoord c : (G latticeCoord).completion) ^ 2,
    (G latticeCoord).pow_sub_one_mem _ 2⟩

@[simp]
theorem coe_squaredDiagonalFunction (c : ℚ) :
    (squaredDiagonalFunction c : (G latticeCoord).completion) =
      (diagonalFunction latticeCoord diagonalNormal_latticeCoord c :
        (G latticeCoord).completion) ^ 2 := by
  simp only [squaredDiagonalFunction]

/-- The tangent monomial map of the identity degree map sends `(1 + c z^{(1,1)})²` over `M` to
the square of `1 + c z^{(1,1)}` over `½M₀`. -/
theorem completedTropicalTangentMap_squaredDiagonalFunction
    (hT : (tropicalTangentMonoid ℕ² latticeCoord ((Int.castAddHom ℚ).comp diagonalNormal)).map
      (PositiveDegreeMap.id ℕ²).toAddMonoidHom ≤
        tropicalTangentMonoid ℕ² halfLatticeCoord ((Int.castAddHom ℚ).comp diagonalNormal))
    (c : ℚ) :
    completedTropicalTangentMap (PositiveDegreeMap.id ℕ²) hT (squaredDiagonalFunction c) =
      (diagonalFunction halfLatticeCoord diagonalNormal_halfLatticeCoord c :
        (G halfLatticeCoord).completion) ^ 2 := by
  have he : (⟨PositiveDegreeMap.id ℕ² (1, 1), hT (AddSubmonoid.mem_map_of_mem _
      (one_one_mem_tropicalTangentMonoid diagonalNormal_latticeCoord))⟩ :
        tropicalTangentMonoid ℕ² halfLatticeCoord ((Int.castAddHom ℚ).comp diagonalNormal)) =
      ⟨(1, 1), one_one_mem_tropicalTangentMonoid diagonalNormal_halfLatticeCoord⟩ :=
    Subtype.ext (PositiveDegreeMap.id_apply _)
  rw [coe_squaredDiagonalFunction, map_pow, coe_diagonalFunction, coe_diagonalFunction,
    completedTropicalTangentMap_toCompletion, map_add, map_one, tropicalTangentMap_single, he]

/-- The normal `n°` pulls back along `M ⊆ ½M₀` to `2 • n°`. -/
theorem diagonalNormal_latticeChange (x : ℤ × ℤ) :
    (diagonalNormal (latticeChange x) : ℚ) = 2 * diagonalNormal x := by
  simpa using latticeChangeNormal_apply_latticeChange diagonalNormal x

/-- **Square of the wall function.** The pushforward along `M ⊆ ½M₀` sends the function-wall
label of `(1 + c z^{(1,1)})²` with normal `n°` over `M` to the function-wall label of
`1 + c z^{(1,1)}` with normal `n°` over `½M₀`. -/
theorem latticeChangePushforward_completedMap (c : ℚ) :
    (latticeChangePushforward h).lieHom.completedMap
        (ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² latticeCoord
          ((Int.castAddHom ℚ).comp diagonalNormal)
          ((G latticeCoord).completedLog (squaredDiagonalFunction c)))) =
      ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² halfLatticeCoord
        ((Int.castAddHom ℚ).comp diagonalNormal) ((G halfLatticeCoord).completedLog
          (diagonalFunction halfLatticeCoord diagonalNormal_halfLatticeCoord c))) :=
  Pushforward.ofFiniteIndex_lieHom_completedMap_completedBCHExp_completedLog _ _ _ _ _ _ _ _ _
    diagonalNormal_latticeChange (r := 2) (by norm_num) _ _
    (completedTropicalTangentMap_squaredDiagonalFunction _ c)

/-- The vector `(1, 1)` is primitive in `ℤ²`. -/
theorem isPrimitive_one_one : TauCeti.IsPrimitive ((1, 1) : ℤ × ℤ) :=
  TauCeti.isPrimitive_def.mpr ⟨LinearMap.fst ℤ ℤ ℤ, by simp⟩

/-- The supported ray of the diagonal degree `(1, 1)`. -/
def diagonalRay : SupportedRay ℕ² := SupportedRay.ofMem (1, 1) one_one_mem isPrimitive_one_one

@[simp]
theorem diagonalRay_generator : diagonalRay.generator = (1, 1) :=
  SupportedRay.generator_ofMem _ _ _

theorem diagonalNormal_ne_zero : diagonalNormal ≠ 0 := fun he => by
  simpa using DFunLike.congr_fun he (1, 0)

/-- The diagonal `{x = y}` of `ℝ²` as a wall over `M` on the ray `(1, 1)`, with normal `n°`,
labelled by the ray factor of the function-wall label of `(1 + c z^{(1,1)})²`. -/
def diagonalWall (c : ℚ) :
    DirectedWall (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) :=
  ofAffineHyperplane _ _ diagonalNormal diagonalNormal_ne_zero 0 diagonalRay (by simp)
    ⟨ℕ².rayFactor _ (ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² latticeCoord
      ((Int.castAddHom ℚ).comp diagonalNormal)
      ((G latticeCoord).completedLog (squaredDiagonalFunction c)))) diagonalRay,
      rayFactor_completedBCHExp_completedTropicalTangentField_mem_wallGroup _ _ _ _ _⟩

@[simp]
theorem diagonalWall_normal (c : ℚ) : (diagonalWall h c).normal = diagonalNormal :=
  ofAffineHyperplane_normal ..

@[simp]
theorem diagonalWall_ray (c : ℚ) : (diagonalWall h c).ray = diagonalRay :=
  ofAffineHyperplane_ray ..

@[simp]
theorem diagonalWall_support (c : ℚ) :
    (diagonalWall h c).support = {x | h.realCharacter diagonalNormal x = 0} :=
  ofAffineHyperplane_support ..

@[simp]
theorem diagonalWall_label (c : ℚ) :
    (diagonalWall h c).label = ℕ².rayFactor _ (ℕ².completedBCHExp _
      (completedTropicalTangentField ℕ² latticeCoord ((Int.castAddHom ℚ).comp diagonalNormal)
        ((G latticeCoord).completedLog (squaredDiagonalFunction c)))) diagonalRay :=
  ofAffineHyperplane_label ..

/-- **Square of the wall function, on a ray wall.** The diagonal wall over `M` labelled by the
ray factor of `(1 + c z^{(1,1)})²` is pushed to the wall on the same ray labelled by the ray
factor of `1 + c z^{(1,1)}` over `½M₀`. -/
theorem diagonalWall_pushforward_label (c : ℚ) :
    ((diagonalWall h c).pushforward (latticeChangePushforward h)).label =
      ℕ².rayFactor _ (ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² halfLatticeCoord
        ((Int.castAddHom ℚ).comp diagonalNormal) ((G halfLatticeCoord).completedLog
          (diagonalFunction halfLatticeCoord diagonalNormal_halfLatticeCoord c)))) diagonalRay :=
  (pushforward_ofFiniteIndex_id_label _ _ _ _ _ _ _ _ diagonalNormal_latticeChange (r := 2)
    (by norm_num) _ _
    (by rw [diagonalWall_label, diagonalWall_ray])
    (completedTropicalTangentMap_squaredDiagonalFunction _ c)).trans
      (by rw [diagonalWall_ray])

end Mei.DirectedWall.LatticeChange.Examples
