/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.Pushforward
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Dilation
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.GermLabel
public import Mei.Geometry.ScatteringDiagram.DirectedWall.TropicalPairing.WallFunction.Examples
public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.LatticeChange.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.TangentLabel

/-!
# The incoming lines of the lattice change for `m₁ = (1, 0)` and `m₂ = (1, 2)`

Let `M = ℤ²`, let `M₀ ⊆ M` be spanned by `m₁ = (1, 0)` and `m₂ = (1, 2)`, of index `ℓ = 2`, and
use the coordinates of `Mei.DirectedWall.LatticeChange.Examples`: the coefficient exponent
`(a, b) ∈ ℕ²` of `x^{a m₁ + b m₂}` has coordinates `latticeCoord (a, b) = (a + b, 2b)` in `M` and
`halfLatticeCoord (a, b) = (2a, 2b)` in `½M₀`, with basis `½m₁, ½m₂`, and `M ⊆ ½M₀` is
`latticeChange (x, y) = (2x - y, y)`. These are the coordinates of `Mei.RankTwoLatticeChange`
for this lattice. Most results below are instances of the general lattice change of two lines
(for example `Mei.RankTwoLatticeChange.exists_germLabel_eq_of_toClass_eq`), for the normal map
`primitiveLatticeChangeNormal` of this file.

The incoming lines `ℝm₁` and `ℝm₂` carry the functions `1 + ∑_{k < K} c_{i,k} x^{(k+1) m_i}`
(`Mei.RankTwoLatticeChange.lineInput`). Over `M` they are cooriented by the normals `e₂*` and
`2e₁* - e₂*` (`latticeLineInput`); over `½M₀` by the normals `e₂*` and `e₁*`
(`halfLatticeLineInput`). Both normals of `M` are restrictions of the normals of `½M₀`, so the
comparison scalar is one on them (`primitiveLatticeChangeNormal_lineNormal`,
`primitiveLatticeChangeScalar_lineNormal`).

The normal map `primitiveLatticeChangeNormal` sends `μ` to the integral character `μ ∘ t⁻¹` of
`½M₀` when it exists, that is when `μ (1, 0)` is even, and to `μ ∘ latticeCoord`, with
comparison scalar `2`, otherwise; for instance it keeps the normal `x - y` of the diagonal. It
gives the finite-index pushforward `primitiveLatticeChangePushforward`, which sends the input
over `M` to the input over `½M₀` (`latticeLineInput_map`). Hence its pushforward of the ray
presentation over `M` is equivalent to the ray presentation over `½M₀`
(`latticeLineInput_pushforward_equivalent`), and it carries the scattering class over `M` to the
scattering class over `½M₀` (`latticeLineInput_pushforward_scat`), so it sends representatives
of the first class to representatives of the second (`latticeLineInput_toClass_pushforward`).

The normal `n° = x - y` of the diagonal `ℝ(1, 1)`, along `m° = m₁ + m₂ = 2 • (1, 1)`, is kept
with comparison scalar `r = 2`. So if a diagram over `M` has a function-wall grouping whose
normals stay primitive under `primitiveLatticeChangeNormal`, and one of its groups has the label
of `(1 + a z^{(1,1)})²` with normal `n°`, then the pushed group has the label of `1 + a z^{(1,1)}`
with normal `n°` over `½M₀` (`diagonal_label_pushforward`); the grouping and the label are
hypotheses. If the diagram over `M` represents the scattering class over `M`, the same label is
carried by any representative of the scattering class over `½M₀` on a group whose crossing
germs at every order are the images of crossing germs of the diagonal group
(`diagonal_label_of_toClass_eq`); these crossing germs are hypotheses. This uses
`DirectedDiagram.FunctionWallGrouping.label_eq_of_equivalent_pushforward_ofFiniteIndex`.

At the level of germ labels no grouping is needed. For any representatives `D` over `M` and `E`
over `½M₀`, every open set meeting the diagonal line (`diagonalLine`) contains a point `θ` that is
generic for `D` on the line, with image `S θ` under the spatial map generic for `E` on the image
line (`exists_isGenericPoint_diagonalLine`). If the germ label of `D` at such a `θ`, in a
direction `v` crossing the diagonal negatively, is the label of `(1 + a z^{(1,1)})²` with normal
`n°`, then the germ label of `E` at `S θ` in the direction `S v` is the label of `1 + a z^{(1,1)}`
with normal `n°` (`diagonal_germLabel_of_toClass_eq`), by
`DirectedDiagram.Equivalent.germLabel_eq_pushforward`.

These germ labels are function-wall labels, and the wall function over `M` is the square of the
wall function over `½M₀`. Every active wall of `D` through `θ` lies on the diagonal ray `(1, 1)`
with a normal proportional to `n°` (`label_mem_wallGroup_of_isGenericPoint_diagonalLine`), so the
germ label of `D` at `θ` is the function-wall label of a completed tangent series `f₀`, by
`Mei.exists_eq_completedBCHExp_completedTropicalTangentField_completedLog_of_mem_wallGroup`. Its
pushforward is the function-wall label of a square root `f₁` of `f₀`, which is the germ label of
`E` at `S θ` (`exists_diagonal_germLabel_eq_of_toClass_eq`). Conversely, the completed Lie map of
the lattice change is injective, so for any `f₀ = f₁ ^ 2` the germ label of `E` at `S θ` is the
label of `f₁` exactly when the germ label of `D` at `θ` is the label of `f₀`
(`diagonal_germLabel_eq_iff_of_toClass_eq`): whatever the wall function over `½M₀` is, the wall
function over `M` is its square.

The lines pass through the origin (`Mei.RankTwoLatticeChange.lineInput_diagram_wall_support`),
so both scattering classes are classes of central inputs, and their germ labels along open rays
of the diagonal do not depend on the representative or on the generic point
(`DirectedDiagram.germLabel_smul_eq_of_toClass_eq_scat`). Over `M` this is
`diagonal_germLabel_smul_eq`: for representatives `D` and `D'` over `M`, the germ label of `D'` at
a generic point `t • θ`, `t > 0`, is the germ label of `D` at the generic point `θ`. Hence the
germ label `(1 + a z^{(1,1)})²` of `D` at a single generic point `θ` gives the germ label
`1 + a z^{(1,1)}` of every representative `E` over `½M₀` at every point `t • S θ`, `t > 0`, that
is generic for `E`, whether or not `S θ` is (`diagonal_germLabel_smul_of_toClass_eq`).

So for this lattice the file proves: the pushforward of the ray presentation of the lines, the
pushforward of their scattering class and of its representatives, the transport of a given
function-wall label on the diagonal, its comparison with groups of representatives over `½M₀`
that are matched with it by crossing germs, the transport of a given germ label on the
diagonal from any representative over `M` to any representative over `½M₀`, the independence
of these germ labels of the point on an open ray of the diagonal, and the existence of the
diagonal wall functions over `M` and over `½M₀` at common generic points, the first the square
of the second. It does not compute the scattering class: the wall functions are not determined,
and the label `(1 + a z^{(1,1)})²` over `M` in `diagonal_germLabel_of_toClass_eq` is a
hypothesis.

The lattice change is motivated by Burcroff–Lee–Mou, *Positivity of generalized cluster
scattering diagrams*, Theorem 9.5 (arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.HyperplaneTermInput.FiniteIndex.Examples

open DirectedWall DirectedDiagram TauCeti.Toric DirectedWall.LatticeChange.Examples

/-- The positive quadrant `ℕ²` of `ℤ²`, with coordinate-sum degree. -/
local notation "ℕ²" => Module.Basis.positiveDegrees (Module.Basis.finTwoProd ℤ)

/-- The normal map of `M ⊆ ½M₀` sending `μ` to `μ ∘ latticeChange⁻¹` when `μ (1, 0)` is even, and
to `μ ∘ latticeCoord` otherwise. -/
def primitiveLatticeChangeNormal (μ : ℤ × ℤ →+ ℤ) : ℤ × ℤ →+ ℤ :=
  if Even (μ (1, 0)) then
    (μ (1, 0) / 2) • (AddMonoidHom.fst ℤ ℤ + AddMonoidHom.snd ℤ ℤ) +
      μ (0, 1) • AddMonoidHom.snd ℤ ℤ
  else latticeChangeNormal μ

/-- The comparison scalar of `primitiveLatticeChangeNormal`: `1` when `μ (1, 0)` is even and `2`
otherwise. -/
def primitiveLatticeChangeScalar (μ : ℤ × ℤ →+ ℤ) : ℚ := if Even (μ (1, 0)) then 1 else 2

/-- For even `μ (1, 0)`, the normal is `(x, y) ↦ (μ (1, 0) / 2) (x + y) + μ (0, 1) y`. -/
theorem primitiveLatticeChangeNormal_apply_of_even {μ : ℤ × ℤ →+ ℤ} (hμ : Even (μ (1, 0)))
    (x : ℤ × ℤ) :
    primitiveLatticeChangeNormal μ x = μ (1, 0) / 2 * (x.1 + x.2) + μ (0, 1) * x.2 := by
  simp [primitiveLatticeChangeNormal, hμ, mul_add]

/-- For odd `μ (1, 0)`, the normal is `μ ∘ latticeCoord`. -/
theorem primitiveLatticeChangeNormal_of_not_even {μ : ℤ × ℤ →+ ℤ} (hμ : ¬Even (μ (1, 0))) :
    primitiveLatticeChangeNormal μ = latticeChangeNormal μ := by
  simp [primitiveLatticeChangeNormal, hμ]

/-- For even `μ (1, 0)`, the comparison scalar is `1`. -/
theorem primitiveLatticeChangeScalar_of_even {μ : ℤ × ℤ →+ ℤ} (hμ : Even (μ (1, 0))) :
    primitiveLatticeChangeScalar μ = 1 := by
  simp [primitiveLatticeChangeScalar, hμ]

/-- For odd `μ (1, 0)`, the comparison scalar is `2`. -/
theorem primitiveLatticeChangeScalar_of_not_even {μ : ℤ × ℤ →+ ℤ} (hμ : ¬Even (μ (1, 0))) :
    primitiveLatticeChangeScalar μ = 2 := by
  simp [primitiveLatticeChangeScalar, hμ]

/-- The comparison scalars are positive. -/
theorem primitiveLatticeChangeScalar_pos (μ : ℤ × ℤ →+ ℤ) : 0 < primitiveLatticeChangeScalar μ := by
  by_cases hμ : Even (μ (1, 0))
  · rw [primitiveLatticeChangeScalar_of_even hμ]
    exact one_pos
  · rw [primitiveLatticeChangeScalar_of_not_even hμ]
    exact two_pos

/-- The normal map pulls back along `latticeChange` to the comparison scalar times the
original normal. -/
theorem primitiveLatticeChangeNormal_apply_latticeChange (μ : ℤ × ℤ →+ ℤ) (x : ℤ × ℤ) :
    (primitiveLatticeChangeNormal μ (latticeChange x) : ℚ) =
      primitiveLatticeChangeScalar μ * μ x := by
  by_cases hμ : Even (μ (1, 0))
  · obtain ⟨k, hk⟩ := hμ
    have hμx : μ x = x.1 * μ (1, 0) + x.2 * μ (0, 1) := by
      rw [← smul_eq_mul, ← smul_eq_mul, ← map_zsmul, ← map_zsmul, ← map_add]
      congr 1
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, and_self]
    have hx : primitiveLatticeChangeNormal μ (latticeChange x) = μ x := by
      rw [primitiveLatticeChangeNormal_apply_of_even ⟨k, hk⟩, hμx, hk, latticeChange_apply,
        show (k + k) / 2 = k by omega]
      ring
    rw [hx, primitiveLatticeChangeScalar_of_even ⟨k, hk⟩, one_mul]
  · rw [primitiveLatticeChangeNormal_of_not_even hμ, primitiveLatticeChangeScalar_of_not_even hμ]
    exact latticeChangeNormal_apply_latticeChange μ x

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The finite-index pushforward along `M ⊆ ½M₀`, with identity degree map and normal map
`primitiveLatticeChangeNormal`: the lattice change `RankTwoLatticeChange.pushforward` for this
normal map. -/
abbrev primitiveLatticeChangePushforward :
    Pushforward ℕ² ℕ² h h (tropicalVertexWallSpaces (R := R) ℕ² latticeCoord)
      (tropicalVertexWallSpaces ℕ² halfLatticeCoord) :=
  RankTwoLatticeChange.pushforward R h det_generators_pos primitiveLatticeChangeNormal
    primitiveLatticeChangeScalar primitiveLatticeChangeScalar_pos
    primitiveLatticeChangeNormal_apply_latticeChange

/-- The normals `e₂*` of `ℝm₁` and `2e₁* - e₂*` of `ℝm₂` in `M`: the normals `det(m₁, ·)` and
`det(·, m₂)` of `RankTwoLatticeChange.lineNormal`. -/
abbrev lineNormal : Fin 2 → ℤ × ℤ →+ ℤ := RankTwoLatticeChange.lineNormal (1, 0) (1, 2)

/-- The normals `e₂*` of `ℝm₁` and `e₁*` of `ℝm₂` in `½M₀`. -/
abbrev halfLineNormal : Fin 2 → ℤ × ℤ →+ ℤ := RankTwoLatticeChange.sublatticeLineNormal

/-- The normal of `ℝm₁` in `M` is `e₂*`. -/
@[simp]
theorem lineNormal_zero : lineNormal 0 = AddMonoidHom.snd ℤ ℤ :=
  AddMonoidHom.ext fun x => by simp [Prod.det_apply]

/-- The normal of `ℝm₂` in `M` is `2e₁* - e₂*`. -/
@[simp]
theorem lineNormal_one :
    lineNormal 1 = (2 : ℤ) • AddMonoidHom.fst ℤ ℤ - AddMonoidHom.snd ℤ ℤ :=
  AddMonoidHom.ext fun x => by simp [Prod.det_apply, mul_comm]

/-- The incoming lines `ℝm₁` and `ℝm₂` over `M`, with the normals `lineNormal`. -/
abbrev latticeLineInput (K : ℕ) : HyperplaneTermInput ℕ² latticeCoord (Fin 2) (Fin 2 × Fin K) :=
  RankTwoLatticeChange.latticeLineInput det_generators_pos K

/-- The incoming lines `ℝm₁` and `ℝm₂` over `½M₀`, with the normals `halfLineNormal`. -/
abbrev halfLatticeLineInput (K : ℕ) :
    HyperplaneTermInput ℕ² halfLatticeCoord (Fin 2) (Fin 2 × Fin K) :=
  RankTwoLatticeChange.sublatticeLineInput (1, 0) (1, 2) K

/-- The normal map sends the normals of the lines in `M` to their normals in `½M₀`. -/
theorem primitiveLatticeChangeNormal_lineNormal (i : Fin 2) :
    primitiveLatticeChangeNormal (lineNormal i) = halfLineNormal i := by
  ext x
  have he : Even (lineNormal i (1, 0)) := by fin_cases i <;> simp
  rw [primitiveLatticeChangeNormal_apply_of_even he]
  fin_cases i <;> simp

/-- The normals of the lines `ℝm_i` over `M` have comparison scalar one. -/
theorem primitiveLatticeChangeScalar_lineNormal (K : ℕ) (i : Fin 2) :
    primitiveLatticeChangeScalar ((latticeLineInput K).normal i) = 1 :=
  RankTwoLatticeChange.scalar_latticeLineInput_normal det_generators_pos
    primitiveLatticeChangeNormal_apply_latticeChange primitiveLatticeChangeNormal_lineNormal K i

/-- The input over `M` mapped along `latticeChange` with the normals
`primitiveLatticeChangeNormal` is the input over `½M₀`. -/
theorem latticeLineInput_map (K : ℕ) :
    (latticeLineInput K).map (PositiveDegreeMap.id ℕ²) latticeChange
        halfLatticeCoord_eq_latticeChange
        (fun i => primitiveLatticeChangeNormal ((latticeLineInput K).normal i))
        ((latticeLineInput K).comp_normal_of_ofFiniteIndex latticeChange
          primitiveLatticeChangeNormal_apply_latticeChange
          (primitiveLatticeChangeScalar_lineNormal K)) =
      halfLatticeLineInput K :=
  RankTwoLatticeChange.latticeLineInput_map det_generators_pos
    primitiveLatticeChangeNormal_apply_latticeChange
    primitiveLatticeChangeNormal_lineNormal K

variable {K : ℕ} (c : Fin 2 × Fin K → R)

/-- **Incoming lines under the lattice change.** The pushforward along `M ⊆ ½M₀` of the ray
presentation of the lines `ℝm_i` with functions `1 + ∑_{k < K} c_{i,k} x^{(k+1) m_i}` over `M` is
equivalent to the ray presentation of the same lines and functions over `½M₀`. -/
theorem latticeLineInput_pushforward_equivalent :
    (((latticeLineInput K).diagram h c).pushforward
      (primitiveLatticeChangePushforward R h)).Equivalent
        ((halfLatticeLineInput K).diagram h c) :=
  RankTwoLatticeChange.pushforward_equivalent R h det_generators_pos
    primitiveLatticeChangeScalar_pos
    primitiveLatticeChangeNormal_apply_latticeChange primitiveLatticeChangeNormal_lineNormal c

/-- **Scattering classes under the lattice change.** The pushforward along `M ⊆ ½M₀` of the
scattering class of the lines `ℝm_i` with functions `1 + ∑_{k < K} c_{i,k} x^{(k+1) m_i}` over
`M` is the scattering class of the same lines and functions over `½M₀`. -/
theorem latticeLineInput_pushforward_scat :
    Class.pushforward (primitiveLatticeChangePushforward R h)
        (((latticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..)) =
      ((halfLatticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..) :=
  RankTwoLatticeChange.pushforward_scat R h det_generators_pos primitiveLatticeChangeScalar_pos
    primitiveLatticeChangeNormal_apply_latticeChange primitiveLatticeChangeNormal_lineNormal c

/-- A diagram representing the scattering class of the lines over `M` is pushed along `M ⊆ ½M₀`
to a diagram representing the scattering class of the lines over `½M₀`. -/
theorem latticeLineInput_toClass_pushforward {κ : Type}
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ² latticeCoord) κ}
    (hD : D.toClass =
      ((latticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..)) :
    (D.pushforward (primitiveLatticeChangePushforward R h)).toClass =
      ((halfLatticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..) :=
  RankTwoLatticeChange.toClass_pushforward R h det_generators_pos primitiveLatticeChangeScalar_pos
    primitiveLatticeChangeNormal_apply_latticeChange primitiveLatticeChangeNormal_lineNormal c hD

/-- The normal map keeps the normal `n°(x, y) = x - y` of the diagonal. -/
@[simp]
theorem primitiveLatticeChangeNormal_diagonalNormal :
    primitiveLatticeChangeNormal diagonalNormal = diagonalNormal := by
  rw [primitiveLatticeChangeNormal_of_not_even (by simp), latticeChangeNormal_diagonalNormal]

/-- The normal `n°` of the diagonal has comparison scalar `r = 2`. -/
@[simp]
theorem primitiveLatticeChangeScalar_diagonalNormal :
    primitiveLatticeChangeScalar diagonalNormal = 2 :=
  primitiveLatticeChangeScalar_of_not_even (by simp)

/-- The normal `n°` pulls back along `M ⊆ ½M₀` to its comparison scalar times `n°`. -/
theorem diagonalNormal_latticeChange_eq_scalar_mul (x : ℤ × ℤ) :
    (diagonalNormal (latticeChange x) : ℚ) =
      primitiveLatticeChangeScalar diagonalNormal * diagonalNormal x := by
  rw [primitiveLatticeChangeScalar_diagonalNormal]
  exact diagonalNormal_latticeChange x

/-- `m° = m₁ + m₂ = 2 • (1, 1)`. -/
theorem two_nsmul_one_one :
    (2 : ℕ) • ((1, 1) : ℤ × ℤ) = (1 : ℤ) • ((1, 0) : ℤ × ℤ) + (1 : ℤ) • ((1, 2) : ℤ × ℤ) := by
  decide

/-- The diagonal ray is the supported ray `RankTwoLatticeChange.coefficientRay` of `(1, 1)`. -/
theorem diagonalRay_eq_coefficientRay :
    diagonalRay = RankTwoLatticeChange.coefficientRay isCoprime_one_left zero_le_one zero_le_one :=
  SupportedRay.ext (by rw [diagonalRay_generator, RankTwoLatticeChange.coefficientRay_generator])

local notation "F" ρ₀ => TropicalVertexCoefficientAction.filtration (R := ℚ) ℕ²
  (tropicalTangentMonoid ℕ² ρ₀ (AddMonoidHom.comp (Int.castAddHom ℚ) diagonalNormal))

/-- **Transport of a diagonal group label.** Let a diagram over `M` have a function-wall
grouping whose normals stay primitive under `primitiveLatticeChangeNormal`, and let its group
`g` have the function-wall label of `(1 + a z^{(1,1)})²` with normal `n°`. Then the group `g` of
the pushforward along `M ⊆ ½M₀` has the function-wall label of `1 + a z^{(1,1)}` with normal
`n°`. -/
theorem diagonal_label_pushforward {κ M κ' : Type*} [AddCommGroup M] {π : ℤ × ℤ →+ M}
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    (G : D.FunctionWallGrouping π κ')
    (hprim : ∀ j, TauCeti.IsPrimitive (primitiveLatticeChangeNormal (D.wall j).normal))
    {g : κ'} (a : ℚ)
    (hg : G.label g = ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² latticeCoord
      ((Int.castAddHom ℚ).comp diagonalNormal)
      ((F latticeCoord).completedLog (squaredDiagonalFunction a)))) :
    (G.pushforward (P := primitiveLatticeChangePushforward ℚ h) (π' := π)
        (fun x _ => by rw [RankTwoLatticeChange.pushforward_degreeMap_apply])
        (fun j => by simpa using hprim j)).label g =
      ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² halfLatticeCoord
        ((Int.castAddHom ℚ).comp diagonalNormal) ((F halfLatticeCoord).completedLog
          (diagonalFunction halfLatticeCoord diagonalNormal_halfLatticeCoord a))) :=
  FunctionWallGrouping.label_pushforward_ofFiniteIndex _ _ latticeChange_injective
    halfLatticeCoord_eq_latticeChange primitiveLatticeChangeNormal primitiveLatticeChangeScalar
    primitiveLatticeChangeScalar_pos primitiveLatticeChangeNormal_apply_latticeChange G
    diagonalNormal_latticeChange_eq_scalar_mul
    (r := 2) (by simp) _ _ _ _ hg (completedTropicalTangentMap_squaredDiagonalFunction _ a)

/-- **The diagonal label in matched representatives over `½M₀`.** Let `D` represent the scattering
class of the lines over `M`, with a function-wall grouping whose normals stay primitive under
`primitiveLatticeChangeNormal`, and let its group `g` have the function-wall label of
`(1 + a z^{(1,1)})²` with normal `n°`. Let `E` be any representative of the scattering class of
the lines over `½M₀`, with a function-wall grouping `G'`. Suppose that at every order `k` the
group `g` has a crossing germ at order `k` (the cutoff modulus is the identity), at a point `θ`
and a direction `v`, and that the group `g'` of `G'` has a crossing germ at order `k` at their
images under the spatial map. Then `g'` has the function-wall label of `1 + a z^{(1,1)}` with
normal `n°`. -/
theorem diagonal_label_of_toClass_eq {κ M κ' ι' M' κ'' : Type} [AddCommGroup M]
    [AddCommGroup M'] {π : ℤ × ℤ →+ M} {π' : ℤ × ℤ →+ M'} (c : Fin 2 × Fin K → ℚ)
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    (hD : D.toClass =
      ((latticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    (G : D.FunctionWallGrouping π κ')
    (hprim : ∀ j, TauCeti.IsPrimitive (primitiveLatticeChangeNormal (D.wall j).normal))
    {g : κ'} (a : ℚ)
    (hg : G.label g = ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² latticeCoord
      ((Int.castAddHom ℚ).comp diagonalNormal)
      ((F latticeCoord).completedLog (squaredDiagonalFunction a))))
    {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² halfLatticeCoord) ι'}
    (hE : E.toClass =
      ((halfLatticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    (G' : E.FunctionWallGrouping π' κ'') {g' : κ''}
    (hgerm : ∀ k, ∃ θ v, G.IsCrossingGerm g k θ v ∧
      G'.IsCrossingGerm g' k ((primitiveLatticeChangePushforward ℚ h).spatialMap θ)
        ((primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.linear v)) :
    G'.label g' =
      ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² halfLatticeCoord
        ((Int.castAddHom ℚ).comp diagonalNormal) ((F halfLatticeCoord).completedLog
          (diagonalFunction halfLatticeCoord diagonalNormal_halfLatticeCoord a))) :=
  FunctionWallGrouping.label_eq_of_equivalent_pushforward_ofFiniteIndex _ _
    latticeChange_injective halfLatticeCoord_eq_latticeChange primitiveLatticeChangeNormal
    primitiveLatticeChangeScalar primitiveLatticeChangeScalar_pos
    primitiveLatticeChangeNormal_apply_latticeChange G
    diagonalNormal_latticeChange_eq_scalar_mul
    (r := 2) (by simp) (π' := π) (fun x _ => by simp)
    (fun j => by simpa using hprim j) _ _ hg
    (completedTropicalTangentMap_squaredDiagonalFunction _ a)
    ((toClass_eq_iff _ _).mp ((latticeLineInput_toClass_pushforward ℚ h c hD).trans hE.symm)) G'
    fun k => by
      obtain ⟨θ, v, hθ, hθ'⟩ := hgerm k
      exact ⟨θ, v, by rwa [PositiveDegreeMap.id_modulus], hθ'⟩

section GermLabel

/-- The diagonal line `{x = y}` of `ℝ²`, the kernel of the real extension of `n°`: the line
`RankTwoLatticeChange.line` of `ℝ(1, 1)`. -/
abbrev diagonalLine : AffineSubspace ℝ (ℝ × ℝ) := RankTwoLatticeChange.line h (1, 1)

/-- The diagonal line is an affine hyperplane of `ℝ²`. -/
theorem finrank_diagonalLine_direction :
    Module.finrank ℝ (diagonalLine h).direction + 1 = Module.finrank ℝ (ℝ × ℝ) :=
  RankTwoLatticeChange.finrank_direction_line (by simp)

/-- **Common generic points on the diagonal.** For any directed diagrams `D` over `M` and `E` over
`½M₀`, every open set meeting the diagonal line contains a generic point of the line for `D`
whose image under the spatial map `S` of the lattice change is a generic point of the image line
for `E`. -/
theorem exists_isGenericPoint_diagonalLine {κ ι' : Type}
    (D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ)
    (E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² halfLatticeCoord) ι')
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hne : (U ∩ diagonalLine h).Nonempty) :
    ∃ θ ∈ U ∩ diagonalLine h, D.IsGenericPoint (diagonalLine h) θ ∧
      E.IsGenericPoint ((diagonalLine h).map
        (primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.toAffineMap)
        ((primitiveLatticeChangePushforward ℚ h).spatialMap θ) :=
  D.exists_isGenericPoint_pair E _ _ (finrank_diagonalLine_direction h) hU hne

/-- The tangent monomial map of the identity degree map, from the coefficients tangent to `n°`
over `M` to those over `½M₀`. -/
local notation "Φ" => completedTropicalTangentMap (R := ℚ) (PositiveDegreeMap.id ℕ²)
  (map_tropicalTangentMonoid_intCast_le (PositiveDegreeMap.id ℕ²)
    halfLatticeCoord_eq_latticeChange diagonalNormal_latticeChange)

/-- The completed Lie map of the lattice change is injective. -/
theorem primitiveLatticeChangePushforward_lieHom_completedMap_injective :
    Function.Injective (primitiveLatticeChangePushforward ℚ h).lieHom.completedMap :=
  RankTwoLatticeChange.pushforward_lieHom_completedMap_injective ℚ h det_generators_pos _ _ _ _

/-- **Squares of diagonal wall functions.** If `f₀ = f₁ ^ 2` under the tangent monomial map, the
lattice change sends the function-wall label of `f₀` with normal `n°` over `M` to the
function-wall label of `f₁` with normal `n°` over `½M₀`. -/
theorem primitiveLatticeChangePushforward_completedMap_diagonal
    (f₀ : {u : (F latticeCoord).completion // u - 1 ∈ (F latticeCoord).completionIdeal 1})
    (f₁ : {u : (F halfLatticeCoord).completion // u - 1 ∈ (F halfLatticeCoord).completionIdeal 1})
    (hf : Φ f₀ = (f₁ : (F halfLatticeCoord).completion) ^ 2) :
    (primitiveLatticeChangePushforward ℚ h).lieHom.completedMap (ℕ².completedBCHExp _
      (completedTropicalTangentField ℕ² latticeCoord ((Int.castAddHom ℚ).comp diagonalNormal)
        ((F latticeCoord).completedLog f₀))) =
      ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² halfLatticeCoord
        ((Int.castAddHom ℚ).comp diagonalNormal) ((F halfLatticeCoord).completedLog f₁)) :=
  RankTwoLatticeChange.pushforward_lieHom_completedMap_label det_generators_pos
    primitiveLatticeChangeScalar_pos
    primitiveLatticeChangeNormal_apply_latticeChange two_nsmul_one_one
    primitiveLatticeChangeNormal_diagonalNormal (by simp) f₀ f₁ hf

/-- Every active wall through a generic point of the diagonal line, for a diagram over `M`, has its
label in the wall group of the diagonal ray `(1, 1)` with normal `n°`. -/
theorem label_mem_wallGroup_of_isGenericPoint_diagonalLine {κ : Type}
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    {θ : ℝ × ℝ} (hθ : D.IsGenericPoint (diagonalLine h) θ) {k : ℕ} (j : D.active k)
    (hj : θ ∈ (D.wall j).support) :
    (D.wall j).label ∈
      (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord).wallGroup diagonalRay diagonalNormal := by
  rw [diagonalRay_eq_coefficientRay]
  exact RankTwoLatticeChange.label_mem_wallGroup_of_isGenericPoint det_generators_pos.ne'
    isCoprime_one_left
    zero_le_one zero_le_one two_nsmul_one_one isPrimitive_one_one hθ j hj

/-- **The diagonal wall function over `M` is the square of the one over `½M₀`.** Let `D` be any
representative of the scattering class of the lines over `M` and `E` any representative over
`½M₀`. Let `θ` be a generic point of the diagonal line for `D` whose image `S θ` under the spatial
map is a generic point of the image line for `E`, and let `v` cross the diagonal. Let `f₀` over `M`
and `f₁` over `½M₀` be completed tangent series congruent to one with `f₀ = f₁ ^ 2` under the
tangent monomial map. Then the germ label of `E` at `S θ` in the direction `S v` is the
function-wall label of `f₁` with normal `n°` exactly when the germ label of `D` at `θ` in the
direction `v` is the function-wall label of `f₀` with normal `n°`. -/
theorem diagonal_germLabel_eq_iff_of_toClass_eq {κ ι' : Type} (c : Fin 2 × Fin K → ℚ)
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    (hD : D.toClass =
      ((latticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² halfLatticeCoord) ι'}
    (hE : E.toClass =
      ((halfLatticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {θ v : ℝ × ℝ} (hθ : D.IsGenericPoint (diagonalLine h) θ)
    (hθ' : E.IsGenericPoint ((diagonalLine h).map
      (primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.toAffineMap)
      ((primitiveLatticeChangePushforward ℚ h).spatialMap θ))
    (hv : h.realCharacter diagonalNormal v ≠ 0)
    (f₀ : {u : (F latticeCoord).completion // u - 1 ∈ (F latticeCoord).completionIdeal 1})
    (f₁ : {u : (F halfLatticeCoord).completion // u - 1 ∈ (F halfLatticeCoord).completionIdeal 1})
    (hf : Φ f₀ = (f₁ : (F halfLatticeCoord).completion) ^ 2) :
    E.germLabel ((primitiveLatticeChangePushforward ℚ h).spatialMap θ)
        ((primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.linear v)
        hθ'.isRegular =
      ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² halfLatticeCoord
        ((Int.castAddHom ℚ).comp diagonalNormal) ((F halfLatticeCoord).completedLog f₁)) ↔
    D.germLabel θ v hθ.isRegular = ℕ².completedBCHExp _
      (completedTropicalTangentField ℕ² latticeCoord ((Int.castAddHom ℚ).comp diagonalNormal)
        ((F latticeCoord).completedLog f₀)) :=
  RankTwoLatticeChange.germLabel_eq_iff_of_toClass_eq det_generators_pos
    primitiveLatticeChangeScalar_pos
    primitiveLatticeChangeNormal_apply_latticeChange two_nsmul_one_one c
    primitiveLatticeChangeNormal_lineNormal primitiveLatticeChangeNormal_diagonalNormal (by simp)
    hD hE hθ hθ' hv f₀ f₁ hf

/-- **The diagonal wall functions over `M` and over `½M₀`.** Let `D`, `E`, `θ` and `v` be as in
`diagonal_germLabel_eq_iff_of_toClass_eq`. Then there are completed tangent series `f₀` over `M`
and `f₁` over `½M₀`, congruent to one, with `f₀ = f₁ ^ 2` under the tangent monomial map, such
that the germ label of `D` at `θ` in the direction `v` is the function-wall label of `f₀` with
normal `n°` and the germ label of `E` at `S θ` in the direction `S v` is the function-wall label
of `f₁` with normal `n°`. The series are not computed. -/
theorem exists_diagonal_germLabel_eq_of_toClass_eq {κ ι' : Type} (c : Fin 2 × Fin K → ℚ)
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    (hD : D.toClass =
      ((latticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² halfLatticeCoord) ι'}
    (hE : E.toClass =
      ((halfLatticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {θ v : ℝ × ℝ} (hθ : D.IsGenericPoint (diagonalLine h) θ)
    (hθ' : E.IsGenericPoint ((diagonalLine h).map
      (primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.toAffineMap)
      ((primitiveLatticeChangePushforward ℚ h).spatialMap θ))
    (hv : h.realCharacter diagonalNormal v ≠ 0) :
    ∃ (f₀ : {u : (F latticeCoord).completion // u - 1 ∈ (F latticeCoord).completionIdeal 1})
      (f₁ : {u : (F halfLatticeCoord).completion //
        u - 1 ∈ (F halfLatticeCoord).completionIdeal 1}),
      Φ f₀ = (f₁ : (F halfLatticeCoord).completion) ^ 2 ∧
      D.germLabel θ v hθ.isRegular = ℕ².completedBCHExp _
        (completedTropicalTangentField ℕ² latticeCoord ((Int.castAddHom ℚ).comp diagonalNormal)
          ((F latticeCoord).completedLog f₀)) ∧
      E.germLabel ((primitiveLatticeChangePushforward ℚ h).spatialMap θ)
          ((primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.linear v)
          hθ'.isRegular =
        ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² halfLatticeCoord
          ((Int.castAddHom ℚ).comp diagonalNormal) ((F halfLatticeCoord).completedLog f₁)) :=
  RankTwoLatticeChange.exists_germLabel_eq_of_toClass_eq det_generators_pos
    primitiveLatticeChangeScalar_pos
    primitiveLatticeChangeNormal_apply_latticeChange two_nsmul_one_one c
    primitiveLatticeChangeNormal_lineNormal primitiveLatticeChangeNormal_diagonalNormal
    isCoprime_one_left zero_le_one zero_le_one isPrimitive_one_one hD hE hθ hθ' hv

/-- **The diagonal wall function over `½M₀` from the one over `M`.** Let `D` be any representative
of the scattering class of the lines over `M` and `E` any representative of the scattering class
over `½M₀`. Let `θ` be a generic point of the diagonal line for `D` whose image under the
spatial map `S` is a generic point of the image line for `E`; such points exist in every open
set meeting the line (`exists_isGenericPoint_diagonalLine`). Let `v` cross the diagonal
negatively. If the germ label of `D` at `θ` in the direction `v` is the function-wall label of
`(1 + a z^{(1,1)})²` with normal `n°`, then the germ label of `E` at `S θ` in the direction `S v`
is the function-wall label of `1 + a z^{(1,1)}` with normal `n°`. The germ label of `D` is a
hypothesis: the scattering class over `M` is not computed. No function-wall grouping of `D` or
`E` is involved. -/
theorem diagonal_germLabel_of_toClass_eq {κ ι' : Type} (c : Fin 2 × Fin K → ℚ)
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    (hD : D.toClass =
      ((latticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² halfLatticeCoord) ι'}
    (hE : E.toClass =
      ((halfLatticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {θ v : ℝ × ℝ} (hθ : D.IsGenericPoint (diagonalLine h) θ)
    (hθ' : E.IsGenericPoint ((diagonalLine h).map
      (primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.toAffineMap)
      ((primitiveLatticeChangePushforward ℚ h).spatialMap θ))
    (hv : h.realCharacter diagonalNormal v < 0) (a : ℚ)
    (hg : D.germLabel θ v hθ.isRegular = ℕ².completedBCHExp _
      (completedTropicalTangentField ℕ² latticeCoord ((Int.castAddHom ℚ).comp diagonalNormal)
        ((F latticeCoord).completedLog (squaredDiagonalFunction a)))) :
    E.germLabel ((primitiveLatticeChangePushforward ℚ h).spatialMap θ)
        ((primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.linear v)
        hθ'.isRegular =
      ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² halfLatticeCoord
        ((Int.castAddHom ℚ).comp diagonalNormal) ((F halfLatticeCoord).completedLog
          (diagonalFunction halfLatticeCoord diagonalNormal_halfLatticeCoord a))) :=
  (diagonal_germLabel_eq_iff_of_toClass_eq h c hD hE hθ hθ' hv.ne _ _
    (completedTropicalTangentMap_squaredDiagonalFunction _ a)).mpr hg

/-- **The diagonal germ label over `M` along a ray.** Let `D` and `D'` be any representatives of
the scattering class of the lines over `M`, let `θ` be a generic point of the diagonal line for
`D`, and let `t • θ`, `t > 0`, be a generic point of the line for `D'`. Then the germ label of
`D'` at `t • θ` is the germ label of `D` at `θ`, in every direction crossing the diagonal. So the
germ label of the class over `M` on each open ray of the diagonal, for instance on the open ray
`ℝ_{<0}(1, 1)` of `m°`, is independent of the representative and of the generic point. -/
theorem diagonal_germLabel_smul_eq {κ κ' : Type} (c : Fin 2 × Fin K → ℚ)
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    (hD : D.toClass =
      ((latticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {D' : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ'}
    (hD' : D'.toClass =
      ((latticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {θ v : ℝ × ℝ} {t : ℝ} (ht : 0 < t) (hθ : D.IsGenericPoint (diagonalLine h) θ)
    (htθ : D'.IsGenericPoint (diagonalLine h) (t • θ)) (hv : h.realCharacter diagonalNormal v ≠ 0) :
    D'.germLabel (t • θ) v htθ.isRegular = D.germLabel θ v hθ.isRegular :=
  germLabel_smul_eq_of_toClass_eq_scat _
    (RankTwoLatticeChange.lineInput_diagram_wall_support _ _ _ _ _ ℚ h c) hD hD' (by simp)
    (finrank_diagonalLine_direction h) ht hθ htθ
    (RankTwoLatticeChange.notMem_direction_line_iff.mpr hv)

/-- The image of the diagonal line under the spatial map of the lattice change passes through the
origin. -/
theorem zero_mem_map_diagonalLine :
    (0 : ℝ × ℝ) ∈ (diagonalLine h).map
      (primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.toAffineMap :=
  RankTwoLatticeChange.zero_mem_map_line _ _ _

/-- The image of the diagonal line under the spatial map of the lattice change is an affine
hyperplane. -/
theorem finrank_map_diagonalLine_direction :
    Module.finrank ℝ ((diagonalLine h).map
      (primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.toAffineMap).direction + 1 =
      Module.finrank ℝ (ℝ × ℝ) :=
  RankTwoLatticeChange.finrank_direction_map_line _ _ _ (m := (1, 1)) (by simp)

/-- **The diagonal wall function over `½M₀` on the whole ray.** Let `D` be any representative of
the scattering class of the lines over `M` and `E` any representative of the scattering class
over `½M₀`. Let `θ` be a generic point of the diagonal line for `D` and let `v` cross the diagonal
negatively. If the germ label of `D` at `θ` in the direction `v` is the function-wall label of
`(1 + a z^{(1,1)})²` with normal `n°`, then at every point `t • S θ`, `t > 0`, of the image ray
under the spatial map `S` that is generic for `E` on the image line, the germ label of `E` in the
direction `S v` is the function-wall label of `1 + a z^{(1,1)}` with normal `n°`. Unlike
`diagonal_germLabel_of_toClass_eq`, `S θ` itself need not be generic for `E`. The germ label of
`D` at one point is a hypothesis: the scattering class over `M` is not computed. -/
theorem diagonal_germLabel_smul_of_toClass_eq {κ ι' : Type} (c : Fin 2 × Fin K → ℚ)
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    (hD : D.toClass =
      ((latticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² halfLatticeCoord) ι'}
    (hE : E.toClass =
      ((halfLatticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {θ v : ℝ × ℝ} (hθ : D.IsGenericPoint (diagonalLine h) θ)
    (hv : h.realCharacter diagonalNormal v < 0) (a : ℚ)
    (hg : D.germLabel θ v hθ.isRegular = ℕ².completedBCHExp _
      (completedTropicalTangentField ℕ² latticeCoord ((Int.castAddHom ℚ).comp diagonalNormal)
        ((F latticeCoord).completedLog (squaredDiagonalFunction a))))
    {t : ℝ} (ht : 0 < t)
    (htθ : E.IsGenericPoint ((diagonalLine h).map
      (primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.toAffineMap)
      (t • (primitiveLatticeChangePushforward ℚ h).spatialMap θ)) :
    E.germLabel (t • (primitiveLatticeChangePushforward ℚ h).spatialMap θ)
        ((primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.linear v)
        htθ.isRegular =
      ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² halfLatticeCoord
        ((Int.castAddHom ℚ).comp diagonalNormal) ((F halfLatticeCoord).completedLog
          (diagonalFunction halfLatticeCoord diagonalNormal_halfLatticeCoord a))) := by
  /- The pushforward of `D` represents the class over `½M₀` and is generic at `S θ`, where its
  germ label is the target label. The germ label of the class over `½M₀` is constant along the
  open ray through `S θ`. -/
  let P := primitiveLatticeChangePushforward ℚ h
  have hθ' := hθ.pushforward P
  have hv' := RankTwoLatticeChange.linear_notMem_direction_map_line (R := ℚ) (h := h)
    det_generators_pos
    primitiveLatticeChangeScalar_pos primitiveLatticeChangeNormal_apply_latticeChange hv.ne
  rw [germLabel_smul_eq_of_toClass_eq_scat _
      (RankTwoLatticeChange.lineInput_diagram_wall_support _ _ _ _ _ ℚ h c)
      (latticeLineInput_toClass_pushforward ℚ h c hD) hE (zero_mem_map_diagonalLine h)
      (finrank_map_diagonalLine_direction h) ht hθ' htθ hv']
  exact diagonal_germLabel_of_toClass_eq h c hD (latticeLineInput_toClass_pushforward ℚ h c hD)
    hθ hθ' hv a hg

end GermLabel

end Mei.HyperplaneTermInput.FiniteIndex.Examples
