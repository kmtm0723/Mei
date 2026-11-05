/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.Pushforward
public import Mei.Geometry.ScatteringDiagram.DirectedWall.TropicalPairing.WallFunction.Examples
public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.LatticeChange.Basic

/-!
# The lattice change of two lines for `m₁ = (1, 0)` and `m₂ = (1, 2)`

Let `M = ℤ²`, let `M₀ ⊆ M` be spanned by `m₁ = (1, 0)` and `m₂ = (1, 2)`, of index `ℓ = 2`, and
use the coordinates of `Mei.DirectedWall.LatticeChange.Examples`, which are the coordinates of
`Mei.RankTwoLatticeChange` for this lattice: the coefficient exponent `(a, b)` of
`x^{a m₁ + b m₂}` is `latticeCoord (a, b) = (a + b, 2b)` in `M` and
`halfLatticeCoord (a, b) = (2a, 2b)` in `½M₀`, and `M ⊆ ½M₀` is
`latticeChange (x, y) = (2x - y, y)`. The lattice change `primitiveLatticeChangePushforward` uses
the canonical normal map `Mei.RankTwoLatticeChange.normalMap`. On this lattice it sends the line
normals `e₂*` and `2e₁* - e₂*` of `M` (`lineNormal_zero`, `lineNormal_one`) to `e₂*` and `e₁*`,
and keeps the normal `n° = x - y` of the diagonal `ℝ(1, 1)` with comparison scalar `r = 2`
(`normalMap_diagonalNormal`, `normalScalar_diagonalNormal`), since `m° = m₁ + m₂ = 2 • (1, 1)`
(`two_nsmul_one_one`).

The general results of `Mei.RankTwoLatticeChange` (for instance
`Mei.RankTwoLatticeChange.exists_germLabel_smul_eq_of_toClass_eq`: on each open ray of the
diagonal the wall function over `M` is the square of the one over `½M₀`) apply to this lattice
with these facts as hypotheses. This file adds the statements for the explicit wall functions
`(1 + a z^{(1,1)})²` over `M` and `1 + a z^{(1,1)}` over `½M₀`:

* a function-wall group with the label of `(1 + a z^{(1,1)})²` is pushed to a group with the label
  of `1 + a z^{(1,1)}` (`diagonal_label_pushforward`), and this label is carried by every group of
  a representative over `½M₀` matched with it by crossing germs (`diagonal_label_of_toClass_eq`);
* if a representative over `M` has the germ label of `(1 + a z^{(1,1)})²` at a generic point `θ`
  of the diagonal, every representative over `½M₀` has the germ label of `1 + a z^{(1,1)}` at
  `S θ` when this point is generic (`diagonal_germLabel_of_toClass_eq`), and at every generic
  point `t • S θ`, `t > 0`, of the image ray (`diagonal_germLabel_smul_of_toClass_eq`).

The germ label `(1 + a z^{(1,1)})²` over `M` is a hypothesis: the scattering class is not
computed. The lattice change is motivated by Burcroff–Lee–Mou, *Positivity of generalized cluster
scattering diagrams*, Theorem 9.5 (arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.HyperplaneTermInput.FiniteIndex.Examples

open DirectedWall DirectedDiagram TauCeti.Toric DirectedWall.LatticeChange.Examples

/-- The positive quadrant `ℕ²` of `ℤ²`, with coordinate-sum degree. -/
local notation "ℕ²" => Module.Basis.positiveDegrees (Module.Basis.finTwoProd ℤ)

/-- The normal of `ℝm₁` in `M` is `e₂*`. -/
theorem lineNormal_zero :
    RankTwoLatticeChange.lineNormal (1, 0) (1, 2) 0 = AddMonoidHom.snd ℤ ℤ :=
  AddMonoidHom.ext fun x => by simp [Prod.det_apply]

/-- The normal of `ℝm₂` in `M` is `2e₁* - e₂*`. -/
theorem lineNormal_one :
    RankTwoLatticeChange.lineNormal (1, 0) (1, 2) 1 =
      (2 : ℤ) • AddMonoidHom.fst ℤ ℤ - AddMonoidHom.snd ℤ ℤ :=
  AddMonoidHom.ext fun x => by simp [Prod.det_apply, mul_comm]

/-- `m° = m₁ + m₂ = 2 • (1, 1)`. -/
theorem two_nsmul_one_one :
    (2 : ℕ) • ((1, 1) : ℤ × ℤ) = (1 : ℤ) • ((1, 0) : ℤ × ℤ) + (1 : ℤ) • ((1, 2) : ℤ × ℤ) := by
  decide

/-- The canonical normal map keeps the normal `n° = x - y` of the diagonal. -/
theorem normalMap_diagonalNormal :
    RankTwoLatticeChange.normalMap (1, 0) (1, 2) diagonalNormal = diagonalNormal :=
  RankTwoLatticeChange.normalMap_normal det_generators_pos isCoprime_one_left two_nsmul_one_one

/-- The normal `n°` of the diagonal has comparison scalar `r = 2`. -/
theorem normalScalar_diagonalNormal :
    RankTwoLatticeChange.normalScalar (1, 0) (1, 2) diagonalNormal = 2 := by
  rw [RankTwoLatticeChange.normalScalar_normal det_generators_pos isCoprime_one_left
    two_nsmul_one_one, Nat.cast_ofNat]

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The lattice change `M ⊆ ½M₀` with the canonical normal map. -/
abbrev primitiveLatticeChangePushforward :
    Pushforward ℕ² ℕ² h h (tropicalVertexWallSpaces (R := R) ℕ² latticeCoord)
      (tropicalVertexWallSpaces ℕ² halfLatticeCoord) :=
  RankTwoLatticeChange.pushforward R h det_generators_pos
    (RankTwoLatticeChange.normalMap (1, 0) (1, 2)) (RankTwoLatticeChange.normalScalar (1, 0) (1, 2))
    (RankTwoLatticeChange.normalScalar_pos det_generators_pos)
    (RankTwoLatticeChange.normalMap_apply_change det_generators_pos)

/-- The coefficients tangent to `n°` over `ρ₀`. -/
local notation "F" ρ₀ => TropicalVertexCoefficientAction.filtration (R := ℚ) ℕ²
  (tropicalTangentMonoid ℕ² ρ₀ (AddMonoidHom.comp (Int.castAddHom ℚ) diagonalNormal))

variable {K : ℕ}

/-- **Transport of a diagonal group label.** Let a diagram over `M` have a function-wall
grouping whose normals stay primitive under the canonical normal map, and let its group `g` have
the function-wall label of `(1 + a z^{(1,1)})²` with normal `n°`. Then the group `g` of the
pushforward along `M ⊆ ½M₀` has the function-wall label of `1 + a z^{(1,1)}` with normal `n°`. -/
theorem diagonal_label_pushforward {κ M κ' : Type*} [AddCommGroup M] {π : ℤ × ℤ →+ M}
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    (G : D.FunctionWallGrouping π κ')
    (hprim : ∀ j,
      TauCeti.IsPrimitive (RankTwoLatticeChange.normalMap (1, 0) (1, 2) (D.wall j).normal))
    {g : κ'} (a : ℚ)
    (hg : G.label g = ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² latticeCoord
      ((Int.castAddHom ℚ).comp diagonalNormal)
      ((F latticeCoord).completedLog (squaredDiagonalFunction a)))) :
    (G.pushforward (P := primitiveLatticeChangePushforward ℚ h) (π' := π)
        (fun x _ => by simp) (fun j => by simpa using hprim j)).label g =
      ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² halfLatticeCoord
        ((Int.castAddHom ℚ).comp diagonalNormal) ((F halfLatticeCoord).completedLog
          (diagonalFunction halfLatticeCoord diagonalNormal_halfLatticeCoord a))) := by
  rw [FunctionWallGrouping.label_pushforward, hg]
  exact RankTwoLatticeChange.pushforward_lieHom_completedMap_label det_generators_pos
    (RankTwoLatticeChange.normalScalar_pos det_generators_pos)
    (RankTwoLatticeChange.normalMap_apply_change det_generators_pos) two_nsmul_one_one
    normalMap_diagonalNormal (by simp) _ _ (completedTropicalTangentMap_squaredDiagonalFunction _ a)

/-- **The diagonal label in matched representatives over `½M₀`.** Let `D` represent the scattering
class of the lines over `M`, with a function-wall grouping whose normals stay primitive under the
canonical normal map, and let its group `g` have the function-wall label of `(1 + a z^{(1,1)})²`
with normal `n°`. Let `E` be any representative of the scattering class of the lines over `½M₀`,
with a function-wall grouping `G'`. Suppose that at every order `k` the group `g` has a crossing
germ at order `k`, at a point `θ` and a direction `v`, and that the group `g'` of `G'` has a
crossing germ at order `k` at their images under the spatial map. Then `g'` has the function-wall
label of `1 + a z^{(1,1)}` with normal `n°`. -/
theorem diagonal_label_of_toClass_eq {κ M κ' ι' M' κ'' : Type} [AddCommGroup M]
    [AddCommGroup M'] {π : ℤ × ℤ →+ M} {π' : ℤ × ℤ →+ M'} (c : Fin 2 × Fin K → ℚ)
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    (hD : D.toClass = ((RankTwoLatticeChange.latticeLineInput det_generators_pos K).diagram h
      c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    (G : D.FunctionWallGrouping π κ')
    (hprim : ∀ j,
      TauCeti.IsPrimitive (RankTwoLatticeChange.normalMap (1, 0) (1, 2) (D.wall j).normal))
    {g : κ'} (a : ℚ)
    (hg : G.label g = ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² latticeCoord
      ((Int.castAddHom ℚ).comp diagonalNormal)
      ((F latticeCoord).completedLog (squaredDiagonalFunction a))))
    {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² halfLatticeCoord) ι'}
    (hE : E.toClass = ((RankTwoLatticeChange.sublatticeLineInput (1, 0) (1, 2) K).diagram h
      c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    (G' : E.FunctionWallGrouping π' κ'') {g' : κ''}
    (hgerm : ∀ k, ∃ θ v, G.IsCrossingGerm g k θ v ∧
      G'.IsCrossingGerm g' k ((primitiveLatticeChangePushforward ℚ h).spatialMap θ)
        ((primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.linear v)) :
    G'.label g' =
      ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² halfLatticeCoord
        ((Int.castAddHom ℚ).comp diagonalNormal) ((F halfLatticeCoord).completedLog
          (diagonalFunction halfLatticeCoord diagonalNormal_halfLatticeCoord a))) := by
  /- `E` is equivalent to the pushforward of `D`, whose group `g` carries the target label by
  `diagonal_label_pushforward`, and the crossing germs of `g` are pushed to crossing germs. -/
  have hDE := (toClass_eq_iff _ _).mp ((RankTwoLatticeChange.toClass_pushforward ℚ h
    det_generators_pos (RankTwoLatticeChange.normalScalar_pos det_generators_pos)
    (RankTwoLatticeChange.normalMap_apply_change det_generators_pos)
    (RankTwoLatticeChange.normalMap_lineNormal det_generators_pos) c hD).trans hE.symm)
  refine (FunctionWallGrouping.label_eq_of_equivalent hDE fun k => ?_).symm.trans
    (diagonal_label_pushforward h G hprim a hg)
  obtain ⟨θ, v, hθ, hθ'⟩ := hgerm k
  exact ⟨_, _, hθ.pushforward _ _ (by simp), hθ'⟩

section GermLabel

/-- **The diagonal wall function over `½M₀` from the one over `M`.** Let `D` be any representative
of the scattering class of the lines over `M` and `E` any representative of the scattering class
over `½M₀`. Let `θ` be a generic point of the diagonal for `D` whose image under the spatial map
`S` is a generic point of the image line for `E`; such points exist in every open set meeting the
diagonal (`Mei.RankTwoLatticeChange.exists_isGenericPoint_pair_line`). Let `v` cross the
diagonal negatively. If the germ label of `D` at `θ` in the direction `v` is the function-wall
label of `(1 + a z^{(1,1)})²` with normal `n°`, then the germ label of `E` at `S θ` in the
direction `S v` is the function-wall label of `1 + a z^{(1,1)}` with normal `n°`. The germ label
of `D` is a hypothesis: the scattering class over `M` is not computed. -/
theorem diagonal_germLabel_of_toClass_eq {κ ι' : Type} (c : Fin 2 × Fin K → ℚ)
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    (hD : D.toClass = ((RankTwoLatticeChange.latticeLineInput det_generators_pos K).diagram h
      c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² halfLatticeCoord) ι'}
    (hE : E.toClass = ((RankTwoLatticeChange.sublatticeLineInput (1, 0) (1, 2) K).diagram h
      c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {θ v : ℝ × ℝ} (hθ : D.IsGenericPoint (RankTwoLatticeChange.line h (1, 1)) θ)
    (hθ' : E.IsGenericPoint ((RankTwoLatticeChange.line h (1, 1)).map
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
  (RankTwoLatticeChange.germLabel_eq_iff_of_toClass_eq det_generators_pos
    (RankTwoLatticeChange.normalScalar_pos det_generators_pos)
    (RankTwoLatticeChange.normalMap_apply_change det_generators_pos) two_nsmul_one_one c
    (RankTwoLatticeChange.normalMap_lineNormal det_generators_pos) normalMap_diagonalNormal
    (by simp) hD hE hθ hθ' hv.ne _ _ (completedTropicalTangentMap_squaredDiagonalFunction _ a)).mpr
    hg

/-- **The diagonal wall function over `½M₀` on the whole ray.** Let `D` be any representative of
the scattering class of the lines over `M` and `E` any representative of the scattering class
over `½M₀`. Let `θ` be a generic point of the diagonal for `D` and let `v` cross the diagonal
negatively. If the germ label of `D` at `θ` in the direction `v` is the function-wall label of
`(1 + a z^{(1,1)})²` with normal `n°`, then at every point `t • S θ`, `t > 0`, of the image ray
under the spatial map `S` that is generic for `E` on the image line, the germ label of `E` in the
direction `S v` is the function-wall label of `1 + a z^{(1,1)}` with normal `n°`. Unlike
`diagonal_germLabel_of_toClass_eq`, `S θ` itself need not be generic for `E`. The germ label of
`D` at one point is a hypothesis: the scattering class over `M` is not computed. -/
theorem diagonal_germLabel_smul_of_toClass_eq {κ ι' : Type} (c : Fin 2 × Fin K → ℚ)
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    (hD : D.toClass = ((RankTwoLatticeChange.latticeLineInput det_generators_pos K).diagram h
      c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² halfLatticeCoord) ι'}
    (hE : E.toClass = ((RankTwoLatticeChange.sublatticeLineInput (1, 0) (1, 2) K).diagram h
      c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {θ v : ℝ × ℝ} (hθ : D.IsGenericPoint (RankTwoLatticeChange.line h (1, 1)) θ)
    (hv : h.realCharacter diagonalNormal v < 0) (a : ℚ)
    (hg : D.germLabel θ v hθ.isRegular = ℕ².completedBCHExp _
      (completedTropicalTangentField ℕ² latticeCoord ((Int.castAddHom ℚ).comp diagonalNormal)
        ((F latticeCoord).completedLog (squaredDiagonalFunction a))))
    {t : ℝ} (ht : 0 < t)
    (htθ : E.IsGenericPoint ((RankTwoLatticeChange.line h (1, 1)).map
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
  have hD' := RankTwoLatticeChange.toClass_pushforward ℚ h det_generators_pos
    (RankTwoLatticeChange.normalScalar_pos det_generators_pos)
    (RankTwoLatticeChange.normalMap_apply_change det_generators_pos)
    (RankTwoLatticeChange.normalMap_lineNormal det_generators_pos) c hD
  have hθ' := hθ.pushforward (primitiveLatticeChangePushforward ℚ h)
  rw [germLabel_smul_eq_of_toClass_eq_scat _
      (RankTwoLatticeChange.lineInput_diagram_wall_support _ _ _ _ _ ℚ h c) hD' hE
      (RankTwoLatticeChange.zero_mem_map_line _ _ _)
      (RankTwoLatticeChange.finrank_direction_map_line _ _ _ (m := (1, 1)) (by simp)) ht hθ' htθ
      (RankTwoLatticeChange.linear_notMem_direction_map_line _ _ _ hv.ne)]
  exact diagonal_germLabel_of_toClass_eq h c hD hD' hθ hθ' hv a hg

end GermLabel

end Mei.HyperplaneTermInput.FiniteIndex.Examples
