/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.CoefficientMap
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Extension

/-!
# Coefficient naturality of probe fields

The coefficient field extracted from actual upward probe crossings commutes with
homogeneous equivariant linear coefficient maps. The target diagram can be any
representative equivalent to the coefficient image of the source diagram. No
injectivity is required: walls and their individual contributions may disappear.

The comparison extends to allowed endpoints and completed fields, as required by
[probe transport](https://github.com/yuma-mizuno/TauCetiRoadmap/blob/mei/TauCetiRoadmap/ScatteringDiagrams/README.md#55-module-probes-and-affine-theta-transport).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι η κ : Type*} {M N L : Type u}
  [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ] [AddCommGroup Λ]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M] [LieRingModule L N] [LieModule R L N]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (𝒩 : Γ → Submodule R N) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [SetLike.GradedBracket ℒ 𝒩]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [IsWallAnnihilating H ℳ] [IsWallAnnihilating H 𝒩]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (f : M →ₗ[R] N) (hf : ∀ q, ℳ q ≤ (𝒩 q).comap f)
  (hequiv : ∀ (x : L) (a : M), f ⁅x, a⁆ = ⁅x, f a⁆)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)
  (D' : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d 𝒩 p ℒ H) η)

local notation "φ" => coefficientGradedLieHom d ℳ 𝒩 p ℒ f hf hequiv
local notation "hφ" => coefficientGradedLieHom_mem_wall d ℳ 𝒩 p ℒ f hf hequiv H
local notation "fₖ" => quotientCoefficientMap d ℳ 𝒩 p f hf

omit [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- Upward crossing labels are natural for actual equivalent target representatives.
The proof compares short paths, so disappearing walls need no matching indices. -/
theorem map_combinedLabel_of_levelEquivalent (k : ℕ)
    (hDD' : (D.map φ hφ).LevelEquivalent D' (k + 1)) (Q : V)
    (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (hQ' : (coefficientArrangement d 𝒩 p ℒ H h h' D' k).IsGeneric Q) :
    ((φ).truncatedMap (k + 1) (by simp)).bchGroupMap
        (D.combinedLabel (k + 1) (Q, 0) (0, j 1)
          (regular_of_isGeneric d ℳ p ℒ H h h' D k Q hQ)) =
      D'.combinedLabel (k + 1) (Q, 0) (0, j 1)
        (regular_of_isGeneric d 𝒩 p ℒ H h h' D' k Q hQ') := by
  let P := DirectedWall.Pushforward.ofFixedDegree (h := h.prod h') φ hφ
  obtain ⟨a, ha, ha'⟩ := ((D.eventually_exists_levelPathProduct_eq_combinedLabel
    (k + 1) (Q, 0) (0, j 1) (regular_of_isGeneric d ℳ p ℒ H h h' D k Q hQ)
      (vertical_transverse_of_isGeneric d ℳ p ℒ H h h' D k Q hQ)).and
    (D'.eventually_exists_levelPathProduct_eq_combinedLabel
      (k + 1) (Q, 0) (0, j 1) (regular_of_isGeneric d 𝒩 p ℒ H h h' D' k Q hQ')
      (vertical_transverse_of_isGeneric d 𝒩 p ℒ H h h' D' k Q hQ'))).exists
  obtain ⟨x, y, e, hx, hy, he⟩ := ha
  obtain ⟨x', y', e', hx', hy', he'⟩ := ha'
  have hEq : (D.pushforward P).LevelEquivalent D' (k + 1) := by
    simpa only [P, DirectedDiagram.pushforward_ofFixedDegree] using hDD'
  have hp := (DirectedDiagram.levelEquivalent_def _ _ _).mp hEq
    ((D.levelPathPushforward P (k + 1) (by simp [P])).mapPath e.toPath) e'.toPath
      (by simp [Quiver.Path.vertices_toPath, P, hx, hy, hx', hy'])
  rw [D.levelPathProduct_pushforward, he, he'] at hp
  simpa only [P, DirectedWall.Pushforward.ofFixedDegree_lieHom_truncatedMap] using hp

omit [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- The finite field commutes with coefficient changes, including noninjective
ones, on the common generic locus of arbitrary actual representatives. -/
theorem map_coefficientField (k : ℕ)
    (hDD' : (D.map φ hφ).LevelEquivalent D' (k + 1)) (Q : V)
    (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (hQ' : (coefficientArrangement d 𝒩 p ℒ H h h' D' k).IsGeneric Q) :
    fₖ k (coefficientField d ℳ p ℒ H h h' D k Q hQ) =
      coefficientField d 𝒩 p ℒ H h h' D' k Q hQ' := by
  simp only [coefficientField_def, verticalCoefficient_def, map_neg]
  rw [← moduleQuotientProjection_coefficientGradedLieHom d ℳ 𝒩 p ℒ f hf hequiv,
    ← LieHom.log_bchGroupMap,
    map_combinedLabel_of_levelEquivalent d ℳ 𝒩 p ℒ H h h' f hf hequiv D D' k hDD' Q hQ hQ']

include hequiv in
/-- Finite coefficient changes intertwine the base BCH action. -/
theorem quotientCoefficientMap_truncatedBCHAction (k : ℕ) (g : d.truncatedGroup ℒ k)
    (a : (d.shiftedFiltration ℳ p).quotient k) :
    fₖ k ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k g a) =
      (d.shiftedLieFiltration ℒ 𝒩 p).truncatedBCHAction d ℒ k g (fₖ k a) := by
  let ψ : d.shiftedLieSubmodule ℒ ℳ p →ₗ[R] d.shiftedLieSubmodule ℒ 𝒩 p :=
    shiftedCoefficientMap d ℳ 𝒩 p f hf
  have hψ (a : d.shiftedLieSubmodule ℒ ℳ p) : (ψ a : N) = f a :=
    coe_shiftedCoefficientMap d ℳ 𝒩 p f hf a
  have heq (x : L) (a : d.shiftedLieSubmodule ℒ ℳ p) : ψ ⁅x, a⁆ = ⁅x, ψ a⁆ := by
    apply Subtype.ext
    simp only [hψ, LieSubmodule.coe_bracket, hequiv]
  have ht := (d.shiftedLieFiltration ℒ ℳ p).mapQ_truncatedBCHAction_of_gradedLieHom
    (d.shiftedLieFiltration ℒ 𝒩 p) (GradedLieHom.id ℒ) ψ
    (fun x a => by simpa only [GradedLieHom.id_apply] using heq x a) k (by simp)
    (fun _ ha => shiftedCoefficientMap_mem_filtration d ℳ 𝒩 p f hf k ha) g a
  simpa only [ψ, quotientCoefficientMap_def, GradedLieHom.truncatedMap_id,
    LieHom.bchGroupMap_id, MonoidHom.id_apply] using ht

variable (B : DirectedDiagram (d := d) h H κ)

/-- Extended fields are natural on every base-allowed endpoint. Both fields are
extracted from their own probe diagrams; the target may have fewer active walls. -/
theorem map_extendedCoefficientField (k : ℕ) (hBc : B.LevelConsistent k)
    (hD : D.LevelConsistent (k + 1)) (hD' : D'.LevelConsistent (k + 1))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) k)
    (hB' : (D'.map (chargeZeroGradedLieHom d 𝒩 p ℒ)
      (chargeZeroGradedLieHom_mem_wall d 𝒩 p ℒ H)).LevelEquivalent
      (cylinderDiagram d 𝒩 p ℒ H h h' B) k)
    (hDD' : (D.map φ hφ).LevelEquivalent D' (k + 1))
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) :
    fₖ k (extendedCoefficientField d ℳ p ℒ H h h' D B k hBc x) =
      extendedCoefficientField d 𝒩 p ℒ H h h' D' B k hBc x := by
  let T := (coefficientArrangement d ℳ p ℒ H h h' D k).union
    (coefficientArrangement d 𝒩 p ℒ H h h' D' k)
  let := h.finiteDimensional
  have hopen : IsOpen {z : V | ∀ c : B.active k, z ∉ (B.wall c).support} := by
    simpa only [ofPred_forall, compl_def] using isOpen_iInter_of_finite
      (fun c : B.active k => (B.wall c).isConvexPolyhedron.isClosed.isOpen_compl)
  obtain ⟨z, hzB, hzT⟩ := T.dense_isGeneric.inter_open_nonempty _ hopen ⟨x.val, x.notMem⟩
  obtain ⟨hz, hz'⟩ := ExceptionalArrangement.isGeneric_union.mp hzT
  let zB : WallComplement (fun c : B.active k => (B.wall c).support) := ⟨z, hzB⟩
  rw [extendedCoefficientField_eq_action d ℳ p ℒ H h h' D B k hBc hD hB x zB hz,
    extendedCoefficientField_eq_action d 𝒩 p ℒ H h h' D' B k hBc hD' hB' x zB hz',
    quotientCoefficientMap_truncatedBCHAction d ℳ 𝒩 p ℒ f hf hequiv,
    map_coefficientField d ℳ 𝒩 p ℒ H h h' f hf hequiv D D' k hDD' z hz hz']

/-- Coefficient maps commute with the completed extension, by comparing its
actual finite crossing coefficients at every relative order. -/
theorem map_completedExtendedCoefficientField
    (hD : D.Consistent) (hD' : D'.Consistent) (hBc : B.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B))
    (hB' : (D'.map (chargeZeroGradedLieHom d 𝒩 p ℒ)
      (chargeZeroGradedLieHom_mem_wall d 𝒩 p ℒ H)).Equivalent
      (cylinderDiagram d 𝒩 p ℒ H h h' B))
    (hDD' : (D.map φ hφ).Equivalent D') (x : B.Point) :
    completionCoefficientMap d ℳ 𝒩 p f hf
        (completedExtendedCoefficientField d ℳ p ℒ H h h' D B hD hBc hB x) =
      completedExtendedCoefficientField d 𝒩 p ℒ H h h' D' B hD' hBc hB' x := by
  apply (d.shiftedFiltration 𝒩 p).completion_ext
  intro k
  rw [projection_completionCoefficientMap, projection_completedExtendedCoefficientField,
    projection_completedExtendedCoefficientField]
  exact map_extendedCoefficientField d ℳ 𝒩 p ℒ H h h' f hf hequiv D D' B k
    ((B.consistent_iff.mp hBc) k) ((D.consistent_iff.mp hD) (k + 1))
    ((D'.consistent_iff.mp hD') (k + 1))
    (((DirectedDiagram.equivalent_iff _ _).mp hB) k)
    (((DirectedDiagram.equivalent_iff _ _).mp hB') k)
    (((DirectedDiagram.equivalent_iff _ _).mp hDD') (k + 1)) (CommonWallComplement.projection k x)

end Mei.ModuleProbe
