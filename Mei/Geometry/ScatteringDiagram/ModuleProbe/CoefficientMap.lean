/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallSpace
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Truncation
public import Mei.Algebra.Lie.Graded.Shifted.Map

/-!
# Coefficient maps of module probes

A homogeneous equivariant linear map of coefficient modules induces a graded Lie
map of their semidirect probes. It fixes the base Lie algebra and preserves the
charge-one coefficient summand, including coefficients killed by the map.

This supplies coefficient naturality for
[module probes](https://github.com/yuma-mizuno/TauCetiRoadmap/blob/mei/TauCetiRoadmap/ScatteringDiagrams/README.md#55-module-probes-and-affine-theta-transport).
-/

public noncomputable section

namespace Mei.ModuleProbe

variable {R M N Γ L : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Γ] [DecidableEq Γ] [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M] [LieRingModule L N] [LieModule R L N]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (𝓝 : Γ → Submodule R N) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [SetLike.GradedBracket ℒ 𝓝]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  (f : M →ₗ[R] N) (hf : ∀ q, ℳ q ≤ (𝓝 q).comap f)
  (hequiv : ∀ (x : L) (a : M), f ⁅x, a⁆ = ⁅x, f a⁆)

/-- Restriction of a degree-preserving coefficient map to the shifted module. -/
def shiftedCoefficientMap : shiftedSubmodule ℳ d.monoid p →ₗ[R]
    shiftedSubmodule 𝓝 d.monoid p :=
  (f.comp (shiftedSubmodule ℳ d.monoid p).subtype).codRestrict _ (fun a => by
    change f (a : M) ∈ shiftedSubmodule 𝓝 d.monoid p
    have ha := (PositiveDegreeMap.id d).map_mem_shiftedSubmodule ℳ 𝓝 p f
      (fun q => by simpa only [PositiveDegreeMap.id_apply] using hf q) a.property
    simpa only [PositiveDegreeMap.id_apply] using ha)

omit [DecidableEq Γ] [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- The restriction retains the original ambient coefficient map. -/
@[simp]
theorem coe_shiftedCoefficientMap (a : shiftedSubmodule ℳ d.monoid p) :
    (shiftedCoefficientMap d ℳ 𝓝 p f hf a : N) = f a := by rfl

omit [DecidableEq Γ] [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- The restriction preserves each relative homogeneous piece. -/
theorem shiftedCoefficientMap_mem_shiftedGrading {q : Γ}
    {a : shiftedSubmodule ℳ d.monoid p}
    (ha : a ∈ shiftedGrading ℳ d.monoid p q) :
    shiftedCoefficientMap d ℳ 𝓝 p f hf a ∈ shiftedGrading 𝓝 d.monoid p q := by
  rw [mem_shiftedGrading, coe_shiftedCoefficientMap]
  exact hf _ ((mem_shiftedGrading ℳ d.monoid p).mp ha)

/-- Homogeneous coefficient changes preserve the relative cutoff filtration. -/
theorem shiftedCoefficientMap_mem_filtration (k : ℕ)
    {a : shiftedSubmodule ℳ d.monoid p}
    (ha : a ∈ (d.shiftedFiltration ℳ p).submodule (k + 1)) :
    shiftedCoefficientMap d ℳ 𝓝 p f hf a ∈ (d.shiftedFiltration 𝓝 p).submodule (k + 1) := by
  rw [d.shiftedFiltration_succ ℳ p, d.degreeSubmodule_def] at ha
  rw [d.shiftedFiltration_succ 𝓝 p]
  refine Submodule.iSup_induction _
    (motive := fun a => shiftedCoefficientMap d ℳ 𝓝 p f hf a ∈
      d.degreeSubmodule (shiftedGrading 𝓝 d.monoid p) k) ha ?_ ?_ ?_
  · intro n a ha
    exact d.le_degreeSubmodule _ n.property
      (shiftedCoefficientMap_mem_shiftedGrading d ℳ 𝓝 p f hf ha)
  · simp
  · intro a b ha hb
    simpa only [map_add] using Submodule.add_mem _ ha hb

/-- The degree-preserving coefficient map on finite shifted quotients. -/
def quotientCoefficientMap (k : ℕ) : (d.shiftedFiltration ℳ p).quotient k →ₗ[R]
    (d.shiftedFiltration 𝓝 p).quotient k :=
  ((d.shiftedFiltration ℳ p).submodule (k + 1)).mapQ
    ((d.shiftedFiltration 𝓝 p).submodule (k + 1)) (shiftedCoefficientMap d ℳ 𝓝 p f hf)
    (fun _ ha => shiftedCoefficientMap_mem_filtration d ℳ 𝓝 p f hf k ha)

/-- The finite coefficient map is the canonical quotient map of the restriction. -/
theorem quotientCoefficientMap_def (k : ℕ) :
    quotientCoefficientMap d ℳ 𝓝 p f hf k =
      ((d.shiftedFiltration ℳ p).submodule (k + 1)).mapQ
        ((d.shiftedFiltration 𝓝 p).submodule (k + 1)) (shiftedCoefficientMap d ℳ 𝓝 p f hf)
        (fun _ ha => shiftedCoefficientMap_mem_filtration d ℳ 𝓝 p f hf k ha) := by rfl

/-- The finite map sends a representative to its coefficient image. -/
@[simp]
theorem quotientCoefficientMap_mk (k : ℕ) (a : shiftedSubmodule ℳ d.monoid p) :
    quotientCoefficientMap d ℳ 𝓝 p f hf k (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (shiftedCoefficientMap d ℳ 𝓝 p f hf a) := by rfl

/-- The induced map of completed shifted coefficient modules. -/
def completionCoefficientMap : d.ShiftedCoefficients ℳ p →ₗ[R] d.ShiftedCoefficients 𝓝 p :=
  (d.shiftedFiltration ℳ p).completionMap (d.shiftedFiltration 𝓝 p)
    (shiftedCoefficientMap d ℳ 𝓝 p f hf) _root_.id monotone_id
    (fun k _ ha => shiftedCoefficientMap_mem_filtration d ℳ 𝓝 p f hf k ha)

/-- The completion map is computed by the finite coefficient maps at every order. -/
@[simp]
theorem projection_completionCoefficientMap (k : ℕ) (a : d.ShiftedCoefficients ℳ p) :
    (d.shiftedFiltration 𝓝 p).projection k (completionCoefficientMap d ℳ 𝓝 p f hf a) =
      quotientCoefficientMap d ℳ 𝓝 p f hf k ((d.shiftedFiltration ℳ p).projection k a) :=
  (d.shiftedFiltration ℳ p).projection_completionMap (d.shiftedFiltration 𝓝 p)
    (shiftedCoefficientMap d ℳ 𝓝 p f hf) _root_.id monotone_id _ k a

/-- The map on the abelian shifted coefficient summands. -/
def coefficientMap : ModuleCoefficients d ℳ p →ₗ[R] ModuleCoefficients d 𝓝 p :=
  (moduleCoefficientsEquiv d 𝓝 p).symm.toLinearMap.comp
    ((shiftedCoefficientMap d ℳ 𝓝 p f hf).comp
      (moduleCoefficientsEquiv d ℳ p).toLinearMap)

omit [DecidableEq Γ] [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- Forgetting the zero bracket recovers the restricted linear coefficient map. -/
@[simp]
theorem moduleCoefficientsEquiv_coefficientMap (a : ModuleCoefficients d ℳ p) :
    moduleCoefficientsEquiv d 𝓝 p (coefficientMap d ℳ 𝓝 p f hf a) =
      shiftedCoefficientMap d ℳ 𝓝 p f hf (moduleCoefficientsEquiv d ℳ p a) := by
  simp [coefficientMap]

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
include hequiv in
/-- Equivariance survives restriction to the shifted coefficient summands. -/
theorem coefficientMap_actionDerivationHom (x : L) (a : ModuleCoefficients d ℳ p) :
    coefficientMap d ℳ 𝓝 p f hf (actionDerivationHom d ℳ p ℒ x a) =
      actionDerivationHom d 𝓝 p ℒ x (coefficientMap d ℳ 𝓝 p f hf a) := by
  let ψ : d.shiftedLieSubmodule ℒ ℳ p →ₗ[R] d.shiftedLieSubmodule ℒ 𝓝 p :=
    shiftedCoefficientMap d ℳ 𝓝 p f hf
  have hψ (a : d.shiftedLieSubmodule ℒ ℳ p) : (ψ a : N) = f a :=
    coe_shiftedCoefficientMap d ℳ 𝓝 p f hf a
  have heq (x : L) (a : d.shiftedLieSubmodule ℒ ℳ p) : ψ ⁅x, a⁆ = ⁅x, ψ a⁆ := by
    apply Subtype.ext
    simp only [hψ, LieSubmodule.coe_bracket, hequiv]
  apply (moduleCoefficientsEquiv d 𝓝 p).injective
  simp only [moduleCoefficientsEquiv_coefficientMap, moduleCoefficientsEquiv_actionDerivationHom]
  exact heq x _

/-- A coefficient map fixes the base summand and maps the coefficient summand. -/
def coefficientLieHom : ProbeLie d ℳ p ℒ →ₗ⁅R⁆ ProbeLie d 𝓝 p ℒ where
  toFun x := ⟨coefficientMap d ℳ 𝓝 p f hf x.left, x.right⟩
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp
  map_lie' {x y} := by
    ext <;> simp [coefficientMap_actionDerivationHom d ℳ 𝓝 p ℒ f hf hequiv]

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- The charge-one projection is the induced coefficient map. -/
@[simp]
theorem coefficientLieHom_left (x : ProbeLie d ℳ p ℒ) :
    (coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv x).left =
      coefficientMap d ℳ 𝓝 p f hf x.left := by rfl

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- The base projection is unchanged by coefficient maps. -/
@[simp]
theorem coefficientLieHom_right (x : ProbeLie d ℳ p ℒ) :
    (coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv x).right = x.right := by rfl

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- The semidirect coefficient map fixes every charge-zero base input. -/
theorem coefficientLieHom_baseInclusion (x : L) :
    coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv (baseInclusion d ℳ p ℒ x) =
      baseInclusion d 𝓝 p ℒ x := by ext <;> simp

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- The semidirect coefficient map restricts to the given coefficient map. -/
theorem coefficientLieHom_moduleInclusion (a : ModuleCoefficients d ℳ p) :
    coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv (moduleInclusion d ℳ p ℒ a) =
      moduleInclusion d 𝓝 p ℒ (coefficientMap d ℳ 𝓝 p f hf a) := by ext <;> simp

/-- The semidirect coefficient map preserves the reduced probe degree `(q,c)`. -/
def coefficientGradedLieHom : GradedLieHom (PositiveDegreeMap.id (positiveDegrees d p))
    (grading d ℳ p ℒ) (grading d 𝓝 p ℒ) where
  toLieHom := coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv
  map_mem {a x} hx := by
    rcases a with ⟨q, c⟩
    simp only [PositiveDegreeMap.id_apply]
    change coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv x ∈ grading d 𝓝 p ℒ (q, c)
    by_cases h0 : c = 0
    · subst c
      rw [mem_grading_base] at hx ⊢
      simpa [hx.1] using hx.2
    · by_cases h1 : c = 1
      · subst c
        rw [mem_grading_module] at hx ⊢
        refine ⟨hx.1, ?_⟩
        rw [coefficientLieHom_left, moduleCoefficientsEquiv_coefficientMap]
        exact shiftedCoefficientMap_mem_shiftedGrading d ℳ 𝓝 p f hf hx.2
      · rw [grading_charge_eq_bot d ℳ p ℒ q c h0 h1, Submodule.mem_bot] at hx
        rw [hx, map_zero]
        exact Submodule.zero_mem _

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- The graded coefficient map has the underlying semidirect coefficient map. -/
@[simp]
theorem coefficientGradedLieHom_apply (x : ProbeLie d ℳ p ℒ) :
    coefficientGradedLieHom d ℳ 𝓝 p ℒ f hf hequiv x =
      coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv x := by rfl

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- Coefficient changes preserve the probe wall spaces, with no injectivity assumption. -/
theorem coefficientGradedLieHom_mem_wall {Λ : Type*} [AddCommMonoid Λ]
    {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
    [IsWallAnnihilating H ℳ] [IsWallAnnihilating H 𝓝]
    (a : Γ × ℤ) (m : (Λ × ℤ) →+ ℤ) (x : ProbeLie d ℳ p ℒ)
    (hx : x ∈ (wallSpaces d ℳ p ℒ H).wall a m) :
    coefficientGradedLieHom d ℳ 𝓝 p ℒ f hf hequiv x ∈
      (wallSpaces d 𝓝 p ℒ H).wall a m := by
  rw [wallSpaces_wall, mem_wallSubmodule_iff] at hx ⊢
  rcases hx with rfl | ⟨q, m₀, y, rfl, rfl, hy, rfl⟩ | ⟨q, c, rfl, hc, rfl, hx⟩
  · exact Or.inl (map_zero _)
  · exact Or.inr (Or.inl ⟨q, m₀, y, rfl, rfl, hy,
      coefficientLieHom_baseInclusion d ℳ 𝓝 p ℒ f hf hequiv y⟩)
  · exact Or.inr (Or.inr ⟨q, c, rfl, hc, rfl,
      by simpa only [PositiveDegreeMap.id_apply, GradedLieHom.coe_toLieHom] using
        (coefficientGradedLieHom d ℳ 𝓝 p ℒ f hf hequiv).map_mem hx⟩)

/-- Extracting a finite coefficient commutes with arbitrary coefficient changes. -/
@[simp]
theorem moduleQuotientProjection_coefficientGradedLieHom (k : ℕ)
    (x : (positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) (k + 1)) :
    moduleQuotientProjection d 𝓝 p ℒ k
        ((coefficientGradedLieHom d ℳ 𝓝 p ℒ f hf hequiv).truncatedMap (k + 1) (by simp) x) =
      quotientCoefficientMap d ℳ 𝓝 p f hf k
        (moduleQuotientProjection d ℳ p ℒ k x) := by
  obtain ⟨x, rfl⟩ := ((positiveDegrees d p).degreeIdeal
    (grading d ℳ p ℒ) (k + 1)).surjective_mkQ x
  rw [LieIdeal.mkQ_apply, GradedLieHom.truncatedMap_mk,
    moduleQuotientProjection_mk, moduleQuotientProjection_mk, quotientCoefficientMap_mk]
  congr 1
  exact moduleCoefficientsEquiv_coefficientMap d ℳ 𝓝 p f hf x.left

end Mei.ModuleProbe
