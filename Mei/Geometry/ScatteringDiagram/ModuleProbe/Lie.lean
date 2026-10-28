/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Degree
public import Mei.Algebra.Lie.Graded.Shifted
public import Mathlib.Algebra.Lie.SemiDirect

/-!
# The graded Lie algebra of a module probe

A positively graded Lie algebra acts on every shifted coefficient module. Giving
that module zero internal bracket makes its semidirect sum with the acting Lie
algebra the module probe: the original Lie algebra has charge zero and the
coefficients have charge one. Their ambient degree and the charge determine the
extended degree in `ModuleProbe.positiveDegrees`.

The construction uses Mathlib's `LieAlgebra.SemiDirectSum` and the existing
restricted action `PositiveDegrees.shiftedLieSubmodule`. This is the algebraic
module probe of Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183).
-/

public section

noncomputable section

namespace Mei.ModuleProbe

variable {R M Γ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)

/-- Shifted coefficients, regarded as an abelian Lie algebra for the module probe. -/
@[expose]
def ModuleCoefficients : Type _ := ↥(shiftedSubmodule ℳ d.monoid p)

instance : AddCommGroup (ModuleCoefficients d ℳ p) :=
  inferInstanceAs (AddCommGroup (shiftedSubmodule ℳ d.monoid p))

instance : Module R (ModuleCoefficients d ℳ p) :=
  inferInstanceAs (Module R (shiftedSubmodule ℳ d.monoid p))

instance : LieRing (ModuleCoefficients d ℳ p) where
  __ := (inferInstance : AddCommGroup (ModuleCoefficients d ℳ p))
  bracket _ _ := 0
  add_lie _ _ _ := (add_zero _).symm
  lie_add _ _ _ := (add_zero _).symm
  lie_self _ := rfl
  leibniz_lie _ _ _ := (add_zero _).symm

instance : LieAlgebra R (ModuleCoefficients d ℳ p) where
  __ := (inferInstance : Module R (ModuleCoefficients d ℳ p))
  lie_smul r _ _ := (smul_zero r).symm

/-- The coefficient summand has zero internal bracket. -/
@[simp]
theorem moduleCoefficients_lie (a b : ModuleCoefficients d ℳ p) : ⁅a, b⁆ = 0 := rfl

instance : IsLieAbelian (ModuleCoefficients d ℳ p) where
  trivial := moduleCoefficients_lie d ℳ p

/-- Forget the zero bracket on the shifted coefficient summand. -/
def moduleCoefficientsEquiv : ModuleCoefficients d ℳ p ≃ₗ[R] shiftedSubmodule ℳ d.monoid p :=
  LinearEquiv.refl R _

variable [DecidableEq Γ] {L : Type*} [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ]

/-- The original Lie action acts by derivations on the abelian coefficient summand. -/
def actionDerivationHom :
    L →ₗ⁅R⁆ LieDerivation R (ModuleCoefficients d ℳ p) (ModuleCoefficients d ℳ p) where
  toFun x :=
    { toLinearMap := LieModule.toEnd R L (d.shiftedLieSubmodule ℒ ℳ p) x
      leibniz' a b := by
        simp only [moduleCoefficients_lie, sub_zero]
        exact map_zero _ }
  map_add' x y := by ext a; exact add_lie x y (show d.shiftedLieSubmodule ℒ ℳ p from a)
  map_smul' r x := by ext a; exact smul_lie r x (show d.shiftedLieSubmodule ℒ ℳ p from a)
  map_lie' {x y} := by
    ext a
    exact lie_lie x y (show d.shiftedLieSubmodule ℒ ℳ p from a)

/-- Forgetting the abelian internal bracket recovers the restricted Lie action. -/
theorem moduleCoefficientsEquiv_actionDerivationHom (x : L) (a : ModuleCoefficients d ℳ p) :
    moduleCoefficientsEquiv d ℳ p (actionDerivationHom d ℳ p (ℒ := ℒ) x a) =
      ⁅x, (show d.shiftedLieSubmodule ℒ ℳ p from moduleCoefficientsEquiv d ℳ p a)⁆ := by
  unfold moduleCoefficientsEquiv actionDerivationHom
  rfl

/-- The semidirect Lie algebra of the module probe. Its coefficient summand is
Mathlib's left factor and its original Lie algebra is the right factor. -/
abbrev ProbeLie :=
  LieAlgebra.SemiDirectSum (ModuleCoefficients d ℳ p) L (actionDerivationHom d ℳ p (ℒ := ℒ))

/-- Include the original Lie algebra in charge zero. -/
abbrev baseInclusion : L →ₗ⁅R⁆ ProbeLie d ℳ p ℒ :=
  LieAlgebra.SemiDirectSum.inr (actionDerivationHom d ℳ p (ℒ := ℒ))

/-- Include shifted coefficients as the abelian charge-one ideal. -/
abbrev moduleInclusion : ModuleCoefficients d ℳ p →ₗ⁅R⁆ ProbeLie d ℳ p ℒ :=
  LieAlgebra.SemiDirectSum.inl (actionDerivationHom d ℳ p (ℒ := ℒ))

/-- The bracket of two coefficient inputs vanishes in the probe. -/
theorem lie_moduleInclusion (a b : ModuleCoefficients d ℳ p) :
    ⁅moduleInclusion d ℳ p ℒ a, moduleInclusion d ℳ p ℒ b⁆ = 0 := by
  rw [← LieHom.map_lie, moduleCoefficients_lie, map_zero]

/-- The mixed bracket is exactly the original restricted coefficient action. -/
theorem lie_baseInclusion_moduleInclusion (x : L) (a : ModuleCoefficients d ℳ p) :
    ⁅baseInclusion d ℳ p ℒ x, moduleInclusion d ℳ p ℒ a⁆ =
      moduleInclusion d ℳ p ℒ (actionDerivationHom d ℳ p (ℒ := ℒ) x a) := by
  apply LieAlgebra.SemiDirectSum.ext <;> simp [baseInclusion, moduleInclusion]

/-- Homogeneous base elements shift coefficient homogeneity by their degree. -/
theorem actionDerivationHom_mem_shiftedGrading {n q : Γ} {x : L}
    {a : ModuleCoefficients d ℳ p} (hx : x ∈ ℒ n)
    (ha : moduleCoefficientsEquiv d ℳ p a ∈ shiftedGrading ℳ d.monoid p q) :
    moduleCoefficientsEquiv d ℳ p (actionDerivationHom d ℳ p (ℒ := ℒ) x a) ∈
      shiftedGrading ℳ d.monoid p (n + q) := by
  rw [moduleCoefficientsEquiv_actionDerivationHom, mem_shiftedGrading]
  change ⁅x, ((moduleCoefficientsEquiv d ℳ p a : shiftedSubmodule ℳ d.monoid p) : M)⁆ ∈
    ℳ (p + (n + q))
  simpa only [vadd_eq_add, add_left_comm] using
    SetLike.GradedBracket.bracket_mem hx ((mem_shiftedGrading ℳ d.monoid p).mp ha)

end Mei.ModuleProbe
