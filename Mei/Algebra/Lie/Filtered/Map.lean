/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.BCH

/-!
# Naturality of filtered BCH actions

An equivariant coefficient map along a graded Lie homomorphism intertwines the
finite and completed BCH actions. Finite comparison requires only the filtration
bound at the selected source and target orders; completed comparison requires
the compatible bounds at every target order. Coefficient continuity has its own
monotone modulus, independent of the positive degree map's modulus. Comparison at
the maximum of the two cutoffs suffices. Coefficient and Lie maps may have kernels,
and degrees may merge.

The finite statement uses the existing quotient Lie representations and Mathlib's
naturality of nilpotent exponentials. The completion maps are the existing maps of
filtered coefficients and graded BCH groups. This is the action compatibility in
Mandel's shifted coefficient setting, *Scattering diagrams, theta functions, and
refined tropical curve counts*, §2.1 (arXiv:1503.06183).
-/

public section

noncomputable section

namespace Mei.ModuleFiltration

section Finite

variable {N N' R L L' M M' : Type*} [AddCommMonoid N] [AddCommMonoid N']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
  [DecidableEq N] [DecidableEq N']
  {d : PositiveDegrees N} {e : PositiveDegrees N'} {T : PositiveDegreeMap d e}
  {ℒ : N → Submodule R L} {ℒ' : N' → Submodule R L'}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℒ'] [IsPositiveGrading e ℒ']
  (F : ModuleFiltration R M) (G : ModuleFiltration R M')
  [IsFiltrationRaising d ℒ F] [IsFiltrationRaising e ℒ' G]
  (φ : GradedLieHom T ℒ ℒ') (ψ : M →ₗ[R] M')
  (hequiv : ∀ (x : L) (a : M), ψ ⁅x, a⁆ = ⁅φ x, ψ a⁆)

include hequiv

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']

/-- Equivariant coefficient maps intertwine finite BCH actions along the induced
map of Lie truncations, allowing different source and target orders. -/
theorem mapQ_truncatedBCHAction_of_gradedLieHom {a : ℕ} (k : ℕ)
    (h : T.modulus k ≤ a)
    (hψ : F.submodule (a + 1) ≤ (G.submodule (k + 1)).comap ψ)
    (g : BCHGroup (d.truncatedLie ℒ a)) (z : F.quotient a) :
    (F.submodule (a + 1)).mapQ (G.submodule (k + 1)) ψ
        hψ
        (F.truncatedBCHAction d ℒ a g z) =
      G.truncatedBCHAction e ℒ' k ((φ.truncatedMap k h).bchGroupMap g)
        ((F.submodule (a + 1)).mapQ (G.submodule (k + 1)) ψ
          hψ z) := by
  rw [F.truncatedBCHAction_apply, G.truncatedBCHAction_apply, LieHom.log_bchGroupMap]
  exact F.mapQ_truncatedExpLieAction_of_gradedLieHom G φ ψ hequiv k h hψ (BCHGroup.log g) z

end Finite

section Completed

variable {N N' R M M' : Type*} {L L' : Type u} [AddCommMonoid N] [AddCommMonoid N']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
  [DecidableEq N] [DecidableEq N']
  {d : PositiveDegrees N} {e : PositiveDegrees N'} {T : PositiveDegreeMap d e}
  {ℒ : N → Submodule R L} {ℒ' : N' → Submodule R L'}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℒ'] [IsPositiveGrading e ℒ']
  (F : ModuleFiltration R M) (G : ModuleFiltration R M')
  [IsFiltrationRaising d ℒ F] [IsFiltrationRaising e ℒ' G]
  (φ : GradedLieHom T ℒ ℒ') (ψ : M →ₗ[R] M')
  (μ : ℕ → ℕ) (hμ : Monotone μ)
  (hψ : ∀ k, F.submodule (μ k + 1) ≤ (G.submodule (k + 1)).comap ψ)
  (hequiv : ∀ (x : L) (a : M), ψ ⁅x, a⁆ = ⁅φ x, ψ a⁆)

include hequiv

/-- The induced maps on completed coefficients and completed BCH groups intertwine
the actions on arbitrary completed coefficient inputs. The coefficient map may
have a continuity modulus independent of the Lie map's degree modulus. -/
theorem completionMap_completedBCHAction_of_gradedLieHom
    (g : d.completedBCHGroup ℒ) (z : F.completion) :
    F.completionMap G ψ μ hμ hψ (F.completedBCHAction d ℒ g z) =
      G.completedBCHAction e ℒ' (φ.completedMap g)
        (F.completionMap G ψ μ hμ hψ z) := by
  apply G.completion_ext
  intro k
  let a := max (T.modulus k) (μ k)
  have hLie : T.modulus k ≤ a := le_max_left _ _
  have hCoeff : μ k ≤ a := le_max_right _ _
  have hψa : F.submodule (a + 1) ≤ (G.submodule (k + 1)).comap ψ :=
    (F.antitone (Nat.add_le_add_right hCoeff 1)).trans (hψ k)
  let gk : BCHGroup (d.truncatedLie ℒ a) := CompletedGroup.projection a g
  let qψ := (F.submodule (a + 1)).mapQ (G.submodule (k + 1)) ψ hψa
  have hl : G.projection k
      (F.completionMap G ψ μ hμ hψ (F.completedBCHAction d ℒ g z)) =
      qψ (F.truncatedBCHAction d ℒ a gk (F.projection a z)) :=
    (F.projection_completionMap_of_le G ψ μ hμ hψ k a hCoeff _).trans
      (congrArg qψ (F.projection_completedBCHAction d ℒ g z a))
  have hr : G.projection k
      (G.completedBCHAction e ℒ' (φ.completedMap g)
        (F.completionMap G ψ μ hμ hψ z)) =
      G.truncatedBCHAction e ℒ' k ((φ.truncatedMap k hLie).bchGroupMap gk)
        (qψ (F.projection a z)) :=
    (G.projection_completedBCHAction e ℒ' (φ.completedMap g) _ k).trans
      (congrArg₂ (fun g z => G.truncatedBCHAction e ℒ' k g z)
        (φ.projection_completedMap_of_le k hLie g)
        (F.projection_completionMap_of_le G ψ μ hμ hψ k a hCoeff z))
  exact hl.trans ((F.mapQ_truncatedBCHAction_of_gradedLieHom G φ ψ hequiv k hLie hψa
    gk (F.projection a z)).trans hr.symm)

end Completed

end Mei.ModuleFiltration
