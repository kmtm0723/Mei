/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.History
public import Mei.LinearAlgebra.LocalResolution

/-!
# Linear resolution certificates from consistent path products

The finite component histories of two admissible path chains in a consistent
directed diagram give a diagonal common-lift certificate in every retained
outgoing degree. The two chains can have different lengths, and the incoming
parameter module is arbitrary. The finite families include zero maps and depend
only on the cutoff and the chains, not on the incoming coefficient.

This constructs the linear coefficient certificate from
`sum_component_homogeneousHistory_levelPathProduct_eq`; it does not identify
which algebraic histories have geometric broken-line realizations. The underlying
component-history identity follows Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3.2 (arXiv:1601.07081v4).
-/

public noncomputable section

open Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ : Type} {Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

variable {M E : Type*} [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M] [AddCommMonoid E] [Module R E]
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ]
  (p : Γ)

/-- Consistent chains with common endpoints supply a common-lift certificate
for their finite outgoing component histories, for every input simultaneously. -/
def localResolutionCertificateLevelPathProduct
    {k : ℕ} (hD : D.LevelConsistent k) {n m : ℕ}
    (x : Fin (n + 1) → WallComplement (fun j : D.active k => (D.wall j).support))
    (y : Fin (m + 1) → WallComplement (fun j : D.active k => (D.wall j).support))
    (γ : (j : Fin n) → AdmissiblePLPath (x j.succ) (x j.castSucc))
    (γ' : (j : Fin m) → AdmissiblePLPath (y j.succ) (y j.castSucc))
    (h₀ : x 0 = y 0) (h₁ : x (Fin.last n) = y (Fin.last m))
    (q : Γ) (hq : d.degree (q - p) ≤ k)
    (a : E →ₗ[R] (d.shiftedLieFiltration ℒ ℳ p).quotient k) :
    LinearMap.LocalResolutionCertificate LinearMap.id LinearMap.id
      (fun r : Fin n → (d.finite_cutoff k).toFinset =>
      (d.shiftedQuotientComponent ℳ p q k hq).comp
        ((homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
          (fun j => ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
            (D.levelPathProduct k (γ j))).toLinearMap)
          (fun j => (r j).val)).comp a))
      (fun r : Fin m → (d.finite_cutoff k).toFinset =>
      (d.shiftedQuotientComponent ℳ p q k hq).comp
        ((homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
          (fun j => ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
            (D.levelPathProduct k (γ' j))).toLinearMap)
          (fun j => (r j).val)).comp a)) :=
  LinearMap.LocalResolutionCertificate.ofSumEq _ _
    (D.sum_component_homogeneousHistory_levelPathProduct_eq ℳ p hD x y γ γ' h₀ h₁ q hq a)

end Mei.DirectedDiagram
