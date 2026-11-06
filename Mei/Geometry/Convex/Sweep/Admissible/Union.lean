/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible

/-!
# Invariance of admissible domains under singular-set unions

The complete singular-avoidance condition depends only on the union of the
singular sets. Replacing that union by an exact finite polyhedral presentation
preserves every endpoint constraint; it introduces no extra forbidden points.
-/

public section

namespace Mei.Convex

open Set

variable {V J K K' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (v : Fin (n + 1) → V) (P : Fin n → Set V)
  (W : J → Set V) (S : K → Set V) (S' : K' → Set V) (C : Set V)

/-- The full ray domain is unchanged by an exact replacement of the union of
singular sets, including at recorded encounters, the endpoint and infinite tail. -/
theorem admissibleBackwardDomain_congr_singular
    (hS : (⋃ a, S a) = ⋃ a, S' a) :
    admissibleBackwardDomain f c v P W S C =
      admissibleBackwardDomain f c v P W S' C := by
  have havoid (x : V) : (∀ a, x ∉ S a) ↔ ∀ a, x ∉ S' a := by
    simpa only [mem_iUnion, not_exists] using
      (congrArg (fun A : Set V => x ∉ A) hS).to_iff
  ext Q
  simp only [mem_admissibleBackwardDomain, mem_backwardSingularAvoidanceDomain,
    mem_backwardAvoidanceDomain, mem_backwardIncomingDomain]
  simp only [show (∀ j a t, 0 < t → t < backwardTime f c (fun j => v j.castSucc) j Q →
      backwardPoint f c (fun j => v j.castSucc) j.castSucc Q + t • v j.castSucc ∉ S a) ↔
      (∀ j a t, 0 < t → t < backwardTime f c (fun j => v j.castSucc) j Q →
        backwardPoint f c (fun j => v j.castSucc) j.castSucc Q + t • v j.castSucc ∉ S' a) by
      constructor
      · intro hg j a t ht hu
        exact (havoid _).mp (fun b => hg j b t ht hu) a
      · intro hg j a t ht hu
        exact (havoid _).mpr (fun b => hg j b t ht hu) a,
    show (∀ a (t : ℝ), 0 < t → backwardPoint f c (fun j => v j.castSucc) (Fin.last n) Q +
      t • v (Fin.last n) ∉ S a) ↔ (∀ a (t : ℝ), 0 < t →
      backwardPoint f c (fun j => v j.castSucc) (Fin.last n) Q + t • v (Fin.last n) ∉ S' a) by
      constructor
      · intro hg a t ht
        exact (havoid _).mp (fun b => hg b t ht) a
      · intro hg a t ht
        exact (havoid _).mpr (fun b => hg b t ht) a, havoid]

end Mei.Convex
