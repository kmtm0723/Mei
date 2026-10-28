/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Recession
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic.Module

/-!
# Affine half-lines and their incoming germs

An affine map from the real line is determined by its germ at negative infinity.
For a set preserved by translation in the negative velocity direction, meeting
that set at one time is equivalent to eventually lying in it. A nonconstant
continuous affine map restricts to a proper half-line on every interval `(-∞, a]`.

These statements use existing affine maps, filter germs and recession cones;
there is no additional tail carrier. They give the geometric representative laws
for incoming affine tails. Coefficients, incoming source labels, and chart or deck
identifications are separate data.
-/

public section

namespace AffineMap

open Filter Set

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- Affine representatives with the same incoming germ agree everywhere. -/
theorem eq_of_eventuallyEq_atBot {f g : ℝ →ᵃ[ℝ] P}
    (h : (f : ℝ → P) =ᶠ[atBot] g) : f = g := by
  obtain ⟨a, ha⟩ := eventually_atBot.mp h
  have hs := congrArg₂ (fun x y : P => x -ᵥ y)
    (ha a le_rfl) (ha (a - 1) (sub_le_self _ zero_le_one))
  rw [← f.linear_apply_vsub, ← g.linear_apply_vsub] at hs
  have hdiff : a - (a - 1) = (1 : ℝ) := by abel
  simp only [vsub_eq_sub, hdiff] at hs
  exact ext_linear (LinearMap.ext_ring hs) (ha a le_rfl)

/-- Equality of incoming affine germs is precisely equality of their representatives. -/
@[simp]
theorem eventuallyEq_atBot_iff {f g : ℝ →ᵃ[ℝ] P} :
    (f : ℝ → P) =ᶠ[atBot] g ↔ f = g :=
  ⟨eq_of_eventuallyEq_atBot, fun h => h ▸ Filter.EventuallyEq.rfl⟩

variable {C : Set V} (f : ℝ →ᵃ[ℝ] V)

/-- A single intersection with a source admitting the backward velocity gives an
incoming tail in that source. No convexity, closedness or nonemptiness is needed. -/
theorem eventually_mem_atBot_iff (hv : -f.linear 1 ∈ recessionCone C) :
    (∀ᶠ t in atBot, f t ∈ C) ↔ ∃ t, f t ∈ C := by
  constructor
  · exact Filter.Eventually.exists
  · rintro ⟨a, ha⟩
    apply eventually_atBot.mpr
    refine ⟨a, fun t ht => ?_⟩
    have hm := (mem_recessionCone.mp hv) (f a) ha (a - t) (sub_nonneg.mpr ht)
    have he : f t = f a + (a - t) • (-f.linear 1) := by
      have hlin : f.linear (t - a) = (t - a) • f.linear 1 := by
        simpa only [smul_eq_mul, mul_one] using f.linear.map_smul (t - a) (1 : ℝ)
      calc
        f t = f.linear (t - a) + f a := by
          simpa only [vadd_eq_add, sub_add_cancel] using f.map_vadd a (t - a)
        _ = f a + (a - t) • (-f.linear 1) := by rw [hlin]; module
    rwa [← he] at hm

end AffineMap

namespace ContinuousAffineMap

open Set Topology

variable {V P : Type*} [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
  [TopologicalSpace P] [AddTorsor V P] [IsTopologicalAddTorsor P]
  (f : ℝ →ᴬ[ℝ] P)

/-- A nonzero velocity gives a closed embedding of the entire affine line. -/
theorem isClosedEmbedding_of_velocity_ne_zero (hv : f.contLinear 1 ≠ 0) :
    IsClosedEmbedding f := by
  have he : (f : ℝ → P) = fun t => t • f.contLinear 1 +ᵥ f 0 := by
    funext t
    have hlin : f.contLinear t = t • f.contLinear 1 := by
      simpa only [smul_eq_mul, mul_one] using f.contLinear.map_smul t (1 : ℝ)
    simpa only [vadd_eq_add, add_zero, hlin] using f.map_vadd 0 t
  rw [he]
  exact (ContinuousAffineEquiv.vaddConst ℝ (f 0)).toHomeomorph.isClosedEmbedding.comp
    (isClosedEmbedding_smul_left hv)

/-- Every closed incoming half-line with nonzero velocity is proper. -/
theorem isProperMap_restrict_Iic (hv : f.contLinear 1 ≠ 0) (a : ℝ) :
    IsProperMap (fun t : Iic a => f t) :=
  ((f.isClosedEmbedding_of_velocity_ne_zero hv).comp
    isClosed_Iic.isClosedEmbedding_subtypeVal).isProperMap

end ContinuousAffineMap
