/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Instances.Sign
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Local constancy of signs

Near a point where a continuous function to a linear order does not vanish, its sign is
constant (`ContinuousAt.eventually_sign_eq`). This uses the continuity of `SignType.sign` away
from zero, `continuousAt_sign_of_ne_zero`, and the discreteness of `SignType`.

In a linearly ordered field with the order topology, for `x ≠ 0` and any `y`, small
multiples `σ * y` have absolute value smaller than `|x|` (`eventually_abs_mul_lt`), so that
`x + σ * y` has the sign of `x`.
-/

public section

open Filter Topology

namespace ContinuousAt

variable {X α : Type*} [TopologicalSpace X] [Zero α] [LinearOrder α] [TopologicalSpace α]
  [OrderTopology α] {f : X → α} {x : X}

/-- Near a point where a continuous function does not vanish, its sign is constant. -/
theorem eventually_sign_eq (hf : ContinuousAt f x) (h : f x ≠ 0) :
    ∀ᶠ y in 𝓝 x, SignType.sign (f y) = SignType.sign (f x) := by
  have hc := (continuousAt_sign_of_ne_zero h).comp hf
  rw [ContinuousAt, nhds_discrete SignType, tendsto_pure] at hc
  exact hc

end ContinuousAt

namespace Mei

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
  [OrderTopology K]

/-- For `x ≠ 0`, small multiples `σ * y` have absolute value smaller than `|x|`. -/
theorem eventually_abs_mul_lt {x : K} (hx : x ≠ 0) (y : K) :
    ∀ᶠ σ in 𝓝 (0 : K), |σ * y| < |x| := by
  have hlim : Tendsto (fun σ : K => |σ * y|) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_id.mul continuous_const).abs.tendsto (0 : K) :
      Tendsto (fun σ : K => |σ * y|) (𝓝 0) (𝓝 |0 * y|))
  exact hlim.eventually_lt_const (abs_pos.mpr hx)

end Mei
