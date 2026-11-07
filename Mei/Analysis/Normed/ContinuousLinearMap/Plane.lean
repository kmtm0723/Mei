/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous linear functionals on the plane

The values of a continuous linear functional `l` on `ℝ × ℝ` at two points `p` and `q` with the
same second coordinate differ by `(q.1 - p.1) * l (1, 0)`
(`ContinuousLinearMap.apply_eq_of_snd_eq`). In particular, `l` is determined along each
horizontal line by its value at one point and its value at `(1, 0)`.
-/

public section

namespace ContinuousLinearMap

/-- A functional on the plane is determined along a horizontal line by its value at one point and
its value at `(1, 0)`. -/
theorem apply_eq_of_snd_eq (l : (ℝ × ℝ) →L[ℝ] ℝ) {p q : ℝ × ℝ} (hpq : q.2 = p.2) :
    l q = l p + (q.1 - p.1) * l (1, 0) := by
  have : q = p + (q.1 - p.1) • ((1 : ℝ), (0 : ℝ)) := by
    ext
    · simp
    · simp [hpq]
  calc l q = l (p + (q.1 - p.1) • ((1 : ℝ), (0 : ℝ))) := congrArg l this
    _ = l p + (q.1 - p.1) * l (1, 0) := by rw [map_add, map_smul, smul_eq_mul]

end ContinuousLinearMap
