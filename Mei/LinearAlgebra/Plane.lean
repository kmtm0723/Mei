/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Linear functionals on the plane

The values of a linear functional `l` on `ℝ × ℝ` at two points `p` and `q` with the same second
coordinate differ by `(q.1 - p.1) * l (1, 0)` (`LinearMap.apply_eq_of_snd_eq`). In particular, `l`
is determined along each horizontal line by its value at one point and its value at `(1, 0)`. A
functional that attains its maximum over a horizontal line at a point vanishes at `(1, 0)`
(`LinearMap.apply_one_zero_eq_zero`), hence is constant on that line.
-/

public section

namespace LinearMap

/-- A functional on the plane is determined along a horizontal line by its value at one point and
its value at `(1, 0)`. -/
theorem apply_eq_of_snd_eq (l : (ℝ × ℝ) →ₗ[ℝ] ℝ) {p q : ℝ × ℝ} (hpq : q.2 = p.2) :
    l q = l p + (q.1 - p.1) * l (1, 0) := by
  have : q = p + (q.1 - p.1) • ((1 : ℝ), (0 : ℝ)) := by
    ext
    · simp
    · simp [hpq]
  calc l q = l (p + (q.1 - p.1) • ((1 : ℝ), (0 : ℝ))) := congrArg l this
    _ = l p + (q.1 - p.1) * l (1, 0) := by rw [map_add, map_smul, smul_eq_mul]

/-- A functional that attains its maximum over the horizontal line through `x` at `x` vanishes on
the direction `(1, 0)` of the line, hence is constant on the line. -/
theorem apply_one_zero_eq_zero (l : (ℝ × ℝ) →ₗ[ℝ] ℝ) {x : ℝ × ℝ}
    (hmax : ∀ y : ℝ × ℝ, y.2 = x.2 → l y ≤ l x) : l (1, 0) = 0 := by
  have hpos := hmax (x + (1, 0)) (by simp)
  have hneg := hmax (x - (1, 0)) (by simp)
  simp only [map_add, map_sub] at hpos hneg
  linarith

end LinearMap
