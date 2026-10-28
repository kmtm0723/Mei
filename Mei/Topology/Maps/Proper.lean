/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper maps under compact perturbations

A continuous map into a Hausdorff space is proper if it agrees with a proper
map outside a compact set. The ultrafilter characterization avoids local
compactness or countability assumptions on either space.
The proof uses Mathlib's `isProperMap_iff_ultrafilter_of_t2` and the compact-set
criterion for convergence of ultrafilters.
-/

public section

open Set Filter Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
  {f g : X → Y} {K : Set X}

/-- Continuous compact perturbations of a proper map are proper. -/
theorem IsProperMap.of_eqOn_compl_isCompact (hg : IsProperMap g) (hf : Continuous f)
    (hK : IsCompact K) (hfg : EqOn f g Kᶜ) : IsProperMap f := by
  refine isProperMap_iff_ultrafilter_of_t2.mpr ⟨hf, ?_⟩
  intro 𝒰 y hy
  by_cases h : K ∈ 𝒰
  · obtain ⟨x, _, hx⟩ := hK.ultrafilter_le_nhds' 𝒰 h
    exact ⟨x, hx⟩
  · have heq : f =ᶠ[(𝒰 : Filter X)] g := by
      filter_upwards [Ultrafilter.compl_mem_iff_notMem.mpr h] with x hx
      exact hfg hx
    obtain ⟨x, _, hx⟩ := hg.ultrafilter_le_nhds_of_tendsto (hy.congr' heq)
    exact ⟨x, hx⟩
