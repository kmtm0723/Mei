/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Connected.Basic

/-!
# Locally constant sheaves of types

A sheaf is locally constant in the restriction sense when every point has an
open neighborhood whose sections restrict bijectively to each nonempty
preconnected open subset. This is the local-constant sheaf condition used for
coefficient transport and facet descent in the scattering-diagram roadmap.
-/

public section

open CategoryTheory TopologicalSpace Opposite

universe u v

namespace TopCat

variable {X : TopCat.{u}}

/-- Locally constant sheaves, expressed by bijective restriction maps on
nonempty preconnected open subsets of a sufficiently small neighborhood. -/
class IsLocallyConstantSheaf (F : X.Sheaf (Type v)) : Prop where
  /-- Each point has an open neighborhood with the local restriction property. -/
  exists_bijective_restrictions (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∀ (V : Opens X) (hVU : V ≤ U),
      (V : Set X).Nonempty → IsPreconnected (V : Set X) →
        Function.Bijective (F.presheaf.map (homOfLE hVU).op)

end TopCat
