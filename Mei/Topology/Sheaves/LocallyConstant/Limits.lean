/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.LocallyConstant
public import Mei.Topology.Sheaves.Limits
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Finite limits of locally constant sheaves

On a locally connected space, a diagram with finitely many objects admits a
common connected neighborhood on which all component restrictions are
isomorphisms. Its limit has the same restriction property. In particular, the
existing restriction-sense local-constancy condition for type-valued sheaves is
closed under these limits. Arrows need not form a finite type.

For chamber-and-face diagrams this applies to their actual limit sheaf, keeping
all face data and incidence equations. No injectivity of the face maps is needed.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Sheaf

universe u v w t z

namespace CategoryTheory.Functor

variable {X : TopCat.{u}} {C : Type w} [Category.{v} C]
  {J : Type t} [Category.{z} J] [HasLimitsOfShape J C]
  (D : J ⥤ X.Sheaf C)

variable [Finite J] [LocallyConnectedSpace X]

/-- A finite-object diagram of sheaves with locally isomorphic restrictions has a
limit sheaf with locally isomorphic restrictions. The coefficient category only
needs limits of this shape; neither face-map injectivity nor finite hom sets are
required. -/
theorem exists_isIso_restrictions_limit
    (hD : ∀ j (x : X), ∃ U : Opens X, x ∈ U ∧
      ∀ (V : Opens X) (hVU : V ≤ U), (V : Set X).Nonempty → _root_.IsPreconnected (V : Set X) →
        IsIso ((D.obj j).presheaf.map (homOfLE hVU).op)) (x : X) :
    ∃ U : Opens X, x ∈ U ∧
      ∀ (V : Opens X) (hVU : V ≤ U), (V : Set X).Nonempty → _root_.IsPreconnected (V : Set X) →
        IsIso ((limit D).presheaf.map (homOfLE hVU).op) := by
  choose W hxW hW using fun j => hD j x
  let O : Opens X := ⨅ j, W j
  have hxO : x ∈ O := by
    dsimp only [O]
    exact (Set.ext_iff.mp (Opens.coe_iInf W) x).mpr (Set.mem_iInter.mpr hxW)
  obtain ⟨N, ⟨hNopen, hxN, hNconn⟩, hNO⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp (O.isOpen.mem_nhds hxO)
  let U : Opens X := ⟨N, hNopen⟩
  have hUW (j : J) : U ≤ W j := le_trans hNO (iInf_le W j)
  refine ⟨U, hxN, fun V hVU hV hVconn => isIso_limit_restrict D hVU (fun j => ?_)⟩
  have := hW j U (hUW j) ⟨x, hxN⟩ hNconn.isPreconnected
  have := hW j V (hVU.trans (hUW j)) hV hVconn
  apply IsIso.of_isIso_fac_left (f := (D.obj j).presheaf.map (homOfLE (hUW j)).op)
    (h := (D.obj j).presheaf.map (homOfLE (hVU.trans (hUW j))).op)
  exact (D.obj j).presheaf.map_comp _ _ |>.symm

/-- Finite limits preserve the existing type-valued restriction-sense local
constancy condition on a locally connected space. -/
instance hasLocallyBijectivePreconnectedRestrictions_limit
    [HasLimitsOfShape J (Type v)] (D : J ⥤ X.Sheaf (Type v))
    [∀ j, HasLocallyBijectivePreconnectedRestrictions (D.obj j)] :
    HasLocallyBijectivePreconnectedRestrictions (limit D) where
  exists_bijective_restrictions x := by
    have hD (j : J) (y : X) : ∃ U : Opens X, y ∈ U ∧
        ∀ (V : Opens X) (hVU : V ≤ U), (V : Set X).Nonempty → _root_.IsPreconnected (V : Set X) →
          IsIso ((D.obj j).presheaf.map (homOfLE hVU).op) := by
      obtain ⟨U, hy, hU⟩ :=
        HasLocallyBijectivePreconnectedRestrictions.exists_bijective_restrictions (F := D.obj j) y
      exact ⟨U, hy, fun V hVU hV hconn => (isIso_iff_bijective _).mpr (hU V hVU hV hconn)⟩
    obtain ⟨U, hx, hU⟩ := exists_isIso_restrictions_limit D hD x
    exact ⟨U, hx, fun V hVU hV hconn => (isIso_iff_bijective _).mp (hU V hVU hV hconn)⟩

end CategoryTheory.Functor
