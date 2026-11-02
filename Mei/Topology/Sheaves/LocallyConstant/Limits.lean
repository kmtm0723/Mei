/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.LocallyConstant
public import Mathlib.Topology.Sheaves.Limits
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

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w t z

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {C : Type w} [Category.{v} C]
  {J : Type t} [Category.{z} J] [HasLimitsOfShape J C]
  (D : J ⥤ X.Sheaf C)

private theorem isIso_limit_restrict {U V : Opens X} (hVU : V ≤ U)
    (h : ∀ j, IsIso ((D.obj j).presheaf.map (homOfLE hVU).op)) :
    IsIso ((limit D).presheaf.map (homOfLE hVU).op) := by
  let ev (W : Opens X) : X.Sheaf C ⥤ C :=
    Sheaf.forget C X ⋙ (evaluation _ C).obj (op W)
  have (W : Opens X) : PreservesLimit (D ⋙ Sheaf.forget C X)
      ((evaluation _ C).obj (op W)) := by
    apply evaluation_preservesLimit
  have (W : Opens X) : PreservesLimit D (ev W) := comp_preservesLimit _ _
  let τ : D ⋙ ev U ⟶ D ⋙ ev V :=
    { app := fun j => (D.obj j).presheaf.map (homOfLE hVU).op
      naturality := fun _ _ f => ((D.map f).hom.naturality (homOfLE hVU).op).symm }
  have : IsIso τ := (NatTrans.isIso_iff_isIso_app τ).mpr h
  let a := asIso τ
  let hU := isLimitOfPreserves (ev U) (limit.isLimit D)
  let hV := isLimitOfPreserves (ev V) (limit.isLimit D)
  let e : (limit D).presheaf.obj (op U) ≅ (limit D).presheaf.obj (op V) :=
    hU.conePointsIsoOfNatIso hV a
  have heq : (limit D).presheaf.map (homOfLE hVU).op = e.hom := by
    apply hV.hom_ext
    intro j
    have he := hU.conePointsIsoOfNatIso_hom_comp hV a j
    change e.hom ≫ (limit.π D j).hom.app (op V) =
      (limit.π D j).hom.app (op U) ≫ (D.obj j).presheaf.map (homOfLE hVU).op at he
    exact ((limit.π D j).hom.naturality (homOfLE hVU).op).trans he.symm
  rw [heq]
  exact e.isIso_hom

variable [Finite J] [LocallyConnectedSpace X]

/-- A finite-object diagram of sheaves with locally isomorphic restrictions has a
limit sheaf with locally isomorphic restrictions. The coefficient category only
needs limits of this shape; neither face-map injectivity nor finite hom sets are
required. -/
theorem exists_isIso_restrictions_limit
    (hD : ∀ j (x : X), ∃ U : Opens X, x ∈ U ∧
      ∀ (V : Opens X) (hVU : V ≤ U), (V : Set X).Nonempty → IsPreconnected (V : Set X) →
        IsIso ((D.obj j).presheaf.map (homOfLE hVU).op)) (x : X) :
    ∃ U : Opens X, x ∈ U ∧
      ∀ (V : Opens X) (hVU : V ≤ U), (V : Set X).Nonempty → IsPreconnected (V : Set X) →
        IsIso ((limit D).presheaf.map (homOfLE hVU).op) := by
  choose W hxW hW using fun j => hD j x
  let O : Opens X := ⨅ j, W j
  have hxO : x ∈ O := by
    change x ∈ (↑(⨅ j, W j) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxW
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
        ∀ (V : Opens X) (hVU : V ≤ U), (V : Set X).Nonempty → IsPreconnected (V : Set X) →
          IsIso ((D.obj j).presheaf.map (homOfLE hVU).op) := by
      obtain ⟨U, hy, hU⟩ :=
        HasLocallyBijectivePreconnectedRestrictions.exists_bijective_restrictions (F := D.obj j) y
      exact ⟨U, hy, fun V hVU hV hconn => (isIso_iff_bijective _).mpr (hU V hVU hV hconn)⟩
    obtain ⟨U, hx, hU⟩ := exists_isIso_restrictions_limit D hD x
    exact ⟨U, hx, fun V hVU hV hconn => (isIso_iff_bijective _).mp (hU V hVU hV hconn)⟩

end TopCat.Sheaf
