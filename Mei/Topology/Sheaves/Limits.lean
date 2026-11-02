/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Restriction isomorphisms for limits of sheaves

When every component of a sheaf diagram restricts isomorphically along one open
inclusion, its limit does too. Neither the diagram nor its arrows need be finite.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w t z

namespace CategoryTheory.Functor

variable {X : TopCat.{u}} {C : Type w} [Category.{v} C]
  {J : Type t} [Category.{z} J] [HasLimitsOfShape J C]
  (D : J ⥤ X.Sheaf C)

/-- The restriction of a limit sheaf is an isomorphism whenever the component
restrictions are isomorphisms. Only limits of the given shape are required. -/
theorem isIso_limit_restrict {U V : Opens X} (hVU : V ≤ U)
    (h : ∀ j, IsIso ((D.obj j).presheaf.map (homOfLE hVU).op)) :
    IsIso ((limit D).presheaf.map (homOfLE hVU).op) := by
  let ev (W : Opens X) : X.Sheaf C ⥤ C :=
    TopCat.Sheaf.forget C X ⋙ (evaluation _ C).obj (op W)
  have : HasLimitsOfShape Jᵒᵖᵒᵖ C :=
    hasLimitsOfShape_of_equivalence (opOpEquivalence J).symm
  have (W : Opens X) : PreservesLimit (D.op.leftOp ⋙ TopCat.Sheaf.forget C X)
      ((evaluation _ C).obj (op W)) := by
    apply evaluation_preservesLimit
  have (W : Opens X) : PreservesLimit D.op.leftOp (ev W) := comp_preservesLimit _ _
  let α : ev U ⟶ ev V :=
    { app := fun F => F.presheaf.map (homOfLE hVU).op
      naturality := fun _ _ f => (f.hom.naturality (homOfLE hVU).op).symm }
  have : IsIso (whiskerLeft D.op (NatTrans.op α)) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro j
    have := h j.unop
    -- Evaluation and the opposite transformation give the opposite component
    -- restriction. Normalize the local functor definitions to expose this map.
    change IsIso (((D.obj j.unop).presheaf.map (homOfLE hVU).op).op)
    infer_instance
  have (W : Opens X) : PreservesColimit D.op (ev W).op := preservesColimit_op _ _
  -- Apply Mathlib's universal-point theorem to the opposite limit cone.
  have : IsIso (((limit D).presheaf.map (homOfLE hVU).op).op) :=
    isIso_app_coconePt_of_preservesColimit D.op (NatTrans.op α)
      (limit.cone D).op (limit.isLimit D).op
  exact isIso_of_op _

end CategoryTheory.Functor
