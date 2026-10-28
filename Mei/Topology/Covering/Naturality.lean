/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Covering.Lift

/-!
# Naturality of covering lifts

A commuting square between two projections transports both the whole lifted map
and its reference value. When the projections are covering maps, this transport
commutes with the lift specified by a reference value. Parameter restriction and
composition of commuting squares preserve the transport. If the map of total
spaces intertwines deck actions, the induced maps of lifts and fibers do as well.

The lift and fiber carriers and the reference-value equivalence come from
`Mei.Topology.Covering.Lift`.
-/

public section

namespace ContinuousMap

open Mei

variable {E E' E'' X X' X'' A B : Type*}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace E'']
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace X'']
  [TopologicalSpace A] [TopologicalSpace B]
  {p : E → X} {q : E' → X'} {r : E'' → X''}
  (u : C(E, E')) (v : C(X, X')) (h : q ∘ u = v ∘ p)

/-- A commuting square of projections maps their reference fibers together. -/
def mapFiber (x : X) : (p ⁻¹' {x}) → (q ⁻¹' {v x}) :=
  Set.MapsTo.restrict u (p ⁻¹' {x}) (q ⁻¹' {v x})
    (fun e he => (congrFun h e).trans (congrArg v he))

/-- The map of fibers applies the map of total spaces to the lifted point. -/
@[simp]
theorem mapFiber_val (x : X) (e : p ⁻¹' {x}) :
    (u.mapFiber v h x e).val = u e.val :=
  Set.MapsTo.val_restrict_apply _ _

/-- The identity square preserves every point of the fiber. -/
@[simp]
theorem mapFiber_id (x : X) (e : p ⁻¹' {x}) :
    (ContinuousMap.id E).mapFiber (ContinuousMap.id X) (by rfl) x e = e := by
  apply Subtype.ext
  exact mapFiber_val _ _ _ _ _

/-- Successive commuting squares compose on the actual reference fiber. -/
theorem mapFiber_comp (u' : C(E', E'')) (v' : C(X', X''))
    (h' : r ∘ u' = v' ∘ q) (x : X) (e : p ⁻¹' {x}) :
    u'.mapFiber v' h' (v x) (u.mapFiber v h x e) =
      (u'.comp u).mapFiber (v'.comp v) (by
        funext e
        exact (congrFun h' (u e)).trans (congrArg v' (congrFun h e))) x e := by
  apply Subtype.ext
  simp only [mapFiber_val, ContinuousMap.comp_apply]

/-- A commuting square of projections maps a lift by postcomposition. -/
def mapLifts (f : C(A, X)) : coveringLifts p f → coveringLifts q (v.comp f) := fun F =>
  ⟨u.comp F.val, (mem_coveringLifts_iff _ _).mpr <| by
    funext a
    exact (congrFun h (F.val a)).trans
      (congrArg v (congrFun ((mem_coveringLifts_iff f F.val).mp F.property) a))⟩

/-- The mapped lift applies the map of total spaces pointwise. -/
@[simp]
theorem mapLifts_apply (f : C(A, X)) (F : coveringLifts p f) (a : A) :
    (u.mapLifts v h f F).val a = u (F.val a) := (rfl)

/-- Restricting parameters commutes with transport by a square of projections. -/
theorem mapLifts_precomp (f : C(A, X)) (g : C(B, A)) (F : coveringLifts p f) :
    u.mapLifts v h (f.comp g) (coveringLifts.precomp f g F) =
      coveringLifts.precomp (v.comp f) g (u.mapLifts v h f F) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro b
  simp only [mapLifts_apply, coveringLifts.precomp_apply]

/-- The identity square preserves the full lifted map. -/
@[simp]
theorem mapLifts_id (f : C(A, X)) (F : coveringLifts p f) :
    (ContinuousMap.id E).mapLifts (ContinuousMap.id X) (by rfl) f F = F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  simp only [mapLifts_apply, ContinuousMap.id_apply]

/-- Transport through successive squares agrees with transport through their composite. -/
theorem mapLifts_comp (u' : C(E', E'')) (v' : C(X', X''))
    (h' : r ∘ u' = v' ∘ q) (f : C(A, X)) (F : coveringLifts p f) :
    u'.mapLifts v' h' (v.comp f) (u.mapLifts v h f F) =
      (u'.comp u).mapLifts (v'.comp v) (by
        funext e
        exact (congrFun h' (u e)).trans (congrArg v' (congrFun h e))) f F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  simp only [mapLifts_apply, ContinuousMap.comp_apply]

/-- An intertwining map transports deck actions on the reference fibers. -/
theorem mapFiber_smul (φ : deck p → deck q)
    (hu : ∀ (g : deck p) e, u (g • e) = φ g • u e)
    (x : X) (g : deck p) (e : p ⁻¹' {x}) :
    u.mapFiber v h x (g • e) = φ g • u.mapFiber v h x e := by
  apply Subtype.ext
  simp only [mapFiber_val, fiber_smul_val]
  exact hu g e.val

/-- An intertwining map transports deck actions on the entire lifted maps. -/
theorem mapLifts_smul (φ : deck p → deck q)
    (hu : ∀ (g : deck p) e, u (g • e) = φ g • u e)
    (f : C(A, X)) (g : deck p) (F : coveringLifts p f) :
    u.mapLifts v h f (g • F) = φ g • u.mapLifts v h f F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  simp only [mapLifts_apply, SubMulAction.val_smul, ContinuousMap.smul_apply]
  exact hu g (F.val a)

variable [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]

/-- A map between coverings transports the chosen reference value and the unique
lift simultaneously. The map of total spaces need not be invertible. -/
theorem mapLifts_liftEquiv_symm (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (f : C(A, X)) (a : A) (e : p ⁻¹' {f a}) :
    u.mapLifts v h f ((hp.liftEquiv f a).symm e) =
      (hq.liftEquiv (v.comp f) a).symm (u.mapFiber v h (f a) e) := by
  apply (hq.liftEquiv (v.comp f) a).injective
  apply Subtype.ext
  simp

end ContinuousMap
