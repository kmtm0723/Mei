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
`Mei.Topology.Covering.Lift`; the proofs use their public evaluation equations.
-/

public section

namespace ContinuousMap

variable {E E' E'' X X' X'' A B : Type*}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace E'']
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace X'']
  [TopologicalSpace A] [TopologicalSpace B]
  {p : E → X} {q : E' → X'} {r : E'' → X''}
  (u : C(E, E')) (v : C(X, X')) (h : q ∘ u = v ∘ p)

/-- A commuting square of projections maps their reference fibers together. -/
def mapCoveringFiber (x : X) : deck.fiber p x → deck.fiber q (v x) := fun e =>
  ⟨u e.val, (deck.mem_fiber_iff _ _).mpr <|
    (congrFun h e.val).trans (congrArg v ((deck.mem_fiber_iff _ _).mp e.property))⟩

/-- The map of fibers applies the map of total spaces to the lifted point. -/
@[simp]
theorem mapCoveringFiber_val (x : X) (e : deck.fiber p x) :
    (u.mapCoveringFiber v h x e).val = u e.val := (rfl)

/-- A commuting square of projections maps a lift by postcomposition. -/
def mapCoveringLift (f : C(A, X)) : deck.lifts p f → deck.lifts q (v.comp f) := fun F =>
  ⟨u.comp F.val, (deck.mem_lifts_iff _ _).mpr <| by
    funext a
    exact (congrFun h (F.val a)).trans
      (congrArg v (congrFun ((deck.mem_lifts_iff f F.val).mp F.property) a))⟩

/-- The mapped lift applies the map of total spaces pointwise. -/
@[simp]
theorem mapCoveringLift_apply (f : C(A, X)) (F : deck.lifts p f) (a : A) :
    (u.mapCoveringLift v h f F).val a = u (F.val a) := (rfl)

/-- Restricting parameters commutes with transport by a square of projections. -/
theorem mapCoveringLift_precomp (f : C(A, X)) (g : C(B, A)) (F : deck.lifts p f) :
    u.mapCoveringLift v h (f.comp g) (deck.precompLift f g F) =
      deck.precompLift (v.comp f) g (u.mapCoveringLift v h f F) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro b
  simp only [mapCoveringLift_apply, deck.precompLift_apply]

/-- The identity square preserves the full lifted map. -/
@[simp]
theorem mapCoveringLift_id (f : C(A, X)) (F : deck.lifts p f) :
    (ContinuousMap.id E).mapCoveringLift (ContinuousMap.id X) (by rfl) f F = F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  rfl

/-- Transport through successive squares agrees with transport through their composite. -/
theorem mapCoveringLift_comp (u' : C(E', E'')) (v' : C(X', X''))
    (h' : r ∘ u' = v' ∘ q) (f : C(A, X)) (F : deck.lifts p f) :
    u'.mapCoveringLift v' h' (v.comp f) (u.mapCoveringLift v h f F) =
      (u'.comp u).mapCoveringLift (v'.comp v) (by
        funext e
        exact (congrFun h' (u e)).trans (congrArg v' (congrFun h e))) f F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  rfl

/-- An intertwining map transports deck actions on the reference fibers. -/
theorem mapCoveringFiber_smul (φ : deck p →* deck q)
    (hu : ∀ (g : deck p) e, u (g • e) = φ g • u e)
    (x : X) (g : deck p) (e : deck.fiber p x) :
    u.mapCoveringFiber v h x (g • e) = φ g • u.mapCoveringFiber v h x e := by
  apply Subtype.ext
  exact hu g e.val

/-- An intertwining map transports deck actions on the entire lifted maps. -/
theorem mapCoveringLift_smul (φ : deck p →* deck q)
    (hu : ∀ (g : deck p) e, u (g • e) = φ g • u e)
    (f : C(A, X)) (g : deck p) (F : deck.lifts p f) :
    u.mapCoveringLift v h f (g • F) = φ g • u.mapCoveringLift v h f F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  exact hu g (F.val a)

variable [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]

/-- A map between coverings transports the chosen reference value and the unique
lift simultaneously. The map of total spaces need not be invertible. -/
theorem mapCoveringLift_symm_liftEquiv (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (f : C(A, X)) (a : A) (e : deck.fiber p (f a)) :
    u.mapCoveringLift v h f ((hp.liftEquiv f a).symm e) =
      (hq.liftEquiv (v.comp f) a).symm (u.mapCoveringFiber v h (f a) e) := by
  apply (hq.liftEquiv (v.comp f) a).injective
  apply Subtype.ext
  simp

end ContinuousMap
