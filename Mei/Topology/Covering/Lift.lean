/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Covering.Deck
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Covering lifts, their reference values and deck transformations

For a map from a simply connected, locally path connected domain, evaluation at
one reference point identifies its continuous lifts through a covering map with
the fiber over that point. This equivalence respects the existing deck action on
both the lifted map and its reference value. Precomposition, including restriction
of an incoming half-line, commutes with the lift determined by a reference value.

The construction reuses Mathlib's continuous-map lifting existence and uniqueness,
its deck transformation group and the standard `SubMulAction` carrier. No extra
path or covering-space carrier is introduced. The lifting supplier is Hatcher,
*Algebraic Topology*, Propositions 1.33--1.34, as implemented in Mathlib.
-/

public section

open Set

variable {E X A B : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace A] [TopologicalSpace B] {p : E → X}

namespace deck

/-- The fiber is stable under every deck transformation. -/
def fiber (p : E → X) (x : X) : SubMulAction (deck p) E where
  carrier := {e | p e = x}
  smul_mem' g {_} he := (proj_smul g _).trans he

omit [TopologicalSpace X] in
/-- Membership in the deck-invariant fiber is the projection equation. -/
@[simp]
theorem mem_fiber_iff (x : X) (e : E) : e ∈ fiber p x ↔ p e = x := Iff.rfl

/-- Continuous lifts form a deck-invariant subset of the existing continuous maps. -/
def lifts (p : E → X) (f : C(A, X)) : SubMulAction (deck p) C(A, E) where
  carrier := {F | p ∘ F = f}
  smul_mem' g {F} hF := by
    funext a
    exact (proj_smul g (F a)).trans (congrFun hF a)

/-- Membership in the lift carrier is the equation with the covering projection. -/
@[simp]
theorem mem_lifts_iff (f : C(A, X)) (F : C(A, E)) :
    F ∈ lifts p f ↔ p ∘ F = f := Iff.rfl

/-- Pulling back a continuous lift by precomposition is equivariant for the deck action. -/
def precompLift (f : C(A, X)) (g : C(B, A)) :
    lifts p f →[deck p] lifts p (f.comp g) where
  toFun F := ⟨F.val.comp g, by
    apply funext
    intro b
    exact congrFun ((mem_lifts_iff f F.val).mp F.property) (g b)⟩
  map_smul' _ _ := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro b
    rfl

/-- Precomposition evaluates the original lifted map at the new parameter. -/
@[simp]
theorem precompLift_apply (f : C(A, X)) (g : C(B, A)) (F : lifts p f) (b : B) :
    (precompLift f g F).val b = F.val (g b) := (rfl)

/-- Precomposition by the identity retains the entire lift. -/
@[simp]
theorem precompLift_id (f : C(A, X)) (F : lifts p f) :
    precompLift f (ContinuousMap.id A) F = F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  rfl

/-- Successive restrictions or parameter changes compose on the lifted map. -/
theorem precompLift_comp {D : Type*} [TopologicalSpace D] (f : C(A, X))
    (g : C(B, A)) (h : C(D, B)) (F : lifts p f) :
    precompLift (f.comp g) h (precompLift f g F) = precompLift f (g.comp h) F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro d
  rfl

end deck

namespace IsCoveringMap

variable (hp : IsCoveringMap p) [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]

/-- A continuous lift is determined by its value at one reference point. Every
point in the corresponding fiber occurs, with no assumption on other fibers. -/
noncomputable def liftEquiv (f : C(A, X)) (a : A) :
    deck.lifts p f ≃ deck.fiber p (f a) where
  toFun F := ⟨F.val a, (deck.mem_fiber_iff _ _).mpr
    (congrFun ((deck.mem_lifts_iff f F.val).mp F.property) a)⟩
  invFun e := ⟨(hp.existsUnique_continuousMap_lifts f a e.val
    ((deck.mem_fiber_iff _ _).mp e.property)).choose,
    (deck.mem_lifts_iff f _).mpr
      (hp.existsUnique_continuousMap_lifts f a e.val
        ((deck.mem_fiber_iff _ _).mp e.property)).choose_spec.1.2⟩
  left_inv F := by
    apply Subtype.ext
    apply DFunLike.ext'
    apply hp.eq_of_comp_eq
    · exact ContinuousMap.continuous _
    · exact F.val.continuous
    · exact (hp.existsUnique_continuousMap_lifts f a (F.val a)
        (congrFun ((deck.mem_lifts_iff f F.val).mp F.property) a)).choose_spec.1.2.trans
          ((deck.mem_lifts_iff f F.val).mp F.property).symm
    · exact (hp.existsUnique_continuousMap_lifts f a (F.val a)
        (congrFun ((deck.mem_lifts_iff f F.val).mp F.property) a)).choose_spec.1.1
  right_inv e := Subtype.ext
    (hp.existsUnique_continuousMap_lifts f a e.val
      ((deck.mem_fiber_iff _ _).mp e.property)).choose_spec.1.1

/-- Evaluation is the forward direction of the lift equivalence. -/
@[simp]
theorem liftEquiv_apply_val (f : C(A, X)) (a : A) (F : deck.lifts p f) :
    (hp.liftEquiv f a F).val = F.val a := (rfl)

/-- The lift selected by a fiber point has exactly that reference value. -/
@[simp]
theorem liftEquiv_symm_apply_at (f : C(A, X)) (a : A) (e : deck.fiber p (f a)) :
    ((hp.liftEquiv f a).symm e).val a = e.val := by
  exact congrArg Subtype.val ((hp.liftEquiv f a).apply_symm_apply e)

/-- The selected continuous map is a lift of the entire original map. -/
theorem liftEquiv_symm_apply_lifts (f : C(A, X)) (a : A) (e : deck.fiber p (f a)) :
    p ∘ ((hp.liftEquiv f a).symm e).val = f :=
  (deck.mem_lifts_iff f _).mp ((hp.liftEquiv f a).symm e).property

/-- Deck transformations act simultaneously on a lift and its reference value. -/
@[simp]
theorem liftEquiv_smul (f : C(A, X)) (a : A) (g : deck p) (F : deck.lifts p f) :
    hp.liftEquiv f a (g • F) = g • hp.liftEquiv f a F := by
  apply Subtype.ext
  rfl

/-- Changing the chosen fiber point by a deck transformation changes the whole lift. -/
@[simp]
theorem liftEquiv_symm_smul (f : C(A, X)) (a : A) (g : deck p)
    (e : deck.fiber p (f a)) :
    (hp.liftEquiv f a).symm (g • e) = g • (hp.liftEquiv f a).symm e := by
  apply (hp.liftEquiv f a).injective
  rw [Equiv.apply_symm_apply, liftEquiv_smul, Equiv.apply_symm_apply]

variable [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]

/-- Restriction or any continuous precomposition commutes with the lift specified
by a reference value. The reference point is transported with the parameter map. -/
theorem liftEquiv_symm_precomp (f : C(A, X)) (g : C(B, A)) (b : B)
    (e : deck.fiber p (f (g b))) :
    (hp.liftEquiv (f.comp g) b).symm e =
      deck.precompLift f g ((hp.liftEquiv f (g b)).symm e) := by
  apply (hp.liftEquiv (f.comp g) b).injective
  apply Subtype.ext
  simp

end IsCoveringMap
