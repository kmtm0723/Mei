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
the fiber over that point. Both directions respect deck transformations.
Precomposition by a continuous parameter map, for example restriction to a
subspace, commutes with the lift determined by a reference value.

The fibers are Mathlib's preimages of singletons, as in its monodromy API.
Existence and uniqueness use `IsCoveringMap.existsUnique_continuousMap_lifts`.
The lifting supplier is Hatcher, *Algebraic Topology*, Propositions 1.33--1.34,
as implemented in Mathlib.
-/

public section

open Set

variable {E X A B : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace A] [TopologicalSpace B] {p : E → X}

namespace Mei

/-- Deck transformations act on the usual preimage fiber of the projection. -/
instance instMulActionDeckFiber (p : E → X) (x : X) : MulAction (deck p) (p ⁻¹' {x}) :=
  SubMulAction.mulAction ⟨p ⁻¹' {x}, fun g _ he => (deck.proj_smul g _).trans he⟩

omit [TopologicalSpace X] in
/-- The deck action on a fiber applies the same deck transformation to its point. -/
@[simp]
theorem fiber_smul_val (x : X) (g : deck p) (e : p ⁻¹' {x}) :
    (g • e : p ⁻¹' {x}).val = g • e.val := (rfl)

/-- Continuous lifts form a deck-invariant subset of the existing continuous maps. -/
def coveringLifts (p : E → X) (f : C(A, X)) : SubMulAction (deck p) C(A, E) where
  carrier := {F | p ∘ F = f}
  smul_mem' g {F} hF := by
    funext a
    exact (deck.proj_smul g (F a)).trans (congrFun hF a)

/-- The lift carrier is the set of maps with the specified projection. -/
@[simp]
theorem coe_coveringLifts (f : C(A, X)) :
    (coveringLifts p f : Set C(A, E)) = {F : C(A, E) | p ∘ F = f} := (rfl)

/-- Membership in the lift carrier is the equation with the covering projection. -/
@[simp]
theorem mem_coveringLifts_iff (f : C(A, X)) (F : C(A, E)) :
    F ∈ coveringLifts p f ↔ p ∘ F = f := Iff.rfl

namespace coveringLifts

/-- Pulling back a continuous lift by precomposition is equivariant for the deck action. -/
def precomp (f : C(A, X)) (g : C(B, A)) :
    coveringLifts p f →[deck p] coveringLifts p (f.comp g) where
  toFun F := ⟨F.val.comp g, by
    funext b
    exact congrFun F.property (g b)⟩
  map_smul' _ _ := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro b
    simp only [SubMulAction.val_smul, ContinuousMap.comp_apply, ContinuousMap.smul_apply, id_eq]

/-- Precomposition evaluates the original lifted map at the new parameter. -/
@[simp]
theorem precomp_apply (f : C(A, X)) (g : C(B, A)) (F : coveringLifts p f) (b : B) :
    (precomp f g F).val b = F.val (g b) := (rfl)

/-- Precomposition by the identity retains the entire lift. -/
@[simp]
theorem precomp_id (f : C(A, X)) (F : coveringLifts p f) :
    precomp f (ContinuousMap.id A) F = F := by
  apply Subtype.ext
  exact ContinuousMap.comp_id _

/-- Successive restrictions or parameter changes compose on the lifted map. -/
theorem precomp_comp {D : Type*} [TopologicalSpace D] (f : C(A, X))
    (g : C(B, A)) (h : C(D, B)) (F : coveringLifts p f) :
    precomp (f.comp g) h (precomp f g F) = precomp f (g.comp h) F := by
  apply Subtype.ext
  exact ContinuousMap.comp_assoc _ _ _

end coveringLifts
end Mei

namespace IsCoveringMap

open Mei

variable (hp : IsCoveringMap p) [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]

/-- The continuous lift with a prescribed point in the reference fiber. -/
noncomputable def liftOfFiber (f : C(A, X)) (a : A) (e : p ⁻¹' {f a}) :
    coveringLifts p f := by
  let hex := hp.existsUnique_continuousMap_lifts f a e.val e.property
  exact ⟨hex.choose, hex.choose_spec.1.2⟩

/-- The selected lift has the prescribed reference value. -/
@[simp]
theorem liftOfFiber_apply_at (f : C(A, X)) (a : A) (e : p ⁻¹' {f a}) :
    (hp.liftOfFiber f a e).val a = e.val :=
  (hp.existsUnique_continuousMap_lifts f a e.val e.property).choose_spec.1.1

/-- Any continuous lift with the prescribed reference value is the selected one. -/
theorem liftOfFiber_unique (f : C(A, X)) (a : A) (e : p ⁻¹' {f a})
    (F : coveringLifts p f) (ha : F.val a = e.val) : F = hp.liftOfFiber f a e := by
  apply Subtype.ext
  exact (hp.existsUnique_continuousMap_lifts f a e.val e.property).unique
    ⟨ha, F.property⟩ ⟨hp.liftOfFiber_apply_at f a e, (hp.liftOfFiber f a e).property⟩

/-- Evaluation at a reference point identifies continuous lifts with the usual fiber. -/
noncomputable def liftEquiv (f : C(A, X)) (a : A) :
    coveringLifts p f ≃ (p ⁻¹' {f a}) where
  toFun F := ⟨F.val a, congrFun F.property a⟩
  invFun := hp.liftOfFiber f a
  left_inv F := (hp.liftOfFiber_unique f a ⟨F.val a, congrFun F.property a⟩ F rfl).symm
  right_inv e := Subtype.ext (hp.liftOfFiber_apply_at f a e)

/-- Evaluation is the forward direction of the lift equivalence. -/
@[simp]
theorem liftEquiv_apply_val (f : C(A, X)) (a : A) (F : coveringLifts p f) :
    (hp.liftEquiv f a F).val = F.val a := (rfl)

/-- The lift selected by a fiber point has exactly that reference value. -/
@[simp]
theorem liftEquiv_symm_apply_at (f : C(A, X)) (a : A) (e : p ⁻¹' {f a}) :
    ((hp.liftEquiv f a).symm e).val a = e.val :=
  congrArg Subtype.val ((hp.liftEquiv f a).apply_symm_apply e)

/-- Deck transformations act simultaneously on a lift and its reference value. -/
@[simp]
theorem liftEquiv_smul (f : C(A, X)) (a : A) (g : deck p) (F : coveringLifts p f) :
    hp.liftEquiv f a (g • F) = g • hp.liftEquiv f a F := by
  apply Subtype.ext
  simp only [liftEquiv_apply_val, fiber_smul_val, SubMulAction.val_smul,
    ContinuousMap.smul_apply]

/-- Changing the chosen fiber point by a deck transformation changes the whole lift. -/
@[simp]
theorem liftEquiv_symm_smul (f : C(A, X)) (a : A) (g : deck p) (e : p ⁻¹' {f a}) :
    (hp.liftEquiv f a).symm (g • e) = g • (hp.liftEquiv f a).symm e := by
  apply (hp.liftEquiv f a).injective
  rw [Equiv.apply_symm_apply, liftEquiv_smul, Equiv.apply_symm_apply]

variable [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]

/-- Continuous precomposition commutes with the lift specified by a reference value. -/
theorem liftEquiv_symm_precomp (f : C(A, X)) (g : C(B, A)) (b : B)
    (e : p ⁻¹' {f (g b)}) :
    (hp.liftEquiv (f.comp g) b).symm e =
      coveringLifts.precomp f g ((hp.liftEquiv f (g b)).symm e) := by
  apply (hp.liftEquiv (f.comp g) b).injective
  apply Subtype.ext
  simp

end IsCoveringMap
