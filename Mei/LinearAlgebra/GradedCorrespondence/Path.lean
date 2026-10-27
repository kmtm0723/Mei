/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedCorrespondence.Hom
public import Mathlib.Algebra.Category.ModuleCat.Semi
public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Homogeneous transfer along admissible paths

Choose an admissible homogeneous piece at each vertex of a quiver and a graded
correspondence on each arrow. Their transfers extend to a functor from the free
path category to semimodules. Thus a finite admissible itinerary has a linear
propagation map, with concatenation given by composition in traversal order.
Vertices may represent occurrences of a chamber with different selected degrees;
neither the quiver nor its sets of arrows need to be finite.

Degree-preserving morphisms of the edge correspondences, with a common chamber
map at incident edges, induce a natural transformation of the transfer functors.
This proves compatibility along arbitrary admissible sequences, including coefficient
truncations. It does not assert invertibility of a selected homogeneous component.

This advances [ScatteringDiagrams §0.8, Morphisms and transfers]
(https://github.com/yuma-mizuno/TauCetiRoadmap/blob/mei/TauCetiRoadmap/ScatteringDiagrams/README.md#08-homogeneous-coefficient-correspondences).
The construction uses Mathlib's `Paths.lift`; its one-step naturality is
`GradedCorrespondence.Hom.transfer_map_of_injective` with identity degree maps.
-/

@[expose] public section

open CategoryTheory

namespace Mei.GradedCorrespondence

universe v

variable {R Q : Type*} [Semiring R] [Quiver Q]
  {M : Q → Type v} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (𝒜 : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (𝒜 q)]
  {I : ∀ q, Set (ι q)}
  {B : ∀ {u v : Q}, (u ⟶ v) → Type*}
  [∀ (u v : Q) (e : u ⟶ v), AddCommMonoid (B e)]
  [∀ (u v : Q) (e : u ⟶ v), Module R (B e)]
  (C : ∀ {u v : Q} (e : u ⟶ v),
    GradedCorrespondence (B := B e) (𝒜 u) (𝒜 v) (I u) (I v))
  (p : ∀ q, I q)

/-- Select one homogeneous transfer on every arrow of an admissible itinerary quiver. -/
noncomputable def transferPrefunctor : Q ⥤q SemimoduleCat R where
  obj q := SemimoduleCat.of R (𝒜 q (p q))
  map {u v} e := SemimoduleCat.ofHom ((C e).transfer (p u) (p v))

/-- Homogeneous propagation along finite paths, freely extending the single-step transfers. -/
noncomputable def transferFunctor : Paths Q ⥤ SemimoduleCat R :=
  Paths.lift (transferPrefunctor 𝒜 C p)

/-- A path with no crossings preserves its decoration. -/
@[simp]
theorem transferFunctor_nil (u : Q) :
    (transferFunctor 𝒜 C p).map (Quiver.Path.nil : Quiver.Path u u) = 𝟙 _ := rfl

/-- A one-crossing path acts by the selected homogeneous component of that crossing. -/
@[simp]
theorem transferFunctor_toPath {u v : Q} (e : u ⟶ v) :
    (transferFunctor 𝒜 C p).map e.toPath =
      SemimoduleCat.ofHom ((C e).transfer (p u) (p v)) := by
  exact Paths.lift_toPath _ e

/-- Appending a crossing applies its transfer after the preceding propagation. -/
@[simp]
theorem transferFunctor_cons {u v w : Q} (γ : Quiver.Path u v) (e : v ⟶ w) :
    (transferFunctor 𝒜 C p).map (γ.cons e) =
      (transferFunctor 𝒜 C p).map γ ≫
        SemimoduleCat.ofHom ((C e).transfer (p v) (p w)) := rfl

/-- Concatenation propagates first along the first itinerary, then along the second. -/
@[simp]
theorem transferFunctor_comp {u v w : Q} (γ : Quiver.Path u v) (δ : Quiver.Path v w) :
    (transferFunctor 𝒜 C p).map (γ.comp δ) =
      (transferFunctor 𝒜 C p).map γ ≫ (transferFunctor 𝒜 C p).map δ :=
  (transferFunctor 𝒜 C p).map_comp γ δ

section Naturality

variable {M' : Q → Type v} [∀ q, AddCommMonoid (M' q)] [∀ q, Module R (M' q)]
  (𝒜' : ∀ q, ι q → Submodule R (M' q)) [∀ q, DirectSum.Decomposition (𝒜' q)]
  {B' : ∀ {u v : Q}, (u ⟶ v) → Type*}
  [∀ (u v : Q) (e : u ⟶ v), AddCommMonoid (B' e)]
  [∀ (u v : Q) (e : u ⟶ v), Module R (B' e)]
  (D : ∀ {u v : Q} (e : u ⟶ v),
    GradedCorrespondence (B := B' e) (𝒜' u) (𝒜' v) (I u) (I v))
  (r : ∀ q, M q →ₗ[R] M' q)
  (hr : ∀ q i a, a ∈ 𝒜 q i → r q a ∈ 𝒜' q i)

variable
  (f : ∀ {u v : Q} (e : u ⟶ v), Hom (C e) (D e) id id)
  (hl : ∀ {u v : Q} (e : u ⟶ v), (f e).left = r u)
  (hv : ∀ {u v : Q} (e : u ⟶ v), (f e).right = r v)

include f hl hv

/-- Chamber maps intertwine a selected homogeneous transfer at every crossing. -/
private theorem restrict_transfer {u v : Q} (e : u ⟶ v) :
    ((r v).restrict (hr v (p v))).comp ((C e).transfer (p u) (p v)) =
      ((D e).transfer (p u) (p v)).comp ((r u).restrict (hr u (p u))) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change r v ((C e).transfer (p u) (p v) a) =
    ((D e).transfer (p u) (p v) ⟨r u a, hr u (p u) a a.property⟩ : M' v)
  have he := (f e).transfer_map_of_injective Function.injective_id (p u) a (p v)
  simpa only [transfer_apply, id_eq, hl e, hv e] using he.symm

/-- Degree-preserving correspondence morphisms intertwine propagation along every
finite admissible sequence. In particular, coefficient truncations commute with all
selected component maps along a broken-line itinerary. -/
noncomputable def transferNatTrans :
    transferFunctor 𝒜 C p ⟶ transferFunctor 𝒜' D p where
  app q := by
    change Q at q
    exact SemimoduleCat.ofHom ((r q).restrict (hr q (p q)))
  naturality {u v} γ := by
    change Q at u v
    induction γ using @Quiver.Path.rec Q _ u with
    | nil => rfl
    | @cons v w γ e ih =>
      apply SemimoduleCat.hom_ext
      ext a
      have hi := congrArg (fun k => k.hom a) ih
      change (r v).restrict (hr v (p v)) (((transferFunctor 𝒜 C p).map γ).hom a) =
        ((transferFunctor 𝒜' D p).map γ).hom ((r u).restrict (hr u (p u)) a) at hi
      change (r w).restrict (hr w (p w))
          ((C e).transfer (p v) (p w) (((transferFunctor 𝒜 C p).map γ).hom a)) =
        (D e).transfer (p v) (p w)
          (((transferFunctor 𝒜' D p).map γ).hom ((r u).restrict (hr u (p u)) a))
      exact (LinearMap.congr_fun
        (restrict_transfer 𝒜 C p 𝒜' D r hr f hl hv e) _).trans
          (congrArg ((D e).transfer (p v) (p w)) hi)

end Naturality

end Mei.GradedCorrespondence
