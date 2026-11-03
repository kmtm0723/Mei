/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Bilinear

/-!
# Reassociation of completed bilinear operations

Four filtered bilinear maps may compute the same trilinear operation through
different intermediate modules. Their canonical extensions to completions obey
the same identity. This applies to associative products and compatible module
actions, with no completeness or separatedness assumption on the original modules.

The finite-order identity is proved on quotient representatives. Projection to
each order then proves the identity for arbitrary completed inputs; these need
not come from elements of the original modules.
-/

public section

namespace Mei.ModuleFiltration

variable {R M N P A B Q : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup Q] [Module R Q]
  (F : ModuleFiltration R M) (G : ModuleFiltration R N) (H : ModuleFiltration R P)
  (I : ModuleFiltration R A) (J : ModuleFiltration R B) (K : ModuleFiltration R Q)
  (f : M →ₗ[R] N →ₗ[R] A) (g : A →ₗ[R] P →ₗ[R] Q)
  (h : N →ₗ[R] P →ₗ[R] B) (l : M →ₗ[R] B →ₗ[R] Q)
  (hf : ∀ a b {x y}, x ∈ F.submodule a → y ∈ G.submodule b →
    f x y ∈ I.submodule (a + b))
  (hg : ∀ a b {x y}, x ∈ I.submodule a → y ∈ H.submodule b →
    g x y ∈ K.submodule (a + b))
  (hh : ∀ a b {x y}, x ∈ G.submodule a → y ∈ H.submodule b →
    h x y ∈ J.submodule (a + b))
  (hl : ∀ a b {x y}, x ∈ F.submodule a → y ∈ J.submodule b →
    l x y ∈ K.submodule (a + b))
  (hassoc : ∀ x y z, g (f x y) z = l x (h y z))

include hassoc in
/-- Reassociation of the original operations descends to each finite quotient,
even when the two intermediate modules differ. -/
theorem quotientBilinear_assoc (k : ℕ)
    (x : F.quotient k) (y : G.quotient k) (z : H.quotient k) :
    quotientBilinear I H K g hg k (quotientBilinear F G I f hf k x y) z =
      quotientBilinear F J K l hl k x (quotientBilinear G H J h hh k y z) := by
  obtain ⟨x, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (G.submodule (k + 1)).mkQ_surjective y
  obtain ⟨z, rfl⟩ := (H.submodule (k + 1)).mkQ_surjective z
  simp only [Submodule.mkQ_apply, quotientBilinear_mk, hassoc]

include hassoc in
/-- Reassociation of filtered bilinear operations holds on all completed inputs.
This includes associativity of products and compatibility of a completed action
with a completed product. -/
theorem completionBilinear_assoc
    (x : F.completion) (y : G.completion) (z : H.completion) :
    completionBilinear I H K g hg (completionBilinear F G I f hf x y) z =
      completionBilinear F J K l hl x (completionBilinear G H J h hh y z) := by
  apply K.completion_ext
  intro k
  simp only [projection_completionBilinear]
  exact quotientBilinear_assoc F G H I J K f g h l hf hg hh hl hassoc k
    (F.projection k x) (G.projection k y) (H.projection k z)

end Mei.ModuleFiltration
