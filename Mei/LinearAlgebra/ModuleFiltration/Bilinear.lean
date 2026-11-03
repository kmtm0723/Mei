/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Map
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Bilinear maps on filtered module completions

A bilinear map that adds filtration orders induces bilinear maps on matching
quotients and on completions. Projections compute the completed pairing, and
the completed pairing still adds filtration orders. This permits products
between different shifted coefficient modules without identifying their carriers.
Completion preserves intertwining identities for bilinear maps, allowing the
three comparison maps to have independent monotone cutoff moduli.

Reassociation identities between bilinear operations hold at every finite cutoff
and on arbitrary completed inputs. The two intermediate modules may differ;
associative products and compatible module actions are instances. The original
modules need not be complete or separated. The finite pairings agree with
Mathlib's `LinearMap.liftQ₂` pairings.
-/

public section

namespace Mei.ModuleFiltration

section Bilinear

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  (F : ModuleFiltration R M) (G : ModuleFiltration R N) (H : ModuleFiltration R P)
  (f : M →ₗ[R] N →ₗ[R] P)
  (hf : ∀ (a b : ℕ) {x y}, x ∈ F.submodule a → y ∈ G.submodule b →
    f x y ∈ H.submodule (a + b))

/-- The bilinear map on quotients retaining the same filtration order. -/
def quotientBilinear (k : ℕ) : F.quotient k →ₗ[R] G.quotient k →ₗ[R] H.quotient k :=
  (f.compr₂ (H.submodule (k + 1)).mkQ).liftQ₂
    (F.submodule (k + 1)) (G.submodule (k + 1))
    (by
      intro x hx
      ext y
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (by simpa using hf (k + 1) 0 hx (by simp)))
    (by
      intro y hy
      ext x
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (by simpa using hf 0 (k + 1) (by simp) hy))

/-- Quotient pairings act on representatives by the original bilinear map. -/
@[simp]
theorem quotientBilinear_mk (k : ℕ) (x : M) (y : N) :
    quotientBilinear F G H f hf k (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (f x y) :=
  LinearMap.liftQ₂_mk _ _ x y

/-- Quotient pairings commute with decreasing the cutoff. -/
@[simp]
theorem transition_quotientBilinear {k l : ℕ} (h : k ≤ l)
    (x : F.quotient l) (y : G.quotient l) :
    H.transition h (quotientBilinear F G H f hf l x y) =
      quotientBilinear F G H f hf k (F.transition h x) (G.transition h y) := by
  obtain ⟨x, rfl⟩ := (F.submodule (l + 1)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (G.submodule (l + 1)).mkQ_surjective y
  simp

/-- Extend a bilinear map adding filtration orders to completed modules. -/
def completionBilinear : F.completion →ₗ[R] G.completion →ₗ[R] H.completion :=
  LinearMap.mk₂ R
    (fun x => H.lift
      (fun k => (quotientBilinear F G H f hf k (F.projection k x)).comp (G.projection k))
      (by
        intro k l h
        ext y
        simp))
    (by intros; ext k; simp)
    (by intros; ext k; simp)
    (by intros; exact map_add _ _ _)
    (by intros; exact map_smul _ _ _)

/-- A completed pairing is computed at any common finite cutoff. -/
@[simp]
theorem projection_completionBilinear (k : ℕ) (x : F.completion) (y : G.completion) :
    H.projection k (completionBilinear F G H f hf x y) =
      quotientBilinear F G H f hf k (F.projection k x) (G.projection k y) := by
  simp [completionBilinear]

/-- The completed pairing extends the original pairing. -/
@[simp]
theorem completionBilinear_of (x : M) (y : N) :
    completionBilinear F G H f hf (F.of x) (G.of y) = H.of (f x y) := by
  apply H.completion_ext
  intro k
  simp

/-- The completed bilinear map adds filtration orders. -/
@[grind .]
theorem completionBilinear_mem_completedFiltration {a b : ℕ}
    {x : F.completion} {y : G.completion}
    (hx : x ∈ F.completedFiltration.submodule a)
    (hy : y ∈ G.completedFiltration.submodule b) :
    completionBilinear F G H f hf x y ∈ H.completedFiltration.submodule (a + b) := by
  cases hab : a + b with
  | zero => simp
  | succ k =>
    rw [completedFiltration_succ, LinearMap.mem_ker, projection_completionBilinear]
    obtain ⟨m, hm, he⟩ := F.exists_projection_eq_of_mem_completedFiltration
      (k := k) hx
    obtain ⟨n, hn, he'⟩ := G.exists_projection_eq_of_mem_completedFiltration
      (k := k) hy
    rw [← he, ← he', quotientBilinear_mk, Submodule.Quotient.mk_eq_zero]
    simpa only [hab] using hf a b hm hn

variable {M' N' P' : Type*}
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  [AddCommGroup P'] [Module R P']
  (F' : ModuleFiltration R M') (G' : ModuleFiltration R N')
  (H' : ModuleFiltration R P') (f' : M' →ₗ[R] N' →ₗ[R] P')
  (hf' : ∀ (a b : ℕ) {x y}, x ∈ F'.submodule a → y ∈ G'.submodule b →
    f' x y ∈ H'.submodule (a + b))
  (u : M →ₗ[R] M') (v : N →ₗ[R] N') (w : P →ₗ[R] P')
  (ρ σ τ : ℕ → ℕ) (hρ : Monotone ρ) (hσ : Monotone σ) (hτ : Monotone τ)
  (hu : ∀ k, F.submodule (ρ k + 1) ≤ (F'.submodule (k + 1)).comap u)
  (hv : ∀ k, G.submodule (σ k + 1) ≤ (G'.submodule (k + 1)).comap v)
  (hw : ∀ k, H.submodule (τ k + 1) ≤ (H'.submodule (k + 1)).comap w)

/-- Linear maps intertwining bilinear pairings also intertwine their completions.
The three linear maps may use independent cutoff moduli. -/
theorem completionMap_completionBilinear (h : ∀ x y, w (f x y) = f' (u x) (v y))
    (x : F.completion) (y : G.completion) :
    H.completionMap H' w τ hτ hw (completionBilinear F G H f hf x y) =
      completionBilinear F' G' H' f' hf'
        (F.completionMap F' u ρ hρ hu x) (G.completionMap G' v σ hσ hv y) := by
  apply H'.completion_ext
  intro k
  -- A common finer cutoff computes all three projections using the same representatives.
  let n := max (ρ k) (max (σ k) (τ k))
  have hρn : ρ k ≤ n := le_max_left _ _
  have hσn : σ k ≤ n := (le_max_left _ _).trans (le_max_right _ _)
  have hτn : τ k ≤ n := (le_max_right _ _).trans (le_max_right _ _)
  rw [H.projection_completionMap_of_le H' w τ hτ hw k n hτn,
    projection_completionBilinear, projection_completionBilinear,
    F.projection_completionMap_of_le F' u ρ hρ hu k n hρn,
    G.projection_completionMap_of_le G' v σ hσ hv k n hσn]
  obtain ⟨a, ha⟩ := (F.submodule (n + 1)).mkQ_surjective (F.projection n x)
  obtain ⟨b, hb⟩ := (G.submodule (n + 1)).mkQ_surjective (G.projection n y)
  simp only [Submodule.mkQ_apply] at ha hb
  rw [← ha, ← hb, quotientBilinear_mk, Submodule.mapQ_apply,
    Submodule.mapQ_apply, Submodule.mapQ_apply, quotientBilinear_mk, h]

end Bilinear

section Associativity

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


end Associativity

end Mei.ModuleFiltration
