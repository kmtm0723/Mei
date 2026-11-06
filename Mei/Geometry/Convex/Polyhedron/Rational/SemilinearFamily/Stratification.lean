/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.Image
public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Basic
public import Mei.Geometry.Convex.Polyhedron.Rational.Stratification

/-!
# Compatible stratifications of finite branches

Let `F` be a finite semilinear family from `V` to `W`, both with integral lattices, all of whose
charts are finite branches. A *branch stratification* of `F`
(`FiniteSemilinearFamily.BranchStratification`) consists of

* a partition of `W` into nonempty locally closed rational-normal polyhedra, the target strata;
* for each chart, a partition of its domain into locally closed rational-normal polyhedra, the
  source strata, on each of which the evaluation is an affine map with rational linear part
  mapping the source stratum bijectively onto one target stratum.

Thus over each target stratum every source stratum is either absent or an affine copy of it, and
the fiber of `F` over a point of a target stratum `T` is in bijection with the source strata over
`T`; in particular the fiber cardinality is constant on each target stratum
(`FiniteSemilinearFamily.BranchStratification.nat_card_fiber`).

Every family of finite branches has a branch stratification
(`FiniteSemilinearFamily.IsFiniteBranch.exists_branchStratification`), so `W` has a finite
partition into nonempty locally closed polyhedra on each of which the fiber cardinality is
constant (`FiniteSemilinearFamily.IsFiniteBranch.exists_partition_nat_card_fiber_eq`). The pieces
of a finite branch may overlap, and a point lying in several pieces of one chart is a single point
of the fiber; every finite branch also has a presentation by pairwise disjoint pieces
(`IsFiniteBranchOn.exists_pairwise_disjoint`).

These are polyhedral analogues of the cell decomposition and uniform finiteness theorems for
definable families in o-minimal geometry (van den Dries, *Tame topology and o-minimal
structures*, Chapter 3). For piecewise-affine families that are not finite branches, a
compatible stratification would need images of polyhedra under non-injective affine maps; it is
not treated here.
-/

public section

open Set

namespace Mei

variable {N V N' W : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup N'] [NormedAddCommGroup W] [NormedSpace ℝ W] {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}

namespace IsFiniteBranchOn

/-- A finite branch has a presentation by finitely many nonempty, pairwise disjoint locally
closed polyhedra covering its domain, on each of which it agrees with an affine map with rational
linear part that is injective on the polyhedron. -/
theorem exists_pairwise_disjoint {D : Set V} {f : D → W} (hf : IsFiniteBranchOn h h' D f) :
    ∃ (κ : Type) (_ : Finite κ) (S : κ → Set V) (g : κ → (V →ᵃ[ℝ] W)),
      (⋃ k, S k) = D ∧ (Pairwise fun a b => Disjoint (S a) (S b)) ∧ ∀ k, (S k).Nonempty ∧
        IsLocallyClosedPolyhedron h (S k) ∧ Toric.IsRationalLinearMap h h' (g k).linear ∧
          InjOn (g k) (S k) ∧ ∀ x : D, x.1 ∈ S k → f x = g k x := by
  classical
  obtain ⟨κ, _, S, g, hD, hS⟩ := isFiniteBranchOn_iff.mp hf
  obtain ⟨A, _, C, hC, hdisj, hcover, hmem⟩ := IsRationalSemilinear.exists_common_partition
    (S := S) fun k => (hS k).1.isRationalSemilinear
  -- A cell of the common partition meeting a piece lies in it.
  have hsub {a k x} (hx : x ∈ C a) (hxk : x ∈ S k) : C a ⊆ S k := fun y hy =>
    (hmem a x hx y hy k).mp hxk
  let A' := {a : A // ∃ k, C a ⊆ S k}
  choose k hk using fun a : A' => a.2
  refine ⟨A', inferInstance, fun a => C a, fun a => g (k a), ?_, fun a b hab =>
    hdisj (Subtype.coe_injective.ne hab), fun a => ⟨(hC a).1, (hC a).2, (hS (k a)).2.1,
      (hS (k a)).2.2.1.mono (hk a), fun x hx => (hS (k a)).2.2.2 x (hk a hx)⟩⟩
  apply Subset.antisymm
  · exact iUnion_subset fun a => (hk a).trans (hD ▸ subset_iUnion S (k a))
  · intro x hx
    obtain ⟨k₀, hx₀⟩ := mem_iUnion.mp (hD ▸ hx)
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hcover ▸ mem_univ x)
    exact mem_iUnion.mpr ⟨⟨a, k₀, hsub ha hx₀⟩, ha⟩

end IsFiniteBranchOn

namespace FiniteSemilinearFamily

universe u

variable {ι : Type u} [Finite ι] (F : FiniteSemilinearFamily h h' ι)

/-- A branch stratification of a finite semilinear family, with target strata indexed by `κ` and
source strata indexed by `μ`. The target strata partition `W` into nonempty locally closed
polyhedra. The source strata over each chart partition its domain into locally closed polyhedra;
on each of them the evaluation is an affine map with rational linear part that maps it
bijectively onto one target stratum. -/
@[ext]
structure BranchStratification (κ μ : Type*) where
  /-- The target strata. -/
  target : κ → Set W
  /-- The chart containing each source stratum. -/
  chart : μ → ι
  /-- The source strata. -/
  source : μ → Set V
  /-- The target stratum onto which each source stratum is mapped. -/
  stratum : μ → κ
  /-- The affine map giving the evaluation on each source stratum. -/
  map : μ → V →ᵃ[ℝ] W
  /-- The target strata are nonempty. -/
  nonempty_target : ∀ b, (target b).Nonempty
  /-- The target strata are locally closed polyhedra. -/
  isLocallyClosedPolyhedron_target : ∀ b, IsLocallyClosedPolyhedron h' (target b)
  /-- Distinct target strata are disjoint. -/
  pairwise_disjoint_target : Pairwise fun b b' => Disjoint (target b) (target b')
  /-- The target strata cover `W`. -/
  iUnion_target : (⋃ b, target b) = univ
  /-- The source strata are locally closed polyhedra. -/
  isLocallyClosedPolyhedron_source : ∀ a, IsLocallyClosedPolyhedron h (source a)
  /-- The maps have rational linear parts. -/
  isRationalLinearMap_map : ∀ a, Toric.IsRationalLinearMap h h' (map a).linear
  /-- Each source stratum is mapped bijectively onto its target stratum. -/
  bijOn : ∀ a, BijOn (map a) (source a) (target (stratum a))
  /-- The source strata of a chart cover its domain. -/
  domain_eq : ∀ c, F.domain c = ⋃ (a) (_ : chart a = c), source a
  /-- Distinct source strata of the same chart are disjoint. -/
  disjoint_source : ∀ a a', chart a = chart a' → a ≠ a' → Disjoint (source a) (source a')
  /-- On a source stratum, the evaluation of its chart is its map. -/
  eval_eq : ∀ a (x : F.domain (chart a)), x.1 ∈ source a → F.eval (chart a) x = map a x

namespace BranchStratification

variable {F} {κ μ : Type*} (S : F.BranchStratification κ μ)

/-- Each source stratum is mapped onto its target stratum. -/
theorem image_source (a : μ) : S.map a '' S.source a = S.target (S.stratum a) :=
  (S.bijOn a).image_eq

/-- The source strata are nonempty. -/
theorem nonempty_source (a : μ) : (S.source a).Nonempty :=
  (S.image_source a ▸ S.nonempty_target (S.stratum a)).of_image

/-- Over a point `w` of the target stratum `b`, the fiber of `F` is in bijection with the source
strata mapped onto `b`. In particular the fiber cardinality is constant on each target
stratum. -/
theorem nat_card_fiber {b : κ} {w : W} (hw : w ∈ S.target b) :
    Nat.card (F.fiber w) = Nat.card {a // S.stratum a = b} := by
  -- Each source stratum over `b` has exactly one point over `w`.
  choose x hx hxw using fun a : {a // S.stratum a = b} => (S.bijOn a).surjOn (a.2 ▸ hw)
  have hdom (a : {a // S.stratum a = b}) : x a ∈ F.domain (S.chart a) :=
    S.domain_eq _ ▸ mem_iUnion₂.mpr ⟨a, rfl, hx a⟩
  let e (a : {a // S.stratum a = b}) : F.fiber w :=
    ⟨S.chart a, ⟨x a, hdom a⟩, (S.eval_eq a ⟨x a, hdom a⟩ (hx a)).trans (hxw a)⟩
  refine (Nat.card_congr (Equiv.ofBijective e ⟨fun a a' he => ?_, ?_⟩)).symm
  · by_contra hne
    have hxx : x a = x a' := congrArg (fun p : F.fiber w => (p.2.1 : V)) he
    exact (S.disjoint_source a a' (congrArg Sigma.fst he) (Subtype.coe_injective.ne hne)).ne_of_mem
      (hx a) (hxx ▸ hx a') rfl
  · rintro ⟨c, y, hy⟩
    have hy' : (y : V) ∈ ⋃ (a) (_ : S.chart a = c), S.source a := by
      rw [← S.domain_eq c]
      exact y.2
    obtain ⟨a, hac, hya⟩ := mem_iUnion₂.mp hy'
    subst hac
    have hmap : S.map a y = w := (S.eval_eq a y hya).symm.trans hy
    have hab : S.stratum a = b := by
      by_contra hne
      exact (S.pairwise_disjoint_target hne).ne_of_mem ((S.bijOn a).mapsTo hya) hw hmap
    have hxy : x ⟨a, hab⟩ = y :=
      (S.bijOn a).injOn (hx ⟨a, hab⟩) hya ((hxw ⟨a, hab⟩).trans hmap.symm)
    exact ⟨⟨a, hab⟩, Sigma.ext rfl (heq_of_eq (Subtype.ext (Subtype.ext hxy)))⟩

end BranchStratification

namespace IsFiniteBranch

variable {F}

/-- Every family of finite branches has a branch stratification. -/
theorem exists_branchStratification (hF : F.IsFiniteBranch) :
    ∃ (κ : Type) (μ : Type u) (_ : Finite κ) (_ : Finite μ),
      Nonempty (F.BranchStratification κ μ) := by
  classical
  let := h.finiteDimensional
  choose κ hκ S g hD hdisj hS using fun c => (F.isFiniteBranch_iff.mp hF c).exists_pairwise_disjoint
  have (c : ι) : Finite (κ c) := hκ c
  -- A common partition of `W` deciding membership in the images of all pieces.
  let Y (p : Σ c, κ c) : Set W := g p.1 p.2 '' S p.1 p.2
  obtain ⟨B, _, T, hT, hTdisj, hTcover, hTmem⟩ := IsRationalSemilinear.exists_common_partition
    (S := Y) fun p => ((hS p.1 p.2).2.1.image_of_injOn _ (hS p.1 p.2).2.2.1
      (hS p.1 p.2).2.2.2.1).isRationalSemilinear
  have hsub {b p w} (hw : w ∈ T b) (hwp : w ∈ Y p) : T b ⊆ Y p := fun w' hw' =>
    (hTmem b w hw w' hw' p).mp hwp
  -- A source stratum is the part of a piece mapped into a target stratum inside its image.
  let μ := {q : (Σ c, κ c) × B // T q.2 ⊆ Y q.1}
  let gc (q : μ) : V →ᴬ[ℝ] W := ⟨g q.1.1.1 q.1.1.2, AffineMap.continuous_of_finiteDimensional _⟩
  refine ⟨B, μ, inferInstance, inferInstance, ⟨{
    target := T
    chart := fun q => q.1.1.1
    source := fun q => S q.1.1.1 q.1.1.2 ∩ gc q ⁻¹' T q.1.2
    stratum := fun q => q.1.2
    map := fun q => g q.1.1.1 q.1.1.2
    nonempty_target := fun b => (hT b).1
    isLocallyClosedPolyhedron_target := fun b => (hT b).2
    pairwise_disjoint_target := hTdisj
    iUnion_target := hTcover
    isLocallyClosedPolyhedron_source := fun q =>
      (hS _ _).2.1.inter ((hT _).2.preimage (gc q) (hS _ _).2.2.1)
    isRationalLinearMap_map := fun q => (hS _ _).2.2.1
    bijOn := fun q => ⟨fun x hx => hx.2, (hS _ _).2.2.2.1.mono inter_subset_left, fun w hw => ?_⟩
    domain_eq := fun c => ?_
    disjoint_source := ?_
    eval_eq := fun q x hx => (hS _ _).2.2.2.2 x hx.1 }⟩⟩
  · obtain ⟨x, hx, rfl⟩ := q.2 hw
    exact ⟨x, ⟨hx, hw⟩, rfl⟩
  · ext x
    rw [← hD c, mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨b, hb⟩ := mem_iUnion.mp (hTcover ▸ mem_univ (g c k x))
      exact mem_iUnion₂.mpr ⟨⟨(⟨c, k⟩, b), hsub hb (mem_image_of_mem _ hk)⟩, rfl, hk, hb⟩
    · intro hx
      obtain ⟨q, rfl, hq⟩ := mem_iUnion₂.mp hx
      exact ⟨_, hq.1⟩
  · rintro ⟨⟨⟨c, k⟩, b⟩, hq⟩ ⟨⟨⟨c', k'⟩, b'⟩, hq'⟩ (hc : c = c') hne
    subst hc
    by_cases hk : k = k'
    · subst hk
      have hb : b ≠ b' := fun hb => hne (by subst hb; rfl)
      exact ((hTdisj hb).preimage _).mono inter_subset_right inter_subset_right
    · exact (hdisj c hk).mono inter_subset_left inter_subset_left

/-- For a family of finite branches, `W` has a finite partition into nonempty locally closed
polyhedra on each of which the fiber cardinality of the family is constant. -/
theorem exists_partition_nat_card_fiber_eq (hF : F.IsFiniteBranch) :
    ∃ (κ : Type) (_ : Finite κ) (T : κ → Set W),
      (∀ b, (T b).Nonempty ∧ IsLocallyClosedPolyhedron h' (T b)) ∧
        (Pairwise fun b b' => Disjoint (T b) (T b')) ∧ (⋃ b, T b) = univ ∧
          ∀ b, ∀ w ∈ T b, ∀ w' ∈ T b, Nat.card (F.fiber w) = Nat.card (F.fiber w') := by
  obtain ⟨κ, μ, _, _, ⟨S⟩⟩ := hF.exists_branchStratification
  exact ⟨κ, inferInstance, S.target,
    fun b => ⟨S.nonempty_target b, S.isLocallyClosedPolyhedron_target b⟩,
    S.pairwise_disjoint_target, S.iUnion_target,
    fun b w hw w' hw' => (S.nat_card_fiber hw).trans (S.nat_card_fiber hw').symm⟩

end IsFiniteBranch

end FiniteSemilinearFamily

end Mei
