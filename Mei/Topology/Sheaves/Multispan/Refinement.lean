/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Multispan.Refinement
public import Mei.Topology.Sheaves.Multispan.Restriction

/-!
# Gluing matching families in locally chosen subdivisions

Different endpoint patches may present the same coefficient diagram using
different subdivisions. Chamber and face copies are retained, and identity
faces connect the copies of each original chamber. Agreement of the original
chamber values on overlaps suffices for a unique global matching family whose
pullback recovers every local refined family, including all face components.

There is no common global subdivision or chosen comparison between the local
subdivisions. Covers, incidence diagrams and copy inventories may be infinite.
The original face pairs need only be jointly injective on patch sections and
pairwise-overlap sections.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r w

namespace CategoryTheory.Limits.MultispanIndex

variable {X : TopCat.{u}} {R : Type r} [Semiring R] {J : MultispanShape}

/-- Matching families on separately subdivided endpoint patches glue uniquely
when their original chamber values agree on overlaps. Every chamber and face
has a copy, and the identity-face graph of each chamber is connected. The global
family recovers all local refined components, not just the chamber evaluations. -/
theorem existsUnique_sections_gluing_of_local_subdivisions
    (I : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R)))
    (E : SemimoduleCat.{v} R) {ι : Type*} (U : ι → Opens X)
    (D : ι → MultispanShape.Subdivision.{w} J)
    [∀ i j, Nonempty ((D i).chambers j)] [∀ i b, Nonempty ((D i).faces b)]
    (hc : ∀ i j a b, Relation.EqvGen ((D i).edgeRel j) a b)
    (hinj : ∀ i b, Function.Injective (((I.sectionsIndex (U i)).fst b).hom.prod
      ((I.sectionsIndex (U i)).snd b).hom))
    (hinjOverlap : ∀ i k b,
      Function.Injective (((I.sectionsIndex (U i ⊓ U k)).fst b).hom.prod
        ((I.sectionsIndex (U i ⊓ U k)).snd b).hom))
    (ℓ : ∀ i, E →ₗ[R]
      SemimoduleCat.sectionsSubmodule ((D i).index (I.sectionsIndex (U i))).multispan)
    (hcompat : ∀ i k a j (c : (D i).chambers j) (d : (D k).chambers j),
      (I.right j).obj.map (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op
          ((ℓ i a).val (.right ⟨j, c⟩)) =
        (I.right j).obj.map (homOfLE (inf_le_right : U i ⊓ U k ≤ U k)).op
          ((ℓ k a).val (.right ⟨j, d⟩))) :
    ∃! L : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex (iSup U)).multispan,
      ∀ i, ((D i).sectionsPullback (I.sectionsIndex (U i))).comp
        ((I.sectionsRestrict (le_iSup U i)).comp L) = ℓ i := by
  let e i := (D i).sectionsEquiv (I.sectionsIndex (U i)) (hc i) (hinj i)
  let a i := (e i).symm.toLinearMap.comp (ℓ i)
  have ha i k : (I.sectionsRestrict (inf_le_left : U i ⊓ U k ≤ U i)).comp (a i) =
      (I.sectionsRestrict (inf_le_right : U i ⊓ U k ≤ U k)).comp (a k) := by
    apply (I.sectionsIndex (U i ⊓ U k)).linearMap_ext_of_injective
      (hinjOverlap i k)
    intro x j
    let c : (D i).chambers j := Classical.choice inferInstance
    let d : (D k).chambers j := Classical.choice inferInstance
    simp only [LinearMap.comp_apply, sectionsRestrict_apply_right, a,
      LinearEquiv.coe_toLinearMap, e]
    rw [(D i).sectionsEquiv_symm_apply_right _ _ _ _ j c,
      (D k).sectionsEquiv_symm_apply_right _ _ _ _ j d]
    exact hcompat i k x j c d
  have hp i x : (D i).sectionsPullback (I.sectionsIndex (U i)) (a i x) = ℓ i x := by
    simpa only [a, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, e,
      MultispanShape.Subdivision.sectionsEquiv_apply] using (e i).apply_symm_apply (ℓ i x)
  obtain ⟨L, hL, huniq⟩ := I.existsUnique_sections_gluing E U a ha
  refine ⟨L, ?_, ?_⟩
  · intro i
    rw [hL i]
    apply LinearMap.ext
    intro x
    exact hp i x
  · intro q hq
    apply huniq q
    intro i
    apply LinearMap.ext
    intro x
    apply (e i).injective
    simp only [e, MultispanShape.Subdivision.sectionsEquiv_apply]
    exact (LinearMap.congr_fun (hq i) x).trans (hp i x).symm

end CategoryTheory.Limits.MultispanIndex
