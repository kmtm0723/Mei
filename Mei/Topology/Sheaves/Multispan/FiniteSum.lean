/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.Multispan.Restriction

/-!
# Gluing finite chamber sums with compatible coefficient images

Finite sums of chamber section maps, with local common face lifts, determine
matching families on each endpoint open. Agreement of the sums on overlaps
makes those families compatible, including their face values. If their chamber
coefficient images are restrictions of a target matching family, the families
glue to a unique global source family with that coefficient image.

The finite branch sets are uniform over inputs. Separate branches need not
match across faces or covers: the hypotheses concern only their sums. Chamber
section maps may in turn be obtained by facet extension from top-stratum data.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r

namespace CategoryTheory.Limits.MultispanIndex

variable {X : TopCat.{u}} {R : Type r} [Semiring R] {J : MultispanShape}
  (I : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R)))

-- Reuse injectivity of restriction to chambers, without reconstructing face values.
private theorem maps_ext_right (E : SemimoduleCat.{v} R) (U : Opens X)
    (hinj : ∀ b, Function.Injective (((I.sectionsIndex U).fst b).hom.prod
      ((I.sectionsIndex U).snd b).hom))
    {s t : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan}
    (h : ∀ a j, (s a).val (.right j) = (t a).val (.right j)) : s = t := by
  apply LinearMap.ext
  intro a
  apply (I.sectionsIndex U).restrictSections_injective hinj
  apply Subtype.ext
  funext j
  simp only [restrictSections_apply]
  exact h a j

/-- Finite chamber sums with local common face lifts, equal sums on overlaps,
and compatible chamber coefficient images glue uniquely over an endpoint cover.
Joint injectivity retains all face values; no individual summand is required to
extend to a matching family or to satisfy a coefficient equation. -/
theorem existsUnique_finiteSum_sections_descent_gluing
    {I' : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R))}
    (η : I.multispan ⟶ I'.multispan) (E : SemimoduleCat.{v} R) {ι : Type*}
    (U : ι → Opens X) (B : ι → J.R → Type*) [∀ i j, Fintype (B i j)]
    (β : ∀ i j, B i j → E →ₗ[R] (I.right j).obj.obj (op (U i)))
    (hinj : ∀ (W : Opens X), W ≤ iSup U → ∀ b,
      Function.Injective (((I.sectionsIndex W).fst b).hom.prod
        ((I.sectionsIndex W).snd b).hom))
    (hinj' : ∀ i b, Function.Injective (((I'.sectionsIndex (U i)).fst b).hom.prod
      ((I'.sectionsIndex (U i)).snd b).hom))
    (hface : ∀ i b x, x ∈ U i → ∃ (N : Opens X) (hNU : N ≤ U i)
      (t : E ⟶ (I.left b).obj.obj (op N)), x ∈ N ∧
        t ≫ (I.fst b).hom.app (op N) = SemimoduleCat.ofHom (∑ a, β i (J.fst b) a) ≫
          (I.right (J.fst b)).obj.map (homOfLE hNU).op ∧
        t ≫ (I.snd b).hom.app (op N) = SemimoduleCat.ofHom (∑ a, β i (J.snd b) a) ≫
          (I.right (J.snd b)).obj.map (homOfLE hNU).op)
    (hoverlap : ∀ i k j,
      ((I.right j).obj.map (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op).hom.comp
          (∑ a, β i j a) =
        ((I.right j).obj.map (homOfLE (inf_le_right : U i ⊓ U k ≤ U k)).op).hom.comp
          (∑ a, β k j a))
    (m : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I'.sectionsIndex (iSup U)).multispan)
    (hcoeff : ∀ i a j, ((η.app (.right j)).hom.app (op (U i))) ((∑ b, β i j b) a) =
      (I'.right j).obj.map (homOfLE (le_iSup U i)).op ((m a).val (.right j))) :
    ∃! L : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex (iSup U)).multispan,
      (∀ i a j, (I.right j).obj.map (homOfLE (le_iSup U i)).op ((L a).val (.right j)) =
        (∑ b, β i j b) a) ∧
      (SemimoduleCat.sectionsMap (η.sectionsMultispan (iSup U))).comp L = m := by
  let α i j := SemimoduleCat.ofHom (∑ b, β i j b)
  have hex i := I.existsUnique_sections_lift_of_local E (U i) (α i)
    (fun W hW => hinj W (hW.trans (le_iSup U i))) (hface i)
  choose ℓ hℓ huniq using hex
  have hℓ' i a j : (ℓ i a).val (.right j) = (∑ b, β i j b) a := by
    simpa only [α, SemimoduleCat.hom_ofHom] using hℓ i a j
  have hc i k :
      (I.sectionsRestrict (inf_le_left : U i ⊓ U k ≤ U i)).comp (ℓ i) =
        (I.sectionsRestrict (inf_le_right : U i ⊓ U k ≤ U k)).comp (ℓ k) := by
    apply I.maps_ext_right E _ (hinj _ (inf_le_left.trans (le_iSup U i)))
    intro a j
    simp only [LinearMap.comp_apply, sectionsRestrict_apply_right, hℓ']
    exact LinearMap.congr_fun (hoverlap i k j) a
  have hm i : (SemimoduleCat.sectionsMap (η.sectionsMultispan (U i))).comp (ℓ i) =
      (I'.sectionsRestrict (le_iSup U i)).comp m := by
    apply I'.maps_ext_right E _ (hinj' i)
    intro a j
    simp only [LinearMap.comp_apply, SemimoduleCat.sectionsMap_apply,
      NatTrans.sectionsMultispan_app_right, sectionsRestrict_apply_right, hℓ']
    exact hcoeff i a j
  obtain ⟨L, ⟨hL, hmap⟩, huniqL⟩ :=
    I.existsUnique_sections_descent_gluing η E U m ℓ hc hm
  refine ⟨L, ⟨?_, hmap⟩, ?_⟩
  · intro i a j
    have he := congrArg (fun q => (q a).val (.right j)) (hL i)
    exact (I.sectionsRestrict_apply_right (le_iSup U i) (L a) j).symm.trans
      (he.trans (hℓ' i a j))
  · intro q hq
    apply huniqL q
    refine ⟨fun i => ?_, hq.2⟩
    apply I.maps_ext_right E _ (hinj _ (le_iSup U i))
    intro a j
    exact (I.sectionsRestrict_apply_right (le_iSup U i) (q a) j).trans
      ((hq.1 i a j).trans (hℓ' i a j).symm)

end CategoryTheory.Limits.MultispanIndex
