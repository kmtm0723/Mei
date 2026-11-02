/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.Multispan.Morphism
public import Mei.Topology.Sheaves.Diagram.Gluing
public import Mei.Topology.Sheaves.Diagram.Morphism

/-!
# Gluing coefficient descents on endpoint covers

Evaluating an incidence index and evaluating its multispan give canonically
linearly equivalent matching families. Transporting the existing diagram
restriction and gluing operations through this equivalence retains all face
and chamber values. Compatible local coefficient descents then glue to a unique
global descent on an arbitrary endpoint cover.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r

namespace CategoryTheory.Limits.MultispanIndex

variable {X : TopCat.{u}} {R : Type r} [Semiring R] {J : MultispanShape}
  (I : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R)))

-- Fix both evaluated diagram types at the module boundary before mapping sections.
private def evaluatedMultispanIso (U : Opens X) :
    (I.sectionsIndex U).multispan ≅ I.multispan.sectionsOver U :=
  I.multispanMapIso (((TopCat.Sheaf.forget (SemimoduleCat.{v} R) X).flip).obj (op U))

/-- The canonical linear equivalence between matching families of the evaluated
incidence index and those of the evaluated sheaf diagram. -/
def sectionsEquiv (U : Opens X) :
    SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan ≃ₗ[R]
      SemimoduleCat.sectionsSubmodule (I.multispan.sectionsOver U) :=
  LinearEquiv.ofLinearMap
    (SemimoduleCat.sectionsMap (I.evaluatedMultispanIso U).hom)
    (SemimoduleCat.sectionsMap (I.evaluatedMultispanIso U).inv)
    (by rw [← SemimoduleCat.sectionsMap_comp, Iso.inv_hom_id, SemimoduleCat.sectionsMap_id])
    (by rw [← SemimoduleCat.sectionsMap_comp, Iso.hom_inv_id, SemimoduleCat.sectionsMap_id])

private theorem sectionsEquiv_toLinearMap (U : Opens X) :
    (I.sectionsEquiv U).toLinearMap =
      SemimoduleCat.sectionsMap (I.evaluatedMultispanIso U).hom := by rfl

-- For an abstract walking object the carriers are dependent matches, so state
-- the common computation heterogeneously and specialize it at faces/chambers.
private theorem sectionsEquiv_apply (U : Opens X)
    (s : SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan)
    (j : WalkingMultispan J) : HEq ((I.sectionsEquiv U s).val j) (s.val j) := by
  have he := SemimoduleCat.sectionsMap_apply (I.evaluatedMultispanIso U).hom s j
  have hv : HEq ((I.sectionsEquiv U s).val j)
      (((I.evaluatedMultispanIso U).hom.app j).hom (s.val j)) := by
    simpa only [← sectionsEquiv_toLinearMap, LinearEquiv.coe_toLinearMap] using heq_of_eq he
  apply hv.trans
  cases j <;> dsimp only [evaluatedMultispanIso] <;>
    erw [I.multispanMapIso_hom_app]
  -- The public component equation leaves the identity on the original section carrier.
  all_goals rfl

/-- The canonical comparison retains each face value. -/
@[simp]
theorem sectionsEquiv_apply_left (U : Opens X)
    (s : SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan) (b : J.L) :
    (I.sectionsEquiv U s).val (.left b) = s.val (.left b) :=
  eq_of_heq (I.sectionsEquiv_apply U s (.left b))

/-- The canonical comparison retains each chamber value. -/
@[simp]
theorem sectionsEquiv_apply_right (U : Opens X)
    (s : SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan) (j : J.R) :
    (I.sectionsEquiv U s).val (.right j) = s.val (.right j) :=
  eq_of_heq (I.sectionsEquiv_apply U s (.right j))

/-- The inverse comparison retains each face value. -/
@[simp]
theorem sectionsEquiv_symm_apply_left (U : Opens X)
    (s : SemimoduleCat.sectionsSubmodule (I.multispan.sectionsOver U)) (b : J.L) :
    ((I.sectionsEquiv U).symm s).val (.left b) = s.val (.left b) := by
  have he := I.sectionsEquiv_apply_left U ((I.sectionsEquiv U).symm s) b
  rw [LinearEquiv.apply_symm_apply] at he
  exact he.symm

/-- The inverse comparison retains each chamber value. -/
@[simp]
theorem sectionsEquiv_symm_apply_right (U : Opens X)
    (s : SemimoduleCat.sectionsSubmodule (I.multispan.sectionsOver U)) (j : J.R) :
    ((I.sectionsEquiv U).symm s).val (.right j) = s.val (.right j) := by
  have he := I.sectionsEquiv_apply_right U ((I.sectionsEquiv U).symm s) j
  rw [LinearEquiv.apply_symm_apply] at he
  exact he.symm

/-- Endpoint restriction on evaluated-index families, transported from the
existing restriction on matching families of the sheaf diagram. -/
def sectionsRestrict {U V : Opens X} (hVU : V ≤ U) :
    SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan →ₗ[R]
      SemimoduleCat.sectionsSubmodule (I.sectionsIndex V).multispan :=
  (I.sectionsEquiv V).symm.toLinearMap.comp
    ((I.multispan.sectionsRestrict hVU).comp (I.sectionsEquiv U).toLinearMap)

/-- The canonical comparison intertwines the two matching-family restrictions. -/
@[simp]
theorem sectionsEquiv_restrict {U V : Opens X} (hVU : V ≤ U)
    (s : SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan) :
    I.sectionsEquiv V (I.sectionsRestrict hVU s) =
      I.multispan.sectionsRestrict hVU (I.sectionsEquiv U s) := by
  simp only [sectionsRestrict, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]

/-- Restriction on evaluated-index families restricts the original face section. -/
@[simp]
theorem sectionsRestrict_apply_left {U V : Opens X} (hVU : V ≤ U)
    (s : SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan) (b : J.L) :
    (I.sectionsRestrict hVU s).val (.left b) =
      (I.left b).obj.map (homOfLE hVU).op (s.val (.left b)) := by
  have he := congrArg (fun z => z.val (.left b)) (I.sectionsEquiv_restrict hVU s)
  simp only [sectionsEquiv_apply_left, Functor.sectionsRestrict_apply] at he
  exact he

/-- Restriction on evaluated-index families restricts the original chamber section. -/
@[simp]
theorem sectionsRestrict_apply_right {U V : Opens X} (hVU : V ≤ U)
    (s : SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan) (j : J.R) :
    (I.sectionsRestrict hVU s).val (.right j) =
      (I.right j).obj.map (homOfLE hVU).op (s.val (.right j)) := by
  have he := congrArg (fun z => z.val (.right j)) (I.sectionsEquiv_restrict hVU s)
  simp only [sectionsEquiv_apply_right, Functor.sectionsRestrict_apply] at he
  exact he

/-- Restriction along the identity inclusion fixes every evaluated-index family. -/
@[simp]
theorem sectionsRestrict_refl (U : Opens X) :
    I.sectionsRestrict (le_refl U) = LinearMap.id := by
  apply LinearMap.ext
  intro s
  apply (I.sectionsEquiv U).injective
  simp only [sectionsEquiv_restrict, Functor.sectionsRestrict_refl, LinearMap.id_apply]

/-- Successive restrictions of evaluated-index families compose along inclusions. -/
@[simp]
theorem sectionsRestrict_comp {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V) :
    (I.sectionsRestrict hWV).comp (I.sectionsRestrict hVU) =
      I.sectionsRestrict (hWV.trans hVU) := by
  apply LinearMap.ext
  intro s
  apply (I.sectionsEquiv W).injective
  simp only [LinearMap.comp_apply, sectionsEquiv_restrict]
  exact LinearMap.congr_fun (I.multispan.sectionsRestrict_comp hVU hWV)
    (I.sectionsEquiv U s)

/-- Coefficient transport commutes with the canonical comparison of evaluated families. -/
@[simp]
theorem sectionsEquiv_naturality {I' : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R))}
    (η : I.multispan ⟶ I'.multispan) (U : Opens X)
    (s : SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan) :
    I'.sectionsEquiv U (SemimoduleCat.sectionsMap (η.sectionsMultispan U) s) =
      η.sectionsMap U (I.sectionsEquiv U s) := by
  have hn : η.sectionsMultispan U ≫ (I'.evaluatedMultispanIso U).hom =
      (I.evaluatedMultispanIso U).hom ≫ Functor.whiskerRight η
        (((TopCat.Sheaf.forget (SemimoduleCat.{v} R) X).flip).obj (op U)) := by
    unfold evaluatedMultispanIso
    exact η.sectionsMultispan_comp_multispanMapIso_hom U
  have he := congrArg SemimoduleCat.sectionsMap hn
  simp only [SemimoduleCat.sectionsMap_comp, ← sectionsEquiv_toLinearMap] at he
  have hm : SemimoduleCat.sectionsMap (Functor.whiskerRight η
      (((TopCat.Sheaf.forget (SemimoduleCat.{v} R) X).flip).obj (op U))) =
        η.sectionsMap U := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    funext j
    simp only [SemimoduleCat.sectionsMap_apply, NatTrans.sectionsMap_apply,
      Functor.whiskerRight_app]
    -- The forgetful evaluation sends a sheaf morphism to its presheaf component.
    rfl
  rw [hm] at he
  exact LinearMap.congr_fun he s

/-- Coefficient transport and endpoint restriction commute on actual matching families. -/
theorem sectionsRestrict_naturality
    {I' : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R))}
    (η : I.multispan ⟶ I'.multispan) {U V : Opens X} (hVU : V ≤ U) :
    (SemimoduleCat.sectionsMap (η.sectionsMultispan V)).comp (I.sectionsRestrict hVU) =
      (I'.sectionsRestrict hVU).comp
        (SemimoduleCat.sectionsMap (η.sectionsMultispan U)) := by
  apply LinearMap.ext
  intro s
  apply (I'.sectionsEquiv V).injective
  simp only [LinearMap.comp_apply, sectionsEquiv_naturality, sectionsEquiv_restrict]
  exact (LinearMap.congr_fun (η.sectionsMap_restrict hVU) (I.sectionsEquiv U s)).symm

/-- Compatible linear maps into evaluated-index matching families on the opens
`U i` glue to a unique linear map on `iSup U` restricting to each of them. -/
theorem existsUnique_sections_gluing (E : SemimoduleCat.{v} R) {ι : Type*}
    (U : ι → Opens X)
    (ℓ : ∀ i, E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex (U i)).multispan)
    (hcompat : ∀ i k,
      (I.sectionsRestrict (inf_le_left : U i ⊓ U k ≤ U i)).comp (ℓ i) =
        (I.sectionsRestrict (inf_le_right : U i ⊓ U k ≤ U k)).comp (ℓ k)) :
    ∃! L : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex (iSup U)).multispan,
      ∀ i, (I.sectionsRestrict (le_iSup U i)).comp L = ℓ i := by
  let a i := (I.sectionsEquiv (U i)).toLinearMap.comp (ℓ i)
  have hc : ∀ i k,
      (I.multispan.sectionsRestrict (inf_le_left : U i ⊓ U k ≤ U i)).comp (a i) =
        (I.multispan.sectionsRestrict (inf_le_right : U i ⊓ U k ≤ U k)).comp (a k) := by
    intro i k
    apply LinearMap.ext
    intro x
    have he := congrArg (fun q => I.sectionsEquiv (U i ⊓ U k) (q x)) (hcompat i k)
    simpa only [a, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      sectionsEquiv_restrict] using he
  obtain ⟨L, hL, huniq⟩ := I.multispan.existsUnique_sections_gluing E U a hc
  let result := (I.sectionsEquiv (iSup U)).symm.toLinearMap.comp L
  have hr : ∀ i, (I.sectionsRestrict (le_iSup U i)).comp result = ℓ i := by
    intro i
    apply LinearMap.ext
    intro x
    apply (I.sectionsEquiv (U i)).injective
    simp only [LinearMap.comp_apply, sectionsEquiv_restrict, result,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (hL i) x
  refine ⟨result, hr, fun m hm => ?_⟩
  have he : (I.sectionsEquiv (iSup U)).toLinearMap.comp m = L := huniq _ (by
    intro i
    apply LinearMap.ext
    intro x
    have hi := congrArg (fun q => I.sectionsEquiv (U i) (q x)) (hm i)
    simpa only [a, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      sectionsEquiv_restrict] using hi)
  apply LinearMap.ext
  intro x
  apply (I.sectionsEquiv (iSup U)).injective
  simpa only [result, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply] using LinearMap.congr_fun he x

/-- Compatible local coefficient descents glue uniquely to a global descent.
Every local descent must include face values as well as chamber values; no
injectivity of the coefficient transformation or finiteness of the cover is required. -/
theorem existsUnique_sections_descent_gluing
    {I' : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R))}
    (η : I.multispan ⟶ I'.multispan) (E : SemimoduleCat.{v} R) {ι : Type*}
    (U : ι → Opens X)
    (m : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I'.sectionsIndex (iSup U)).multispan)
    (ℓ : ∀ i, E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex (U i)).multispan)
    (hcompat : ∀ i k,
      (I.sectionsRestrict (inf_le_left : U i ⊓ U k ≤ U i)).comp (ℓ i) =
        (I.sectionsRestrict (inf_le_right : U i ⊓ U k ≤ U k)).comp (ℓ k))
    (hℓ : ∀ i, (SemimoduleCat.sectionsMap (η.sectionsMultispan (U i))).comp (ℓ i) =
      (I'.sectionsRestrict (le_iSup U i)).comp m) :
    ∃! L : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex (iSup U)).multispan,
      (∀ i, (I.sectionsRestrict (le_iSup U i)).comp L = ℓ i) ∧
        (SemimoduleCat.sectionsMap (η.sectionsMultispan (iSup U))).comp L = m := by
  obtain ⟨L, hL, huniqL⟩ := I.existsUnique_sections_gluing E U ℓ hcompat
  let a i := (SemimoduleCat.sectionsMap (η.sectionsMultispan (U i))).comp (ℓ i)
  have hc : ∀ i k,
      (I'.sectionsRestrict (inf_le_left : U i ⊓ U k ≤ U i)).comp (a i) =
        (I'.sectionsRestrict (inf_le_right : U i ⊓ U k ≤ U k)).comp (a k) := by
    intro i k
    dsimp only [a]
    rw [← LinearMap.comp_assoc, ← sectionsRestrict_naturality, LinearMap.comp_assoc,
      hcompat, ← LinearMap.comp_assoc, sectionsRestrict_naturality, LinearMap.comp_assoc]
  obtain ⟨M, -, huniqM⟩ := I'.existsUnique_sections_gluing E U a hc
  have he : (SemimoduleCat.sectionsMap (η.sectionsMultispan (iSup U))).comp L = M :=
    huniqM _ (by
      intro i
      rw [← LinearMap.comp_assoc, ← sectionsRestrict_naturality, LinearMap.comp_assoc, hL])
  have hm : m = M := huniqM m (fun i => (hℓ i).symm)
  exact ⟨L, ⟨hL, he.trans hm.symm⟩, fun q hq => huniqL q hq.1⟩

/-- Chamber section maps with inputwise local common face lifts glue uniquely
over an endpoint cover when their restrictions and coefficient images agree.
Joint injectivity is required only on subopens of members of the cover. -/
theorem existsUnique_sections_lift_descent_gluing
    {I' : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R))}
    (η : I.multispan ⟶ I'.multispan) (E : SemimoduleCat.{v} R) {ι : Type*}
    (U : ι → Opens X)
    (α : ∀ i j, E →ₗ[R] (I.right j).obj.obj (op (U i)))
    (hinj : ∀ i (W : Opens X), W ≤ U i → ∀ b,
      Function.Injective (((I.sectionsIndex W).fst b).hom.prod
        ((I.sectionsIndex W).snd b).hom))
    (hinj' : ∀ i b, Function.Injective (((I'.sectionsIndex (U i)).fst b).hom.prod
      ((I'.sectionsIndex (U i)).snd b).hom))
    (hface : ∀ i (a : E) b x, x ∈ U i → ∃ (N : Opens X) (hNU : N ≤ U i)
      (t : (I.left b).obj.obj (op N)), x ∈ N ∧
        (I.fst b).hom.app (op N) t =
          (I.right (J.fst b)).obj.map (homOfLE hNU).op (α i (J.fst b) a) ∧
        (I.snd b).hom.app (op N) t =
          (I.right (J.snd b)).obj.map (homOfLE hNU).op (α i (J.snd b) a))
    (hoverlap : ∀ i k j,
      ((I.right j).obj.map (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op).hom.comp
          (α i j) =
        ((I.right j).obj.map (homOfLE (inf_le_right : U i ⊓ U k ≤ U k)).op).hom.comp
          (α k j))
    (m : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I'.sectionsIndex (iSup U)).multispan)
    (hcoeff : ∀ i a j, ((η.app (.right j)).hom.app (op (U i))) ((α i j) a) =
      (I'.right j).obj.map (homOfLE (le_iSup U i)).op ((m a).val (.right j))) :
    ∃! L : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex (iSup U)).multispan,
      (∀ i a j, (I.right j).obj.map (homOfLE (le_iSup U i)).op ((L a).val (.right j)) =
        (α i j) a) ∧
      (SemimoduleCat.sectionsMap (η.sectionsMultispan (iSup U))).comp L = m := by
  let aMap i j := SemimoduleCat.ofHom (α i j)
  have hex i := I.existsUnique_sections_lift_of_local E (U i) (aMap i)
    (hinj i) (hface i)
  choose ℓ hℓ huniq using hex
  have hℓ' i a j : (ℓ i a).val (.right j) = (α i j) a := by
    simpa only [aMap, SemimoduleCat.hom_ofHom] using hℓ i a j
  have hc i k :
      (I.sectionsRestrict (inf_le_left : U i ⊓ U k ≤ U i)).comp (ℓ i) =
        (I.sectionsRestrict (inf_le_right : U i ⊓ U k ≤ U k)).comp (ℓ k) := by
    apply (I.sectionsIndex (U i ⊓ U k)).linearMap_ext_of_injective (hinj i _ inf_le_left)
    intro a j
    simp only [LinearMap.comp_apply, sectionsRestrict_apply_right, hℓ']
    exact LinearMap.congr_fun (hoverlap i k j) a
  have hm i : (SemimoduleCat.sectionsMap (η.sectionsMultispan (U i))).comp (ℓ i) =
      (I'.sectionsRestrict (le_iSup U i)).comp m := by
    apply (I'.sectionsIndex (U i)).linearMap_ext_of_injective (hinj' i)
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
    apply (I.sectionsIndex (U i)).linearMap_ext_of_injective (hinj i _ le_rfl)
    intro a j
    exact (I.sectionsRestrict_apply_right (le_iSup U i) (q a) j).trans
      ((hq.1 i a j).trans (hℓ' i a j).symm)

end CategoryTheory.Limits.MultispanIndex
