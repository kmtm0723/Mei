/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.Multispan.Morphism
public import Mei.Topology.Sheaves.Diagram.Gluing

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
  I.multispanMapIso ((sheafSections (Opens.grothendieckTopology X)
    (SemimoduleCat.{v} R)).obj (op U))

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

/-- The canonical comparison retains each face value. -/
@[simp]
theorem sectionsEquiv_apply_left (U : Opens X)
    (s : SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan) (b : J.L) :
    (I.sectionsEquiv U s).val (.left b) = s.val (.left b) := by
  have he := SemimoduleCat.sectionsMap_apply (I.evaluatedMultispanIso U).hom s (.left b)
  have hc : (I.evaluatedMultispanIso U).hom.app (.left b) =
      𝟙 ((I.left b).obj.obj (op U)) :=
    I.multispanMapIso_hom_app ((sheafSections (Opens.grothendieckTopology X)
      (SemimoduleCat.{v} R)).obj (op U)) (.left b)
  have hi : ((I.evaluatedMultispanIso U).hom.app (.left b)).hom
      (s.val (.left b)) = s.val (.left b) := by
    rw [hc]
    -- This identity is on the original component carrier after the public comparison equation.
    rfl
  simpa only [← sectionsEquiv_toLinearMap, LinearEquiv.coe_toLinearMap] using he.trans hi

/-- The canonical comparison retains each chamber value. -/
@[simp]
theorem sectionsEquiv_apply_right (U : Opens X)
    (s : SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan) (j : J.R) :
    (I.sectionsEquiv U s).val (.right j) = s.val (.right j) := by
  have he := SemimoduleCat.sectionsMap_apply (I.evaluatedMultispanIso U).hom s (.right j)
  have hc : (I.evaluatedMultispanIso U).hom.app (.right j) =
      𝟙 ((I.right j).obj.obj (op U)) :=
    I.multispanMapIso_hom_app ((sheafSections (Opens.grothendieckTopology X)
      (SemimoduleCat.{v} R)).obj (op U)) (.right j)
  have hi : ((I.evaluatedMultispanIso U).hom.app (.right j)).hom
      (s.val (.right j)) = s.val (.right j) := by
    rw [hc]
    -- This identity is on the original component carrier after the public comparison equation.
    rfl
  simpa only [← sectionsEquiv_toLinearMap, LinearEquiv.coe_toLinearMap] using he.trans hi

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

/-- Coefficient transport commutes with the canonical comparison of evaluated families. -/
@[simp]
theorem sectionsEquiv_naturality {I' : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R))}
    (η : I.multispan ⟶ I'.multispan) (U : Opens X)
    (s : SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan) :
    I'.sectionsEquiv U (SemimoduleCat.sectionsMap (η.sectionsMultispan U) s) =
      SemimoduleCat.sectionsMap (Functor.whiskerRight η
        (((TopCat.Sheaf.forget (SemimoduleCat.{v} R) X).flip).obj (op U)))
          (I.sectionsEquiv U s) := by
  have hn : η.sectionsMultispan U ≫ (I'.evaluatedMultispanIso U).hom =
      (I.evaluatedMultispanIso U).hom ≫ Functor.whiskerRight η
        (((TopCat.Sheaf.forget (SemimoduleCat.{v} R) X).flip).obj (op U)) := by
    unfold evaluatedMultispanIso
    exact η.sectionsMultispan_comp_multispanMapIso_hom U
  have he := congrArg SemimoduleCat.sectionsMap hn
  simp only [SemimoduleCat.sectionsMap_comp, ← sectionsEquiv_toLinearMap] at he
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
  apply Subtype.ext
  funext j
  simp only [SemimoduleCat.sectionsMap_apply, Functor.sectionsRestrict_apply]
  exact ConcreteCategory.congr_hom ((η.app j).hom.naturality (homOfLE hVU).op)
    ((I.sectionsEquiv U s).val j)

/-- Compatible linear matching families on evaluated incidence indices glue
uniquely, using the existing gluing theorem for sheaf diagrams. -/
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

end CategoryTheory.Limits.MultispanIndex
