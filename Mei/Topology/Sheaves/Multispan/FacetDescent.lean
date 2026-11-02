/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.Multispan
public import Mei.Topology.Sheaves.LocallyConstant.FacetDescent.Hom

/-!
# Matching linear families from top-stratum data

For an incidence diagram of semimodule-valued sheaves, linear maps prescribed on
the dense top-stratum opens extend uniquely to matching families. Each chamber
map must extend locally across its interior facets. At a coefficient face a
common local lift need only agree with the prescribed maps on the incident top
strata; equality with the extended chamber maps follows from density.

Facet extension of the chamber maps, together with gluing of local face lifts,
produces a matching family of sections. The chamber stratifications may differ
and the incidence diagram may be infinite.

Usage note: if a prescribed chamber map is a finite sum of branch maps, the
conditions concern that sum; the separate branches need not extend or lift.
-/

public section

open CategoryTheory TopologicalSpace Opposite Topology Set TopCat

universe u v r

namespace CategoryTheory.Limits.MultispanIndex

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {S : Set V} {R : Type r} [Semiring R]
  {J : MultispanShape}
  (I : MultispanIndex J ((TopCat.of S).Sheaf (SemimoduleCat.{v} R)))

/-- On an open subset `S` of a finite-dimensional real vector space, the linear
chamber maps `α j` extend uniquely to a matching family under these conditions:
the right sheaves have locally isomorphic restrictions on nonempty preconnected
opens; `G j ≤ O j ≤ U` and `G j` is dense in `O j`; each `α j` extends locally across
`O j \ G j`; `U \ O j` lies in countably many affine subspaces of codimension at
least two; each face span is jointly injective on every subopen of `U`; and common
local face lifts agree with the incident `α j` on `N ⊓ G j`.

Usage note: when `α j` is a finite sum, the conditions apply to that map, without
requiring extensions or lifts of its individual summands. -/
theorem existsUnique_sections_lift_of_facets (hS : IsOpen S)
    (hRight : ∀ j x, ∃ W : Opens (TopCat.of S), x ∈ W ∧
      ∀ (B : Opens (TopCat.of S)) (hBW : B ≤ W),
        (B : Set (TopCat.of S)).Nonempty → _root_.IsPreconnected (B : Set (TopCat.of S)) →
          IsIso ((I.right j).obj.map (homOfLE hBW).op))
    (E : SemimoduleCat.{v} R) (U : Opens (TopCat.of S))
    (G O : J.R → Opens (TopCat.of S)) (hGO : ∀ j, G j ≤ O j) (hOU : ∀ j, O j ≤ U)
    (hdense : ∀ j, (O j : Set (TopCat.of S)) ⊆ closure (G j : Set (TopCat.of S)))
    {κ : Type*} [Countable κ] (A : J.R → κ → AffineSubspace ℝ V)
    (hA : ∀ j k, Module.finrank ℝ (A j k).direction + 1 < Module.finrank ℝ V)
    (hsing : ∀ j x, x ∈ U → x ∉ O j → ∃ k, (x : V) ∈ A j k)
    (α : ∀ j, E ⟶ (I.right j).obj.obj (op (G j)))
    (hfacet : ∀ j x, x ∈ O j → x ∉ G j →
      ∃ (N : Opens (TopCat.of S)) (t : E ⟶ (I.right j).obj.obj (op N)), x ∈ N ∧
        t ≫ (I.right j).obj.map (homOfLE (inf_le_left : N ⊓ G j ≤ N)).op =
          α j ≫ (I.right j).obj.map (homOfLE (inf_le_right : N ⊓ G j ≤ G j)).op)
    (hinj : ∀ (W : Opens (TopCat.of S)), W ≤ U → ∀ b,
      Function.Injective (((I.sectionsIndex W).fst b).hom.prod
        ((I.sectionsIndex W).snd b).hom))
    (hface : ∀ b x, x ∈ U → ∃ (N : Opens (TopCat.of S)) (_ : N ≤ U)
      (t : E ⟶ (I.left b).obj.obj (op N)), x ∈ N ∧
        (t ≫ (I.fst b).hom.app (op N)) ≫ (I.right (J.fst b)).obj.map
          (homOfLE (inf_le_left : N ⊓ G (J.fst b) ≤ N)).op =
          α (J.fst b) ≫ (I.right (J.fst b)).obj.map
            (homOfLE (inf_le_right : N ⊓ G (J.fst b) ≤ G (J.fst b))).op ∧
        (t ≫ (I.snd b).hom.app (op N)) ≫ (I.right (J.snd b)).obj.map
          (homOfLE (inf_le_left : N ⊓ G (J.snd b) ≤ N)).op =
          α (J.snd b) ≫ (I.right (J.snd b)).obj.map
            (homOfLE (inf_le_right : N ⊓ G (J.snd b) ≤ G (J.snd b))).op) :
    ∃! ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan,
      ∀ a j, (I.right j).obj.map (homOfLE ((hGO j).trans (hOU j))).op
        ((ℓ a).val (.right j)) = (α j).hom a := by
  classical
  have : LocallyConnectedSpace (TopCat.of S) := hS.locallyConnectedSpace
  have hdenseU (j : J.R) : (U : Set (TopCat.of S)) ⊆ closure (G j : Set (TopCat.of S)) := by
    have hOUdense : (U : Set (TopCat.of S)) ⊆ closure (O j : Set (TopCat.of S)) := by
      intro x hx
      apply mem_closure_iff.mpr
      intro W hW hxW
      obtain ⟨N, _, hNW, _, _, y, hyN, hyO⟩ :=
        hS.exists_isPreconnected_inter_of_subset_iUnion (A j) (hA j)
          (O := (O j : Set (TopCat.of S))) (hsing j) hx (hW.mem_nhds hxW)
      exact ⟨y, hNW hyN, hyO⟩
    exact hOUdense.trans (closure_minimal (hdense j) isClosed_closure)
  have hExt (j : J.R) := TopCat.Sheaf.existsUnique_hom_extension_of_facets
    (I.right j) (hRight j) hS (A j) (hA j) (hGO j) (hOU j)
    (hdense j) (hsing j) E (α j) (hfacet j)
  choose β hβ using fun j => (hExt j).exists
  have hβN (j : J.R) (N : Opens (TopCat.of S)) (hNU : N ≤ U) :
      (β j ≫ (I.right j).obj.map (homOfLE hNU).op) ≫
          (I.right j).obj.map (homOfLE (inf_le_left : N ⊓ G j ≤ N)).op =
        α j ≫ (I.right j).obj.map (homOfLE (inf_le_right : N ⊓ G j ≤ G j)).op := by
    simpa only [Category.assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp] using
      congrArg (fun t => t ≫ (I.right j).obj.map
        (homOfLE (inf_le_right : N ⊓ G j ≤ G j)).op) (hβ j)
  obtain ⟨ℓ, hℓ, huniq⟩ := I.existsUnique_sections_lift_of_local E U β hinj (by
    intro b x hx
    obtain ⟨N, hNU, t, hxN, hf, hg⟩ := hface b x hx
    refine ⟨N, hNU, t, hxN, ?_, ?_⟩
    · apply (I.right (J.fst b)).hom_restrict_injective_of_subset_closure
        (hRight (J.fst b)) E inf_le_left
        (fun z hz => N.isOpen.inter_closure ⟨hz, hdenseU _ (hNU hz)⟩)
      exact hf.trans (hβN _ N hNU).symm
    · apply (I.right (J.snd b)).hom_restrict_injective_of_subset_closure
        (hRight (J.snd b)) E inf_le_left
        (fun z hz => N.isOpen.inter_closure ⟨hz, hdenseU _ (hNU hz)⟩)
      exact hg.trans (hβN _ N hNU).symm)
  refine ⟨ℓ, ?_, fun m hm => huniq m ?_⟩
  · intro a j
    rw [hℓ]
    exact ConcreteCategory.congr_hom (hβ j) a
  · intro a j
    let ev : SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan →ₗ[R]
        (I.right j).obj.obj (op U) :=
      SemimoduleCat.sectionsEval (I.sectionsIndex U).multispan (.right j)
    let δ : E ⟶ (I.right j).obj.obj (op U) := SemimoduleCat.ofHom (ev.comp m)
    have hδa (a : E) : δ.hom a = (m a).val (.right j) := by
      simp only [δ, SemimoduleCat.hom_ofHom]
      exact SemimoduleCat.sectionsEval_apply (I.sectionsIndex U).multispan (.right j) (m a)
    have hδ : δ ≫ (I.right j).obj.map (homOfLE ((hGO j).trans (hOU j))).op = α j := by
      apply SemimoduleCat.hom_ext
      apply LinearMap.ext
      intro a
      simpa only [SemimoduleCat.hom_comp, LinearMap.comp_apply, hδa] using hm a j
    exact (hδa a).symm.trans (ConcreteCategory.congr_hom
      ((hExt j).unique hδ (hβ j)) a)

end CategoryTheory.Limits.MultispanIndex
