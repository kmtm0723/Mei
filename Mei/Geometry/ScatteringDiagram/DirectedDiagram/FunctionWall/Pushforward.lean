/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedWall.TropicalPairing.WallFunction

/-!
# Function-wall groupings under pushforward

Let `P` be `DirectedWall.Pushforward` data over a positive degree map `T`, and let spatial
projections `π : Γ → M` and `π' : Γ' → M` satisfy `π' ∘ T = π` on allowed degrees. The projected
generator of a wall is then a positive rational multiple of the projected generator of the pushed
wall (`DirectedWall.exists_nsmul_projection_pushforward_ray_generator`). Hence a function-wall
grouping of a diagram `D` is a grouping of `D.pushforward P`
(`DirectedDiagram.FunctionWallGrouping.pushforward`), provided the normal map keeps the normals
of the walls primitive: supports move by the spatial map and normals by the normal map, both
uniformly in each group. The completed label of a pushed group is the image of the completed
group label under the completed Lie map (`FunctionWallGrouping.label_pushforward`).

For the finite-index pushforward `DirectedWall.Pushforward.ofFiniteIndex`, where the normal `n`
of a group goes to `ν n` with `ν n ∘ t = q n • n`, a group with function-wall label
`exp(log(f₀) ∂_n)` such that `q n = r` and `T_* f₀ = f₁ ^ r` is pushed to a group with label
`exp(log(f₁) ∂_{ν n})` (`FunctionWallGrouping.label_pushforward_ofFiniteIndex`; any normal `n'`
with `n' ∘ t = q n • n` may replace `ν n` in the label). This is the
ray-power comparison
`Mei.DirectedWall.Pushforward.ofFiniteIndex_lieHom_completedMap_completedBCHExp_completedLog`
for grouped walls, as in the lattice change of Burcroff–Lee–Mou, *Positivity of generalized
cluster scattering diagrams*, Theorem 9.5 (arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei

universe u v

section Pushforward

variable {Γ Γ' Λ Λ' R V V' M : Type*} {L L' : Type v} {ι : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup M]
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'}
  [DecidableEq Γ] [DecidableEq Γ']
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {i : Λ →+ V} {i' : Λ' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  (P : DirectedWall.Pushforward d d' h h' H H')
  {π : Γ →+ M} {π' : Γ' →+ M} (hπ : ∀ n ∈ d.monoid, π' (P.degreeMap n) = π n)

include hπ in
/-- If `π' ∘ T = π` on allowed degrees, a positive multiple of the projected generator of a wall
is a positive multiple of the projected generator of the pushed wall. -/
theorem DirectedWall.exists_nsmul_projection_pushforward_ray_generator
    (W : DirectedWall (d := d) h H) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      a • π W.ray.generator = b • π' (W.pushforward P).ray.generator := by
  obtain ⟨m, hm⟩ := W.ray.rayDegrees_nonempty
  obtain ⟨hn, a, ha, rfl⟩ := SupportedRay.mem_rayDegrees.mp hm
  obtain ⟨-, b, hb, hbn⟩ := SupportedRay.mem_rayDegrees.mp
    (W.degreeMap_mem_pushforward_rayDegrees P hm)
  refine ⟨a.toNat, b.toNat, by omega, by omega, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul ℤ a.toNat, ← Nat.cast_smul_eq_nsmul ℤ b.toNat,
    Int.toNat_of_nonneg ha.le, Int.toNat_of_nonneg hb.le, ← map_zsmul, ← map_zsmul, ← hbn, hπ _ hn]

namespace DirectedDiagram.FunctionWallGrouping

variable {P} {D : DirectedDiagram (d := d) h H ι} {κ : Type*} (G : D.FunctionWallGrouping π κ)
  (hprim : ∀ j, TauCeti.IsPrimitive (P.normalMap (D.wall j).normal))

/-- If `π' ∘ T = π` on allowed degrees and the normal map keeps the normals of the walls
primitive, a function-wall grouping of a diagram is a grouping of its pushforward, with the same
groups. -/
def pushforward : (D.pushforward P).FunctionWallGrouping π' κ where
  group := G.group
  support_eq hj := by
    rw [pushforward_wall_support, pushforward_wall_support, G.support_eq hj]
  normal_eq hj := by
    rw [pushforward_wall, pushforward_wall, DirectedWall.pushforward_normal,
      DirectedWall.pushforward_normal, G.normal_eq hj]
  projectedDirection_eq {j j'} hj hj1 hj'1 := by
    have hne (j : ι) (h1 : ((D.pushforward P).wall j).label ≠ 1) : (D.wall j).label ≠ 1 :=
      fun he => h1 (by rw [pushforward_wall, DirectedWall.pushforward_label, he, map_one])
    obtain ⟨x, y, hx, hy, hxy⟩ := G.projectedDirection_eq hj (hne j hj1) (hne j' hj'1)
    obtain ⟨a, b, ha, hb, hab⟩ :=
      (D.wall j).exists_nsmul_projection_pushforward_ray_generator P hπ
    obtain ⟨a', b', ha', hb', hab'⟩ :=
      (D.wall j').exists_nsmul_projection_pushforward_ray_generator P hπ
    refine ⟨x * a' * b, y * a * b', by positivity, by positivity, ?_⟩
    rw [pushforward_wall, pushforward_wall]
    calc (x * a' * b) • π' ((D.wall j).pushforward P).ray.generator
        = (x * a') • a • π (D.wall j).ray.generator := by rw [mul_smul, ← hab]
      _ = (a' * a) • x • π (D.wall j).ray.generator := by
        rw [smul_smul, smul_smul]
        congr 1
        ring
      _ = (y * a) • a' • π (D.wall j').ray.generator := by
        rw [hxy, smul_smul, smul_smul]
        congr 1
        ring
      _ = (y * a * b') • π' ((D.wall j').pushforward P).ray.generator := by rw [hab', smul_smul]
  isPrimitive_normal j := by
    simpa only [pushforward_wall, DirectedWall.pushforward_normal] using hprim j

/-- The pushed grouping places every wall in its original group. -/
@[simp]
theorem pushforward_group (j : ι) : (G.pushforward hπ hprim).group j = G.group j := by
  simp [pushforward]

/-- The order-`k` label of a pushed group is the truncated image of the group label at the
order of the cutoff modulus. -/
theorem groupLabel_pushforward (g : κ) (k : ℕ) :
    (G.pushforward hπ hprim).groupLabel g k =
      (P.lieHom.truncatedMap k le_rfl).bchGroupMap (G.groupLabel g (P.degreeMap.modulus k)) := by
  classical
  let s := (Set.toFinite (D.active (P.degreeMap.modulus k))).toFinset.filter
    fun j => G.group j = g
  have hs : ∀ j ∈ s, G.group j = g := fun j hj => (Finset.mem_filter.mp hj).2
  have hact : ∀ j ∈ D.active (P.degreeMap.modulus k), G.group j = g → j ∈ s := fun j hj hg =>
    Finset.mem_filter.mpr ⟨(Set.toFinite _).mem_toFinset.mpr hj, hg⟩
  rw [(G.pushforward hπ hprim).groupLabel_eq_noncommProd g k s
      (fun j hj => by simpa using hs j hj)
      fun j hj hg => hact j (D.active_pushforward_subset P k le_rfl hj) (by simpa using hg),
    G.groupLabel_eq_noncommProd g _ s hs hact]
  exact (Finset.noncommProd_congr rfl (fun j _ => D.projection_pushforward_wall_label P k le_rfl j)
    _).trans (Finset.map_noncommProd s _ _ _).symm

/-- The completed label of a pushed group is the image of the completed group label. -/
@[simp]
theorem label_pushforward (g : κ) :
    (G.pushforward hπ hprim).label g = P.lieHom.completedMap (G.label g) :=
  (((G.pushforward hπ hprim).eq_label_iff g _).mpr fun k => by
    rw [P.lieHom.projection_completedMap k, projection_label, groupLabel_pushforward]).symm

end DirectedDiagram.FunctionWallGrouping

end Pushforward

namespace DirectedDiagram.FunctionWallGrouping

open LogarithmicVectorField

variable {R Γ Λ Γ' Λ' : Type u} {V V' M : Type*} {ι : Type v} [CommRing R] [Algebra ℚ R]
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup Γ'] [AddCommGroup Λ'] [Module.Free ℤ Γ']
  [DecidableEq Γ] [DecidableEq Γ'] [AddCommGroup M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {i : Λ →+ V} {i' : Λ' →+ V'} {h : TauCeti.Toric.IsIntegralLattice i}
  {h' : TauCeti.Toric.IsIntegralLattice i'}
  (T : PositiveDegreeMap d e) (t : Λ →+ Λ') (ht : Function.Injective t)
  [t.range.FiniteIndex] (hρ : ∀ n ∈ d.monoid, ρ' (T n) = t (ρ n))
  (ν : (Λ →+ ℤ) → (Λ' →+ ℤ)) (q : (Λ →+ ℤ) → ℚ) (hq : ∀ m, 0 < q m)
  (hν : ∀ m x, (ν m (t x) : ℚ) = q m * m x)
  {D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ) ι}
  {π : Γ →+ M} {π' : Γ' →+ M} {κ : Type*} (G : D.FunctionWallGrouping π κ)

local notation "P" =>
  DirectedWall.Pushforward.ofFiniteIndex (R := R) (h := h) (h' := h') T t ht hρ ν q hq hν

variable {g : κ} {n : Λ →+ ℤ} {n' : Λ' →+ ℤ} (hn' : ∀ x, (n' (t x) : ℚ) = q n * n x) {r : ℕ}
  (hr : q n = r)

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d
  (tropicalTangentMonoid d ρ (AddMonoidHom.comp (Int.castAddHom R) n))
local notation "F'" => TropicalVertexCoefficientAction.filtration (R := R) e
  (tropicalTangentMonoid e ρ' (AddMonoidHom.comp (Int.castAddHom R) n'))

include hr in
/-- **Ray-power comparison of function walls.** Let `n'` be an integral normal with
`n' ∘ t = q n • n`, for instance `ν n`. If a group has the function-wall label `exp(log(f₀) ∂_n)`,
where `q n = r` and the tangent monomial map sends `f₀` to `f₁ ^ r`, the finite-index
pushforward of the group has the function-wall label `exp(log(f₁) ∂_{n'})`. -/
theorem label_pushforward_ofFiniteIndex (hπ : ∀ x ∈ d.monoid, π' ((P).degreeMap x) = π x)
    (hprim : ∀ j, TauCeti.IsPrimitive ((P).normalMap (D.wall j).normal))
    (f₀ : {u : (F).completion // u - 1 ∈ (F).completionIdeal 1})
    (f₁ : {u : (F').completion // u - 1 ∈ (F').completionIdeal 1})
    (hg : G.label g = d.completedBCHExp _ (completedTropicalTangentField d ρ
      ((Int.castAddHom R).comp n) ((F).completedLog f₀)))
    (hf : completedTropicalTangentMap T (map_tropicalTangentMonoid_intCast_le T hρ hn') f₀ =
      (f₁ : (F').completion) ^ r) :
    (G.pushforward hπ hprim).label g = e.completedBCHExp _ (completedTropicalTangentField e ρ'
      ((Int.castAddHom R).comp n') ((F').completedLog f₁)) := by
  rw [label_pushforward, hg]
  exact DirectedWall.Pushforward.ofFiniteIndex_lieHom_completedMap_completedBCHExp_completedLog
    T t ht hρ ν q hq hν n hn' hr f₀ f₁ hf

end DirectedDiagram.FunctionWallGrouping

end Mei
