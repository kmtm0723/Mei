/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Toric.Algebraic.RationalFunctional
public import Mei.Analysis.Convex.Exposed
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Integral affine equivalences

An integral affine equivalence is a real affine equivalence together with an
isomorphism of the integral lattices compatible with its linear part. Its
translation is arbitrary. Both directions pull rational functionals back to
rational functionals. In normed spaces the integral lattice supplies finite
dimensionality and hence continuity without further assumptions. These
equivalences preserve exposed subsets. Self-equivalences form a group whose
integral lattice map is split surjective, with the real translations as its kernel.
-/

public section

namespace Mei.Toric

open TauCeti.Toric

section Algebra

variable {N N' N'' V V' V'' : Type*}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V'']
  [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}

/-- An affine equivalence whose linear part identifies the integral lattices. -/
structure IntegralAffineEquiv (h : IsIntegralLattice i) (h' : IsIntegralLattice i') where
  /-- The underlying real affine equivalence, with arbitrary translation. -/
  toAffineEquiv : V ≃ᵃ[ℝ] V'
  /-- The isomorphism of the integral vectors. -/
  latticeEquiv : N ≃+ N'
  /-- Compatibility concerns the linear part, not the translated lattice points. -/
  map_lattice : ∀ n, toAffineEquiv.linear (i n) = i' (latticeEquiv n)

namespace IntegralAffineEquiv

variable {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}
  {h'' : IsIntegralLattice i''}

instance : CoeFun (IntegralAffineEquiv h h') (fun _ => V → V') :=
  ⟨fun e => e.toAffineEquiv⟩

/-- The real affine equivalence determines the integral lattice map uniquely. -/
theorem toAffineEquiv_injective :
    Function.Injective (toAffineEquiv : IntegralAffineEquiv h h' → V ≃ᵃ[ℝ] V') := by
  rintro ⟨e, l, hl⟩ ⟨f, l', hl'⟩ (rfl : e = f)
  obtain rfl : l = l' := AddEquiv.ext fun n => h'.injective <| by rw [← hl, ← hl']
  rfl

/-- Integral affine equivalences agreeing pointwise are equal. -/
@[ext]
theorem ext {e f : IntegralAffineEquiv h h'} (H : ∀ x, e x = f x) : e = f :=
  toAffineEquiv_injective (AffineEquiv.ext H)

/-- The real linear part is the canonical scalar extension of the integral lattice map. -/
theorem linear_eq_extend (e : IntegralAffineEquiv h h') :
    e.toAffineEquiv.linear.toLinearMap = h.extend i' e.latticeEquiv.toAddMonoidHom :=
  h.eq_extend e.map_lattice

/-- The identity preserves the integral lattice. -/
def refl (h : IsIntegralLattice i) : IntegralAffineEquiv h h where
  toAffineEquiv := AffineEquiv.refl ℝ V
  latticeEquiv := AddEquiv.refl N
  map_lattice _ := rfl

/-- Inverting the affine and integral equivalences preserves compatibility. -/
def symm (e : IntegralAffineEquiv h h') : IntegralAffineEquiv h' h where
  toAffineEquiv := e.toAffineEquiv.symm
  latticeEquiv := e.latticeEquiv.symm
  map_lattice n := by
    apply e.toAffineEquiv.linear.injective
    simp [e.map_lattice]

/-- Compose integral affine equivalences, applying the left one first. -/
def trans (e : IntegralAffineEquiv h h') (f : IntegralAffineEquiv h' h'') :
    IntegralAffineEquiv h h'' where
  toAffineEquiv := e.toAffineEquiv.trans f.toAffineEquiv
  latticeEquiv := e.latticeEquiv.trans f.latticeEquiv
  map_lattice n := by
    dsimp only [AffineEquiv.trans]
    rw [LinearEquiv.trans_apply, e.map_lattice, f.map_lattice]
    rfl

/-- The identity has the identity affine equivalence. -/
@[simp]
theorem refl_toAffineEquiv (h : IsIntegralLattice i) :
    (refl h).toAffineEquiv = AffineEquiv.refl ℝ V := (rfl)

/-- The identity has the identity lattice equivalence. -/
@[simp]
theorem refl_latticeEquiv (h : IsIntegralLattice i) :
    (refl h).latticeEquiv = AddEquiv.refl N := (rfl)

/-- Inversion inverts the underlying affine equivalence. -/
@[simp]
theorem symm_toAffineEquiv (e : IntegralAffineEquiv h h') :
    e.symm.toAffineEquiv = e.toAffineEquiv.symm := (rfl)

/-- Inversion inverts the lattice equivalence. -/
@[simp]
theorem symm_latticeEquiv (e : IntegralAffineEquiv h h') :
    e.symm.latticeEquiv = e.latticeEquiv.symm := (rfl)

/-- Composition composes the underlying affine equivalences. -/
@[simp]
theorem trans_toAffineEquiv (e : IntegralAffineEquiv h h') (f : IntegralAffineEquiv h' h'') :
    (e.trans f).toAffineEquiv = e.toAffineEquiv.trans f.toAffineEquiv := (rfl)

/-- Composition composes the lattice equivalences. -/
@[simp]
theorem trans_latticeEquiv (e : IntegralAffineEquiv h h') (f : IntegralAffineEquiv h' h'') :
    (e.trans f).latticeEquiv = e.latticeEquiv.trans f.latticeEquiv := (rfl)

/-- Inverting twice recovers the integral affine equivalence. -/
@[simp]
theorem symm_symm (e : IntegralAffineEquiv h h') : e.symm.symm = e := by
  ext; rfl

/-- Applying the inverse to an image recovers the original set carrier. -/
@[simp↓]
theorem symm_image_image (e : IntegralAffineEquiv h h') (P : Set V) :
    e.symm '' (e '' P) = P :=
  e.toAffineEquiv.toEquiv.symm_image_image P

/-- Applying an equivalence after its inverse recovers the set carrier. -/
@[simp↓]
theorem image_symm_image (e : IntegralAffineEquiv h h') (P : Set V') :
    e '' (e.symm '' P) = P :=
  e.toAffineEquiv.toEquiv.image_symm_image P

/-- Composition with the identity on the target changes nothing. -/
@[simp]
theorem trans_refl (e : IntegralAffineEquiv h h') : e.trans (refl h') = e := by
  ext; rfl

/-- Composition with the identity on the source changes nothing. -/
@[simp]
theorem refl_trans (e : IntegralAffineEquiv h h') : (refl h).trans e = e := by
  ext; rfl

/-- Composition with the inverse on the right gives the source identity. -/
@[simp]
theorem self_trans_symm (e : IntegralAffineEquiv h h') : e.trans e.symm = refl h := by
  ext; simp [trans, symm, refl]

/-- Composition with the inverse on the left gives the target identity. -/
@[simp]
theorem symm_trans_self (e : IntegralAffineEquiv h h') : e.symm.trans e = refl h' := by
  ext; simp [trans, symm, refl]

/-- Composition of integral affine equivalences is associative. -/
theorem trans_assoc {N''' V''' : Type*} [AddCommGroup N'''] [AddCommGroup V''']
    [Module ℝ V'''] {i''' : N''' →+ V'''} {h''' : IsIntegralLattice i'''}
    (e : IntegralAffineEquiv h h') (f : IntegralAffineEquiv h' h'')
    (g : IntegralAffineEquiv h'' h''') :
    (e.trans f).trans g = e.trans (f.trans g) := by
  ext; rfl

/-- The linear part is rational relative to the given integral lattices. -/
theorem isRationalLinearMap (e : IntegralAffineEquiv h h') :
    IsRationalLinearMap h h' e.toAffineEquiv.linear.toLinearMap :=
  .of_integral_compatible h h' e.latticeEquiv.toAddMonoidHom
    e.toAffineEquiv.linear.toLinearMap e.map_lattice

end IntegralAffineEquiv

end Algebra

/-! ### The integral affine symmetry group -/

namespace IntegralAffineEquiv

open TauCeti.Toric

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}

private noncomputable def latticeLinearEquiv (h : IsIntegralLattice i)
    (h' : IsIntegralLattice i') (σ : N ≃+ N') : V ≃ₗ[ℝ] V' :=
  LinearEquiv.ofLinearMap (h.extend i' σ.toAddMonoidHom)
    (h'.extend i σ.symm.toAddMonoidHom)
    ((h'.eq_extend (f := AddMonoidHom.id N') (fun n => by simp)).trans h'.extend_id)
    ((h.eq_extend (f := AddMonoidHom.id N) (fun n => by simp)).trans h.extend_id)

/-- Extend a lattice equivalence with zero translation using scalar extension. -/
noncomputable def ofLatticeEquiv (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (σ : N ≃+ N') : IntegralAffineEquiv h h' where
  toAffineEquiv := (latticeLinearEquiv h h' σ).toAffineEquiv
  latticeEquiv := σ
  map_lattice n := h.extend_apply i' σ.toAddMonoidHom n

/-- The zero-translation lift evaluates by the canonical real-linear extension. -/
@[simp↓] theorem ofLatticeEquiv_apply (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (σ : N ≃+ N') (x : V) :
    ofLatticeEquiv h h' σ x = h.extend i' σ.toAddMonoidHom x := by rfl

/-- Scalar extension preserves the specified lattice equivalence. -/
@[simp] theorem ofLatticeEquiv_latticeEquiv (h : IsIntegralLattice i)
    (h' : IsIntegralLattice i') (σ : N ≃+ N') :
    (ofLatticeEquiv h h' σ).latticeEquiv = σ := by rfl

/-- The real linear part of the zero-translation lift is scalar extension. -/
@[simp] theorem ofLatticeEquiv_linear (h : IsIntegralLattice i)
    (h' : IsIntegralLattice i') (σ : N ≃+ N') :
    (ofLatticeEquiv h h' σ).toAffineEquiv.linear.toLinearMap =
      h.extend i' σ.toAddMonoidHom := by rfl

/-- Extending the identity lattice equivalence gives the identity affine equivalence. -/
@[simp] theorem ofLatticeEquiv_refl (h : IsIntegralLattice i) :
    ofLatticeEquiv h h (AddEquiv.refl N) = refl h := by
  ext x
  simp [ofLatticeEquiv_apply, h.extend_id, refl]

/-- Inversion commutes with the zero-translation extension of a lattice equivalence. -/
@[simp] theorem ofLatticeEquiv_symm (h : IsIntegralLattice i)
    (h' : IsIntegralLattice i') (σ : N ≃+ N') :
    (ofLatticeEquiv h h' σ).symm = ofLatticeEquiv h' h σ.symm := by
  ext x
  rfl

/-- Zero-translation extension respects composition between arbitrary integral lattices. -/
@[simp] theorem ofLatticeEquiv_trans {N'' V'' : Type*} [AddCommGroup N'']
    [AddCommGroup V''] [Module ℝ V''] {i'' : N'' →+ V''}
    (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (h'' : IsIntegralLattice i'') (σ : N ≃+ N') (τ : N' ≃+ N'') :
    (ofLatticeEquiv h h' σ).trans (ofLatticeEquiv h' h'' τ) =
      ofLatticeEquiv h h'' (σ.trans τ) := by
  ext x
  exact congrArg (fun F : V →ₗ[ℝ] V'' => F x)
    (h.extend_comp h' σ.toAddMonoidHom τ.toAddMonoidHom)

/-- Integral affine self-equivalences form a group under function composition. -/
instance (h : IsIntegralLattice i) : Group (IntegralAffineEquiv h h) where
  mul e f := f.trans e
  one := refl h
  inv e := e.symm
  mul_assoc e f g := (trans_assoc g f e).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm

variable (h : IsIntegralLattice i)

/-- Group multiplication agrees with composition, applying the right map first. -/
theorem mul_def (e f : IntegralAffineEquiv h h) : e * f = f.trans e := (rfl)

/-- The group identity is the identity integral affine equivalence. -/
theorem one_def : (1 : IntegralAffineEquiv h h) = refl h := (rfl)

/-- Group inversion agrees with the inverse integral affine equivalence. -/
theorem inv_def (e : IntegralAffineEquiv h h) : e⁻¹ = e.symm := (rfl)

/-- Multiplication composes the integral lattice equivalences. -/
@[simp]
theorem mul_latticeEquiv (e f : IntegralAffineEquiv h h) :
    (e * f).latticeEquiv = f.latticeEquiv.trans e.latticeEquiv := (rfl)

/-- Multiplication composes the real affine equivalences. -/
@[simp]
theorem mul_toAffineEquiv (e f : IntegralAffineEquiv h h) :
    (e * f).toAffineEquiv = f.toAffineEquiv.trans e.toAffineEquiv := (rfl)

/-- The group identity acts identically on the lattice. -/
@[simp]
theorem one_latticeEquiv :
    (1 : IntegralAffineEquiv h h).latticeEquiv = AddEquiv.refl N := (rfl)

/-- The group identity has the identity real affine equivalence. -/
@[simp]
theorem one_toAffineEquiv :
    (1 : IntegralAffineEquiv h h).toAffineEquiv = AffineEquiv.refl ℝ V := (rfl)

/-- The inverse group element inverts the lattice equivalence. -/
@[simp]
theorem inv_latticeEquiv (e : IntegralAffineEquiv h h) :
    e⁻¹.latticeEquiv = e.latticeEquiv.symm := (rfl)

/-- The inverse group element inverts the real affine equivalence. -/
@[simp]
theorem inv_toAffineEquiv (e : IntegralAffineEquiv h h) :
    e⁻¹.toAffineEquiv = e.toAffineEquiv.symm := (rfl)

/-- Multiplication applies the right-hand map first. -/
@[simp↓]
theorem mul_apply (e f : IntegralAffineEquiv h h) (x : V) :
    (e * f) x = e (f x) := by rfl

/-- The group identity is the identity on the ambient vector space. -/
@[simp↓]
theorem one_apply (x : V) : (1 : IntegralAffineEquiv h h) x = x := by rfl

/-- Group inversion agrees with the existing inverse equivalence. -/
@[simp↓]
theorem inv_apply (e : IntegralAffineEquiv h h) (x : V) :
    e⁻¹ x = e.symm x := by rfl

/-- Forgetting the integral data respects composition. -/
def toAffineEquivHom : IntegralAffineEquiv h h →* (V ≃ᵃ[ℝ] V) where
  toFun := toAffineEquiv
  map_one' := by rfl
  map_mul' _ _ := by rfl

/-- The affine homomorphism keeps the given real affine equivalence. -/
@[simp] theorem toAffineEquivHom_apply (e : IntegralAffineEquiv h h) :
    toAffineEquivHom h e = e.toAffineEquiv := by rfl

/-- The lattice part of an integral affine symmetry, as a group homomorphism.
Mathlib uses an additive group for `AddAut`, so its multiplicative tag records composition. -/
def latticeHom : IntegralAffineEquiv h h →* Multiplicative (AddAut N) where
  toFun e := Multiplicative.ofAdd e.latticeEquiv
  map_one' := by rfl
  map_mul' _ _ := by rfl

/-- The lattice homomorphism returns the specified integral lattice map. -/
@[simp] theorem latticeHom_apply (e : IntegralAffineEquiv h h) :
    latticeHom h e = Multiplicative.ofAdd e.latticeEquiv := by rfl

/-- The zero-translation lift is compatible with composition of lattice automorphisms. -/
noncomputable def latticeLift : Multiplicative (AddAut N) →* IntegralAffineEquiv h h where
  toFun σ := ofLatticeEquiv h h σ.toAdd
  map_one' := by
    exact ofLatticeEquiv_refl h
  map_mul' σ τ := (ofLatticeEquiv_trans h h h τ.toAdd σ.toAdd).symm

/-- The lifted lattice action evaluates by scalar extension. -/
@[simp↓] theorem latticeLift_apply (σ : Multiplicative (AddAut N)) (x : V) :
    latticeLift h σ x = h.extend i σ.toAdd.toAddMonoidHom x := by rfl

/-- The real linear part of the lifted lattice automorphism is scalar extension. -/
@[simp] theorem latticeLift_linear (σ : Multiplicative (AddAut N)) :
    (latticeLift h σ).toAffineEquiv.linear.toLinearMap =
      h.extend i σ.toAdd.toAddMonoidHom :=
  ofLatticeEquiv_linear h h σ.toAdd

/-- The lift retains its input lattice automorphism. -/
@[simp] theorem latticeLift_latticeEquiv (σ : Multiplicative (AddAut N)) :
    (latticeLift h σ).latticeEquiv = σ.toAdd := by rfl

/-- The zero-translation lift is a section of the lattice homomorphism. -/
theorem latticeHom_latticeLift (σ : Multiplicative (AddAut N)) :
    latticeHom h (latticeLift h σ) = σ := by rfl

/-- Every integral lattice automorphism is realized by a global integral affine symmetry. -/
theorem latticeHom_surjective : Function.Surjective (latticeHom h) :=
  fun σ => ⟨latticeLift h σ, latticeHom_latticeLift h σ⟩

/-- Arbitrary real translations are integral affine symmetries.
Compatibility is imposed on the linear part, so the translation need not be integral. -/
def constVAddHom : Multiplicative V →* IntegralAffineEquiv h h where
  toFun v :=
    { toAffineEquiv := AffineEquiv.constVAdd ℝ V v.toAdd
      latticeEquiv := AddEquiv.refl N
      map_lattice _ := by rfl }
  map_one' := by
    apply toAffineEquiv_injective
    exact AffineEquiv.constVAdd_zero ℝ V
  map_mul' v w := by
    apply toAffineEquiv_injective
    exact AffineEquiv.constVAdd_add ℝ V v.toAdd w.toAdd

/-- The translation homomorphism acts by addition of its real vector. -/
@[simp↓] theorem constVAddHom_apply (v : Multiplicative V) (x : V) :
    constVAddHom h v x = v.toAdd + x := by rfl

/-- The underlying affine equivalence is translation by the given real vector. -/
@[simp] theorem constVAddHom_toAffineEquiv (v : Multiplicative V) :
    (constVAddHom h v).toAffineEquiv = AffineEquiv.constVAdd ℝ V v.toAdd := by rfl

/-- A real translation has the identity integral linear part. -/
@[simp] theorem constVAddHom_latticeEquiv (v : Multiplicative V) :
    (constVAddHom h v).latticeEquiv = AddEquiv.refl N := by rfl

/-- Translations act trivially on the integral tangent lattice. -/
theorem latticeHom_constVAddHom (v : Multiplicative V) :
    latticeHom h (constVAddHom h v) = 1 := by rfl

/-- Different translation vectors give different integral affine symmetries. -/
theorem constVAddHom_injective : Function.Injective (constVAddHom h) := by
  intro v w he
  apply Multiplicative.toAdd.injective
  simpa only [constVAddHom_apply, add_zero] using
    congrArg (fun e : IntegralAffineEquiv h h => e 0) he

/-- Every integral affine symmetry is its canonical zero-translation lattice lift
followed by translation by its value at the origin. -/
theorem eq_constVAddHom_mul_latticeLift (e : IntegralAffineEquiv h h) :
    e = constVAddHom h (Multiplicative.ofAdd (e 0)) * latticeLift h (latticeHom h e) := by
  ext x
  rw [mul_apply, constVAddHom_apply, latticeLift_apply, latticeHom_apply]
  have he := congrFun e.toAffineEquiv.toAffineMap.decomp x
  simp only [Pi.add_apply, AffineEquiv.linear_toAffineMap] at he
  rw [e.linear_eq_extend] at he
  exact he.trans (add_comm _ _)

/-- The kernel of the lattice homomorphism consists exactly of real translations. -/
theorem ker_latticeHom : (latticeHom h).ker = (constVAddHom h).range := by
  ext e
  simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro he
    refine ⟨Multiplicative.ofAdd (e 0), ?_⟩
    simpa only [he, map_one, mul_one] using (eq_constVAddHom_mul_latticeLift h e).symm
  · rintro ⟨v, rfl⟩
    exact latticeHom_constVAddHom h v

end IntegralAffineEquiv

namespace IntegralAffineEquiv

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup V'] [NormedSpace ℝ V] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}

/-- Agreement on a nonempty open set determines the entire integral affine equivalence. -/
theorem eq_of_eqOn_open {e f : IntegralAffineEquiv h h'} {s : Set V}
    (hs : IsOpen s) (hne : s.Nonempty) (he : Set.EqOn e f s) : e = f := by
  apply toAffineEquiv_injective
  exact AffineEquiv.ext_on (hs.affineSpan_eq_top hne) e.toAffineEquiv f.toAffineEquiv he

/-- Continuity follows from the finite dimensionality supplied by the lattice. -/
theorem continuous (e : IntegralAffineEquiv h h') : Continuous e := by
  let := h.finiteDimensional
  exact e.toAffineEquiv.continuous_of_finiteDimensional

/-- The continuous affine equivalence underlying an integral affine equivalence.
This allows transport of topological constructions, such as admissible wall paths. -/
def toContinuousAffineEquiv (e : IntegralAffineEquiv h h') : V ≃ᴬ[ℝ] V' :=
  { e.toAffineEquiv with
    continuous_toFun := e.continuous
    continuous_invFun := e.symm.continuous }

@[simp]
theorem toContinuousAffineEquiv_apply (e : IntegralAffineEquiv h h') (x : V) :
    e.toContinuousAffineEquiv x = e x := (rfl)

@[simp]
theorem toContinuousAffineEquiv_toAffineEquiv (e : IntegralAffineEquiv h h') :
    e.toContinuousAffineEquiv.toAffineEquiv = e.toAffineEquiv := (rfl)

/-- The underlying continuous affine map used to transport affine inequalities. -/
def toContinuousAffineMap (e : IntegralAffineEquiv h h') : V →ᴬ[ℝ] V' :=
  { e.toAffineEquiv.toAffineMap with cont := e.continuous }

/-- Bundling continuity does not change evaluation. -/
@[simp]
theorem toContinuousAffineMap_apply (e : IntegralAffineEquiv h h') (x : V) :
    e.toContinuousAffineMap x = e x := (rfl)

/-- Forgetting continuity gives the original affine map. -/
@[simp]
theorem toContinuousAffineMap_toAffineMap (e : IntegralAffineEquiv h h') :
    e.toContinuousAffineMap.toAffineMap = e.toAffineEquiv.toAffineMap := (rfl)

/-- Rationality with the exact bundled continuous-map type, for use in public
constructions without relying on unfolding the rational-map predicate. -/
theorem isRational_toContinuousAffineMap (e : IntegralAffineEquiv h h') :
    IsRationalLinearMap h h' e.toContinuousAffineMap.toAffineMap.linear := by
  simpa only [toContinuousAffineMap_toAffineMap, AffineEquiv.linear_toAffineMap]
    using e.isRationalLinearMap

end IntegralAffineEquiv

end Mei.Toric

namespace IsExposed

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace ℝ V] [NormedSpace ℝ W]
  {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {P F : Set V}

/-- Integral affine equivalences preserve actual exposed subsets. -/
theorem image_integralAffineEquiv (hF : IsExposed ℝ P F)
    (e : Mei.Toric.IntegralAffineEquiv h h') : IsExposed ℝ (e '' P) (e '' F) := by
  apply hF.image_affineEquiv e.toAffineEquiv
  simpa only [Mei.Toric.IntegralAffineEquiv.symm_toAffineEquiv] using e.symm.continuous

end IsExposed
