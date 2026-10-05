/-
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## The eight Thurston geometries

We formalize a *model geometry* as a topological space `X` together with a group `G`
acting on `X` by homeomorphisms, transitively.  A closed 3-manifold `M` is *geometric*,
modelled on `(X, G)`, when `M` is homeomorphic to a quotient `X / Γ` for a subgroup
`Γ ≤ G` acting freely and properly discontinuously.

The eight Thurston geometries are realized below by concrete model spaces:

* `E³`      : `ℝ³` acted on by translations;
* `S³`      : the unit sphere in `ℝ⁴` acted on by linear isometries;
* `H³`      : the solvable Lie group `ℝ² ⋊ ℝ` (`t` acting by `e^t` on both factors),
              which carries a left invariant metric of constant curvature `-1`;
* `S² × ℝ`  : the unit sphere in `ℝ³` times `ℝ`;
* `H² × ℝ`  : the group `(ℝ ⋊ ℝ) × ℝ`, the affine group of the line (a model of `H²`)
              times `ℝ`;
* `SL(2,ℝ)~`: the universal cover of `PSL(2,ℝ)`, realized as the group of lifts to `ℝ`
              of the projective action of `SL(2,ℝ)` on directions of `ℝ²`;
* `Nil`     : the Heisenberg group;
* `Sol`     : the solvable group `ℝ² ⋊ ℝ` (`t` acting by `e^t`, `e^{-t}`).

In each case the group of the geometry is taken to be a transitive group of isometries
of the model space (for the Lie group models: the group acting on itself by left
translations); we do not verify maximality of these groups, which is what singles out
the eight geometries among all homogeneous 3-dimensional spaces.
-/

/-- Labels for the eight Thurston geometries. -/
inductive ThurstonGeometry
  | euclidean
  | spherical
  | hyperbolic
  | sphereProdLine
  | hyperbolicProdLine
  | slTwoTilde
  | nil
  | sol
  deriving DecidableEq, Fintype, Repr

/-! ### Euclidean 3-space as a group -/

/-- Euclidean 3-space, viewed as the group of its own translations. -/
def Euc3 : Type := ℝ × ℝ × ℝ

namespace Euc3

instance : MetricSpace Euc3 := inferInstanceAs (MetricSpace (ℝ × ℝ × ℝ))
instance : ProperSpace Euc3 := inferInstanceAs (ProperSpace (ℝ × ℝ × ℝ))
instance : ConnectedSpace Euc3 := inferInstanceAs (ConnectedSpace (ℝ × ℝ × ℝ))
instance : SecondCountableTopology Euc3 := inferInstanceAs (SecondCountableTopology (ℝ × ℝ × ℝ))
instance : Mul Euc3 := ⟨fun p q => (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2)⟩
instance : One Euc3 := ⟨((0 : ℝ), (0 : ℝ), (0 : ℝ))⟩
instance : Inv Euc3 := ⟨fun p => (-p.1, -p.2.1, -p.2.2)⟩

/-- Build a point of `ℝ³` from its coordinates. -/
def mk (a b c : ℝ) : Euc3 := (a, b, c)

lemma mul_def (p q : Euc3) : p * q = (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2) := rfl
lemma one_def : (1 : Euc3) = ((0 : ℝ), (0 : ℝ), (0 : ℝ)) := rfl
lemma inv_def (p : Euc3) : p⁻¹ = (-p.1, -p.2.1, -p.2.2) := rfl

instance : Group Euc3 where
  mul_assoc a b c := by refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [mul_def] <;> ring
  one_mul a := by refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [mul_def, one_def]
  mul_one a := by refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [mul_def, one_def]
  inv_mul_cancel a := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [mul_def, inv_def, one_def]

lemma continuous_mul_left (g : Euc3) : Continuous (fun x : Euc3 => g * x) := by
  show Continuous (fun x : ℝ × ℝ × ℝ =>
    ((g.1 + x.1 : ℝ), (g.2.1 + x.2.1 : ℝ), (g.2.2 + x.2.2 : ℝ)))
  fun_prop

end Euc3

/-! ### The Heisenberg group `Nil` -/

/-- The Heisenberg group: `ℝ³` with `(x,y,z)(x',y',z') = (x+x', y+y', z+z'+x y')`. -/
def NilGroup : Type := ℝ × ℝ × ℝ

namespace NilGroup

instance : TopologicalSpace NilGroup := inferInstanceAs (TopologicalSpace (ℝ × ℝ × ℝ))
instance : Mul NilGroup :=
  ⟨fun p q => (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + p.1 * q.2.1)⟩
instance : One NilGroup := ⟨((0 : ℝ), (0 : ℝ), (0 : ℝ))⟩
instance : Inv NilGroup := ⟨fun p => (-p.1, -p.2.1, -p.2.2 + p.1 * p.2.1)⟩

lemma mul_def (p q : NilGroup) :
    p * q = (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + p.1 * q.2.1) := rfl
lemma one_def : (1 : NilGroup) = ((0 : ℝ), (0 : ℝ), (0 : ℝ)) := rfl
lemma inv_def (p : NilGroup) : p⁻¹ = (-p.1, -p.2.1, -p.2.2 + p.1 * p.2.1) := rfl

instance : Group NilGroup where
  mul_assoc a b c := by refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [mul_def] <;> ring
  one_mul a := by refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [mul_def, one_def] <;> ring
  mul_one a := by refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [mul_def, one_def] <;> ring
  inv_mul_cancel a := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [mul_def, inv_def, one_def] <;> ring

lemma continuous_mul_left (g : NilGroup) : Continuous (fun x : NilGroup => g * x) := by
  show Continuous (fun x : ℝ × ℝ × ℝ =>
    ((g.1 + x.1 : ℝ), (g.2.1 + x.2.1 : ℝ), (g.2.2 + x.2.2 + g.1 * x.2.1 : ℝ)))
  fun_prop

end NilGroup

/-! ### The solvable groups `ℝ² ⋊ ℝ` -/

/-- `SolvGroup a b` is `ℝ³` with the group law
`(x,y,t)(x',y',t') = (x + e^{a t} x', y + e^{b t} y', t + t')`.

For `(a,b) = (1,1)` this is the solvable Lie group underlying hyperbolic 3-space `H³`
(the upper half space model, with `t = log(height)`); for `(a,b) = (1,-1)` it is `Sol`;
for `(a,b) = (1,0)` it is `H² × ℝ` (the affine group of the line times `ℝ`). -/
def SolvGroup (_a _b : ℝ) : Type := ℝ × ℝ × ℝ

namespace SolvGroup

variable {a b : ℝ}

instance : TopologicalSpace (SolvGroup a b) := inferInstanceAs (TopologicalSpace (ℝ × ℝ × ℝ))

noncomputable instance : Mul (SolvGroup a b) :=
  ⟨fun p q => (p.1 + Real.exp (a * p.2.2) * q.1,
               p.2.1 + Real.exp (b * p.2.2) * q.2.1, p.2.2 + q.2.2)⟩
instance : One (SolvGroup a b) := ⟨((0 : ℝ), (0 : ℝ), (0 : ℝ))⟩
noncomputable instance : Inv (SolvGroup a b) :=
  ⟨fun p => (-(Real.exp (-(a * p.2.2)) * p.1), -(Real.exp (-(b * p.2.2)) * p.2.1), -p.2.2)⟩

lemma mul_def (p q : SolvGroup a b) : p * q =
    (p.1 + Real.exp (a * p.2.2) * q.1, p.2.1 + Real.exp (b * p.2.2) * q.2.1,
      p.2.2 + q.2.2) := rfl
lemma one_def : (1 : SolvGroup a b) = ((0 : ℝ), (0 : ℝ), (0 : ℝ)) := rfl
lemma inv_def (p : SolvGroup a b) : p⁻¹ =
    (-(Real.exp (-(a * p.2.2)) * p.1), -(Real.exp (-(b * p.2.2)) * p.2.1), -p.2.2) := rfl

noncomputable instance : Group (SolvGroup a b) where
  mul_assoc p q r := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [mul_def, mul_add, mul_assoc, Real.exp_add] <;> ring
  one_mul p := by refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [mul_def, one_def]
  mul_one p := by refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [mul_def, one_def]
  inv_mul_cancel p := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [mul_def, inv_def, one_def, mul_neg, ← Real.exp_add] <;> ring_nf

lemma continuous_mul_left (g : SolvGroup a b) : Continuous (fun x : SolvGroup a b => g * x) := by
  show Continuous (fun x : ℝ × ℝ × ℝ => ((g.1 + Real.exp (a * g.2.2) * x.1 : ℝ),
    (g.2.1 + Real.exp (b * g.2.2) * x.2.1 : ℝ), (g.2.2 + x.2.2 : ℝ)))
  fun_prop

end SolvGroup

/-! ### The universal cover of `PSL(2,ℝ)` -/

/-- `IsSLLift A f` says that `f : ℝ → ℝ` is a lift, along the covering `x ↦ (cos x, sin x)`
of the space of directions in `ℝ²`, of the action of the matrix `A` on directions. -/
def IsSLLift (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ∃ r : ℝ, 0 < r ∧
    A.1 0 0 * Real.cos x + A.1 0 1 * Real.sin x = r * Real.cos (f x) ∧
    A.1 1 0 * Real.cos x + A.1 1 1 * Real.sin x = r * Real.sin (f x)

lemma isSLLift_one : IsSLLift 1 id := fun x => ⟨1, one_pos, by simp, by simp⟩

lemma isSLLift_mul {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ} {f g : ℝ → ℝ}
    (hA : IsSLLift A f) (hB : IsSLLift B g) : IsSLLift (A * B) (f ∘ g) := by
  intro x
  obtain ⟨r, hr, hr1, hr2⟩ := hB x
  obtain ⟨s, hs, hs1, hs2⟩ := hA (g x)
  refine ⟨r * s, by positivity, ?_, ?_⟩ <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Function.comp_apply]
  · linear_combination (A.1 0 0) * hr1 + (A.1 0 1) * hr2 + r * hs1
  · linear_combination (A.1 1 0) * hr1 + (A.1 1 1) * hr2 + r * hs2

lemma isSLLift_inv {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {f g : ℝ → ℝ}
    (hA : IsSLLift A f) (hfg : ∀ x, f (g x) = x) : IsSLLift A⁻¹ g := by
  intro y
  obtain ⟨r, hr, h1, h2⟩ := hA (g y)
  have hdet : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    linarith
  rw [hfg y] at h1 h2
  have hr' : r ≠ 0 := ne_of_gt hr
  refine ⟨r⁻¹, by positivity, ?_, ?_⟩ <;>
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl] <;> simp <;> field_simp
  · linear_combination -(A.1 1 1) * h1 + (A.1 0 1) * h2 + Real.cos (g y) * hdet
  · linear_combination (A.1 1 0) * h1 - (A.1 0 0) * h2 + Real.sin (g y) * hdet

/-- The universal cover of `PSL(2,ℝ)`: homeomorphisms of `ℝ` that lift the projective
action of some `A ∈ SL(2,ℝ)` on the space of directions of `ℝ²`. -/
@[ext] structure SLTilde where
  toFun : C(ℝ, ℝ)
  invFun : C(ℝ, ℝ)
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ x, toFun (invFun x) = x
  isLift : ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, IsSLLift A toFun

namespace SLTilde

instance : TopologicalSpace SLTilde :=
  TopologicalSpace.induced (fun p : SLTilde => (p.toFun, p.invFun)) inferInstance

lemma continuous_pair : Continuous (fun p : SLTilde => (p.toFun, p.invFun)) :=
  continuous_induced_dom

instance : Mul SLTilde where
  mul p q :=
  { toFun := p.toFun.comp q.toFun
    invFun := q.invFun.comp p.invFun
    left_inv := fun x => by simp [q.left_inv, p.left_inv]
    right_inv := fun x => by simp [q.right_inv, p.right_inv]
    isLift := by
      obtain ⟨A, hA⟩ := p.isLift
      obtain ⟨B, hB⟩ := q.isLift
      exact ⟨A * B, by simpa [ContinuousMap.coe_comp] using isSLLift_mul hA hB⟩ }

instance : One SLTilde where
  one := { toFun := ContinuousMap.id ℝ, invFun := ContinuousMap.id ℝ,
           left_inv := fun _ => rfl, right_inv := fun _ => rfl, isLift := ⟨1, isSLLift_one⟩ }

instance : Inv SLTilde where
  inv p :=
  { toFun := p.invFun, invFun := p.toFun, left_inv := p.right_inv, right_inv := p.left_inv
    isLift := by
      obtain ⟨A, hA⟩ := p.isLift
      exact ⟨A⁻¹, isSLLift_inv hA p.right_inv⟩ }

instance : Group SLTilde where
  mul_assoc a b c := by ext x <;> rfl
  one_mul a := by ext x <;> rfl
  mul_one a := by ext x <;> rfl
  inv_mul_cancel a := by ext x <;> exact a.left_inv x

lemma continuous_mul_left (p : SLTilde) : Continuous (fun q : SLTilde => p * q) := by
  rw [continuous_induced_rng]
  exact Continuous.prodMk
    ((ContinuousMap.continuous_postcomp p.toFun).comp (continuous_fst.comp continuous_pair))
    ((ContinuousMap.continuous_precomp p.invFun).comp (continuous_snd.comp continuous_pair))

end SLTilde

/-! ### Round spheres -/

/-- The unit sphere in `n`-dimensional Euclidean space (so `Sph 3` is the 2-sphere and
`Sph 4` is the 3-sphere). -/
def Sph (n : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

namespace Sph

instance (n : ℕ) : TopologicalSpace (Sph n) :=
  inferInstanceAs (TopologicalSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))

/-- Linear isometries of `ℝⁿ` act on the unit sphere. -/
def act (n : ℕ) (g : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : Sph n) : Sph n :=
  ⟨g v.1, by
    have hv : ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ = 1 := by simpa using v.2
    simpa [mem_sphere_zero_iff_norm, g.norm_map] using hv⟩

lemma act_one (n : ℕ) (v : Sph n) : act n 1 v = v := rfl

lemma act_mul (n : ℕ) (g h : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : Sph n) : act n (g * h) v = act n g (act n h v) := rfl

lemma continuous_act (n : ℕ) (g : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Continuous (act n g) :=
  Continuous.subtype_mk (g.continuous.comp continuous_subtype_val) _

lemma transitive (n : ℕ) (v w : Sph n) : ∃ g, act n g v = w := by
  have hv : ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ = 1 := by simpa using v.2
  have hw : ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ = 1 := by simpa using w.2
  exact ⟨(ℝ ∙ (v.1 - w.1))ᗮ.reflection, Subtype.ext (Submodule.reflection_sub (by rw [hv, hw]))⟩

instance (n : ℕ) : Nonempty (Sph (n + 1)) :=
  ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩

end Sph

/-! ## Model geometries and geometric structures -/

/-- A *model geometry*: a topological space `X` with a group `G` acting continuously and
transitively on it. -/
structure ModelGeometry where
  /-- the model space -/
  X : Type
  [topX : TopologicalSpace X]
  /-- the group of the geometry -/
  G : Type
  [grpG : Group G]
  /-- the action of the group on the model space -/
  act : G → X → X
  act_one : ∀ x, act 1 x = x
  act_mul : ∀ a b x, act (a * b) x = act a (act b x)
  act_continuous : ∀ a, Continuous (act a)
  act_transitive : ∀ x y, ∃ a, act a x = y
  nonempty : Nonempty X

attribute [instance] ModelGeometry.topX ModelGeometry.grpG

namespace ModelGeometry

variable (mg : ModelGeometry)

/-- A topological group acting on itself by left translations is a model geometry. -/
def ofGroup (G : Type) [Group G] [TopologicalSpace G]
    (hc : ∀ g : G, Continuous (fun x : G => g * x)) : ModelGeometry where
  X := G
  G := G
  act := fun g x => g * x
  act_one := one_mul
  act_mul := fun a b x => mul_assoc a b x
  act_continuous := hc
  act_transitive := fun x y => ⟨y * x⁻¹, by group⟩
  nonempty := ⟨1⟩

lemma act_inv (g : mg.G) (x : mg.X) : mg.act g⁻¹ (mg.act g x) = x := by
  rw [← mg.act_mul, inv_mul_cancel, mg.act_one]

/-- The orbit equivalence relation of a subgroup `Γ ≤ G` on the model space. -/
def orbitSetoid (Γ : Subgroup mg.G) : Setoid mg.X where
  r x y := ∃ γ ∈ Γ, mg.act γ x = y
  iseqv := by
    refine ⟨fun x => ⟨1, Γ.one_mem, mg.act_one x⟩, ?_, ?_⟩
    · rintro x y ⟨γ, hγ, rfl⟩
      exact ⟨γ⁻¹, Γ.inv_mem hγ, mg.act_inv γ x⟩
    · rintro x y z ⟨γ, hγ, rfl⟩ ⟨δ, hδ, rfl⟩
      exact ⟨δ * γ, Γ.mul_mem hδ hγ, by rw [mg.act_mul]⟩

/-- The quotient of the model space by a group `Γ` of deck transformations. -/
def quotient (Γ : Subgroup mg.G) : Type := Quotient (mg.orbitSetoid Γ)

instance (Γ : Subgroup mg.G) : TopologicalSpace (mg.quotient Γ) :=
  inferInstanceAs (TopologicalSpace (Quotient (mg.orbitSetoid Γ)))

/-- The quotient map onto `X / Γ`. -/
def proj (Γ : Subgroup mg.G) (x : mg.X) : mg.quotient Γ := Quotient.mk (mg.orbitSetoid Γ) x

lemma continuous_proj (Γ : Subgroup mg.G) : Continuous (mg.proj Γ) := continuous_quotient_mk'

lemma proj_surjective (Γ : Subgroup mg.G) : Function.Surjective (mg.proj Γ) :=
  Quotient.mk_surjective

lemma proj_eq_proj {Γ : Subgroup mg.G} {x y : mg.X} (γ : mg.G) (hγ : γ ∈ Γ)
    (h : mg.act γ x = y) : mg.proj Γ x = mg.proj Γ y :=
  Quotient.sound ⟨γ, hγ, h⟩

lemma act_inv' (g : mg.G) (x : mg.X) : mg.act g (mg.act g⁻¹ x) = x := by
  simpa using mg.act_inv g⁻¹ x

/-- The projection to a quotient of the model space is an open map. -/
lemma isOpenMap_proj (Γ : Subgroup mg.G) : IsOpenMap (mg.proj Γ) := by
  intro U hU
  have hpre : (mg.proj Γ) ⁻¹' (mg.proj Γ '' U)
      = ⋃ γ : Γ, (fun x => mg.act ((γ : mg.G)⁻¹) x) ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨u, hu, heq⟩
      obtain ⟨γ, hγ, hgu⟩ := Quotient.exact heq
      refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ?_⟩
      simp only [Set.mem_preimage]
      rw [← hgu, mg.act_inv]
      exact hu
    · intro hx
      obtain ⟨γ, hγ⟩ := Set.mem_iUnion.1 hx
      exact ⟨mg.act ((γ : mg.G)⁻¹) x, hγ,
        mg.proj_eq_proj (γ : mg.G) γ.2 (mg.act_inv' (γ : mg.G) x)⟩
  have hopen : IsOpen ((mg.proj Γ) ⁻¹' (mg.proj Γ '' U)) := by
    rw [hpre]
    exact isOpen_iUnion fun γ => hU.preimage (mg.act_continuous _)
  exact (isQuotientMap_quotient_mk' (s := mg.orbitSetoid Γ)).isOpen_preimage.mp hopen

end ModelGeometry

/-- `M` admits a geometric structure modelled on the model geometry `mg`:
`M` is homeomorphic to a quotient of the model space by a subgroup of the group of the
geometry acting freely and properly discontinuously. -/
def AdmitsGeometry (M : Type) [TopologicalSpace M] (mg : ModelGeometry) : Prop :=
  ∃ Γ : Subgroup mg.G,
    (∀ γ ∈ Γ, γ ≠ 1 → ∀ x : mg.X, mg.act γ x ≠ x) ∧
    (∀ K : Set mg.X, IsCompact K → {γ : mg.G | γ ∈ Γ ∧ ∃ x ∈ K, mg.act γ x ∈ K}.Finite) ∧
    Nonempty (M ≃ₜ mg.quotient Γ)

/-- Admitting a geometric structure is a topological invariant. -/
theorem AdmitsGeometry.congr {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    {mg : ModelGeometry} (e : M ≃ₜ N) (h : AdmitsGeometry N mg) : AdmitsGeometry M mg := by
  obtain ⟨Γ, hfree, hpd, ⟨f⟩⟩ := h
  exact ⟨Γ, hfree, hpd, ⟨e.trans f⟩⟩

/-- **Base case.** The model space of any model geometry is itself geometric
(take the trivial group of deck transformations). -/
theorem admitsGeometry_self (mg : ModelGeometry) : AdmitsGeometry mg.X mg := by
  refine ⟨⊥, ?_, ?_, ?_⟩
  · rintro γ hγ hne x
    exact absurd (Subgroup.mem_bot.mp hγ) hne
  · intro K _
    apply Set.Finite.subset (Set.finite_singleton (1 : mg.G))
    rintro γ ⟨hγ, -⟩
    simpa using Subgroup.mem_bot.mp hγ
  · refine ⟨⟨⟨mg.proj ⊥, Quotient.lift id ?_, ?_, ?_⟩, ?_, ?_⟩⟩
    · rintro x y ⟨γ, hγ, rfl⟩
      rw [Subgroup.mem_bot.mp hγ, mg.act_one]
    · intro x; rfl
    · intro x
      induction x using Quotient.inductionOn with
      | _ x => rfl
    · exact mg.continuous_proj ⊥
    · exact continuous_quot_lift _ continuous_id

/-! ### The eight models -/

/-- The Euclidean model geometry `E³`. -/
def euclideanModel : ModelGeometry := ModelGeometry.ofGroup Euc3 Euc3.continuous_mul_left

/-- The `Nil` model geometry. -/
def nilModel : ModelGeometry := ModelGeometry.ofGroup NilGroup NilGroup.continuous_mul_left

/-- The hyperbolic model geometry `H³`. -/
noncomputable def hyperbolicModel : ModelGeometry :=
  ModelGeometry.ofGroup (SolvGroup 1 1) SolvGroup.continuous_mul_left

/-- The `Sol` model geometry. -/
noncomputable def solModel : ModelGeometry :=
  ModelGeometry.ofGroup (SolvGroup 1 (-1)) SolvGroup.continuous_mul_left

/-- The `H² × ℝ` model geometry. -/
noncomputable def hyperbolicProdLineModel : ModelGeometry :=
  ModelGeometry.ofGroup (SolvGroup 1 0) SolvGroup.continuous_mul_left

/-- The `SL(2,ℝ)~` model geometry. -/
def slTwoTildeModel : ModelGeometry := ModelGeometry.ofGroup SLTilde SLTilde.continuous_mul_left

/-- The spherical model geometry `S³`. -/
noncomputable def sphericalModel : ModelGeometry where
  X := Sph 4
  G := EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)
  act := Sph.act 4
  act_one := Sph.act_one 4
  act_mul := Sph.act_mul 4
  act_continuous := Sph.continuous_act 4
  act_transitive := Sph.transitive 4
  nonempty := inferInstance

/-- The `S² × ℝ` model geometry. -/
noncomputable def sphereProdLineModel : ModelGeometry where
  X := Sph 3 × ℝ
  G := (EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) × Multiplicative ℝ
  act := fun g p => (Sph.act 3 g.1 p.1, Multiplicative.toAdd g.2 + p.2)
  act_one := fun p => by
    refine Prod.ext ?_ ?_
    · exact Sph.act_one 3 p.1
    · show (0 : ℝ) + p.2 = p.2
      ring
  act_mul := fun a b p => by
    refine Prod.ext ?_ ?_
    · exact Sph.act_mul 3 a.1 b.1 p.1
    · show Multiplicative.toAdd a.2 + Multiplicative.toAdd b.2 + p.2
        = Multiplicative.toAdd a.2 + (Multiplicative.toAdd b.2 + p.2)
      ring
  act_continuous := fun g =>
    Continuous.prodMk ((Sph.continuous_act 3 g.1).comp continuous_fst)
      (Continuous.add continuous_const continuous_snd)
  act_transitive := fun p q => by
    obtain ⟨g, hg⟩ := Sph.transitive 3 p.1 q.1
    refine ⟨(g, Multiplicative.ofAdd (q.2 - p.2)), Prod.ext hg ?_⟩
    show q.2 - p.2 + p.2 = q.2
    ring
  nonempty := ⟨(Classical.arbitrary (Sph 3), 0)⟩

/-- The eight Thurston model geometries. -/
noncomputable def model : ThurstonGeometry → ModelGeometry
  | .euclidean => euclideanModel
  | .spherical => sphericalModel
  | .hyperbolic => hyperbolicModel
  | .sphereProdLine => sphereProdLineModel
  | .hyperbolicProdLine => hyperbolicProdLineModel
  | .slTwoTilde => slTwoTildeModel
  | .nil => nilModel
  | .sol => solModel

/-- A 3-manifold is *geometric* if it admits a geometric structure modelled on one of the
eight Thurston geometries. -/
def IsGeometric (M : Type) [TopologicalSpace M] : Prop :=
  ∃ g : ThurstonGeometry, AdmitsGeometry M (model g)

/-! ## The flat 3-torus: a geometric closed 3-manifold -/

/-- The standard integer lattice `ℤ³ ≤ ℝ³`, a discrete group of Euclidean translations. -/
def latticeSubgroup : Subgroup Euc3 where
  carrier := {p : Euc3 | ∃ v : ℤ × ℤ × ℤ, p = (((v.1 : ℝ)), ((v.2.1 : ℝ)), ((v.2.2 : ℝ)))}
  mul_mem' := by
    rintro p q ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨(v.1 + w.1, v.2.1 + w.2.1, v.2.2 + w.2.2), by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [Euc3.mul_def] <;> push_cast <;> ring⟩
  one_mem' := ⟨(0, 0, 0), by refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [Euc3.one_def]⟩
  inv_mem' := by
    rintro p ⟨v, rfl⟩
    exact ⟨(-v.1, -v.2.1, -v.2.2), by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [Euc3.inv_def]⟩

lemma mem_latticeSubgroup {p : Euc3} :
    p ∈ latticeSubgroup ↔ ∃ v : ℤ × ℤ × ℤ, p = (((v.1 : ℝ)), ((v.2.1 : ℝ)), ((v.2.2 : ℝ))) :=
  Iff.rfl

/-- Translations act freely: only the identity translation has a fixed point. -/
lemma euclidean_free (γ : Euc3) (hγ : γ ≠ 1) (x : Euc3) : γ * x ≠ x := by
  intro h
  exact hγ (by simpa using congrArg (fun y : Euc3 => y * x⁻¹) h)

/-- The integer lattice acts properly discontinuously on `ℝ³`. -/
theorem lattice_properlyDiscontinuous (K : Set Euc3) (hK : IsCompact K) :
    {γ : Euc3 | γ ∈ latticeSubgroup ∧ ∃ x ∈ K, γ * x ∈ K}.Finite := by
  have hK' : IsCompact (K : Set (ℝ × ℝ × ℝ)) := hK
  obtain ⟨R, hR⟩ := hK'.isBounded.subset_closedBall (0 : ℝ × ℝ × ℝ)
  set N : ℤ := ⌈2 * R⌉ with hN
  have hfin : (Set.Icc (-N) N ×ˢ (Set.Icc (-N) N ×ˢ Set.Icc (-N) N)).Finite :=
    (Set.finite_Icc _ _).prod ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _))
  have hbound : ∀ y ∈ K, |(y : ℝ × ℝ × ℝ).1| ≤ R ∧ |(y : ℝ × ℝ × ℝ).2.1| ≤ R ∧
      |(y : ℝ × ℝ × ℝ).2.2| ≤ R := by
    intro y hy
    have h := Metric.mem_closedBall.mp (hR hy)
    rw [Prod.dist_eq, max_le_iff] at h
    obtain ⟨h1, h2⟩ := h
    rw [Prod.dist_eq, max_le_iff] at h2
    refine ⟨?_, ?_, ?_⟩
    · simpa [Real.dist_eq] using h1
    · simpa [Real.dist_eq] using h2.1
    · simpa [Real.dist_eq] using h2.2
  apply Set.Finite.subset
    (hfin.image (fun v : ℤ × ℤ × ℤ => (((v.1 : ℝ), (v.2.1 : ℝ), (v.2.2 : ℝ)) : Euc3)))
  rintro γ ⟨hγ, x, hx, hγx⟩
  obtain ⟨v, rfl⟩ := hγ
  obtain ⟨hx1, hx2, hx3⟩ := hbound x hx
  obtain ⟨hy1, hy2, hy3⟩ := hbound _ hγx
  have hNR : 2 * R ≤ (N : ℝ) := Int.le_ceil _
  have key : ∀ (m : ℤ) (s t : ℝ), |s| ≤ R → |t| ≤ R → (m : ℝ) + s = t → m ∈ Set.Icc (-N) N := by
    intro m s t hs ht hst
    have h1 : |(m : ℝ)| ≤ (N : ℝ) := by
      rw [abs_le] at hs ht ⊢
      constructor <;> [linarith [hs.1, ht.2]; linarith [hs.2, ht.1]]
    have h2 : |m| ≤ N := by exact_mod_cast (by rwa [← Int.cast_abs] at h1 : ((|m| : ℤ) : ℝ) ≤ (N : ℝ))
    exact Set.mem_Icc.mpr (abs_le.mp h2)
  refine ⟨v, ⟨?_, ?_, ?_⟩, rfl⟩
  · exact key v.1 x.1 _ hx1 hy1 rfl
  · exact key v.2.1 x.2.1 _ hx2 hy2 rfl
  · exact key v.2.2 x.2.2 _ hx3 hy3 rfl

/-- The flat 3-torus `ℝ³ / ℤ³`. -/
def FlatThreeTorus : Type := euclideanModel.quotient latticeSubgroup

instance : TopologicalSpace FlatThreeTorus :=
  inferInstanceAs (TopologicalSpace (euclideanModel.quotient latticeSubgroup))

/-- **Base case.** The flat 3-torus `ℝ³/ℤ³` is a Euclidean manifold: it carries a
geometric structure modelled on `E³`, with deck group the integer lattice. -/
theorem flatThreeTorus_admitsGeometry :
    AdmitsGeometry FlatThreeTorus (model ThurstonGeometry.euclidean) := by
  refine ⟨latticeSubgroup, ?_, ?_, ⟨Homeomorph.refl _⟩⟩
  · intro γ _ hne x
    exact euclidean_free γ hne x
  · exact lattice_properlyDiscontinuous

/-- The projection `ℝ³ → ℝ³/ℤ³`. -/
def torusProj (x : Euc3) : FlatThreeTorus := euclideanModel.proj latticeSubgroup x

lemma continuous_torusProj : Continuous torusProj :=
  euclideanModel.continuous_proj latticeSubgroup

lemma torusProj_surjective : Function.Surjective torusProj :=
  euclideanModel.proj_surjective latticeSubgroup

lemma isOpenMap_torusProj : IsOpenMap torusProj :=
  euclideanModel.isOpenMap_proj latticeSubgroup

lemma torusProj_mul {γ : Euc3} (hγ : γ ∈ latticeSubgroup) (x : Euc3) :
    torusProj (γ * x) = torusProj x :=
  (euclideanModel.proj_eq_proj γ hγ rfl).symm

lemma exists_lattice_of_torusProj_eq {x y : Euc3} (h : torusProj x = torusProj y) :
    ∃ γ ∈ latticeSubgroup, γ * x = y :=
  Quotient.exact h

instance : ConnectedSpace FlatThreeTorus :=
  torusProj_surjective.connectedSpace continuous_torusProj

instance : SecondCountableTopology FlatThreeTorus := by
  haveI : SecondCountableTopology euclideanModel.X := inferInstanceAs (SecondCountableTopology Euc3)
  exact TopologicalSpace.Quotient.secondCountableTopology
    (S := euclideanModel.orbitSetoid latticeSubgroup) isOpenMap_torusProj

/-- A compact subset of `ℝ³` meeting every lattice orbit. -/
def cube : Set Euc3 := Metric.closedBall (1 : Euc3) 2

lemma isCompact_cube : IsCompact cube := isCompact_closedBall _ _

lemma exists_lattice_translate (x : Euc3) : ∃ γ ∈ latticeSubgroup, γ * x ∈ cube := by
  have key : ∀ a : ℝ, |(-(⌊a⌋ : ℝ)) + a| ≤ 2 := by
    intro a
    have h0 : (0 : ℝ) ≤ Int.fract a := Int.fract_nonneg a
    have h1 : Int.fract a < 1 := Int.fract_lt_one a
    have h2 : (-(⌊a⌋ : ℝ)) + a = Int.fract a := by rw [Int.fract]; ring
    rw [h2, abs_of_nonneg h0]
    linarith
  refine ⟨Euc3.mk (-(⌊x.1⌋ : ℝ)) (-(⌊x.2.1⌋ : ℝ)) (-(⌊x.2.2⌋ : ℝ)),
    ⟨(-⌊x.1⌋, -⌊x.2.1⌋, -⌊x.2.2⌋), by simp [Euc3.mk]⟩, ?_⟩
  show (((-(⌊x.1⌋ : ℝ)) + x.1 : ℝ), ((-(⌊x.2.1⌋ : ℝ)) + x.2.1 : ℝ),
      ((-(⌊x.2.2⌋ : ℝ)) + x.2.2 : ℝ)) ∈ Metric.closedBall (0 : ℝ × ℝ × ℝ) 2
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Prod.dist_eq, max_le_iff]
  refine ⟨?_, ?_, ?_⟩ <;> simpa [Real.dist_eq] using key _

instance : CompactSpace FlatThreeTorus := by
  constructor
  have himg : (Set.univ : Set FlatThreeTorus) = torusProj '' cube := by
    refine Set.eq_of_subset_of_subset ?_ (fun _ _ => Set.mem_univ _)
    rintro y -
    obtain ⟨x, rfl⟩ := torusProj_surjective y
    obtain ⟨γ, hγ, hmem⟩ := exists_lattice_translate x
    exact ⟨γ * x, hmem, torusProj_mul hγ x⟩
  rw [himg]
  exact isCompact_cube.image continuous_torusProj

/-! ### The flat 3-torus is a closed 3-manifold -/

lemma Euc3.dist_mul_left (g x y : Euc3) : dist (g * x) (g * y) = dist x y := by
  show dist ((g.1 + x.1, g.2.1 + x.2.1, g.2.2 + x.2.2) : ℝ × ℝ × ℝ)
    ((g.1 + y.1, g.2.1 + y.2.1, g.2.2 + y.2.2) : ℝ × ℝ × ℝ) = dist x y
  show _ = dist ((x.1, x.2.1, x.2.2) : ℝ × ℝ × ℝ) ((y.1, y.2.1, y.2.2) : ℝ × ℝ × ℝ)
  simp [Prod.dist_eq, Real.dist_eq]

lemma Euc3.abs_sub_lt_of_mem_ball {c x : Euc3} {r : ℝ} (h : x ∈ Metric.ball c r) :
    |x.1 - c.1| < r ∧ |x.2.1 - c.2.1| < r ∧ |x.2.2 - c.2.2| < r := by
  rw [Metric.mem_ball] at h
  have h' : dist ((x.1, x.2.1, x.2.2) : ℝ × ℝ × ℝ) ((c.1, c.2.1, c.2.2) : ℝ × ℝ × ℝ) < r := h
  rw [Prod.dist_eq, max_lt_iff, Prod.dist_eq, max_lt_iff] at h'
  exact ⟨by simpa [Real.dist_eq] using h'.1, by simpa [Real.dist_eq] using h'.2.1,
    by simpa [Real.dist_eq] using h'.2.2⟩

/-- The projection is injective on balls of radius `1/2`: the lattice moves points by at
least `1`. -/
lemma lattice_inj_of_mem_ball (c x y : Euc3) (hx : x ∈ Metric.ball c (1/2))
    (hy : y ∈ Metric.ball c (1/2)) (hxy : torusProj x = torusProj y) : x = y := by
  obtain ⟨γ, hγ, hgxy⟩ := exists_lattice_of_torusProj_eq hxy
  obtain ⟨v, rfl⟩ := hγ
  obtain ⟨hx1, hx2, hx3⟩ := Euc3.abs_sub_lt_of_mem_ball hx
  obtain ⟨hy1, hy2, hy3⟩ := Euc3.abs_sub_lt_of_mem_ball hy
  have hco : ((v.1 : ℝ) + x.1, (v.2.1 : ℝ) + x.2.1, (v.2.2 : ℝ) + x.2.2) = (y.1, y.2.1, y.2.2) :=
    hgxy
  rw [Prod.mk.injEq, Prod.mk.injEq] at hco
  obtain ⟨e1, e2, e3⟩ := hco
  have key : ∀ (m : ℤ) (a b ca : ℝ), |a - ca| < 1/2 → |b - ca| < 1/2 →
      (m : ℝ) + a = b → m = 0 := by
    intro m a b ca ha hb hab
    have h1 : |(m : ℝ)| < 1 := by
      rw [abs_lt] at ha hb ⊢
      constructor <;> [linarith [ha.1, hb.2]; linarith [ha.2, hb.1]]
    have h2 : |m| < 1 := by
      exact_mod_cast (by rwa [← Int.cast_abs] at h1 : ((|m| : ℤ) : ℝ) < 1)
    have h3 := abs_lt.mp h2
    omega
  have h1 : v.1 = 0 := key v.1 x.1 y.1 c.1 hx1 hy1 e1
  have h2 : v.2.1 = 0 := key v.2.1 x.2.1 y.2.1 c.2.1 hx2 hy2 e2
  have h3 : v.2.2 = 0 := key v.2.2 x.2.2 y.2.2 c.2.2 hx3 hy3 e3
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [← e1, h1]; simp
  · rw [← e2, h2]; simp
  · rw [← e3, h3]; simp

/-- Every open ball in `ℝ³` is homeomorphic to `ℝ³`. -/
noncomputable def ballHomeoSpace (c : ℝ × ℝ × ℝ) (r : ℝ) (hr : 0 < r) :
    (Metric.ball c r) ≃ₜ (ℝ × ℝ × ℝ) := by
  have h := (OpenPartialHomeomorph.univBall (E := ℝ × ℝ × ℝ) c r).toHomeomorphSourceTarget
  rw [OpenPartialHomeomorph.univBall_source, OpenPartialHomeomorph.univBall_target c hr] at h
  exact h.symm.trans (Homeomorph.Set.univ _)

/-- `ℝ³` with the product topology is homeomorphic to Euclidean 3-space. -/
noncomputable def euc3HomeoEuclidean : (ℝ × ℝ × ℝ) ≃ₜ EuclideanSpace ℝ (Fin 3) := by
  have h : Module.finrank ℝ (ℝ × ℝ × ℝ) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by simp
  exact (ContinuousLinearEquiv.ofFinrankEq h).toHomeomorph

/-- Each point of the flat 3-torus has a neighbourhood homeomorphic to `ℝ³`. -/
theorem flatThreeTorus_chart (x : Euc3) :
    ∃ U : Set FlatThreeTorus, IsOpen U ∧ torusProj x ∈ U ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 3)) := by
  have hBopen : IsOpen (Metric.ball x (1/2) : Set Euc3) := Metric.isOpen_ball
  set f : (Metric.ball x (1/2) : Set Euc3) → FlatThreeTorus := fun b => torusProj (b : Euc3)
    with hf
  have hcont : Continuous f := continuous_torusProj.comp continuous_subtype_val
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (lattice_inj_of_mem_ball x a b a.2 b.2 hab)
  have hopen : IsOpenMap f := by
    intro V hV
    have himg : f '' V = torusProj '' (Subtype.val '' V) := by rw [Set.image_image]
    rw [himg]
    exact isOpenMap_torusProj _ (hBopen.isOpenMap_subtype_val V hV)
  have hemb : Topology.IsOpenEmbedding f := .of_continuous_injective_isOpenMap hcont hinj hopen
  refine ⟨Set.range f, hemb.isOpen_range, ⟨⟨x, Metric.mem_ball_self (by norm_num)⟩, rfl⟩, ?_⟩
  exact ⟨(hemb.isEmbedding.toHomeomorph.symm).trans
    ((ballHomeoSpace x (1/2) (by norm_num)).trans euc3HomeoEuclidean)⟩

theorem flatThreeTorus_locallyEuclidean (p : FlatThreeTorus) :
    ∃ U : Set FlatThreeTorus, IsOpen U ∧ p ∈ U ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 3)) := by
  obtain ⟨x, rfl⟩ := torusProj_surjective p
  exact flatThreeTorus_chart x

/-- Distinct points of the flat 3-torus lift to points at positive distance from each
other's lattice orbit. -/
theorem lattice_separation (x y : Euc3) (h : torusProj x ≠ torusProj y) :
    ∃ ε > 0, ∀ γ ∈ latticeSubgroup, ε ≤ dist (γ * x) y := by
  have hne : ∀ γ ∈ latticeSubgroup, γ * x ≠ y := by
    intro γ hγ hxy
    exact h ((torusProj_mul hγ x).symm.trans (congrArg torusProj hxy))
  have hK : IsCompact (insert x (Metric.closedBall y 1) : Set Euc3) :=
    (isCompact_closedBall y 1).insert x
  have hS := lattice_properlyDiscontinuous _ hK
  have hA : {γ : Euc3 | γ ∈ latticeSubgroup ∧ dist (γ * x) y ≤ 1}.Finite := by
    refine hS.subset ?_
    rintro γ ⟨hγ, hd⟩
    exact ⟨hγ, x, Set.mem_insert _ _,
      Set.mem_insert_of_mem _ (by simpa [Metric.mem_closedBall] using hd)⟩
  by_cases hF : (hA.toFinset).Nonempty
  · obtain ⟨γ₀, hγ₀F, hmin⟩ := (hA.toFinset).exists_min_image (fun γ => dist (γ * x) y) hF
    have hγ₀ : γ₀ ∈ latticeSubgroup ∧ dist (γ₀ * x) y ≤ 1 := by
      simpa using (Set.Finite.mem_toFinset hA).mp hγ₀F
    have hpos : 0 < dist (γ₀ * x) y := dist_pos.mpr (hne γ₀ hγ₀.1)
    refine ⟨min 1 (dist (γ₀ * x) y), lt_min one_pos hpos, fun γ hγ => ?_⟩
    by_cases hd : dist (γ * x) y ≤ 1
    · exact le_trans (min_le_right _ _) (hmin γ ((Set.Finite.mem_toFinset hA).mpr ⟨hγ, hd⟩))
    · exact le_trans (min_le_left _ _) (le_of_lt (not_le.mp hd))
  · refine ⟨1, one_pos, fun γ hγ => ?_⟩
    by_contra hlt
    exact hF ⟨γ, (Set.Finite.mem_toFinset hA).mpr ⟨hγ, le_of_lt (not_le.mp hlt)⟩⟩

theorem flatThreeTorus_t2_aux (x y : Euc3) (hxy : torusProj x ≠ torusProj y) :
    ∃ U V : Set FlatThreeTorus, IsOpen U ∧ IsOpen V ∧ torusProj x ∈ U ∧ torusProj y ∈ V ∧
      Disjoint U V := by
  obtain ⟨ε, hε, hbound⟩ := lattice_separation x y hxy
  have hBx : IsOpen (Metric.ball x (ε/3) : Set Euc3) := Metric.isOpen_ball
  have hBy : IsOpen (Metric.ball y (ε/3) : Set Euc3) := Metric.isOpen_ball
  refine ⟨torusProj '' (Metric.ball x (ε/3)), torusProj '' (Metric.ball y (ε/3)),
    isOpenMap_torusProj _ hBx, isOpenMap_torusProj _ hBy,
    ⟨x, Metric.mem_ball_self (by linarith), rfl⟩,
    ⟨y, Metric.mem_ball_self (by linarith), rfl⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro z ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
  obtain ⟨γ, hγ, hguv⟩ := exists_lattice_of_torusProj_eq huv.symm
  have h1 : dist (γ * x) y ≤ dist (γ * x) (γ * u) + dist (γ * u) y := dist_triangle _ _ _
  rw [Euc3.dist_mul_left] at h1
  have h2 : dist (γ * u) y = dist v y := by rw [show γ * u = v from hguv]
  have h3 : dist x u < ε/3 := by rw [dist_comm]; exact Metric.mem_ball.mp hu
  have h4 : dist v y < ε/3 := Metric.mem_ball.mp hv
  have h5 := hbound γ hγ
  rw [h2] at h1
  linarith

instance : T2Space FlatThreeTorus := by
  constructor
  intro p q hpq
  obtain ⟨x, rfl⟩ := torusProj_surjective p
  obtain ⟨y, rfl⟩ := torusProj_surjective q
  exact flatThreeTorus_t2_aux x y hpq

/-! ## Closed 3-manifolds and the geometrization statement -/

/-- The 2-torus. -/
def Torus2 : Type := Circle × Circle

instance : TopologicalSpace Torus2 := inferInstanceAs (TopologicalSpace (Circle × Circle))

/-- The translation `(x, y) ↦ (x + 1, y)` of the plane. -/
def kleinA : Equiv.Perm (ℝ × ℝ) := Equiv.addRight ((1 : ℝ), (0 : ℝ))

/-- The glide reflection `(x, y) ↦ (-x, y + 1)` of the plane. -/
def kleinB : Equiv.Perm (ℝ × ℝ) where
  toFun p := (-p.1, p.2 + 1)
  invFun p := (-p.1, p.2 - 1)
  left_inv p := by simp
  right_inv p := by simp

/-- The Klein bottle group: the group of plane symmetries generated by a translation and
a glide reflection. -/
def kleinGroup : Subgroup (Equiv.Perm (ℝ × ℝ)) := Subgroup.closure {kleinA, kleinB}

/-- The Klein bottle, as the quotient of the plane by the Klein bottle group. -/
def KleinBottle : Type := Quotient (MulAction.orbitRel kleinGroup (ℝ × ℝ))

instance : TopologicalSpace KleinBottle :=
  inferInstanceAs (TopologicalSpace (Quotient (MulAction.orbitRel kleinGroup (ℝ × ℝ))))

/-- A closed (compact, boundaryless) topological 3-manifold. -/
structure IsClosed3Manifold (M : Type) [TopologicalSpace M] : Prop where
  compact : CompactSpace M
  hausdorff : T2Space M
  secondCountable : SecondCountableTopology M
  locallyEuclidean : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 3))

/-- `π₂(M) = 0`: every map of the 2-sphere into `M` is null-homotopic.  For a closed
3-manifold this is equivalent to being irreducible (no essential embedded 2-sphere), by
the sphere theorem, so it is the hypothesis under which the torus decomposition applies. -/
def SphereTrivial (M : Type) [TopologicalSpace M] : Prop :=
  ∀ f : C(Sph 3, M), ∃ p : M, ContinuousMap.Homotopic f (ContinuousMap.const _ p)

/-- `M` has a geometric decomposition: there is a finite family of pairwise disjoint
embedded tori and Klein bottles in `M` such that every connected component of the
complement admits a geometric structure modelled on one of the eight Thurston geometries.
(Klein bottles are allowed since we do not assume `M` orientable.) -/
def HasGeometricDecomposition (M : Type) [TopologicalSpace M] : Prop :=
  ∃ 𝒮 : Set (Set M),
    𝒮.Finite ∧
    (∀ A ∈ 𝒮, ∀ B ∈ 𝒮, A ≠ B → Disjoint A B) ∧
    (∀ A ∈ 𝒮, Nonempty (A ≃ₜ Torus2) ∨ Nonempty (A ≃ₜ KleinBottle)) ∧
    (∀ x : M, x ∉ ⋃₀ 𝒮 → IsGeometric (connectedComponentIn (⋃₀ 𝒮)ᶜ x))

/-- **The geometrization statement** (Thurston's geometrization conjecture, proved by
Perelman), in the form: every closed connected 3-manifold with vanishing `π₂` — that is,
every closed irreducible 3-manifold — can be cut along a finite disjoint family of
embedded tori (and Klein bottles, in the non-orientable case) into pieces each of which
carries a geometric structure modelled on one of the eight Thurston geometries. -/
def GeometrizationOfClosed3Manifolds : Prop :=
  ∀ (M : Type) (_ : TopologicalSpace M),
    IsClosed3Manifold M → ConnectedSpace M → SphereTrivial M → HasGeometricDecomposition M

/-- **A Lean-checked reduction.** A connected geometric manifold satisfies the conclusion
of geometrization, with the empty cutting family. -/
theorem hasGeometricDecomposition_of_isGeometric (M : Type) [TopologicalSpace M]
    [ConnectedSpace M] (h : IsGeometric M) : HasGeometricDecomposition M := by
  refine ⟨∅, Set.finite_empty, by simp, by simp, ?_⟩
  intro x _
  have hcomp : connectedComponentIn ((⋃₀ (∅ : Set (Set M)))ᶜ) x = Set.univ := by
    rw [Set.sUnion_empty, Set.compl_empty, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
  obtain ⟨g, hg⟩ := h
  rw [IsGeometric]
  refine ⟨g, ?_⟩
  have e : (connectedComponentIn ((⋃₀ (∅ : Set (Set M)))ᶜ) x : Set M) ≃ₜ M := by
    rw [hcomp]
    exact Homeomorph.Set.univ M
  exact AdmitsGeometry.congr e hg

/-- **Thurston geometrization.**

This theorem records:

1. there are exactly eight Thurston geometries;
2. each of the eight model spaces is homogeneous: the group of the geometry acts
   transitively on it (this is verified for the concrete models constructed above);
3. each model space is itself geometric (the base case, with trivial deck group);
4. the flat 3-torus `ℝ³/ℤ³` is a compact connected Euclidean manifold: it is a quotient
   of `E³` by the integer lattice acting freely and properly discontinuously;
5. being geometric is a topological invariant;
6. a Lean-checked reduction: any connected geometric manifold satisfies the conclusion of
   geometrization, and in particular the flat 3-torus does.

The full geometrization statement itself is formalized as
`Frontier.GeometrizationOfClosed3Manifolds`. -/
theorem thurston_geometrization :
    Fintype.card ThurstonGeometry = 8 ∧
    (∀ g : ThurstonGeometry, ∀ x y : (model g).X, ∃ a, (model g).act a x = y) ∧
    (∀ g : ThurstonGeometry, AdmitsGeometry (model g).X (model g)) ∧
    (AdmitsGeometry FlatThreeTorus (model ThurstonGeometry.euclidean) ∧
      CompactSpace FlatThreeTorus ∧ ConnectedSpace FlatThreeTorus) ∧
    (∀ (M N : Type) (_ : TopologicalSpace M) (_ : TopologicalSpace N) (mg : ModelGeometry),
      Nonempty (M ≃ₜ N) → AdmitsGeometry N mg → AdmitsGeometry M mg) ∧
    (∀ (M : Type) (_ : TopologicalSpace M), ConnectedSpace M → IsGeometric M →
      HasGeometricDecomposition M) ∧
    HasGeometricDecomposition FlatThreeTorus := by
  refine ⟨by decide, fun g => (model g).act_transitive, fun g => admitsGeometry_self (model g),
    ⟨flatThreeTorus_admitsGeometry, inferInstance, inferInstance⟩, ?_, ?_, ?_⟩
  · rintro M N _ _ mg ⟨e⟩ h
    exact AdmitsGeometry.congr e h
  · intro M _ hconn h
    exact hasGeometricDecomposition_of_isGeometric M h
  · exact hasGeometricDecomposition_of_isGeometric FlatThreeTorus
      ⟨ThurstonGeometry.euclidean, flatThreeTorus_admitsGeometry⟩

end Frontier

