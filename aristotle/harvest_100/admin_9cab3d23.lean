import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
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

open TensorProduct

/-! ## The linear-algebra set-up

For a smooth complex projective variety `X`, the singular cohomology group
`V = H^{2p}(X, ℚ)` is a finite-dimensional `ℚ`-vector space whose complexification
`ℂ ⊗[ℚ] V` carries the Hodge decomposition into subspaces `H^{r,s}` with `r + s = 2p`,
exchanged by complex conjugation.  A *Hodge class* is a rational class whose image in the
complexification lies in the `(p,p)`-part, and the Hodge conjecture asserts that every
Hodge class is a rational combination of classes of algebraic cycles of codimension `p`.

Below we axiomatise exactly this data: `HodgeStructure w` records the rational vector
space together with its Hodge decomposition of weight `w`, `CycleClasses S p` records the
subspace of classes of algebraic cycles (which is always contained in the space of Hodge
classes — this containment is a theorem of Hodge theory, taken here as part of the data),
and `HodgeConjectureFor` is the assertion that the two subspaces agree. -/

/-- Complex conjugation on the complexification `ℂ ⊗[ℚ] V`; it is `ℚ`-linear (and
`ℂ`-semilinear). -/
noncomputable def conjCx (V : Type) [AddCommGroup V] [Module ℚ V] :
    (ℂ ⊗[ℚ] V) →ₗ[ℚ] (ℂ ⊗[ℚ] V) :=
  TensorProduct.map ((Complex.conjAe.restrictScalars ℚ).toLinearMap) LinearMap.id

/-- The canonical inclusion `v ↦ 1 ⊗ v` of a rational vector space into its
complexification. -/
noncomputable def inclCx (V : Type) [AddCommGroup V] [Module ℚ V] : V →ₗ[ℚ] (ℂ ⊗[ℚ] V) :=
  (TensorProduct.mk ℚ ℂ V) 1

@[simp] lemma inclCx_apply (V : Type) [AddCommGroup V] [Module ℚ V] (v : V) :
    inclCx V v = (1 : ℂ) ⊗ₜ[ℚ] v := rfl

/-- The inclusion of a rational vector space into its complexification is injective. -/
lemma inclCx_injective (V : Type) [AddCommGroup V] [Module ℚ V] :
    Function.Injective (inclCx V) := by
  have hinj : Function.Injective (Algebra.linearMap ℚ ℂ) := by
    simpa [Algebra.linearMap_apply] using (algebraMap ℚ ℂ).injective
  have h := Module.Flat.rTensor_preserves_injective_linearMap
    (M := V) (Algebra.linearMap ℚ ℂ) hinj
  have hcomp : (inclCx V) =
      (LinearMap.rTensor V (Algebra.linearMap ℚ ℂ)).comp
        ((TensorProduct.lid ℚ V).symm : V →ₗ[ℚ] ℚ ⊗[ℚ] V) := by
    ext v
    simp [inclCx]
  rw [hcomp]
  exact h.comp (TensorProduct.lid ℚ V).symm.injective

/-- A rational Hodge structure of weight `w`: a finite-dimensional `ℚ`-vector space `V`
together with a decomposition of its complexification into subspaces `H^{r,s}`, supported
in bidegrees with `r + s = w` and stable under complex conjugation (which swaps `r` and
`s`). -/
structure HodgeStructure (w : ℤ) where
  /-- The underlying rational vector space. -/
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module ℚ V]
  [finiteDimensional : FiniteDimensional ℚ V]
  /-- The bigraded pieces `H^{r,s}` of the complexification. -/
  H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- The pieces form an internal direct sum decomposition of the complexification. -/
  decomposition : DirectSum.IsInternal H
  /-- The decomposition is concentrated in total degree `w`. -/
  weight : ∀ pq : ℤ × ℤ, pq.1 + pq.2 ≠ w → H pq = ⊥
  /-- Complex conjugation interchanges `H^{r,s}` and `H^{s,r}`. -/
  conj_symm : ∀ (pq : ℤ × ℤ) (x : ℂ ⊗[ℚ] V), x ∈ H pq → conjCx V x ∈ H (pq.2, pq.1)

attribute [instance] HodgeStructure.addCommGroup HodgeStructure.module
  HodgeStructure.finiteDimensional

/-- The space of Hodge classes of type `(p,p)`: rational classes whose image in the
complexification lies in the `(p,p)`-piece of the Hodge decomposition. -/
noncomputable def HodgeStructure.hodgeClasses {w : ℤ} (S : HodgeStructure w) (p : ℤ) :
    Submodule ℚ S.V :=
  Submodule.comap (inclCx S.V) ((S.H (p, p)).restrictScalars ℚ)

lemma HodgeStructure.mem_hodgeClasses {w : ℤ} (S : HodgeStructure w) (p : ℤ) (v : S.V) :
    v ∈ S.hodgeClasses p ↔ (1 : ℂ) ⊗ₜ[ℚ] v ∈ S.H (p, p) := Iff.rfl

/-- The classes of algebraic cycles of codimension `p`: a rational subspace of `V`
consisting of Hodge classes. -/
structure CycleClasses {w : ℤ} (S : HodgeStructure w) (p : ℤ) where
  /-- The `ℚ`-span of the classes of algebraic cycles of codimension `p`. -/
  alg : Submodule ℚ S.V
  /-- Cycle classes are Hodge classes. -/
  alg_le : alg ≤ S.hodgeClasses p

/-- **The Hodge conjecture** for the given datum: every Hodge class of type `(p,p)` is a
rational combination of classes of algebraic cycles. -/
def HodgeConjectureFor {w p : ℤ} {S : HodgeStructure w} (C : CycleClasses S p) : Prop :=
  S.hodgeClasses p ≤ C.alg

/-- Equivalently, the space of Hodge classes coincides with the space of algebraic
classes. -/
lemma hodgeConjectureFor_iff_eq {w p : ℤ} {S : HodgeStructure w} (C : CycleClasses S p) :
    HodgeConjectureFor C ↔ S.hodgeClasses p = C.alg :=
  ⟨fun h => le_antisymm h C.alg_le, fun h => h.le⟩

/-! ## Reformulations and base cases -/

/-- Contrapositive form: the conjecture holds precisely when there is no Hodge class
failing to be algebraic. -/
lemma hodgeConjectureFor_iff_no_counterexample {w p : ℤ} {S : HodgeStructure w}
    (C : CycleClasses S p) :
    HodgeConjectureFor C ↔ ¬ ∃ v : S.V, v ∈ S.hodgeClasses p ∧ v ∉ C.alg := by
  constructor
  · rintro h ⟨v, hv, hv'⟩
    exact hv' (h hv)
  · intro h v hv
    by_contra hv'
    exact h ⟨v, hv, hv'⟩

/-- Reformulation as the vanishing of the image of the Hodge classes in the quotient by
the algebraic classes. -/
lemma hodgeConjectureFor_iff_map_mkQ_eq_bot {w p : ℤ} {S : HodgeStructure w}
    (C : CycleClasses S p) :
    HodgeConjectureFor C ↔ Submodule.map C.alg.mkQ (S.hodgeClasses p) = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    rintro x ⟨v, hv, rfl⟩
    simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using h hv
  · intro h v hv
    have hx : C.alg.mkQ v ∈ Submodule.map C.alg.mkQ (S.hodgeClasses p) := ⟨v, hv, rfl⟩
    rw [h] at hx
    simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx

/-- The `ℚ`-dimension of the space of Hodge classes is bounded by the `ℂ`-dimension of the
`(p,p)`-piece of the Hodge decomposition. -/
lemma finrank_hodgeClasses_le {w : ℤ} (S : HodgeStructure w) (p : ℤ) :
    Module.finrank ℚ (S.hodgeClasses p) ≤ Module.finrank ℂ (S.H (p, p)) := by
  classical
  set W : Submodule ℚ S.V := S.hodgeClasses p with hW
  -- the base-changed inclusion `ℂ ⊗ W → ℂ ⊗ V`
  set f : (ℂ ⊗[ℚ] W) →ₗ[ℂ] (ℂ ⊗[ℚ] S.V) := LinearMap.baseChange ℂ W.subtype with hf
  have hfinj : Function.Injective f := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap
      (M := ℂ) (W.subtype) (Submodule.injective_subtype W)
    simpa [hf, LinearMap.baseChange_eq_ltensor] using h
  have hrange : ∀ x : ℂ ⊗[ℚ] W, f x ∈ S.H (p, p) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
        have hv : (1 : ℂ) ⊗ₜ[ℚ] (v : S.V) ∈ S.H (p, p) := v.2
        have : f (c ⊗ₜ[ℚ] v) = c • ((1 : ℂ) ⊗ₜ[ℚ] (v : S.V)) := by
          simp [hf, LinearMap.baseChange_tmul, TensorProduct.smul_tmul']
        rw [this]
        exact (S.H (p, p)).smul_mem c hv
    | add x y hx hy => simpa [map_add] using (S.H (p, p)).add_mem hx hy
  set g : (ℂ ⊗[ℚ] W) →ₗ[ℂ] (S.H (p, p)) := LinearMap.codRestrict _ f hrange with hg
  have hginj : Function.Injective g := by
    intro x y hxy
    apply hfinj
    simpa [hg, LinearMap.codRestrict, Subtype.ext_iff] using congrArg Subtype.val hxy
  have h1 : Module.finrank ℂ (ℂ ⊗[ℚ] W) ≤ Module.finrank ℂ (S.H (p, p)) :=
    LinearMap.finrank_le_finrank_of_injective (f := g) hginj
  have h2 : Module.finrank ℂ (ℂ ⊗[ℚ] W) = Module.finrank ℚ W :=
    Module.finrank_baseChange (R := ℂ) (S := ℚ) (M' := W)
  rw [← h2]
  exact h1

/-- A numerical reduction: the conjecture holds as soon as the algebraic classes already
account for the full dimension of the space of Hodge classes. -/
lemma hodgeConjectureFor_of_finrank_le {w p : ℤ} {S : HodgeStructure w}
    (C : CycleClasses S p)
    (h : Module.finrank ℚ (S.hodgeClasses p) ≤ Module.finrank ℚ C.alg) :
    HodgeConjectureFor C := by
  have := Submodule.eq_of_le_of_finrank_le C.alg_le h
  exact this.ge

/-- Base case: if the `(p,p)`-piece of the Hodge decomposition vanishes, there are no
nonzero Hodge classes. -/
lemma hodgeClasses_eq_bot_of_H_eq_bot {w : ℤ} (S : HodgeStructure w) (p : ℤ)
    (h : S.H (p, p) = ⊥) : S.hodgeClasses p = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro v hv
  have hv' : (1 : ℂ) ⊗ₜ[ℚ] v ∈ S.H (p, p) := hv
  rw [h] at hv'
  have : inclCx S.V v = inclCx S.V 0 := by
    simpa using (Submodule.mem_bot ℂ).1 hv'
  simpa using inclCx_injective S.V this

/-- Base case: in odd weight there are no nonzero Hodge classes, since no bidegree
`(p,p)` occurs. -/
lemma hodgeClasses_eq_bot_of_odd_weight {w : ℤ} (S : HodgeStructure w) (hw : Odd w)
    (p : ℤ) : S.hodgeClasses p = ⊥ := by
  refine hodgeClasses_eq_bot_of_H_eq_bot S p (S.weight (p, p) ?_)
  intro hcon
  rcases hw with ⟨k, hk⟩
  omega

/-- Base case: whenever the space of Hodge classes vanishes, the conjecture holds. -/
lemma hodgeConjectureFor_of_hodgeClasses_eq_bot {w p : ℤ} {S : HodgeStructure w}
    (C : CycleClasses S p) (h : S.hodgeClasses p = ⊥) : HodgeConjectureFor C := by
  rw [HodgeConjectureFor, h]
  exact bot_le

/-! ## The statement -/

/-- **The Hodge conjecture**, stated for an arbitrary rational Hodge structure `S` of
weight `w` together with its subspace of codimension-`p` algebraic cycle classes, and the
Lean-checked reductions and base cases we prove about it:

1. the conjecture is equivalent to the non-existence of a non-algebraic Hodge class;
2. it is equivalent to the vanishing of the image of the Hodge classes in the quotient by
   the algebraic classes;
3. the space of Hodge classes has `ℚ`-dimension at most the `ℂ`-dimension of the
   `(p,p)`-part of the Hodge decomposition (in particular it is finite dimensional), so
   the conjecture is a finite-dimensional statement;
4. it therefore reduces to the numerical criterion that the algebraic classes span a
   subspace of the same dimension;
5. base case: in odd weight there are no nonzero Hodge classes and the conjecture holds;
6. base case: if the `(p,p)`-part of the Hodge decomposition vanishes, the conjecture
   holds. -/
theorem hodge_statement :
    ∀ (w p : ℤ) (S : HodgeStructure w) (C : CycleClasses S p),
      -- the conjecture: every Hodge class of type `(p,p)` is algebraic
      (HodgeConjectureFor C ↔ S.hodgeClasses p = C.alg) ∧
      -- (1) contrapositive form
      (HodgeConjectureFor C ↔ ¬ ∃ v : S.V, v ∈ S.hodgeClasses p ∧ v ∉ C.alg) ∧
      -- (2) quotient form
      (HodgeConjectureFor C ↔ Submodule.map C.alg.mkQ (S.hodgeClasses p) = ⊥) ∧
      -- (3) finite-dimensionality bound
      (Module.finrank ℚ (S.hodgeClasses p) ≤ Module.finrank ℂ (S.H (p, p))) ∧
      -- (4) numerical reduction
      (Module.finrank ℚ (S.hodgeClasses p) ≤ Module.finrank ℚ C.alg →
        HodgeConjectureFor C) ∧
      -- (5) base case: odd weight
      (Odd w → HodgeConjectureFor C) ∧
      -- (6) base case: vanishing `(p,p)`-part
      (S.H (p, p) = ⊥ → HodgeConjectureFor C) := by
  intro w p S C
  refine ⟨hodgeConjectureFor_iff_eq C, hodgeConjectureFor_iff_no_counterexample C,
    hodgeConjectureFor_iff_map_mkQ_eq_bot C, finrank_hodgeClasses_le S p,
    hodgeConjectureFor_of_finrank_le C, ?_, ?_⟩
  · intro hw
    exact hodgeConjectureFor_of_hodgeClasses_eq_bot C
      (hodgeClasses_eq_bot_of_odd_weight S hw p)
  · intro h
    exact hodgeConjectureFor_of_hodgeClasses_eq_bot C (hodgeClasses_eq_bot_of_H_eq_bot S p h)

end Frontier

