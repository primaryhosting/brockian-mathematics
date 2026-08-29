import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede every other syntactic item, including module
-- doc comments, so the mandated header block appears immediately after the import.)

/-!
## The Hodge conjecture

Let `X` be a connected smooth complex projective variety of complex dimension `n`.
Its rational cohomology `Hⁱ(X, ℚ)` is a finite dimensional `ℚ`-vector space, and its
complexification `Hⁱ(X, ℂ) = ℂ ⊗_ℚ Hⁱ(X, ℚ)` carries the Hodge decomposition

`Hⁱ(X, ℂ) = ⨁_{p + q = i} H^{p,q}(X)`.

A *Hodge class* of codimension `k` is a class `v ∈ H^{2k}(X, ℚ)` whose complexification
lies in the `(k, k)`-piece.  Every algebraic cycle of codimension `k` has a cycle class in
`H^{2k}(X, ℚ)`, and these classes are Hodge classes; the **Hodge conjecture** asserts the
converse: every Hodge class of codimension `k` is a rational linear combination of classes
of algebraic cycles.

In this file the geometric input is packaged into the structure `Frontier.HodgeVariety`,
whose fields record exactly the pieces of structure used in the statement:

* the graded rational cohomology `H i`;
* the Hodge decomposition of each complexified `H i`, encoded by the family of projectors
  onto the pieces `H^{p, i - p}` (a decomposition of a vector space into a direct sum of
  subspaces is the same thing as a complete family of orthogonal idempotents);
* the subspaces `alg k ≤ H (2k)` spanned by classes of codimension-`k` algebraic cycles,
  together with the (elementary) fact that algebraic classes are of type `(k, k)`;
* the fundamental class of `X` spanning `H⁰` and the class of a point spanning `H^{2n}`,
  both algebraic;
* the hard Lefschetz isomorphisms `L^{n - 2k} : H^{2k}(X, ℚ) ≃ H^{2(n-k)}(X, ℚ)`, which
  are given by cup product with a hyperplane class and therefore send algebraic classes to
  algebraic classes and shift the Hodge type by `(n - 2k, n - 2k)`.

`Frontier.HodgeConjecture X` is then the statement of the conjecture for `X`, and the main
theorem `Frontier.hodge_statement` proves, for every such `X`:

* the base case in codimension `0` (Hodge classes in `H⁰` are multiples of the fundamental
  class, hence algebraic);
* the base case in codimension `n` (Hodge classes in `H^{2n}` are multiples of the class of
  a point, hence algebraic);
* a Lean-checked reduction: the Hodge conjecture for `X` follows from its validity in
  codimensions `k` with `2k ≤ n`, i.e. it suffices to treat the range below the middle
  dimension.
-/

namespace Frontier

open scoped TensorProduct

/-- A decomposition of a complex vector space `E` into `n + 1` pieces, encoded by the
family of projectors onto the pieces.  In the application `E = Hⁿ(X, ℂ)` and `proj p` is
the projector onto the Hodge piece `H^{p, n - p}(X)`. -/
structure HodgeDecomposition (E : Type*) [AddCommGroup E] [Module ℂ E] (n : ℕ) where
  /-- `proj p` is the projection onto the `(p, n - p)` piece. -/
  proj : ℕ → E →ₗ[ℂ] E
  /-- Each `proj p` is idempotent. -/
  idem : ∀ p, (proj p).comp (proj p) = proj p
  /-- Distinct pieces are transverse. -/
  orth : ∀ p q, p ≠ q → (proj p).comp (proj q) = 0
  /-- There are no pieces of bidegree `(p, n - p)` with `p > n`. -/
  vanish : ∀ p, n < p → proj p = 0
  /-- The pieces span: the projectors sum to the identity. -/
  total : ∀ x : E, ∑ p ∈ Finset.range (n + 1), proj p x = x

namespace HodgeDecomposition

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {n : ℕ}

/-- The `(p, n - p)`-piece of the decomposition. -/
def piece (d : HodgeDecomposition E n) (p : ℕ) : Submodule ℂ E :=
  LinearMap.range (d.proj p)

lemma mem_piece_iff (d : HodgeDecomposition E n) (p : ℕ) (x : E) :
    x ∈ d.piece p ↔ d.proj p x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact congrArg (fun f => f y) (d.idem p)
  · intro h; exact ⟨x, h⟩

/-- The pieces span the whole space. -/
lemma iSup_piece_eq_top (d : HodgeDecomposition E n) :
    ⨆ p : Fin (n + 1), d.piece p = ⊤ := by
  refine top_unique fun x _ => ?_
  have hx : x = ∑ p ∈ Finset.range (n + 1), d.proj p x := (d.total x).symm
  rw [hx, ← Fin.sum_univ_eq_sum_range (fun p => d.proj p x)]
  refine Submodule.sum_mem _ fun p _ => ?_
  exact Submodule.mem_iSup_of_mem p ⟨x, rfl⟩

/-- Distinct pieces intersect trivially: the projector `proj q` kills every piece `p ≠ q`. -/
lemma proj_eq_zero_of_mem_piece (d : HodgeDecomposition E n) {p q : ℕ} (hpq : p ≠ q)
    {x : E} (hx : x ∈ d.piece p) : d.proj q x = 0 := by
  rw [d.mem_piece_iff] at hx
  have := congrArg (fun f => f x) (d.orth q p hpq.symm)
  simpa [hx] using this

/-- The pieces are independent. -/
lemma iSupIndep_piece (d : HodgeDecomposition E n) :
    iSupIndep (fun p : Fin (n + 1) => d.piece p) := by
  intro p
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j : Fin (n + 1)) (_ : j ≠ p), d.piece j) ≤ LinearMap.ker (d.proj p) := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    rintro y hy
    exact d.proj_eq_zero_of_mem_piece (q := p) (by simpa [Fin.val_eq_val] using hj) hy
  have h0 : d.proj p x = 0 := hle hx'
  rw [d.mem_piece_iff] at hx
  rw [← hx, h0]

/-- The projectors do encode a genuine direct sum decomposition
`E = ⨁_{p = 0}^{n} H^{p, n - p}`, which is the content of the Hodge decomposition. -/
lemma isInternal_piece (d : HodgeDecomposition E n) :
    DirectSum.IsInternal (fun p : Fin (n + 1) => d.piece p) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨d.iSupIndep_piece, d.iSup_piece_eq_top⟩

end HodgeDecomposition

/-- The rational classes whose complexification lies in the `p`-th piece. -/
noncomputable def hodgeClassesOf {A : Type*} [AddCommGroup A] [Module ℚ A] {a : ℕ}
    (d : HodgeDecomposition (ℂ ⊗[ℚ] A) a) (p : ℕ) : Submodule ℚ A :=
  LinearMap.ker (((d.proj p - LinearMap.id).restrictScalars ℚ).comp
    (TensorProduct.mk ℚ ℂ A 1))

lemma mem_hodgeClassesOf {A : Type*} [AddCommGroup A] [Module ℚ A] {a : ℕ}
    (d : HodgeDecomposition (ℂ ⊗[ℚ] A) a) (p : ℕ) (v : A) :
    v ∈ hodgeClassesOf d p ↔ d.proj p ((1 : ℂ) ⊗ₜ[ℚ] v) = (1 : ℂ) ⊗ₜ[ℚ] v := by
  simp [hodgeClassesOf, LinearMap.mem_ker, sub_eq_zero]

/-- The geometric input for the Hodge conjecture: the cohomology of a connected smooth
complex projective variety of dimension `dim`, with its Hodge decomposition, its subspaces
of algebraic classes, and the hard Lefschetz isomorphisms. -/
structure HodgeVariety where
  /-- The complex dimension of the variety. -/
  dim : ℕ
  /-- The rational cohomology groups `Hⁱ(X, ℚ)`. -/
  H : ℕ → Type
  [instAG : ∀ i, AddCommGroup (H i)]
  [instMod : ∀ i, Module ℚ (H i)]
  /-- The Hodge decomposition of `Hⁱ(X, ℂ) = ℂ ⊗ Hⁱ(X, ℚ)`. -/
  hodge : ∀ i, HodgeDecomposition (ℂ ⊗[ℚ] H i) i
  /-- The subspace of `H^{2k}(X, ℚ)` spanned by the classes of codimension-`k`
  algebraic cycles. -/
  alg : ∀ k, Submodule ℚ (H (2 * k))
  /-- Algebraic classes are Hodge classes. -/
  alg_hodge : ∀ k, ∀ v ∈ alg k,
    (hodge (2 * k)).proj k ((1 : ℂ) ⊗ₜ[ℚ] v) = (1 : ℂ) ⊗ₜ[ℚ] v
  /-- The fundamental class of the (connected) variety. -/
  fundamentalClass : H 0
  /-- `H⁰(X, ℚ)` is spanned by the fundamental class. -/
  H_zero_spanned : ∀ v : H 0, ∃ c : ℚ, v = c • fundamentalClass
  /-- The fundamental class is the class of the algebraic cycle `X` itself. -/
  fundamentalClass_alg : fundamentalClass ∈ alg 0
  /-- The class of a point. -/
  pointClass : H (2 * dim)
  /-- `H^{2n}(X, ℚ)` is spanned by the class of a point. -/
  H_top_spanned : ∀ v : H (2 * dim), ∃ c : ℚ, v = c • pointClass
  /-- The class of a point is algebraic. -/
  pointClass_alg : pointClass ∈ alg dim
  /-- Hard Lefschetz: for `2k ≤ n`, cup product with the `(n - 2k)`-th power of a
  hyperplane class is an isomorphism `H^{2k}(X, ℚ) ≃ H^{2(n-k)}(X, ℚ)`; being given by an
  algebraic correspondence it carries algebraic classes to algebraic classes, and it shifts
  the Hodge type by `(n - 2k, n - 2k)`. -/
  lefschetz : ∀ k, 2 * k ≤ dim → ∃ f : H (2 * k) →ₗ[ℚ] H (2 * (dim - k)),
    Function.Bijective f ∧
    (∀ v ∈ alg k, f v ∈ alg (dim - k)) ∧
    (hodge (2 * (dim - k))).proj (dim - k) ∘ₗ f.baseChange ℂ
      = (f.baseChange ℂ) ∘ₗ (hodge (2 * k)).proj k

attribute [instance] HodgeVariety.instAG HodgeVariety.instMod

namespace HodgeVariety

variable (X : HodgeVariety)

/-- The space of Hodge classes of codimension `k`: rational classes in `H^{2k}(X, ℚ)`
whose complexification is of type `(k, k)`. -/
noncomputable def hodgeClasses (k : ℕ) : Submodule ℚ (X.H (2 * k)) :=
  hodgeClassesOf (X.hodge (2 * k)) k

lemma mem_hodgeClasses (k : ℕ) (v : X.H (2 * k)) :
    v ∈ X.hodgeClasses k ↔
      (X.hodge (2 * k)).proj k ((1 : ℂ) ⊗ₜ[ℚ] v) = (1 : ℂ) ⊗ₜ[ℚ] v :=
  mem_hodgeClassesOf _ _ _

/-- Algebraic classes are Hodge classes (the easy inclusion). -/
lemma alg_le_hodgeClasses (k : ℕ) : X.alg k ≤ X.hodgeClasses k := fun v hv =>
  (X.mem_hodgeClasses k v).2 (X.alg_hodge k v hv)

end HodgeVariety

/-- **The Hodge conjecture** for a smooth complex projective variety `X`: in every
codimension `k` (at most the dimension of `X`), every Hodge class is a rational linear
combination of classes of algebraic cycles. -/
def HodgeConjecture (X : HodgeVariety) : Prop :=
  ∀ k ≤ X.dim, X.hodgeClasses k ≤ X.alg k

/-- Transfer of the Hodge conjecture along a rational isomorphism which shifts the Hodge
type and preserves algebraicity. -/
theorem hodge_transfer {A B : Type} [AddCommGroup A] [Module ℚ A] [AddCommGroup B]
    [Module ℚ B] {a b p q : ℕ} (dA : HodgeDecomposition (ℂ ⊗[ℚ] A) a)
    (dB : HodgeDecomposition (ℂ ⊗[ℚ] B) b) (f : A →ₗ[ℚ] B) (hbij : Function.Bijective f)
    (hcomm : dB.proj q ∘ₗ f.baseChange ℂ = (f.baseChange ℂ) ∘ₗ dA.proj p)
    {algA : Submodule ℚ A} {algB : Submodule ℚ B} (hmap : ∀ v ∈ algA, f v ∈ algB)
    (hA : hodgeClassesOf dA p ≤ algA) :
    hodgeClassesOf dB q ≤ algB := by
  -- the complexification of `f` is injective
  have hinj : Function.Injective (f.baseChange ℂ) := by
    set e : A ≃ₗ[ℚ] B := LinearEquiv.ofBijective f hbij with he
    have hgf : (e.symm : B →ₗ[ℚ] A) ∘ₗ f = LinearMap.id := by
      ext x
      simp [he]
    have : (LinearMap.baseChange ℂ (e.symm : B →ₗ[ℚ] A)) ∘ₗ
        (LinearMap.baseChange ℂ f) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hgf, LinearMap.baseChange_id]
    exact Function.LeftInverse.injective (g := LinearMap.baseChange ℂ (e.symm : B →ₗ[ℚ] A))
      fun x => congrArg (fun g => g x) this
  intro w hw
  rw [mem_hodgeClassesOf] at hw
  obtain ⟨v, rfl⟩ := hbij.surjective w
  refine hmap v (hA ?_)
  rw [mem_hodgeClassesOf]
  apply hinj
  have h1 : (f.baseChange ℂ) ((1 : ℂ) ⊗ₜ[ℚ] v) = (1 : ℂ) ⊗ₜ[ℚ] f v :=
    LinearMap.baseChange_tmul _ _ _
  have h2 := congrArg (fun g => g ((1 : ℂ) ⊗ₜ[ℚ] v)) hcomm
  simp only [LinearMap.coe_comp, Function.comp_apply] at h2
  rw [h1]
  rw [h1] at h2
  rw [← h2, hw]

/-- The main statement.  For every smooth connected complex projective variety `X`
(packaged as a `HodgeVariety`):

1. the Hodge conjecture holds in codimension `0`;
2. the Hodge conjecture holds in codimension `n = dim X`;
3. the Hodge conjecture for `X` reduces to the range `2k ≤ n`: if every Hodge class of
   codimension `k` with `2k ≤ n` is algebraic, then the full Hodge conjecture holds
   for `X`. -/
theorem hodge_statement (X : HodgeVariety) :
    X.hodgeClasses 0 ≤ X.alg 0 ∧
    X.hodgeClasses X.dim ≤ X.alg X.dim ∧
    ((∀ k, 2 * k ≤ X.dim → X.hodgeClasses k ≤ X.alg k) → HodgeConjecture X) := by
  refine ⟨?_, ?_, ?_⟩
  · -- codimension 0: `H⁰` is spanned by the fundamental class, which is algebraic
    intro v _
    obtain ⟨c, rfl⟩ := X.H_zero_spanned v
    exact Submodule.smul_mem _ _ X.fundamentalClass_alg
  · -- codimension `n`: `H^{2n}` is spanned by the class of a point, which is algebraic
    intro v _
    obtain ⟨c, rfl⟩ := X.H_top_spanned v
    exact Submodule.smul_mem _ _ X.pointClass_alg
  · -- reduction to the range below the middle dimension, via hard Lefschetz
    intro hlow k hk
    by_cases h : 2 * k ≤ X.dim
    · exact hlow k h
    · -- write `k = n - j` with `2j ≤ n`
      set j := X.dim - k with hj
      have hjk : X.dim - j = k := by omega
      have h2j : 2 * j ≤ X.dim := by omega
      obtain ⟨f, hbij, hmapalg, hcomm⟩ := X.lefschetz j h2j
      rw [← hjk]
      exact hodge_transfer _ _ f hbij hcomm hmapalg (hlow j h2j)

end Frontier

