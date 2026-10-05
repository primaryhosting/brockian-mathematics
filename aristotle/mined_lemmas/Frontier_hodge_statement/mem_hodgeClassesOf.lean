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
