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
