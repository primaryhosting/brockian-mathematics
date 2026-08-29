/-
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The Jones polynomial of a link is constructed from the *Kauffman bracket*: each crossing of a
link diagram is resolved by the skein relation

  `⟨crossing⟩ = A ⬝ ⟨0-smoothing⟩ + A⁻¹ ⬝ ⟨∞-smoothing⟩`,

a free closed loop contributes the *loop value* `δ = -A² - A⁻²`, and the resulting bracket is
normalised by the writhe, `V(L) = (-A³)^(-w(L)) ⟨L⟩`.

Well-definedness of this construction is exactly the statement that the above data is invariant
under the three Reidemeister moves.  Passing to the *skein-algebraic* (Temperley–Lieb) picture,
which is the standard way Kauffman's argument is organised, the three moves become three purely
algebraic identities in the Temperley–Lieb algebra over the coefficient ring:

* **R2**: the resolved crossing `σ = A·1 + A⁻¹·e` is invertible, with inverse the resolved
  *opposite* crossing `σ⁻¹ = A⁻¹·1 + A·e`.
* **R3**: the resolved crossings satisfy the braid relation `σ₁σ₂σ₁ = σ₂σ₁σ₂`.
* **R1**: adding a kink multiplies the bracket by the unit `-A³`; since a kink also changes the
  writhe by `1`, the writhe-normalised bracket is unchanged.

This file develops that algebra over an arbitrary commutative coefficient ring `R` with a
distinguished invertible element `A`, in an arbitrary `R`-algebra `T` carrying elements `eᵢ`
subject to the Temperley–Lieb relations.  The main theorem `Frontier.jones_polynomial_invariant`
collects the three statements.  A concrete non-degenerate model (`Frontier.TLModel`) over the ring
of Laurent polynomials `ℤ[A, A⁻¹]` is provided at the end, so the hypotheses are known to be
satisfiable by genuinely distinct, nonzero elements.
-/

namespace Frontier

section Kauffman

variable {R : Type*} [CommRing R] {T : Type*} [Ring T] [Algebra R T]

/-- The Kauffman loop value `δ = -A² - A⁻²`, written using an explicit inverse `Ainv` of `A`.
It is the scalar by which the bracket gets multiplied when a free closed loop is added. -/

theorem jones_polynomial_invariant_model :
    (kauffmanCrossing kA kAinv tlE₁ * kauffmanCrossing kAinv kA tlE₁ = 1 ∧
      kauffmanCrossing kAinv kA tlE₁ * kauffmanCrossing kA kAinv tlE₁ = 1) ∧
    (kauffmanCrossing kA kAinv tlE₁ * kauffmanCrossing kA kAinv tlE₂ * kauffmanCrossing kA kAinv tlE₁
      = kauffmanCrossing kA kAinv tlE₂ * kauffmanCrossing kA kAinv tlE₁ *
          kauffmanCrossing kA kAinv tlE₂) ∧
    (∃ u : KauffmanRingˣ, (u : KauffmanRing) = -kA ^ 3 ∧
      (∀ x : TLModel, kA • (loopValue kA kAinv • x) + kAinv • x = (u : KauffmanRing) • x) ∧
      (∀ (w : ℤ) (b : KauffmanRing),
          normalizedBracket u (w + 1) ((u : KauffmanRing) * b) = normalizedBracket u w b) ∧
      (∀ (w : ℤ) (b : KauffmanRing),
          normalizedBracket u (w - 1) (((u⁻¹ : KauffmanRingˣ) : KauffmanRing) * b)
            = normalizedBracket u w b)) :=
  jones_polynomial_invariant kA kAinv kA_mul_kAinv tlE₁ tlE₂ tlE₁_sq tlE₂_sq
    tlE₁_tlE₂_tlE₁ tlE₂_tlE₁_tlE₂

end Model

end Frontier

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

