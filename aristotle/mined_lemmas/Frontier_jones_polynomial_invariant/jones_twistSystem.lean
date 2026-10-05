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

set_option grind.warning false

namespace Frontier

open LaurentPolynomial

/-! ## The coefficient ring

The Kauffman bracket takes values in the ring of Laurent polynomials `ℤ[A, A⁻¹]`,
which we realise as `LaurentPolynomial ℤ` with `A = T 1`. -/

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev KR : Type := LaurentPolynomial ℤ

/-- The variable `A`. -/

theorem jones_twistSystem (k : ℕ) (w : ℤ) : jones twistSystem (k, w) = loopValue ^ k := by
  have h : ((kinkUnit ^ (-w) : KRˣ) : KR) * ((kinkUnit ^ w : KRˣ) : KR) = 1 := by
    rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
  show ((kinkUnit ^ (-w) : KRˣ) : KR) * (loopValue ^ k * ((kinkUnit ^ w : KRˣ) : KR)) = _
  calc ((kinkUnit ^ (-w) : KRˣ) : KR) * (loopValue ^ k * ((kinkUnit ^ w : KRˣ) : KR))
      = (((kinkUnit ^ (-w) : KRˣ) : KR) * ((kinkUnit ^ w : KRˣ) : KR)) * loopValue ^ k := by
        ring
    _ = loopValue ^ k := by rw [h, one_mul]

/-! ## A second model: the Temperley–Lieb algebra on two strands

The model above has only Reidemeister I sites.  A model containing Reidemeister II
and III configurations is provided by the Temperley–Lieb algebra `TL₂` with its
Markov trace: a diagram is an element `a·1 + b·e` of `TL₂`, the bracket is the
trace of its closure, and a crossing site is a pair (prefix, suffix) of `TL₂`
elements between which a crossing or one of its two smoothings is inserted. -/

/-- The Temperley–Lieb algebra on two strands, in the basis `1, e`. -/
abbrev TL2 : Type := KR × KR

/-- Multiplication of `TL₂`, using `e * e = δ * e`. -/
