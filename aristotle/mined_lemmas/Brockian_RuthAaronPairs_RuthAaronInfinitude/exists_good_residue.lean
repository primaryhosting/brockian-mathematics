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

/-
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A *Ruth–Aaron pair* is a pair of consecutive integers `(n, n+1)` whose sums of prime factors,
counted with multiplicity, agree; e.g. `(5, 6)`, `(8, 9)`, `(714, 715)`.  Whether there are
infinitely many such pairs is a well-known open problem (Erdős).

This file gives a Lean-checked conditional proof: assuming **Schinzel's Hypothesis H**, there
are infinitely many Ruth–Aaron pairs.  The reduction goes through the polynomial identity
```
(12u² + 36u + 23)(4u + 9) + 1 = 4 (12u² + 39u + 26)(u + 2)
```
together with the matching identity of sums
```
(12u² + 36u + 23) + (4u + 9) = 4 + (12u² + 39u + 26) + (u + 2) .
```
Hence whenever the four polynomial values are simultaneously prime, `n = (12u²+36u+23)(4u+9)`
and `n + 1 = 2 · 2 · (12u²+39u+26) · (u+2)` have the same sum of prime factors.  The four
polynomials are irreducible, have positive leading coefficients, and have no fixed prime
divisor (`u = 5` already gives the Ruth–Aaron pair `(14587, 14588)`), so Hypothesis H supplies
arbitrarily large such `u`.
-/

namespace Brockian.RuthAaronPairs

open Polynomial

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(`sopfr 1 = 0`, `sopfr 12 = 2 + 2 + 3 = 7`). -/

lemma exists_good_residue {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) :
    ∃ x : ZMod p, 12 * x ^ 2 + 36 * x + 23 ≠ 0 ∧ 4 * x + 9 ≠ 0 ∧
      12 * x ^ 2 + 39 * x + 26 ≠ 0 ∧ x + 2 ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set G : (ZMod p)[X] := (C 12 * X ^ 2 + C 36 * X + C 23) *
      ((C 4 * X + C 9) * ((C 12 * X ^ 2 + C 39 * X + C 26) * (X + C 2))) with hG
  have hdeg : G.natDegree ≤ 6 := by rw [hG]; compute_degree
  have hp576 : ¬ (p ∣ 576) := by
    intro hdvd
    have h2 : p ∣ 2 ^ 6 * 3 ^ 2 := by norm_num at hdvd ⊢; exact hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h3); omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3); omega
  have h576 : ((576 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hp576
  have hcoeff : G.coeff 6 = 576 := by rw [hG]; compute_degree!
  have hGne : G ≠ 0 := by
    intro h
    rw [h] at hcoeff
    simp only [coeff_zero] at hcoeff
    exact h576 (by exact_mod_cast hcoeff.symm)
  by_contra hcon
  push_neg at hcon
  refine hGne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero G
    (f := (id : ZMod p → ZMod p)) Function.injective_id ?_ ?_)
  · intro x
    rw [hG]
    simp only [eval_mul, eval_add, eval_C, eval_X, eval_pow, id]
    rcases eq_or_ne (12 * x ^ 2 + 36 * x + 23) 0 with h | h
    · rw [h]; ring
    rcases eq_or_ne (4 * x + 9) 0 with h2 | h2
    · rw [h2]; ring
    rcases eq_or_ne (12 * x ^ 2 + 39 * x + 26) 0 with h3 | h3
    · rw [h3]; ring
    · rw [hcon x h h2 h3]; ring
  · rw [ZMod.card]
    omega

/-- No prime divides the product of the four forms at every integer. -/
