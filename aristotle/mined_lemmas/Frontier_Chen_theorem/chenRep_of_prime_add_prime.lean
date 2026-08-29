/-
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Formalization of the statement

Chen's theorem asserts that every sufficiently large even number `n` can be written as
`n = p + q` where `p` is prime and `q` has at most two prime factors (counted with
multiplicity).  We formalize "number of prime factors with multiplicity" as `Ω`, the
length of the list of prime factors.
-/

/-- `bigOmega q = Ω(q)` is the number of prime factors of `q`, counted with multiplicity. -/

theorem chenRep_of_prime_add_prime {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : n = p + q) :
    ChenRep n :=
  ⟨p, q, hp, by rw [bigOmega_prime hq]; norm_num, h⟩

/-! ## The verified base case

For every even `n` with `6 ≤ n < 500` we exhibit, by a kernel-checked computation, a prime
`p < 40` such that `n - p` is prime; in particular `n` has a Chen representation. -/

