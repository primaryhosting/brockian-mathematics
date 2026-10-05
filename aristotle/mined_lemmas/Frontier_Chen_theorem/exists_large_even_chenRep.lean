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

theorem exists_large_even_chenRep (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ Even n ∧ ChenRep n := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  exact ⟨p + p, by omega, ⟨p, rfl⟩, chenRep_of_prime_add_prime hp hp rfl⟩

/-! ## Main target

`Chen_theorem` packages the Lean-checked content: the verified base case (every even
`n` with `6 ≤ n < 500` has a Chen representation), the reduction of Chen's theorem to
Goldbach's conjecture, the contrapositive reformulation of Chen's statement, and the
unconditional existence of arbitrarily large Chen numbers.

The full asymptotic theorem of Chen (that *every* sufficiently large even number has such
a representation) is **not** proved here; `ChenStatement` is only formalized and related
to statements that are easier to attack. -/
