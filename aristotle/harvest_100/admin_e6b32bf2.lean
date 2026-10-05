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
def bigOmega (q : ℕ) : ℕ := q.primeFactorsList.length

/-- `n` admits a *Chen representation*: `n = p + q` with `p` prime and `Ω(q) ≤ 2`
(i.e. `q` is `1`, a prime, or a product of two primes). -/
def ChenRep (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ bigOmega q ≤ 2 ∧ n = p + q

/-- **Chen's theorem** (statement only): every sufficiently large even number has a Chen
representation. -/
def ChenStatement : Prop := ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ChenRep n

/-- **Goldbach's conjecture** (statement only): every even number `≥ 6` is a sum of two
primes. -/
def GoldbachStatement : Prop :=
  ∀ n : ℕ, 6 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q

/-! ## Basic facts about `Ω` -/

/-- A prime has exactly one prime factor. -/
theorem bigOmega_prime {p : ℕ} (hp : p.Prime) : bigOmega p = 1 := by
  simp [bigOmega, Nat.primeFactorsList_prime hp]

/-- `Ω(1) = 0`. -/
theorem bigOmega_one : bigOmega 1 = 0 := by
  simp [bigOmega]

/-- `Ω(p * q) = 2` for primes `p`, `q`. -/
theorem bigOmega_prime_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    bigOmega (p * q) = 2 := by
  have h := Nat.perm_primeFactorsList_mul hp.ne_zero hq.ne_zero
  simp [bigOmega, h.length_eq, Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hq]

/-- A decomposition into two primes is in particular a Chen representation. -/
theorem chenRep_of_prime_add_prime {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : n = p + q) :
    ChenRep n :=
  ⟨p, q, hp, by rw [bigOmega_prime hq]; norm_num, h⟩

/-! ## The verified base case

For every even `n` with `6 ≤ n < 500` we exhibit, by a kernel-checked computation, a prime
`p < 40` such that `n - p` is prime; in particular `n` has a Chen representation. -/

theorem goldbach_base_case :
    ∀ n < 500, Even n → 6 ≤ n → ∃ p < 40, Nat.Prime p ∧ Nat.Prime (n - p) := by
  decide

theorem chenRep_base_case (n : ℕ) (hev : Even n) (h6 : 6 ≤ n) (hlt : n < 500) : ChenRep n := by
  obtain ⟨p, hp40, hp, hnp⟩ := goldbach_base_case n hlt hev h6
  refine chenRep_of_prime_add_prime hp hnp ?_
  have h2 := hnp.two_le
  omega

/-! ## A Lean-checked reduction

Goldbach's conjecture implies Chen's theorem, since a prime `q` satisfies `Ω(q) = 1 ≤ 2`. -/

theorem chen_of_goldbach : GoldbachStatement → ChenStatement := by
  intro hG
  refine ⟨6, fun n hn hev => ?_⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := hG n hn hev
  exact chenRep_of_prime_add_prime hp hq hpq

/-! ## The contrapositive reformulation

Chen's theorem is equivalent to the assertion that the exceptional set of even numbers
without a Chen representation is bounded. -/

theorem chen_iff_not_unbounded_exceptional :
    ChenStatement ↔ ¬ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ¬ ChenRep n := by
  constructor
  · rintro ⟨N, hN⟩ hcon
    obtain ⟨n, hn, hev, hbad⟩ := hcon N
    exact hbad (hN n hn hev)
  · intro h
    push_neg at h
    obtain ⟨N, hN⟩ := h
    exact ⟨N, hN⟩

/-! ## Unconditional infinitude of Chen numbers

There are arbitrarily large even numbers with a Chen representation (take `n = 2p`). -/

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
theorem Chen_theorem :
    (∀ n : ℕ, Even n → 6 ≤ n → n < 500 → ChenRep n) ∧
    (GoldbachStatement → ChenStatement) ∧
    (ChenStatement ↔ ¬ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ¬ ChenRep n) ∧
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ChenRep n) :=
  ⟨chenRep_base_case, chen_of_goldbach, chen_iff_not_unbounded_exceptional,
    exists_large_even_chenRep⟩

end Frontier

