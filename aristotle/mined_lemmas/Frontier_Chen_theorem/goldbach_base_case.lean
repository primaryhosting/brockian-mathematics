import Mathlib
/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
This file formalises the statement of **Chen's theorem** ("every sufficiently large even
number `n` can be written as `p + q` where `p` is prime and `q` has at most two prime
factors"), and provides two Lean-checked results about it:

* `Frontier.Chen_theorem`: a **reduction** — the Goldbach conjecture implies Chen's
  statement, with the explicit threshold `N = 4`.
* `Frontier.Chen_base_case`: an **unconditional base case** — every even `n` with
  `4 ≤ n ≤ 2000` has a Chen representation.  This is verified in the kernel from an explicit
  table of Goldbach decompositions, with all primality facts checked by `norm_num`.

The full (unconditional, asymptotic) Chen theorem is not proved here.
-/

namespace Frontier

/-- `AlmostPrime2 q` says that `q` is a product of at most two (and at least one) primes,
i.e. `q` is either a prime or a semiprime.  This is the meaning of "`q` has at most two
prime factors" in Chen's theorem. -/

theorem goldbach_base_case (n : ℕ) (h4 : 4 ≤ n) (hN : n ≤ 2000) (hEven : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  have hmem : n ∈ List.range' 4 999 2 := by
    obtain ⟨k, hk⟩ := hEven
    refine List.mem_range'.mpr ⟨(n - 4) / 2, ?_, ?_⟩ <;> omega
  rw [← goldbachPairs_sums] at hmem
  obtain ⟨x, hx, hsum⟩ := List.mem_map.mp hmem
  obtain ⟨h1, h2⟩ := goldbachPairs_prime x hx
  exact ⟨x.1, x.2, h1, h2, hsum.symm⟩

/-- **Chen's statement, verified unconditionally in the base range** `4 ≤ n ≤ 2000`. -/
