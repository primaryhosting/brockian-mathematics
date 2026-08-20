/-
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `Omega n` is the number of prime factors of `n`, counted with multiplicity
(the classical arithmetic function `Ω`). -/

theorem Chen_base_case {n : ℕ} (h4 : 4 ≤ n) (h500 : n ≤ 500) (hn : Even n) : IsChenSum n := by
  obtain ⟨p, hp, hp1, hp2⟩ := base_check n (Finset.mem_Icc.2 ⟨h4, h500⟩) hn
  have hple : p ≤ n := by
    have := Finset.mem_range.1 hp
    omega
  have : n = p + (n - p) := by omega
  exact this ▸ chenSum_of_add_primes hp1 hp2

/-- **Unconditional infinitude.** Infinitely many even numbers are Chen sums: for every odd
prime `p`, the even number `2 * p = p + p` is one. -/
