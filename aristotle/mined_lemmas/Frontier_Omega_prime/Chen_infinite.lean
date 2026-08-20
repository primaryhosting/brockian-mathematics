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

theorem Chen_infinite : {n : ℕ | Even n ∧ IsChenSum n}.Infinite := by
  have hinj : Set.InjOn (fun p : ℕ => 2 * p) {p : ℕ | p.Prime} := fun a _ b _ h => by
    simpa using h
  have hsub : (fun p : ℕ => 2 * p) '' {p : ℕ | p.Prime} ⊆ {n : ℕ | Even n ∧ IsChenSum n} := by
    rintro n ⟨p, hp, rfl⟩
    have hpp : (fun p : ℕ => 2 * p) p = p + p := by simp; ring
    rw [Set.mem_setOf_eq, hpp]
    exact ⟨⟨p, rfl⟩, chenSum_of_add_primes hp hp⟩
  exact Set.Infinite.mono hsub ((Nat.infinite_setOf_prime).image hinj)

/-! ## Reductions -/

/-- **A Lean-checked reduction: Goldbach implies Chen.** If every even number `≥ 4` is a sum
of two primes, then Chen's statement holds (with threshold `4`). -/
