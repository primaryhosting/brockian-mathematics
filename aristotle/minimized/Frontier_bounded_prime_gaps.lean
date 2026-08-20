import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter

/-- `nthPrime n` is the `n`-th prime number, counting from `nthPrime 0 = 2`. -/

noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The `n`-th prime gap `p_{n+1} - p_n`. -/

noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

theorem bounded_prime_gaps :
    (∃ B : ℕ, ∀ N : ℕ, ∃ n, N ≤ n ∧ primeGap n ≤ B) ↔
      liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤ := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  constructor
  · rintro ⟨B, hB⟩
    have hle : (⨆ n : ℕ, ⨅ i, ⨅ _ : n ≤ i, (primeGap i : ℕ∞)) ≤ (B : ℕ∞) := by
      refine iSup_le fun n => ?_
      obtain ⟨m, hnm, hm⟩ := hB n
      exact le_trans (iInf₂_le m hnm) (by exact_mod_cast hm)
    exact lt_of_le_of_lt hle (by simp)
  · intro h
    obtain ⟨B, hB⟩ : ∃ B : ℕ, (⨆ n : ℕ, ⨅ i, ⨅ _ : n ≤ i, (primeGap i : ℕ∞)) = (B : ℕ∞) := by
      obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.1 (ne_of_lt h)
      exact ⟨B, hB.symm⟩
    refine ⟨B, fun N => ?_⟩
    by_contra hcon
    push_neg at hcon
    have : ((B : ℕ∞) + 1) ≤ ⨅ i, ⨅ _ : N ≤ i, (primeGap i : ℕ∞) := by
      refine le_iInf₂ fun i hi => ?_
      have := hcon i hi
      exact_mod_cast this
    have h2 : ((B : ℕ∞) + 1) ≤ (B : ℕ∞) :=
      this.trans (hB ▸ le_iSup (fun n : ℕ => ⨅ i, ⨅ _ : n ≤ i, (primeGap i : ℕ∞)) N)
    have h3 : B + 1 ≤ B := by exact_mod_cast h2
    omega

/-- Unconditionally, the liminf of the prime gaps is at least `1`, since consecutive
primes are distinct. -/
