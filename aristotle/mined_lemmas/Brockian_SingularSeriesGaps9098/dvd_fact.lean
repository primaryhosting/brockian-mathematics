/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses no imports at all), so that the
required header comment can literally be the first thing in the file.  Everything below is
built from the Lean 4 core library only.
-/

namespace Brockian

/-! ## Primality, admissible gap patterns -/

/-- Primality, spelled out from first principles: `p` is at least `2` and its only divisors
are `1` and `p`. -/

theorem dvd_fact : ∀ (k m : Nat), 0 < m → m ≤ k → m ∣ fact k
  | 0, m, hm, hmk => by omega
  | k + 1, m, hm, hmk => by
      rcases Nat.eq_or_lt_of_le hmk with h | h
      · subst h
        exact ⟨fact k, rfl⟩
      · have hmk' : m ≤ k := by omega
        exact Nat.dvd_trans (dvd_fact k m hm hmk') (Nat.dvd_mul_left (fact k) (k + 1))

/-- With common difference `k!`, every length is allowed: the arithmetic progression
`{0, k!, 2·k!, …, (k-1)·k!}` is an admissible gap pattern. -/
