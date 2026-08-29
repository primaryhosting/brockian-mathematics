/-
/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
(Lean requires the `import` command to be the very first command of a file, so
the header above is reproduced verbatim inside this comment and again as the
module docstring below.)
-/
import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

/-- The set of residue classes modulo `p` that are occupied by the shift set `H`. -/

theorem admissible_of_not_dvd_small_primes {H : Finset ℤ}
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → ∀ x ∈ H, ¬ ((p : ℤ) ∣ x)) :
    Admissible H := by
  refine (admissible_iff_small_primes H).mpr ?_
  intro p hp hple
  refine ⟨0, ?_⟩
  intro x hx hx0
  exact h p hp hple x hx ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx0)

/-- **Main result (admissible gap ranges).**
Let `k` be a length, `a` a starting point and `d` a common difference such that every prime
`p ≤ k` divides `d` but does not divide `a`.  Then the arithmetic progression
`a, a + d, …, a + (k-1)d` is an admissible pattern of shifts: modulo every prime it misses a
residue class, hence its Hardy–Littlewood singular series does not vanish.

This produces admissible gap ranges of arbitrary length `k` and arbitrary diameter `(k-1)|d|`,
extending the `SingularSeriesGaps` family. -/
