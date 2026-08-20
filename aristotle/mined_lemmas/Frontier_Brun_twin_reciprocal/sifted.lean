import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


def sifted (N z : ℕ) : ℕ :=
  ((range N).filter (fun n => ¬ 2 ∣ n ∧ ∀ p ∈ oddPrimes z, ¬ p ∣ n * (n + 2))).card

/-- The number of twin primes `p < N` (i.e. `p` and `p + 2` both prime). -/
