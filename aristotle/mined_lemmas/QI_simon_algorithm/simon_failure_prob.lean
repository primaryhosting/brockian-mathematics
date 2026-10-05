import RequestProject.SimonQuantum

/-!
# Recovering the hidden shift from the measured samples

Each run of the quantum subroutine returns a uniformly random `y ∈ s^⊥`.  After `m`
runs the classical post-processing solves the linear system `t ⬝ y_i = 0` and outputs the
unique nonzero solution, which succeeds exactly when the samples *determine* `s`.
We bound the number of sample sequences that fail to determine `s`.
-/

open scoped BigOperators

namespace QI

variable {n : ℕ}

/-- The samples `y : Fin m → BV n` determine the hidden shift `s`: the only vectors
orthogonal to all of them are `0` and `s`. -/

theorem simon_failure_prob (s : BV n) (k : ℕ) :
    2 ^ k * (badSamples s (n + k)).card ≤ (allSamples s (n + k)).card := by
  have h := card_badSamples_le s (n + k)
  rw [card_allSamples]
  have hpow : (2 : ℕ) ^ (n + k) = 2 ^ n * 2 ^ k := pow_add 2 n k
  rw [hpow] at h
  have h2 : 2 ^ n * (2 ^ k * (badSamples s (n + k)).card)
      ≤ 2 ^ n * ((perp s).card ^ (n + k)) := by
    calc 2 ^ n * (2 ^ k * (badSamples s (n + k)).card)
        = 2 ^ n * 2 ^ k * (badSamples s (n + k)).card := by ring
      _ ≤ 2 ^ n * (perp s).card ^ (n + k) := h
  exact Nat.le_of_mul_le_mul_left h2 (Nat.two_pow_pos n)

end QI

import RequestProject.SimonBasic

/-!
# Orthogonal complements in `F_2^n`

Counting lemmas for the hyperplanes `{y : dotp t y = 0}` used both in the analysis of
Simon's algorithm and in the classical lower bound.
-/

open scoped BigOperators

namespace QI

variable {n : ℕ}

/-- If `A` is closed under translation by `a` and `dotp t a = 1`, then exactly half of `A`
is orthogonal to `t`. -/
