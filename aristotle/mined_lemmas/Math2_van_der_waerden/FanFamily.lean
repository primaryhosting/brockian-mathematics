/-
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Statement: Any finite coloring of ℕ has arbitrarily long monochromatic APs (van der Waerden).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math2

/-- `HasAP c m N` says the coloring `c` admits a monochromatic arithmetic progression of
length `m` with positive common difference, contained (together with a little slack) in
`[0, N]`. -/

@[reducible] def FanFamily {K : Type*} (c : ℕ → K) (k s N : ℕ) : Prop :=
  ∃ (f : ℕ) (a d : ℕ → ℕ), f ≤ N ∧ (∀ j < s, 0 < d j) ∧
    (∀ j < s, a j + k * d j = f) ∧
    (∀ j < s, ∀ i < k, c (a j + i * d j) = c (a j)) ∧
    (∀ i < s, ∀ j < s, c (a i) = c (a j) → i = j)

/-- The finitary van der Waerden statement for progressions of length `k`. -/
