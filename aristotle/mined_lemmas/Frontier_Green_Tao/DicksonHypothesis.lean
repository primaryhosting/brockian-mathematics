import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

open Finset

/-- `HasAPOfLength S k` says that the set `S` contains a `k`-term arithmetic progression
`a, a + d, …, a + (k-1) d` with positive common difference `d`. -/

def DicksonHypothesis : Prop :=
  ∀ (k : ℕ) (b : ℕ → ℕ),
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ i < k, ¬ p ∣ (n + b i)) →
    ∃ n : ℕ, ∀ i < k, Nat.Prime (n + b i)

/-- Containing an arithmetic progression of length `m` implies containing one of any
shorter length. -/
