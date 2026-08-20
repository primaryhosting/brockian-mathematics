import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-- A `±1` sequence, indexed by the positive integers. -/

theorem erdosDiscrepancy_iff_no_uniform_bound :
    ErdosDiscrepancy ↔
      ∀ f : ℕ → ℤ, IsPlusMinusOne f →
        ¬ ∃ C : ℤ, ∀ d n : ℕ, 0 < d → 0 < n → |apSum f d n| ≤ C := by
  constructor
  · rintro h f hf ⟨C, hC⟩
    obtain ⟨d, n, hd, hn, hlt⟩ := h f hf C
    exact absurd (hC d n hd hn) (not_le.2 hlt)
  · intro h f hf C
    by_contra hcon
    push_neg at hcon
    exact h f hf ⟨C, fun d n hd hn => hcon d n hd hn⟩

/-- Key finite step: a `±1` sequence whose discrepancy over homogeneous APs never exceeds
`1` does not exist.  Only the progressions with `d * n ≤ 12`, hence only the values
`f 1, …, f 12`, are involved. -/
