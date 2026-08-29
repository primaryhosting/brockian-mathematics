/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is written in plain Lean 4 core (no imports), so that the header comment above
can legally be the very first thing in the file.
-/

namespace Frontier

/-- A `±1` sequence: `f n ∈ {1, -1}` for every index `n ≥ 1`. -/

theorem exists_boolSeq_hapSum_eq (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ g : ℕ → Bool, ∀ d n : ℕ, 1 ≤ d → hapSum (boolSeq g) d n = hapSum f d n := by
  refine ⟨fun k => decide (f k = 1), fun d n hd => hapSum_congr hd (fun k hk => ?_) n⟩
  rcases hf k hk with h | h <;> simp [boolSeq, h]

