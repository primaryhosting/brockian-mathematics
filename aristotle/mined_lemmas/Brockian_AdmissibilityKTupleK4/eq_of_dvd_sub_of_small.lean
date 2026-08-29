/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean requires every `import` line to precede all other commands, while the
required header above is itself a command (a module docstring).  The development below is
therefore written against the Lean 4 core library only, with no `import` line, so that the
file both begins with the exact required header and compiles.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- Primality, spelled out without Mathlib: `p ≥ 2` and the only divisors of `p` are `1` and
`p`. -/

theorem eq_of_dvd_sub_of_small {p a b : Int} (hp : 5 ≤ p) (hab : (p : Int) ∣ (a - b))
    (ha0 : 0 ≤ a) (ha : a < 5) (hb0 : 0 ≤ b) (hb : b < 5) : a = b := by
  rcases Int.lt_trichotomy a b with h1 | h1 | h1
  · obtain ⟨c, hc⟩ := hab
    have hdvd : p ∣ (b - a) := ⟨-c, by rw [Int.mul_neg, ← hc]; omega⟩
    have := Int.le_of_dvd (by omega) hdvd
    omega
  · exact h1
  · have := Int.le_of_dvd (by omega) hab
    omega

/-- Two residues represented by the *same* integer, both small, coincide. -/
