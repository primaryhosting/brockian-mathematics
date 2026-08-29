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

theorem five_le_of_prime {p : Nat} (hp : PrimeNat p) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  obtain ⟨hple, hdiv⟩ := hp
  rcases Nat.lt_or_ge p 5 with hlt | hge
  · exfalso
    have hp4 : p = 4 := by omega
    subst hp4
    rcases hdiv 2 ⟨2, rfl⟩ with h | h <;> omega
  · exact hge

/-! ## Main result -/

/-- **Admissibility for `4`-tuples.**  A tuple of four integers is admissible for the prime
`k`-tuples conjecture if and only if it fails to cover the residues modulo `2` and modulo `3`.
All larger primes are automatic: four integers can never occupy all `p ≥ 5` residue classes. -/
