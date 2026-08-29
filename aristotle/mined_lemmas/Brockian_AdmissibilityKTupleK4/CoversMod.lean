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

def CoversMod (L : List Int) (p : Nat) : Prop :=
  ∀ a : Int, ∃ h ∈ L, (p : Int) ∣ (h - a)

/-- A list of integers is **admissible** (in the sense of the prime `k`-tuples conjecture) when
for every prime `p` it misses at least one residue class modulo `p`. -/
