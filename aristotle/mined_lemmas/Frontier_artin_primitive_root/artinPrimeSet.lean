import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the header block above sits immediately after the single import.)

namespace Frontier

/-! ## Definitions -/

/-- `a : ℤ` is a *primitive root* modulo `p` when the residue of `a` generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/

def artinPrimeSet (a : ℤ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}

/-- **Artin's conjecture on primitive roots**: every integer `a` which is neither `-1`
nor a perfect square is a primitive root modulo infinitely many primes. -/
