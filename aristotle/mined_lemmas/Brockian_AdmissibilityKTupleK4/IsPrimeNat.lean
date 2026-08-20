/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, stated from first principles:
`p` is at least `2` and its only divisors are `1` and `p`. -/

def IsPrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- A list `H` of shifts (a *k*-tuple, with `k = H.length`) is **admissible** if for every
prime `p` the shifts do not cover all residue classes modulo `p`: there is a residue
class `a < p` avoided by `h % p` for every `h ∈ H`.

This is the classical admissibility condition from the Hardy–Littlewood prime `k`-tuple
conjecture: it is exactly the condition preventing the pattern `n + h`, `h ∈ H`, from being
forced to contain a multiple of some prime. -/
