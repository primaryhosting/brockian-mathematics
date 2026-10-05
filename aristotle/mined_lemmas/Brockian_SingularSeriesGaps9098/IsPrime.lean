/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses no imports at all), so that the
required header comment can literally be the first thing in the file.  Everything below is
built from the Lean 4 core library only.
-/

namespace Brockian

/-! ## Primality, admissible gap patterns -/

/-- Primality, spelled out from first principles: `p` is at least `2` and its only divisors
are `1` and `p`. -/

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- A finite gap pattern `H` (a list of non-negative shifts) is **admissible** if, for every
prime `p`, some residue class `r mod p` contains no member of `H`.  Admissibility is exactly
the condition for the Hardy–Littlewood singular series attached to `H` to be non-zero: a
non-admissible pattern has a prime `p` whose residues are completely covered, which forces the
local factor at `p`, and hence the whole singular series, to vanish. -/
