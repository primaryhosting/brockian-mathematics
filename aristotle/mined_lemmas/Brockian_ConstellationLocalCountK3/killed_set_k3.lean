/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The local count of a constellation (admissible tuple) `H` at the prime `p`:
the number of residue classes `n` mod `p` such that `n + h ≢ 0 (mod p)` for every
shift `h ∈ H`, i.e. the number of residues that survive the sieve at `p`. -/

theorem killed_set_k3 (p : ℕ) [hp : Fact p.Prime] (h₁ h₂ h₃ : ZMod p) :
    (Finset.univ.filter fun n : ZMod p => (n + h₁) * (n + h₂) * (n + h₃) = 0)
      = ({-h₁, -h₂, -h₃} : Finset (ZMod p)) := by
  ext n
  simp [mul_eq_zero, add_eq_zero_iff_eq_neg, or_assoc]

/-- Three pairwise distinct shifts kill exactly three residue classes. -/
