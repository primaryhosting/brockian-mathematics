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

theorem card_killed_set_k3 (p : ℕ) (h₁ h₂ h₃ : ZMod p)
    (h12 : h₁ ≠ h₂) (h13 : h₁ ≠ h₃) (h23 : h₂ ≠ h₃) :
    ({-h₁, -h₂, -h₃} : Finset (ZMod p)).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23])]
  simp

/--
**Constellation local count for `k = 3`.**

For a prime `p` and a triple of shifts `h₁, h₂, h₃` in `ZMod p`:

* the local count of the constellation `{h₁, h₂, h₃}` equals the number of residues `n`
  with `(n + h₁)(n + h₂)(n + h₃) ≠ 0` (the product form of the sieve condition);
* it equals `p` minus the number of distinct residues killed, namely `#{-h₁, -h₂, -h₃}`;
* in particular, if the three shifts are pairwise distinct mod `p`, the count is `p - 3`.
-/
