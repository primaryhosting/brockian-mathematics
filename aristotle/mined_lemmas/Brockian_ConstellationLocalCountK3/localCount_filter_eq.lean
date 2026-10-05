import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The local count, modulo `p`, of a constellation with offset set `A`:
the number of residues `n : ZMod p` such that none of the shifted values `n + a`
(for `a ∈ A`) is divisible by `p`. -/

theorem localCount_filter_eq (p : ℕ) [NeZero p] (A : Finset (ZMod p)) :
    (Finset.univ.filter (fun n : ZMod p => ∀ a ∈ A, n + a ≠ 0))
      = (A.image (fun a => -a))ᶜ := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
    Finset.mem_image, not_exists, not_and]
  constructor
  · intro h a ha hna
    exact h a ha (by rw [← hna]; ring)
  · intro h a ha hna
    exact h a ha (by linear_combination -hna)

/-- General local count formula: the number of admissible residues is `p - |A|`. -/
