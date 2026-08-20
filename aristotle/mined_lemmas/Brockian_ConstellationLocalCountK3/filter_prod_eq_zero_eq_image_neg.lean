/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The *local count* of a `3`-element constellation `h = (h 0, h 1, h 2)` modulo a prime `p`:
the number of residues `n : ZMod p` for which the shifted product `∏ i, (n + h i)` vanishes,
i.e. the number of residue classes that a prime constellation `(n + h 0, n + h 1, n + h 2)`
must avoid modulo `p`. -/

lemma filter_prod_eq_zero_eq_image_neg (p : ℕ) [Fact p.Prime] (h : Fin 3 → ZMod p) :
    (Finset.univ.filter (fun n : ZMod p => ∏ i, (n + h i) = 0))
      = ({h 0, h 1, h 2} : Finset (ZMod p)).image (fun x => -x) := by
  ext n
  simp [Fin.prod_univ_three, mul_eq_zero, add_eq_zero_iff_eq_neg, or_assoc]

/-- The local count equals the number of *distinct* shifts modulo `p`. -/
