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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

/-- A finite set `H` of natural numbers is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture) if for every prime `p` the residues
of the elements of `H` modulo `p` do not cover all of `ZMod p`. -/

lemma card_gapTuple_le (n : ℕ) : (gapTuple n).card ≤ 7 := by
  unfold gapTuple
  have h1 := Finset.card_insert_le 0 ({4, 6, 10, 12, 16, n} : Finset ℕ)
  have h2 := Finset.card_insert_le 4 ({6, 10, 12, 16, n} : Finset ℕ)
  have h3 := Finset.card_insert_le 6 ({10, 12, 16, n} : Finset ℕ)
  have h4 := Finset.card_insert_le 10 ({12, 16, n} : Finset ℕ)
  have h5 := Finset.card_insert_le 12 ({16, n} : Finset ℕ)
  have h6 := Finset.card_insert_le 16 ({n} : Finset ℕ)
  have h7 : ({n} : Finset ℕ).card = 1 := Finset.card_singleton n
  omega

