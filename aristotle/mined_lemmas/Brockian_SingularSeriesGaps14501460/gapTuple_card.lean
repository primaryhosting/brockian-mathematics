/-
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
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

namespace Brockian

/-- A finite set `H` of integers is *admissible* (equivalently, its Hardy–Littlewood
singular series `𝔖(H)` is nonzero) when for every prime `p` the elements of `H` fail
to occupy all residue classes modulo `p`. -/

lemma gapTuple_card : gapTuple.card = 4 := by decide

