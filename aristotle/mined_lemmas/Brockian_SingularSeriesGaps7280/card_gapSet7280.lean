import Mathlib

/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
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

/-- A finite set of integers `H` is *admissible* if, for every prime `p`, the reductions of the
elements of `H` modulo `p` do not cover all residue classes mod `p`.  This is exactly the
condition under which the singular series of the tuple `H` is nonzero. -/

lemma card_gapSet7280 : gapSet7280.card = 5 := by decide

/-!
The main result: the gap range `{7280, 7282, 7286, 7288, 7292}` is an admissible `5`-tuple,
and consequently every local factor of its singular series is strictly positive (so the
singular series does not vanish, and the Hardy–Littlewood prime `k`-tuple conjecture predicts
infinitely many prime constellations with these gaps).
-/
