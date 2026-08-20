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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The **local count** of a constellation with shift set `H` at modulus `n`:
the number of residues `a : ZMod n` such that none of the shifted values `a + h`
(`h ∈ H`) vanishes modulo `n`.  This is the local factor appearing in the
singular series of a constellation / prime-tuple counting problem. -/

noncomputable def localCount (n : ℕ) [NeZero n] (H : Finset (ZMod n)) : ℕ :=
  (Finset.univ.filter (fun a : ZMod n => ∀ h ∈ H, a + h ≠ 0)).card

/-- The local count of a shift set `H` modulo `n` is `n - |H|`: the forbidden
residues are exactly the negatives `-h` of the elements of `H`, and negation is
injective (`neg_injective`), so the excluded set has exactly `|H|` elements
(`Finset.card_image_of_injective`, `Finset.card_univ_diff`, `ZMod.card`). -/
