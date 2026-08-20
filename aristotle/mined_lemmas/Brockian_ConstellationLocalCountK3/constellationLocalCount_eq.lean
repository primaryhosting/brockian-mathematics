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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The local count of a constellation (`k`-tuple of shifts) `H` modulo `p`: the number of
residues `n` such that none of the shifted values `n + h`, `h ∈ H`, is divisible by `p`.
This is the quantity `p - ν_H(p)` appearing in the singular series of the Hardy–Littlewood
prime `k`-tuple heuristic. -/

theorem constellationLocalCount_eq (p : ℕ) [NeZero p] (H : Finset (ZMod p)) :
    constellationLocalCount p H = p - H.card := by
  have hinj : Set.InjOn (fun h : ZMod p => -h) H := fun x _ y _ h => by
    simpa using neg_injective h
  have hcard : (H.image (fun h => -h)).card = H.card := Finset.card_image_of_injOn hinj
  rw [constellationLocalCount, constellationAvoidSetEqSdiff p H,
    Finset.card_univ_diff, hcard, ZMod.card]

/-- **Constellation local count, `k = 3`.**  For a prime `p` and three pairwise distinct
shifts `a, b, c` modulo `p`, the number of residues `n` mod `p` for which none of
`n + a`, `n + b`, `n + c` vanishes — equivalently `(n+a)(n+b)(n+c) ≢ 0 (mod p)` — is exactly
`p - 3`. -/
