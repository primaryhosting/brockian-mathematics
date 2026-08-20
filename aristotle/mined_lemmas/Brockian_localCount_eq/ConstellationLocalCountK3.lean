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

theorem ConstellationLocalCountK3 (n : ℕ) [NeZero n] (h₁ h₂ h₃ : ZMod n)
    (h12 : h₁ ≠ h₂) (h13 : h₁ ≠ h₃) (h23 : h₂ ≠ h₃) :
    localCount n {h₁, h₂, h₃} = n - 3 := by
  rw [localCount_eq]
  congr 1
  rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
    Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]

/-- Product form of the `k = 3` local count over a prime modulus: since `ZMod p`
is an integral domain, the admissible residues are exactly those for which the
product `(a + h₁)(a + h₂)(a + h₃)` is nonzero, and there are `p - 3` of them. -/
