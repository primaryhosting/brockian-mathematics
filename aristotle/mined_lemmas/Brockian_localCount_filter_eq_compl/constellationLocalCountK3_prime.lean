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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The *local count* of a shift pattern `H` at modulus `n`: the number of residues
`a : ZMod n` for which none of the shifted values `a + h`, `h ∈ H`, vanishes modulo `n`.
For a prime `n = p` this is the quantity `ν_H(p)` occurring in the singular series of the
Hardy–Littlewood prime constellation conjecture. -/

theorem constellationLocalCountK3_prime (p : ℕ) (hp : p.Prime) (h₁ h₂ h₃ : ℤ)
    (h12 : (h₁ : ZMod p) ≠ (h₂ : ZMod p)) (h13 : (h₁ : ZMod p) ≠ (h₃ : ZMod p))
    (h23 : (h₂ : ZMod p) ≠ (h₃ : ZMod p)) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    localCount {h₁, h₂, h₃} p = p - 3 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h := (ConstellationLocalCountK3 p h₁ h₂ h₃).1
  have hne12 : -(h₁ : ZMod p) ≠ -(h₂ : ZMod p) := fun hc => h12 (neg_injective hc)
  have hne13 : -(h₁ : ZMod p) ≠ -(h₃ : ZMod p) := fun hc => h13 (neg_injective hc)
  have hne23 : -(h₂ : ZMod p) ≠ -(h₃ : ZMod p) := fun hc => h23 (neg_injective hc)
  rw [h, Finset.card_insert_of_notMem (by simp [hne12, hne13]),
    Finset.card_insert_of_notMem (by simp [hne23]), Finset.card_singleton]

end Brockian

