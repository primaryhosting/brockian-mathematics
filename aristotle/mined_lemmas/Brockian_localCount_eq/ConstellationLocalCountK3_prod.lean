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

theorem ConstellationLocalCountK3_prod (p : ℕ) [Fact (Nat.Prime p)]
    (h₁ h₂ h₃ : ZMod p) (h12 : h₁ ≠ h₂) (h13 : h₁ ≠ h₃) (h23 : h₂ ≠ h₃) :
    (Finset.univ.filter
        (fun a : ZMod p => (a + h₁) * (a + h₂) * (a + h₃) ≠ 0)).card = p - 3 := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).ne_zero⟩
  rw [← ConstellationLocalCountK3 p h₁ h₂ h₃ h12 h13 h23]
  unfold localCount
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, mul_eq_zero,
    not_or, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  tauto

end Brockian

