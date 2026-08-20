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

theorem ConstellationLocalCountK3 (p : ℕ) [Fact (Nat.Prime p)] (a b c : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (Finset.univ.filter
        (fun n : ZMod p => (n + a) * (n + b) * (n + c) ≠ 0)).card = p - 3 := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).ne_zero⟩
  have hset :
      (Finset.univ.filter (fun n : ZMod p => (n + a) * (n + b) * (n + c) ≠ 0)) =
        (Finset.univ.filter (fun n : ZMod p => ∀ h ∈ ({a, b, c} : Finset (ZMod p)), n + h ≠ 0)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, mul_ne_zero_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩ h (rfl | rfl | rfl) <;> assumption
    · intro h
      exact ⟨⟨h a (Or.inl rfl), h b (Or.inr (Or.inl rfl))⟩, h c (Or.inr (Or.inr rfl))⟩
  have hcard : ({a, b, c} : Finset (ZMod p)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  have := constellationLocalCount_eq p ({a, b, c} : Finset (ZMod p))
  rw [constellationLocalCount, hcard] at this
  rw [hset, this]

/-- Sanity check: mod `5`, the shifts `0, 1, 2` leave exactly `5 - 3 = 2` admissible residues. -/
example : (Finset.univ.filter
    (fun n : ZMod 5 => (n + 0) * (n + 1) * (n + 2) ≠ 0)).card = 5 - 3 :=
  @ConstellationLocalCountK3 5 ⟨by norm_num⟩ 0 1 2 (by decide) (by decide) (by decide)

end Brockian

