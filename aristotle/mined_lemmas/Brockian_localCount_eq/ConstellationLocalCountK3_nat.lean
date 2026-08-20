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

/-- The **local count** of a constellation (tuple of shifts) `H` modulo `p`:
the number of residues `a` mod `p` such that none of the shifted values `a + h`,
`h ∈ H`, is divisible by `p`.  This is the local factor `ν_p(H)` appearing in the
Hardy–Littlewood prime-tuple heuristics. -/

theorem ConstellationLocalCountK3_nat (p : ℕ) [NeZero p] (a b c : ℕ)
    (hab : (a : ZMod p) ≠ (b : ZMod p)) (hac : (a : ZMod p) ≠ (c : ZMod p))
    (hbc : (b : ZMod p) ≠ (c : ZMod p)) :
    ((Finset.range p).filter
        (fun n => ¬ p ∣ (n + a) ∧ ¬ p ∣ (n + b) ∧ ¬ p ∣ (n + c))).card = p - 3 := by
  classical
  rw [← ConstellationLocalCountK3 p (a : ZMod p) (b : ZMod p) (c : ZMod p) hab hac hbc,
    localCount]
  refine Finset.card_bij' (fun n _ => ((n : ZMod p))) (fun x _ => ZMod.val x) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rintro h (rfl | rfl | rfl) <;>
      · rw [← Nat.cast_add, Ne, ZMod.natCast_eq_zero_iff]
        tauto
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_range, ZMod.val_lt, true_and]
    refine ⟨?_, ?_, ?_⟩ <;>
      · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, ZMod.natCast_val, ZMod.cast_id]
        exact hx _ (by simp)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact ZMod.val_natCast_of_lt hn.1
  · intro x _
    simp

end Brockian

