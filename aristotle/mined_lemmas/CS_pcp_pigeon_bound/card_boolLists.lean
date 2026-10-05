/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
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

set_option grind.warning false

namespace CS

/-- The finset of all binary strings (lists of booleans) of length `n`. -/

lemma card_boolLists (n : ℕ) : (boolLists n).card = 2 ^ n := by
  induction n with
  | zero => simp [boolLists]
  | succ n ih =>
    have hdisj : ((Finset.univ : Finset Bool) : Set Bool).PairwiseDisjoint
        (fun b => (boolLists n).image (fun l => b :: l)) := by
      intro x _ y _ hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      rintro a ha hb
      simp only [Finset.mem_image] at ha hb
      obtain ⟨u, _, hu⟩ := ha
      obtain ⟨v, _, hv⟩ := hb
      subst hu
      simp only [List.cons.injEq] at hv
      exact hxy hv.1.symm
    have hinj : ∀ b : Bool, Function.Injective (fun l : List Bool => b :: l) := by
      intro b x y h
      simpa using h
    rw [boolLists, Finset.card_biUnion hdisj]
    simp only [Finset.card_image_of_injective _ (hinj _), ih, Finset.sum_const,
      Finset.card_univ, Fintype.card_bool, smul_eq_mul]
    ring

/-- **Kraft's inequality.** For any finite prefix-free binary code `S` (a finite set of
binary strings none of which is a prefix of another), the sum of `2 ^ (-ℓ)` over the
codeword lengths `ℓ` is at most `1`. -/
