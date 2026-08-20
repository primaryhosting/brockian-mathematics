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

/-- The *local count* `ν_p(H)` of a finite set of integer offsets `H` at a modulus `p`:
the number of distinct residue classes modulo `p` occupied by the members of `H`. -/

theorem localCount_triple_eq_three_iff (a b c : ℤ) (p : ℕ) :
    localCount ({a, b, c} : Finset ℤ) p = 3 ↔
      ((a : ZMod p) ≠ (b : ZMod p) ∧ (a : ZMod p) ≠ (c : ZMod p) ∧
        (b : ZMod p) ≠ (c : ZMod p)) := by
  have himg : (({a, b, c} : Finset ℤ).image (fun x : ℤ => (x : ZMod p)))
      = ({(a : ZMod p), (b : ZMod p), (c : ZMod p)} : Finset (ZMod p)) := by
    simp [Finset.image_insert]
  constructor
  · intro h
    rw [localCount, himg] at h
    by_contra hcon
    push_neg at hcon
    have : ({(a : ZMod p), (b : ZMod p), (c : ZMod p)} : Finset (ZMod p)).card ≤ 2 := by
      rcases eq_or_ne (a : ZMod p) (b : ZMod p) with hab | hab
      · rw [hab]
        calc ({(b : ZMod p), (b : ZMod p), (c : ZMod p)} : Finset (ZMod p)).card
            = ({(b : ZMod p), (c : ZMod p)} : Finset (ZMod p)).card := by
              simp
          _ ≤ ({(c : ZMod p)} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
          _ ≤ 2 := by simp
      · rcases eq_or_ne (a : ZMod p) (c : ZMod p) with hac | hac
        · rw [hac]
          calc ({(c : ZMod p), (b : ZMod p), (c : ZMod p)} : Finset (ZMod p)).card
              = ({(b : ZMod p), (c : ZMod p)} : Finset (ZMod p)).card := by
                rw [Finset.insert_comm]
                simp
            _ ≤ ({(c : ZMod p)} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
            _ ≤ 2 := by simp
        · have hbc : (b : ZMod p) = (c : ZMod p) := hcon hab hac
          rw [hbc]
          calc ({(a : ZMod p), (c : ZMod p), (c : ZMod p)} : Finset (ZMod p)).card
              = ({(a : ZMod p), (c : ZMod p)} : Finset (ZMod p)).card := by
                simp
            _ ≤ ({(c : ZMod p)} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
            _ ≤ 2 := by simp
    omega
  · rintro ⟨hab, hac, hbc⟩
    rw [localCount, himg]
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc])]
    simp

/-- Sanity check: the triple `(0, 2, 6)` is an admissible constellation pattern. -/
