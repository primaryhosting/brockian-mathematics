/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
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

namespace CS

/-! ## The communication model

A two-party deterministic communication protocol on inputs `X` (Alice) and `Y` (Bob) is a
binary tree.  At an `alice` node the bit sent depends only on Alice's input, at a `bob` node
only on Bob's input, and a `leaf` carries the output of the protocol.  The `cost` of a protocol
is the depth of the tree, i.e. the number of bits exchanged in the worst case. -/
inductive Protocol (X Y : Type) : Type
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | bob : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

variable {X Y : Type}

/-- The output of a protocol on a given pair of inputs. -/

lemma reveal_run (n : ℕ) : ∀ (k : ℕ) (acc x y : Inp n),
    (reveal n k acc).run x y = decide (Disjoint (acc ∪ x.filter (fun i : Fin n => (i : ℕ) < k)) y) := by
  intro k
  induction k with
  | zero =>
      intro acc x y
      simp [reveal, Protocol.run]
  | succ k ih =>
      intro acc x y
      have hsplit : x.filter (fun i : Fin n => (i : ℕ) < k + 1)
          = x.filter (fun i : Fin n => (i : ℕ) < k) ∪ x.filter (fun i : Fin n => (i : ℕ) = k) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hi, hlt⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
          · exact Or.inl ⟨hi, h⟩
          · exact Or.inr ⟨hi, h⟩
        · rintro (⟨hi, h⟩ | ⟨hi, h⟩)
          · exact ⟨hi, Nat.lt_succ_of_lt h⟩
          · exact ⟨hi, by omega⟩
      by_cases hmem : pt n k ⊆ x
      · have hpt : x.filter (fun i : Fin n => (i : ℕ) = k) = pt n k := (pt_subset_iff x k).mp hmem
        simp only [reveal, Protocol.run, hmem, decide_true, if_true, ih]
        rw [hsplit, hpt]
        congr 2
        ext i
        simp [Finset.mem_union]
        tauto
      · have hpt : x.filter (fun i : Fin n => (i : ℕ) = k) = ∅ := by
          by_contra hne
          apply hmem
          obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          simp only [Finset.mem_filter] at hi
          intro j hj
          simp only [pt, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have : j = i := Fin.ext (by rw [hj, hi.2])
          rw [this]
          exact hi.1
        simp only [reveal, Protocol.run, hmem, decide_false, ih]
        rw [hsplit, hpt]
        simp

/-- Non-vacuity / near-tightness: there is a deterministic protocol of cost `n + 1` computing
set disjointness on a universe of size `n`. -/
