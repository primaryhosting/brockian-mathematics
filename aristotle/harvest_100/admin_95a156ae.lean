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
def localCount (H : Finset ℤ) (p : ℕ) : ℕ :=
  (H.image (fun a : ℤ => (a : ZMod p))).card

/-- A set of integer offsets is *admissible* (i.e. forms a constellation pattern) when for
every prime `p` it fails to cover all residue classes modulo `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → localCount H p < p

/-- The local count never exceeds the number of offsets. -/
theorem localCount_le_card (H : Finset ℤ) (p : ℕ) : localCount H p ≤ H.card :=
  Finset.card_image_le

/-- The local count never exceeds the modulus, for a positive modulus. -/
theorem localCount_le_modulus (H : Finset ℤ) {p : ℕ} (hp : 0 < p) :
    localCount H p ≤ p := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have := Finset.card_le_univ (H.image (fun a : ℤ => (a : ZMod p)))
  simpa [localCount, ZMod.card p] using this

/-- A triple of offsets occupies at most three residue classes. -/
theorem localCount_triple_le_three (a b c : ℤ) (p : ℕ) :
    localCount ({a, b, c} : Finset ℤ) p ≤ 3 := by
  refine le_trans (localCount_le_card _ _) ?_
  calc ({a, b, c} : Finset ℤ).card ≤ ({b, c} : Finset ℤ).card + 1 := Finset.card_insert_le _ _
    _ ≤ (({c} : Finset ℤ).card + 1) + 1 := by
        exact Nat.add_le_add_right (Finset.card_insert_le _ _) 1
    _ = 3 := by simp

/-- For a prime `p ≥ 5`, every triple is automatically locally admissible. -/
theorem localCount_triple_lt_of_five_le (a b c : ℤ) {p : ℕ} (hp : 5 ≤ p) :
    localCount ({a, b, c} : Finset ℤ) p < p :=
  lt_of_le_of_lt (localCount_triple_le_three a b c p) (by omega)

/-- **Local count criterion for `k = 3` constellations.**
A triple of integer offsets is admissible if and only if it fails to cover all residues
modulo `2` and modulo `3`; all larger primes impose no condition. -/
theorem ConstellationLocalCountK3 (a b c : ℤ) :
    Admissible ({a, b, c} : Finset ℤ) ↔
      (localCount ({a, b, c} : Finset ℤ) 2 < 2 ∧ localCount ({a, b, c} : Finset ℤ) 3 < 3) := by
  constructor
  · intro h
    exact ⟨h 2 Nat.prime_two, h 3 Nat.prime_three⟩
  · rintro ⟨h2, h3⟩ p hp
    rcases lt_or_ge p 5 with hlt | hge
    · interval_cases p
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
      · exact h2
      · exact h3
      · exact absurd hp (by decide)
    · exact localCount_triple_lt_of_five_le a b c hge

/-- A triple occupies exactly three residue classes mod `p` precisely when its three members
are pairwise incongruent mod `p`. -/
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
theorem admissible_zero_two_six : Admissible ({0, 2, 6} : Finset ℤ) :=
  (ConstellationLocalCountK3 0 2 6).mpr ⟨by decide, by decide⟩

/-- Sanity check: the triple `(0, 1, 2)` is not admissible, since it covers all residues mod `3`. -/
theorem not_admissible_zero_one_two : ¬ Admissible ({0, 1, 2} : Finset ℤ) := by
  intro h
  have h3 := h 3 Nat.prime_three
  revert h3
  decide

end Brockian

