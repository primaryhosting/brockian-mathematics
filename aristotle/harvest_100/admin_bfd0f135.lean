/-!
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

/-- The *local count* `ν_p(H)` of a finite tuple `H` of integers at a modulus `p`:
the number of distinct residue classes modulo `p` occupied by the members of `H`. -/
def localCount (p : ℕ) (H : Finset ℤ) : ℕ :=
  (H.image (fun n : ℤ => (n : ZMod p))).card

/-- A finite tuple `H ⊆ ℤ` is an *admissible constellation* when, for every prime `p`,
the members of `H` fail to cover all residue classes modulo `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → localCount p H < p

/-- The local count never exceeds the size of the tuple. -/
theorem localCount_le_card (p : ℕ) (H : Finset ℤ) : localCount p H ≤ H.card :=
  Finset.card_image_le

/-- For a modulus larger than the size of the tuple, the local condition is automatic. -/
theorem localCount_lt_of_card_lt {p : ℕ} {H : Finset ℤ} (h : H.card < p) :
    localCount p H < p :=
  lt_of_le_of_lt (localCount_le_card p H) h

/-- **Local reduction.** Admissibility only has to be tested at the primes `p ≤ |H|`;
all larger primes are automatically fine. -/
theorem admissible_iff_le_card (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → p ≤ H.card → localCount p H < p := by
  constructor
  · intro h p hp _
    exact h p hp
  · intro h p hp
    rcases le_or_gt p H.card with hle | hgt
    · exact h p hp hle
    · exact localCount_lt_of_card_lt hgt

/-- Any prime other than `2` and `3` is at least `5`. -/
theorem five_le_of_prime_ne {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  by_contra hlt
  have h2le := hp.two_le
  interval_cases p
  · exact h2 rfl
  · exact h3 rfl
  · norm_num at hp

/-- **Constellation local count, `k = 3`.**

For a triple `H` of integers, admissibility as a constellation — a condition a priori
involving *all* primes — is equivalent to the two finite conditions at `p = 2` and `p = 3`:
the triple must miss a residue class mod `2` and a residue class mod `3`. -/
theorem ConstellationLocalCountK3 (H : Finset ℤ) (hH : H.card = 3) :
    Admissible H ↔ (localCount 2 H < 2 ∧ localCount 3 H < 3) := by
  constructor
  · intro h
    exact ⟨h 2 Nat.prime_two, h 3 Nat.prime_three⟩
  · rintro ⟨h2, h3⟩ p hp
    rcases eq_or_ne p 2 with rfl | hp2
    · exact h2
    rcases eq_or_ne p 3 with rfl | hp3
    · exact h3
    have h5 : 5 ≤ p := five_le_of_prime_ne hp hp2 hp3
    exact localCount_lt_of_card_lt (by omega : H.card < p)

/-- Contrapositive form: a triple fails to be an admissible constellation exactly when it
covers all residues mod `2` or all residues mod `3`. -/
theorem not_admissible_k3_iff (H : Finset ℤ) (hH : H.card = 3) :
    ¬ Admissible H ↔ (localCount 2 H = 2 ∨ localCount 3 H = 3) := by
  have hb2 : localCount 2 H ≤ 2 := by
    have := localCount_le_card 2 H
    have h2 : localCount 2 H ≤ Fintype.card (ZMod 2) :=
      Finset.card_le_univ _
    simpa using h2
  have hb3 : localCount 3 H ≤ 3 := by
    have := localCount_le_card 3 H
    omega
  rw [ConstellationLocalCountK3 H hH]
  omega

/-- The triple `{0, 2, 6}` is an admissible constellation. -/
theorem admissible_zero_two_six : Admissible ({0, 2, 6} : Finset ℤ) := by
  have hcard : ({0, 2, 6} : Finset ℤ).card = 3 := by decide
  rw [ConstellationLocalCountK3 _ hcard]
  constructor
  · show (({0, 2, 6} : Finset ℤ).image (fun n : ℤ => (n : ZMod 2))).card < 2
    norm_num [Finset.image_insert, localCount]
  · show (({0, 2, 6} : Finset ℤ).image (fun n : ℤ => (n : ZMod 3))).card < 3
    norm_num [Finset.image_insert, localCount]
    decide

/-- The triple `{0, 2, 4}` is *not* admissible: it covers every residue class mod `3`. -/
theorem not_admissible_zero_two_four : ¬ Admissible ({0, 2, 4} : Finset ℤ) := by
  intro h
  have h3 := h 3 Nat.prime_three
  have : localCount 3 ({0, 2, 4} : Finset ℤ) = 3 := by decide
  omega

end Brockian

