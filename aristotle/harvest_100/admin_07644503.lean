import Mathlib

/-!
# Local constellation counts for `k`-tuples

For a tuple `H : Fin k → ℤ` (a candidate *prime constellation* / admissible tuple)
and a prime `p`, the **local count** `localCount p H` is the number of distinct
residue classes modulo `p` occupied by the entries of `H`.  The tuple is
**admissible** when `localCount p H < p` for every prime `p`, i.e. no prime
completely covered by the tuple obstructs the tuple from being a prime
constellation infinitely often.

The main results here reduce admissibility to a finite check:

* `Brockian.ConstellationLocalCountK2` : for `k = 2` admissibility is exactly the
  condition at `p = 2`;
* `Brockian.ConstellationLocalCountK3` : for `k = 3` admissibility is exactly the
  conjunction of the conditions at `p = 2` and `p = 3`.
-/

namespace Brockian

open Finset

/-- The number of distinct residue classes modulo `p` occupied by the entries of
the tuple `H`. -/
def localCount (p : ℕ) {k : ℕ} (H : Fin k → ℤ) : ℕ :=
  (Finset.image (fun i => ((H i : ZMod p))) Finset.univ).card

/-- A tuple is admissible when, for every prime `p`, its entries miss at least one
residue class modulo `p`. -/
def Admissible {k : ℕ} (H : Fin k → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → localCount p H < p

/-- A `k`-tuple occupies at most `k` residue classes modulo any `p`. -/
theorem localCount_le (p : ℕ) {k : ℕ} (H : Fin k → ℤ) : localCount p H ≤ k := by
  refine le_trans (Finset.card_image_le) ?_
  simp [Finset.card_univ]

/-- Primes larger than the length of the tuple never obstruct admissibility. -/
theorem localCount_lt_of_lt {p k : ℕ} (H : Fin k → ℤ) (h : k < p) :
    localCount p H < p :=
  lt_of_le_of_lt (localCount_le p H) h

/-- Admissibility of a tuple only needs to be checked at primes `p ≤ k`. -/
theorem admissible_iff_forall_le {k : ℕ} (H : Fin k → ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → p ≤ k → localCount p H < p := by
  constructor
  · intro h p hp _
    exact h p hp
  · intro h p hp
    by_cases hpk : p ≤ k
    · exact h p hp hpk
    · exact localCount_lt_of_lt H (lt_of_not_ge hpk)

/-- **Local constellation count, `k = 2`.**  A pair of integers is admissible iff
its two entries occupy a single residue class modulo `2`, i.e. iff they have the
same parity. -/
theorem ConstellationLocalCountK2 (H : Fin 2 → ℤ) :
    Admissible H ↔ localCount 2 H < 2 := by
  rw [admissible_iff_forall_le]
  constructor
  · intro h
    exact h 2 Nat.prime_two le_rfl
  · intro h p hp hp2
    have hp2' : 2 ≤ p := hp.two_le
    interval_cases p
    · exact h

/-- **Local constellation count, `k = 3`.**  A triple of integers is admissible iff
it misses a residue class modulo `2` and a residue class modulo `3`; no other prime
imposes a condition. -/
theorem ConstellationLocalCountK3 (H : Fin 3 → ℤ) :
    Admissible H ↔ localCount 2 H < 2 ∧ localCount 3 H < 3 := by
  rw [admissible_iff_forall_le]
  constructor
  · intro h
    exact ⟨h 2 Nat.prime_two (by norm_num), h 3 Nat.prime_three le_rfl⟩
  · rintro ⟨h2, h3⟩ p hp hp3
    have hp2 : 2 ≤ p := hp.two_le
    interval_cases p
    · exact h2
    · exact h3

/-- The parity form of the `p = 2` condition for a triple: all three entries lie in
the same class mod `2`. -/
theorem localCount_two_lt_two_iff (H : Fin 3 → ℤ) :
    localCount 2 H < 2 ↔ ∀ i j, ((H i : ZMod 2)) = ((H j : ZMod 2)) := by
  constructor
  · intro h i j
    by_contra hne
    have hsub : ({(H i : ZMod 2), (H j : ZMod 2)} : Finset (ZMod 2)) ⊆
        Finset.image (fun i => ((H i : ZMod 2))) Finset.univ := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton] at hcard
    rw [localCount] at h
    omega
  · intro h
    have : Finset.image (fun i => ((H i : ZMod 2))) Finset.univ
        = {((H 0 : ZMod 2))} := by
      apply Finset.eq_singleton_iff_unique_mem.2
      refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ 0), ?_⟩
      rintro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact h i 0
    simp [localCount, this]

/-- The triple `(0, 2, 6)` is admissible. -/
theorem admissible_zero_two_six : Admissible ![(0 : ℤ), 2, 6] := by
  rw [ConstellationLocalCountK3]
  constructor
  · have h2 : Finset.image (fun i => ((![(0 : ℤ), 2, 6] i : ZMod 2))) Finset.univ = {0} := by
      decide
    rw [localCount, h2]
    decide
  · have h3 : Finset.image (fun i => ((![(0 : ℤ), 2, 6] i : ZMod 3))) Finset.univ = {0, 2} := by
      decide
    rw [localCount, h3]
    decide

/-- The triple `(0, 2, 4)` is *not* admissible: it covers all residues mod `3`. -/
theorem not_admissible_zero_two_four : ¬ Admissible ![(0 : ℤ), 2, 4] := by
  intro h
  have h3 := h 3 Nat.prime_three
  have : Finset.image (fun i => ((![(0 : ℤ), 2, 4] i : ZMod 3))) Finset.univ = {0, 1, 2} := by
    decide
  rw [localCount, this] at h3
  revert h3
  decide

end Brockian

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

