/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number: `2 ≤ p` and the only divisors of `p` are `1` and `p`.
(This is the usual notion of a prime natural number.) -/
def NatPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- A list of offsets `H` is *admissible* when, for every prime `p`, the offsets fail to
cover all residue classes modulo `p`; equivalently, every local factor of the
Hardy–Littlewood singular series attached to `H` is nonzero. -/
def Admissible (H : List Nat) : Prop :=
  ∀ p : Nat, NatPrime p → ∃ r, r < p ∧ ∀ h ∈ H, h % p ≠ r

/-- A number with a divisor other than `1` and itself is not prime. -/
theorem not_natPrime_of_dvd {p a : Nat} (ha1 : a ≠ 1) (hap : a ≠ p) (h : a ∣ p) :
    ¬ NatPrime p := by
  intro hp
  rcases hp.2 a h with h1 | h2
  · exact ha1 h1
  · exact hap h2

/-- The eight-element gap pattern of diameter `26`. -/
def gapTuple : List Nat := [0, 2, 6, 8, 12, 18, 20, 26]

/-- For primes larger than the diameter of the pattern, the residue `1` is omitted. -/
theorem gapTuple_missing_one {p : Nat} (hp : 26 < p) : ∀ h ∈ gapTuple, h % p ≠ 1 := by
  intro h hh
  have hle : h ≤ 26 := by revert h; decide
  have hne : h ≠ 1 := by revert h hh; decide
  rw [Nat.mod_eq_of_lt (by omega)]
  exact hne

/-- The pattern `{0, 2, 6, 8, 12, 18, 20, 26}` is admissible. -/
theorem gapTuple_admissible : Admissible gapTuple := by
  intro p hp
  by_cases hbig : 26 < p
  · exact ⟨1, by omega, gapTuple_missing_one hbig⟩
  · have h2 := hp.1
    have hcases : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨
        p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 ∨ p = 17 ∨ p = 18 ∨ p = 19 ∨
        p = 20 ∨ p = 21 ∨ p = 22 ∨ p = 23 ∨ p = 24 ∨ p = 25 ∨ p = 26 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, by omega, by decide⟩
    · exact ⟨1, by omega, by decide⟩
    · exact absurd hp (not_natPrime_of_dvd (a := 2) (by decide) (by decide) ⟨2, by decide⟩)
    · exact ⟨4, by omega, by decide⟩
    · exact absurd hp (not_natPrime_of_dvd (a := 2) (by decide) (by decide) ⟨3, by decide⟩)
    · exact ⟨3, by omega, by decide⟩
    · exact absurd hp (not_natPrime_of_dvd (a := 2) (by decide) (by decide) ⟨4, by decide⟩)
    · exact absurd hp (not_natPrime_of_dvd (a := 3) (by decide) (by decide) ⟨3, by decide⟩)
    · exact absurd hp (not_natPrime_of_dvd (a := 2) (by decide) (by decide) ⟨5, by decide⟩)
    · exact ⟨3, by omega, by decide⟩
    · exact absurd hp (not_natPrime_of_dvd (a := 2) (by decide) (by decide) ⟨6, by decide⟩)
    · exact ⟨1, by omega, by decide⟩
    · exact absurd hp (not_natPrime_of_dvd (a := 2) (by decide) (by decide) ⟨7, by decide⟩)
    · exact absurd hp (not_natPrime_of_dvd (a := 3) (by decide) (by decide) ⟨5, by decide⟩)
    · exact absurd hp (not_natPrime_of_dvd (a := 2) (by decide) (by decide) ⟨8, by decide⟩)
    · exact ⟨4, by omega, by decide⟩
    · exact absurd hp (not_natPrime_of_dvd (a := 2) (by decide) (by decide) ⟨9, by decide⟩)
    · exact ⟨3, by omega, by decide⟩
    · exact absurd hp (not_natPrime_of_dvd (a := 2) (by decide) (by decide) ⟨10, by decide⟩)
    · exact absurd hp (not_natPrime_of_dvd (a := 3) (by decide) (by decide) ⟨7, by decide⟩)
    · exact absurd hp (not_natPrime_of_dvd (a := 2) (by decide) (by decide) ⟨11, by decide⟩)
    · exact ⟨1, by omega, by decide⟩
    · exact absurd hp (not_natPrime_of_dvd (a := 2) (by decide) (by decide) ⟨12, by decide⟩)
    · exact absurd hp (not_natPrime_of_dvd (a := 5) (by decide) (by decide) ⟨5, by decide⟩)
    · exact absurd hp (not_natPrime_of_dvd (a := 2) (by decide) (by decide) ⟨13, by decide⟩)

/-- **Singular series gaps 16021610.**  The gap pattern `{0, 2, 6, 8, 12, 18, 20, 26}` is an
admissible `8`-tuple of diameter `26`: its entries are pairwise distinct, both endpoints `0`
and `26` occur, every entry lies in `[0, 26]`, and for every prime `p` the pattern omits at
least one residue class modulo `p` (so no prime obstructs the pattern and every local factor
of the associated singular series is nonzero). -/
theorem SingularSeriesGaps16021610 :
    Admissible gapTuple ∧ gapTuple.length = 8 ∧ gapTuple.Nodup ∧
      0 ∈ gapTuple ∧ 26 ∈ gapTuple ∧ ∀ h ∈ gapTuple, h ≤ 26 :=
  ⟨gapTuple_admissible, by decide, by decide, by decide, by decide, by decide⟩

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

