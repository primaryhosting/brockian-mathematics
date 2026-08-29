import Mathlib
import RequestProject.Main

/-!
# Admissibility of 4-tuples, `ZMod` formulation

Companion to `RequestProject.Main`.  The main file is developed without `import`s (its header
comment must be the very first thing in the file, which rules out importing Mathlib), so the
notions used there — primality and "the tuple avoids a residue class mod `p`" — are spelled out
from first principles.  Here we check, using Mathlib, that those notions agree with the
standard ones (`Nat.Prime` and non-surjectivity into `ZMod p`), and restate the main theorem
`Brockian.AdmissibilityKTupleK4` in that language.
-/

namespace Brockian

/-- The primality notion of `RequestProject.Main` is Mathlib's `Nat.Prime`. -/
theorem isPrime_iff_nat_prime (p : ℕ) : IsPrime p ↔ Nat.Prime p :=
  Nat.prime_def.symm

/-- Avoiding the residue class of `r` modulo `p` in the divisibility sense is the same as
avoiding the image of `r` in `ZMod p`. -/
theorem not_dvd_sub_iff_zmod_ne (p : ℕ) (a r : ℤ) :
    ¬ ((p : ℤ) ∣ (a - r)) ↔ ((a : ZMod p) ≠ (r : ZMod p)) := by
  rw [Ne, ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
  constructor
  · intro h hd
    exact h (by simpa using (dvd_neg.mpr hd))
  · intro h hd
    exact h (by simpa using (dvd_neg.mpr hd))

/-- Admissibility, as defined in `RequestProject.Main`, is the standard notion: for every prime
`p` the residues of the tuple do not cover all of `ZMod p`. -/
theorem admissible_iff_zmod {k : ℕ} (h : Fin k → ℤ) :
    Admissible h ↔ ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ i, ((h i : ZMod p)) ≠ r := by
  constructor
  · intro H p hp
    obtain ⟨r, hr⟩ := H p ((isPrime_iff_nat_prime p).mpr hp)
    exact ⟨(r : ZMod p), fun i => (not_dvd_sub_iff_zmod_ne p (h i) r).mp (hr i)⟩
  · intro H p hp
    obtain ⟨r, hr⟩ := H p ((isPrime_iff_nat_prime p).mp hp)
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective (n := p) r
    exact ⟨z, fun i => (not_dvd_sub_iff_zmod_ne p (h i) z).mpr (hr i)⟩

/-- **Admissibility of 4-tuples, `ZMod` form.**  A 4-tuple of integers is admissible
(no prime `p` has all of `ZMod p` covered by its residues) if and only if this already holds
for the two primes `p = 2` and `p = 3`. -/
theorem admissibility_kTuple_k4_zmod (h : Fin 4 → ℤ) :
    (∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ i, ((h i : ZMod p)) ≠ r) ↔
      ((∃ r : ZMod 2, ∀ i, ((h i : ZMod 2)) ≠ r) ∧
       (∃ r : ZMod 3, ∀ i, ((h i : ZMod 3)) ≠ r)) := by
  rw [← admissible_iff_zmod, AdmissibilityKTupleK4]
  constructor
  · rintro ⟨⟨r2, hr2⟩, ⟨r3, hr3⟩⟩
    refine ⟨⟨(r2 : ZMod 2), fun i => ?_⟩, ⟨(r3 : ZMod 3), fun i => ?_⟩⟩
    · simpa using (not_dvd_sub_iff_zmod_ne 2 (h i) r2).mp (by simpa using hr2 i)
    · simpa using (not_dvd_sub_iff_zmod_ne 3 (h i) r3).mp (by simpa using hr3 i)
  · rintro ⟨⟨r2, hr2⟩, ⟨r3, hr3⟩⟩
    obtain ⟨z2, rfl⟩ := ZMod.intCast_surjective (n := 2) r2
    obtain ⟨z3, rfl⟩ := ZMod.intCast_surjective (n := 3) r3
    refine ⟨⟨z2, fun i => ?_⟩, ⟨z3, fun i => ?_⟩⟩
    · simpa using (not_dvd_sub_iff_zmod_ne 2 (h i) z2).mpr (hr2 i)
    · simpa using (not_dvd_sub_iff_zmod_ne 3 (h i) z3).mpr (hr3 i)

end Brockian

/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no `import`s): Lean requires every `import`
command to precede all other syntax, so keeping the header comment above at the very top
of the file rules out importing Mathlib.  Everything below is therefore developed from
first principles using only the Lean 4 core library.
-/

namespace Brockian

/-- Primality of a natural number, in the usual sense: `p ≥ 2` and every divisor of `p`
is either `1` or `p`. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

theorem isPrime_two : IsPrime 2 := by
  refine ⟨by omega, ?_⟩
  intro m hm
  have hle : m ≤ 2 := Nat.le_of_dvd (by omega) hm
  match m, hle, hm with
  | 0, _, hm => exact absurd hm (by omega)
  | 1, _, _ => exact Or.inl rfl
  | 2, _, _ => exact Or.inr rfl
  | (_ + 3), hle, _ => exact absurd hle (by omega)

theorem isPrime_three : IsPrime 3 := by
  refine ⟨by omega, ?_⟩
  intro m hm
  have hle : m ≤ 3 := Nat.le_of_dvd (by omega) hm
  match m, hle, hm with
  | 0, _, hm => exact absurd hm (by omega)
  | 1, _, _ => exact Or.inl rfl
  | 2, _, hm => exact absurd hm (by omega)
  | 3, _, _ => exact Or.inr rfl
  | (_ + 4), hle, _ => exact absurd hle (by omega)

theorem not_isPrime_four : ¬ IsPrime 4 := by
  intro hp
  cases hp.2 2 ⟨2, rfl⟩ with
  | inl h => exact absurd h (by omega)
  | inr h => exact absurd h (by omega)

/-- A prime other than `2` and `3` is at least `5`. -/
theorem five_le_of_isPrime {p : Nat} (hp : IsPrime p) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  have h4 : p ≠ 4 := by
    intro he
    exact not_isPrime_four (he ▸ hp)
  have := hp.1
  omega

/-- A `k`-tuple of integers `h : Fin k → ℤ` is *admissible* if for every prime `p` some
residue class `r` modulo `p` is avoided by the whole tuple, i.e. `p ∤ h i - r` for all `i`.
(Equivalently: the residues `h i mod p` do not cover all of `ZMod p`.) -/
def Admissible {k : Nat} (h : Fin k → Int) : Prop :=
  ∀ p : Nat, IsPrime p → ∃ r : Int, ∀ i, ¬ ((p : Int) ∣ (h i - r))

/-- If two entries of a tuple are congruent to `a` and to `b` modulo `p`, with `a ≠ b`
and `|a - b| ≤ 4 < p`, then the two entries sit at different indices. -/
theorem index_ne_of_dvd {p : Nat} (hp : 5 ≤ p) (h : Fin 4 → Int) (a b : Int) (i j : Fin 4)
    (hi : (p : Int) ∣ (h i - a)) (hj : (p : Int) ∣ (h j - b)) (hab : a ≠ b)
    (hl : -4 ≤ a - b) (hu : a - b ≤ 4) : i.val ≠ j.val := by
  intro hv
  have hij : i = j := Fin.eq_of_val_eq hv
  subst hij
  have e1 : (h i - a) - (h i - b) = b - a := by omega
  have e2 : (h i - b) - (h i - a) = a - b := by omega
  have hd1 : (p : Int) ∣ (b - a) := e1 ▸ Int.dvd_sub hi hj
  have hd2 : (p : Int) ∣ (a - b) := e2 ▸ Int.dvd_sub hj hi
  have hcast : (5 : Int) ≤ (p : Int) := by exact_mod_cast hp
  have hne : a - b ≠ 0 := by omega
  cases Int.lt_or_lt_of_ne hne with
  | inl hlt => have := Int.le_of_dvd (by omega) hd1; omega
  | inr hgt => have := Int.le_of_dvd (by omega) hd2; omega

/-- **Pigeonhole step.**  A tuple of length `4` cannot meet all residue classes modulo a
number `p ≥ 5`: among the five classes `0, 1, 2, 3, 4` some class is missed. -/
theorem missed_residue_of_five_le {p : Nat} (hp : 5 ≤ p) (h : Fin 4 → Int) :
    ∃ r : Int, ∀ i : Fin 4, ¬ ((p : Int) ∣ (h i - r)) := by
  apply Classical.byContradiction
  intro hcon
  have key : ∀ r : Int, ∃ i : Fin 4, (p : Int) ∣ (h i - r) := by
    intro r
    apply Classical.byContradiction
    intro hne
    exact hcon ⟨r, fun i hd => hne ⟨i, hd⟩⟩
  cases key 0 with | intro i0 d0 =>
  cases key 1 with | intro i1 d1 =>
  cases key 2 with | intro i2 d2 =>
  cases key 3 with | intro i3 d3 =>
  cases key 4 with | intro i4 d4 =>
  have n01 := index_ne_of_dvd hp h 0 1 i0 i1 d0 d1 (by decide) (by decide) (by decide)
  have n02 := index_ne_of_dvd hp h 0 2 i0 i2 d0 d2 (by decide) (by decide) (by decide)
  have n03 := index_ne_of_dvd hp h 0 3 i0 i3 d0 d3 (by decide) (by decide) (by decide)
  have n04 := index_ne_of_dvd hp h 0 4 i0 i4 d0 d4 (by decide) (by decide) (by decide)
  have n12 := index_ne_of_dvd hp h 1 2 i1 i2 d1 d2 (by decide) (by decide) (by decide)
  have n13 := index_ne_of_dvd hp h 1 3 i1 i3 d1 d3 (by decide) (by decide) (by decide)
  have n14 := index_ne_of_dvd hp h 1 4 i1 i4 d1 d4 (by decide) (by decide) (by decide)
  have n23 := index_ne_of_dvd hp h 2 3 i2 i3 d2 d3 (by decide) (by decide) (by decide)
  have n24 := index_ne_of_dvd hp h 2 4 i2 i4 d2 d4 (by decide) (by decide) (by decide)
  have n34 := index_ne_of_dvd hp h 3 4 i3 i4 d3 d4 (by decide) (by decide) (by decide)
  have b0 := i0.isLt
  have b1 := i1.isLt
  have b2 := i2.isLt
  have b3 := i3.isLt
  have b4 := i4.isLt
  omega

/-- **Admissibility of 4-tuples.**  For a `4`-tuple of integers the infinite family of
conditions defining admissibility (one condition per prime) collapses to just the two
conditions at the primes `2` and `3`: at every prime `p ≥ 5` a `4`-tuple automatically
misses a residue class, since `4 < p`. -/
theorem AdmissibilityKTupleK4 (h : Fin 4 → Int) :
    Admissible h ↔
      ((∃ r : Int, ∀ i, ¬ ((2 : Int) ∣ (h i - r))) ∧
       (∃ r : Int, ∀ i, ¬ ((3 : Int) ∣ (h i - r)))) := by
  constructor
  · intro H
    exact ⟨H 2 isPrime_two, H 3 isPrime_three⟩
  · intro H p hp
    by_cases hp2 : p = 2
    · subst hp2
      exact_mod_cast H.1
    by_cases hp3 : p = 3
    · subst hp3
      exact_mod_cast H.2
    exact missed_residue_of_five_le (five_le_of_isPrime hp hp2 hp3) h

/-- The 4-tuple `(0, 2, 6, 8)`. -/
def tuple0268 : Fin 4 → Int :=
  fun i => if i.val = 0 then 0 else if i.val = 1 then 2 else if i.val = 2 then 6 else 8

/-- Sanity check for the criterion: the prime constellation `(0, 2, 6, 8)` is admissible. -/
theorem admissible_tuple0268 : Admissible tuple0268 := by
  rw [AdmissibilityKTupleK4]
  exact ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩

end Brockian

