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

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (no imports beyond Lean's `Init`), so that the
header comment above can literally begin the file.

We study the Hardy-Littlewood data attached to a prime gap `d`:

* admissibility of the two-element tuple `{0, d}` (no prime obstruction to `n`, `n + d` being
  simultaneously prime infinitely often), and
* the singular-series factor `∏_{p ∣ d, p odd prime} (p-1)/(p-2)`, recorded as an explicit
  positive rational `gapNum d / gapDen d`.

The main result `Brockian.SingularSeriesGaps12401250` verifies both for every even gap `d` in the
range `1240 ≤ d ≤ 1250`, extending the `SingularSeriesGaps` family to this range.
-/

namespace Brockian

/-! ## Primes -/

/-- Primality, stated from first principles. -/
def IsPrimeN (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- A boolean primality test by trial division. -/
def isPrimeB (p : Nat) : Bool := 2 ≤ p && (List.range p).all (fun m => m < 2 || p % m != 0)

/-- The trial-division test decides primality. -/
theorem isPrimeB_iff (p : Nat) : isPrimeB p = true ↔ IsPrimeN p := by
  constructor
  · intro h
    simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨h2, hall⟩ := h
    refine ⟨h2, ?_⟩
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · exfalso
      have : p = 0 := Nat.eq_zero_of_zero_dvd hm
      omega
    · by_cases hm1 : m = 1
      · exact Or.inl hm1
      by_cases hmp : m = p
      · exact Or.inr hmp
      exfalso
      have hle : m ≤ p := Nat.le_of_dvd (by omega) hm
      have hlt : m < p := by omega
      have hnot := hall m hlt
      have hmod : p % m = 0 := by
        obtain ⟨c, rfl⟩ := hm
        exact Nat.mul_mod_right m c
      omega
  · intro h
    obtain ⟨h2, hdvd⟩ := h
    simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq]
    refine ⟨h2, ?_⟩
    intro m hm
    by_cases hm2 : m < 2
    · exact Or.inl hm2
    · refine Or.inr ?_
      intro hmod
      have hdvd' : m ∣ p := Nat.dvd_of_mod_eq_zero hmod
      rcases hdvd m hdvd' with rfl | rfl <;> omega

/-! ## Admissibility -/

/-- A tuple `H` of integers is *admissible* if for every prime `p` some residue class mod `p`
contains no member of `H`. -/
def Admissible (H : List Int) : Prop :=
  ∀ p : Nat, IsPrimeN p → ∃ r : Int, 0 ≤ r ∧ r < (p : Int) ∧ ∀ x ∈ H, x % (p : Int) ≠ r

/-- Every even gap `d` gives an admissible pair `{0, d}`. -/
theorem admissible_pair_of_even (d : Int) (hd : ∃ k : Int, d = 2 * k) : Admissible [0, d] := by
  intro p hp
  have h2 : 2 ≤ p := hp.1
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨1, by decide, by decide, ?_⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨k, rfl⟩ := hd
    rcases hx with rfl | rfl
    · decide
    · omega
  · have hpos : (0 : Int) < (p : Int) := by omega
    have hnn : 0 ≤ d % (p : Int) := Int.emod_nonneg d (by omega)
    have hlt : d % (p : Int) < (p : Int) := Int.emod_lt_of_pos d hpos
    by_cases h : d % (p : Int) = 1
    · refine ⟨2, by decide, by omega, ?_⟩
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [Int.zero_emod]; omega
      · omega
    · refine ⟨1, by decide, by omega, ?_⟩
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [Int.zero_emod]; omega
      · omega

/-! ## The singular-series factor -/

/-- The odd prime divisors of `d`. -/
def oddPrimeDivisors (d : Nat) : List Nat :=
  (List.range (d + 1)).filter (fun p => 3 ≤ p && isPrimeB p && d % p == 0)

/-- Membership in `oddPrimeDivisors d` means exactly what the name says. -/
theorem mem_oddPrimeDivisors {d p : Nat} (h : p ∈ oddPrimeDivisors d) :
    3 ≤ p ∧ IsPrimeN p ∧ p ∣ d := by
  simp only [oddPrimeDivisors, List.mem_filter, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨-, ⟨⟨h3, hpb⟩, hmod⟩⟩ := h
  exact ⟨h3, (isPrimeB_iff p).mp hpb, Nat.dvd_of_mod_eq_zero hmod⟩

/-- Numerator of the singular-series factor `∏_{p ∣ d, p odd prime} (p-1)/(p-2)`. -/
def gapNum (d : Nat) : Nat := (oddPrimeDivisors d).foldr (fun p acc => (p - 1) * acc) 1

/-- Denominator of the singular-series factor `∏_{p ∣ d, p odd prime} (p-1)/(p-2)`. -/
def gapDen (d : Nat) : Nat := (oddPrimeDivisors d).foldr (fun p acc => (p - 2) * acc) 1

theorem foldr_pos (c : Nat) (hc : c ≤ 2) :
    ∀ l : List Nat, (∀ p ∈ l, 3 ≤ p) → 0 < l.foldr (fun p acc => (p - c) * acc) 1
  | [], _ => Nat.zero_lt_one
  | p :: l, h => by
      have hp : 3 ≤ p := h p (List.mem_cons_self ..)
      have hrec : 0 < l.foldr (fun p acc => (p - c) * acc) 1 :=
        foldr_pos c hc l (fun q hq => h q (List.mem_cons_of_mem _ hq))
      have : 0 < p - c := by omega
      simpa using Nat.mul_pos this hrec

/-- The numerator of the singular-series factor is positive. -/
theorem gapNum_pos (d : Nat) : 0 < gapNum d :=
  foldr_pos 1 (by omega) _ (fun p hp => (mem_oddPrimeDivisors hp).1)

/-- The denominator of the singular-series factor is positive. -/
theorem gapDen_pos (d : Nat) : 0 < gapDen d :=
  foldr_pos 2 (by omega) _ (fun p hp => (mem_oddPrimeDivisors hp).1)

/-! ## Main result -/

/-- **Singular series gaps, range 1240–1250.**

For every even gap `d` with `1240 ≤ d ≤ 1250`:

* the pair `{0, d}` is an admissible tuple, i.e. no prime obstructs `n` and `n + d` from being
  simultaneously prime; and
* the associated singular-series factor `∏_{p ∣ d, p odd prime} (p-1)/(p-2)` is a well-defined
  positive rational `gapNum d / gapDen d` (both numerator and denominator are positive), so the
  Hardy–Littlewood singular series for the gap `d` does not vanish. -/
theorem SingularSeriesGaps12401250 :
    ∀ d : Nat, 1240 ≤ d → d ≤ 1250 → (∃ k : Nat, d = 2 * k) →
      Admissible [0, (d : Int)] ∧ 0 < gapNum d ∧ 0 < gapDen d := by
  intro d _ _ hd
  refine ⟨admissible_pair_of_even (d : Int) ?_, gapNum_pos d, gapDen_pos d⟩
  obtain ⟨k, hk⟩ := hd
  exact ⟨(k : Int), by omega⟩

end Brockian

