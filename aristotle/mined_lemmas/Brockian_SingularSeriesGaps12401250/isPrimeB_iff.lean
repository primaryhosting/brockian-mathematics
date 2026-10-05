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
