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
