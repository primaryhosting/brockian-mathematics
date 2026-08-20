/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of Hardy–Littlewood, i.e. the
singular series `𝔖(H)` is nonzero) when for every prime `p` some residue class mod `p`
contains no element of `H`. -/

theorem admissible_pair_iff (n : ℤ) : Admissible ({0, n} : Finset ℤ) ↔ Even n := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := h 2 Nat.prime_two
    have h0 := hr 0 (by simp)
    have hn := hr n (by simp)
    simp only [Nat.cast_ofNat, zero_sub] at h0 hn
    rw [Int.even_iff]
    omega
  · intro hn p hp
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨1, ?_⟩
      intro h hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      obtain ⟨m, hm⟩ := hn
      rcases hh with rfl | rfl <;> intro hd <;> simp at hd
      omega
    · exact pair_odd_prime n p hp hp2

/-- The admissible gaps in the range `[1350, 1360]`. -/
