/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
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

/-- A finite set of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) if for every prime `p` the elements of `H` do not cover all
residue classes modulo `p`; equivalently the singular series attached to `H` is nonzero. -/

lemma primeBlock_mem_bounds {k : ℕ} {h : ℤ} (hh : h ∈ primeBlock k) :
    (Nat.nth Nat.Prime k : ℤ) ≤ h ∧ h ≤ (Nat.nth Nat.Prime (2 * k) : ℤ) := by
  rw [primeBlock, Finset.mem_image] at hh
  obtain ⟨i, hi, rfl⟩ := hh
  have hi' : i < k := Finset.mem_range.mp hi
  have hmono := (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone
  constructor
  · exact_mod_cast hmono (Nat.le_add_right k i)
  · exact_mod_cast hmono (by omega : k + i ≤ 2 * k)

