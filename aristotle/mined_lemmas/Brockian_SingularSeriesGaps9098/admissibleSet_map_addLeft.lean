/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
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

/-- A finite set of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) when, for every prime `p`, it misses at least one
residue class modulo `p`.  Equivalently, the singular series attached to the tuple
is nonzero. -/

theorem admissibleSet_map_addLeft {H : Finset ℤ} (hH : AdmissibleSet H) (a : ℤ) :
    AdmissibleSet (H.image (fun x => a + x)) := by
  intro p hp
  obtain ⟨r, hr⟩ := hH p hp
  refine ⟨(a : ZMod p) + r, ?_⟩
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have := hr y hy
  push_cast
  simpa using this

/-- Only the primes `p ≤ #H` need to be checked for admissibility: for larger primes
the pigeonhole principle supplies a missing residue class. -/
