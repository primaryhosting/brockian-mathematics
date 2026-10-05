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

/-- A finite set of integer shifts `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture: the associated singular series is
nonzero) when for every prime `p` the shifts miss at least one residue class
modulo `p`. -/

theorem admissible_map_add (H : Finset ℤ) (hH : Admissible H) (c : ℤ) :
    Admissible (H.image (fun h => h + c)) := by
  intro p hp
  obtain ⟨r, hr⟩ := hH p hp
  refine ⟨r + (c : ZMod p), ?_⟩
  intro h hh
  simp only [Finset.mem_image] at hh
  obtain ⟨h₀, hh₀, rfl⟩ := hh
  have := hr h₀ hh₀
  push_cast
  exact fun hc => this (add_right_cancel hc)

/--
**Singular Series Gaps 9098.**

Admissibility of a finite set of integer shifts (nonvanishing of the associated
singular series in the Hardy–Littlewood prime `k`-tuples conjecture) needs to be
tested only at the primes `p ≤ |H|`, since larger primes are automatically
missed for cardinality reasons.  Consequently the gap pattern `{0, 2, 6, 8, 12}`
is admissible, and so is every translate of it, giving admissible ranges
`{c, c+2, c+6, c+8, c+12}` of diameter `12` at every starting point `c`.
-/
