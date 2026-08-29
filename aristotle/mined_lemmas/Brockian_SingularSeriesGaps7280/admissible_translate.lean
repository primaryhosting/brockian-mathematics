import Mathlib

/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
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
prime `k`-tuples conjecture) when, for every prime `p`, the elements of `H` do not cover
all residue classes modulo `p`; equivalently the local factor of the singular series
`𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}` is nonzero at every prime. -/

theorem admissible_translate (H : Finset ℤ) (t : ℤ) (hH : Admissible H) :
    Admissible (H.image (fun h => h + t)) := by
  intro p hp
  obtain ⟨r, hr⟩ := hH p hp
  refine ⟨r + t, ?_⟩
  intro h hh hdvd
  obtain ⟨h₀, hh₀, rfl⟩ := Finset.mem_image.mp hh
  have hrw : h₀ + t - (r + t) = h₀ - r := by ring
  rw [hrw] at hdvd
  exact hr h₀ hh₀ hdvd

/-- The explicit `8`-tuple `{0, 2, 6, 8, 12, 18, 20, 26}` of diameter `26`. -/
