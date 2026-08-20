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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GilbreathConjecture

/-! ## Primes -/

/-- `n` is prime: it is at least `2` and has no divisor `d` with `2 ≤ d < n`. -/

theorem isOdlyzko_diffSeq {a : Nat → Nat} {n : Nat} (h : IsOdlyzko a (n + 1)) :
    IsOdlyzko (diffSeq a) n := by
  obtain ⟨h0, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have h1 : a 1 = 0 ∨ a 1 = 2 := h2 1 (by omega) (by omega)
    rcases h1 with h1 | h1 <;> simp [diffSeq, adist, h0, h1]
  · intro i hi hin
    have hai : a i = 0 ∨ a i = 2 := h2 i hi (by omega)
    have hai1 : a (i + 1) = 0 ∨ a (i + 1) = 2 := h2 (i + 1) (by omega) (by omega)
    rcases hai with h | h <;> rcases hai1 with h' | h' <;>
      simp [diffSeq, adist, h, h']

/-- If a row has the shape `1, 0/2, …, 0/2` with `n` entries in `{0, 2}`, then each
of the following `n` rows again begins with `1`. -/
