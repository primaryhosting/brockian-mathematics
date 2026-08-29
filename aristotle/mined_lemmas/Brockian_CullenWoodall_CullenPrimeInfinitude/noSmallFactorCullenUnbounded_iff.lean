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

import Mathlib

/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed immediately after `import Mathlib` because Lean 4
requires `import` commands to precede every other command, including module
docstrings; the header text itself is verbatim.)
-/

set_option maxHeartbeats 1000000

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem noSmallFactorCullenUnbounded_iff :
    NoSmallFactorCullenUnbounded ↔ {n : ℕ | (cullen n).Prime}.Infinite := by
  refine ⟨CullenPrimeInfinitude, ?_⟩
  intro hinf N
  obtain ⟨n, hn, hgt⟩ : ∃ n ∈ {n : ℕ | (cullen n).Prime}, N < n := by
    by_contra hcon
    push_neg at hcon
    exact hinf.not_bddAbove ⟨N, fun x hx => hcon x hx⟩
  refine ⟨n, le_of_lt hgt, ?_⟩
  intro p hp hple hdvd
  have hprime : (cullen n).Prime := hn
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
  · exact hp.one_lt.ne' h
  · subst h
    nlinarith [hp.two_le]

end Brockian.CullenWoodall

