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

/-
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Note: the requested header is written as a plain block comment `/- ... -/` rather than a
-- module doc comment `/-! ... -/`, because Lean 4 requires `import` to precede every command,
-- and a module doc comment counts as a command.  The text is otherwise verbatim.)

import Mathlib

set_option maxHeartbeats 1000000

namespace Brockian.FortunateNumbers

open Finset

/-- `IsFortunate n m` says that `m` is *the* Fortunate number attached to the primorial `n#`:
it is the least integer `m > 1` such that `n# + m` is prime. -/

theorem prime_factor_gt {n m : ℕ} (h : IsFortunate n m) {p : ℕ} (hp : p.Prime)
    (hpm : p ∣ m) : n < p := by
  obtain ⟨hm1, hprime, -⟩ := h
  by_contra hle
  push_neg at hle
  have hdvd : p ∣ primorial n := prime_dvd_primorial hp hle
  have hdvd' : p ∣ primorial n + m := Dvd.dvd.add hdvd hpm
  have hple : p ≤ primorial n := Nat.le_of_dvd (primorial_pos n) hdvd
  have := (hprime.eq_one_or_self_of_dvd p hdvd').resolve_left hp.ne_one
  omega

/-- Consequently, a *composite* Fortunate number would have to be at least `(n+1)^2`. -/
