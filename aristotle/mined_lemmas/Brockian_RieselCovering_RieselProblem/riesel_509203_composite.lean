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
import Brockian.RieselCovering

/-!
# Riesel problem, Mathlib-facing statement

`Brockian.RieselCovering` must begin with a mandated header comment, which forces it to be
import-free (Lean requires `import`s to come first in a file).  This module imports Mathlib and
restates the main result using Mathlib's `Nat.Prime`.
-/

namespace Brockian
namespace RieselCovering


theorem riesel_509203_composite (n : ℕ) (hn : 1 ≤ n) :
    ∃ d, d ∣ 509203 * 2 ^ n - 1 ∧ 1 < d ∧ d < 509203 * 2 ^ n - 1 := by
  have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hbig : 1 < 509203 * 2 ^ n - 1 := by simp only [pow_one] at h2; omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := 509203 * 2 ^ n - 1) (by omega)
  refine ⟨p, hpd, hp.one_lt, ?_⟩
  rcases lt_or_eq_of_le (Nat.le_of_dvd (by omega) hpd) with h | h
  · exact h
  · exact absurd (h ▸ hp) (riesel_509203_not_prime n hn)

end RieselCovering
end Brockian

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE ON IMPORTS: Lean requires `import` commands to precede every other command,
-- including module docstrings such as the mandated header above.  The development below is
-- therefore written so that it needs no imports at all (only Lean's automatic `Init`).
-- The companion module `Brockian.RieselCoveringMathlib` imports Mathlib and restates the
-- main theorem with Mathlib's `Nat.Prime`.

namespace Brockian
namespace RieselCovering

/-- Primality of a natural number, spelled out (equivalent to Mathlib's `Nat.Prime`;
see `Brockian.RieselCoveringMathlib`). -/
