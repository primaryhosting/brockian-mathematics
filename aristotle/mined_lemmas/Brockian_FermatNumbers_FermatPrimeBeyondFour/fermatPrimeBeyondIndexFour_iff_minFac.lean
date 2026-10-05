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
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

-- Note: the header above is a plain block comment rather than a module docstring,
-- since Lean 4 does not allow a module docstring to precede the `import` lines.

namespace Brockian.FermatNumbers

open Nat

/-- The Fermat numbers `Fₙ = 2 ^ (2 ^ n) + 1` (Mathlib's `Nat.fermatNumber`). -/
local notation "F" => Nat.fermatNumber

/-!
## The main statement

`FermatPrimeBeyondFour`: there is a Fermat prime exceeding `4`.
-/

/-- **Fermat prime beyond four.** There exists a Fermat number `Fₙ = 2 ^ (2 ^ n) + 1`
which is greater than `4` and prime.  (Witness: `F 4 = 65537`.) -/

theorem fermatPrimeBeyondIndexFour_iff_minFac :
    FermatPrimeBeyondIndexFour ↔ ∃ n : ℕ, 4 < n ∧ (F n).minFac = F n := by
  constructor
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, hn, (Nat.prime_def_minFac.mp hp).2⟩
  · rintro ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    have h2 : 2 ≤ F n := (Nat.two_lt_fermatNumber n).le
    exact Nat.prime_def_minFac.mpr ⟨h2, h⟩

/-- **Reduction to Pépin's test.** If for some `n > 4` we have `3 ^ ((Fₙ - 1) / 2) = -1`
in `ZMod Fₙ`, then there is a Fermat prime beyond index four. -/
