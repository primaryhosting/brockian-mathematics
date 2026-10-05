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

-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is
-- repeated below verbatim as this module's docstring.)
import Mathlib

/-!
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FermatNumbers

open Nat

/-- Pépin's condition for the `n`-th Fermat number `Fₙ = 2 ^ (2 ^ n) + 1`:
`3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`. -/

lemma legendreSym_three_eq_neg_one (p : ℕ) [Fact p.Prime] (h4 : p % 4 = 1) (h3 : p % 3 = 2) :
    legendreSym p 3 = -1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hqr : legendreSym 3 (p : ℤ) = legendreSym p 3 :=
    legendreSym.quadratic_reciprocity_one_mod_four h4 (by norm_num)
  have hmod : legendreSym 3 (p : ℤ) = legendreSym 3 ((p : ℤ) % ((3 : ℕ) : ℤ)) :=
    legendreSym.mod (p := 3) _
  have hcast : ((p : ℤ) % ((3 : ℕ) : ℤ)) = 2 := by push_cast; omega
  rw [← hqr, hmod, hcast]
  exact legendreSym_three_two

/-- **Pépin's test, necessity.** If the `n`-th Fermat number (`n ≥ 1`) is prime, then
`3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`. -/
