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
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` lines to come first, so the required header block
appears at the very top of the file as a plain comment and is repeated verbatim as the module
docstring immediately after `import Mathlib`.

What is discharged here: the functional-equation ("reflection of zeros") sub-lemma
`zeta_reflect_zero`, which is proved from Mathlib's `riemannZeta_one_sub`, together with the
classification of the zeros with `Re s ≤ 0` as the trivial ones.  The remaining input of the
main theorem is the Brockian non-vanishing system itself.
-/

open Complex

namespace Brockian
namespace RiemannScaffold

/-- A *Brockian system* is a witness for the non-vanishing of the Riemann zeta function
on the right half `1/2 < Re s < 1` of the critical strip. -/
structure BrockianSystem : Prop where
  /-- `ζ` has no zero with `1/2 < Re s < 1`. -/
  nonvanishing_right : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0

/-- **Discharged hypothesis (reflection of zeros).**  Originally this was a named hypothesis of
`RH_of_BrockianSystem`; it is discharged here from Mathlib's functional equation
`riemannZeta_one_sub`. -/

theorem zeta_reflect_zero {s : ℂ} (hn : ∀ n : ℕ, s ≠ -n) (h1 : s ≠ 1)
    (hz : riemannZeta s = 0) : riemannZeta (1 - s) = 0 := by
  rw [riemannZeta_one_sub hn h1, hz, mul_zero]

/-- If `Re s > 1` and `ζ (1 - s) = 0`, then `1 - s = -2 * (n + 1)` for some `n : ℕ`.
This isolates the trivial zeros. -/
