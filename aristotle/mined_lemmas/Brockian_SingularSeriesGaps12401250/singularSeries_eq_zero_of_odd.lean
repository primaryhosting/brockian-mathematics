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

namespace Brockian

/-- A finite set of integers is *admissible* (in the sense of the prime `k`-tuples
conjecture) if for every prime `p` it fails to cover all residue classes modulo `p`. -/

theorem singularSeries_eq_zero_of_odd {h : ℕ} (ho : Odd h) : singularSeries h = 0 := by
  rw [singularSeries, if_neg]
  rintro ⟨he, -⟩
  exact (Nat.not_even_iff_odd.mpr ho) he

/-- **Admissible gap ranges 1240–1250.**  For every gap `h` with `1240 ≤ h ≤ 1250`, the pair
`{0, h}` is admissible if and only if `h` is even, and this happens exactly when the
Hardy–Littlewood singular series for the gap `h` is positive (it vanishes otherwise).

(The upper bound `h ≤ 1250` is kept because the statement is about the range 1240–1250, but
the proof only uses `1240 ≤ h` — indeed the underlying equivalences hold for all `h`.) -/
