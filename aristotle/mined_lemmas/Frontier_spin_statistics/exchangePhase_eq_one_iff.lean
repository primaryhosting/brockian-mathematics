/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-!
## The spin–statistics connection

The spin–statistics theorem of relativistic quantum field theory states that a field of
integer spin must be quantized with commutators (Bose statistics) and a field of
half-odd-integer spin with anticommutators (Fermi statistics); equivalently, the exchange
phase of a field of spin `j` is `(-1)^(2j)`.  Quantizing with the *wrong* statistics forces
the field to vanish identically (Pauli's argument, in the Wightman framework:
Streater–Wightman, *PCT, Spin and Statistics, and All That*).

Below, spin is recorded by the natural number `s = 2j` ("twice the spin"), so that integer
spin means `Even s` and half-odd-integer spin means `Odd s`.  The exchange phase is
`exchangePhase s = (-1)^s`.

The main theorem `Frontier.spin_statistics` is the Pauli argument, formalized as a
Lean-checked *reduction*: from
* the abstract Wightman data (a complex inner-product space of states, a vacuum vector,
  smeared field operators together with their adjoints), and
* the identity relating the two orders of the two-point function which the analytic
  continuation step of the proof (Lorentz covariance + locality + edge-of-the-wedge)
  produces, carrying the sign `ε · (-1)^s`,

positivity of the inner product forces the field and its adjoint to annihilate the vacuum
whenever `ε ≠ (-1)^s`, i.e. whenever the statistics is wrong for the spin.  If in addition
the vacuum is separating, the field vanishes identically.

The only genuinely nontrivial Mathlib input is positivity of the inner product,
`inner_self_eq_norm_sq_to_K` together with `inner_self_eq_zero`.
-/

/-- The exchange phase of a field of spin `j`, where `s = 2j` is twice the spin:
`(-1)^(2j)`. -/

@[simp] lemma exchangePhase_eq_one_iff (s : ℕ) : exchangePhase s = 1 ↔ IsBosonic s := by
  simpa [exchangePhase, IsBosonic] using (neg_one_pow_eq_one_iff_even (R := ℤ) (by norm_num))

