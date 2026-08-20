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
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to precede every other
command in a file, so the header block above is placed immediately after the
single `import Mathlib` line.

Mathematical content.  The Fermat numbers are `F n = 2 ^ (2 ^ n) + 1`.  The
only known Fermat primes are `F 0, …, F 4` (namely `3, 5, 17, 257, 65537`), and
whether any Fermat prime exists beyond `F 4` is an open problem.  We therefore
prove a Lean-checked *conditional reduction*: the existence of a Fermat prime
`F n` with `n > 4` is equivalent to the existence of `n > 4` satisfying Pépin's
residue condition `3 ^ ((F n - 1) / 2) = -1` in `ZMod (F n)`.  Both directions
of Pépin's test are proved: sufficiency via the Lucas primality criterion, and
necessity via quadratic reciprocity.  We also record that `F 5` and `F 6` are
composite, so the search for a Fermat prime beyond four starts at `n = 7`.
-/

namespace Brockian.FermatNumbers

/-- The `n`-th Fermat number `F n = 2 ^ (2 ^ n) + 1`. -/

theorem prime_of_pepinResidue {n : ℕ} (h : PepinResidue n) : Nat.Prime (fermat n) := by
  haveI : Fact (2 < fermat n) := ⟨two_lt_fermat n⟩
  refine lucas_primality (fermat n) 3 ?_ ?_
  · rw [fermat_sub_one, two_pow_split n, mul_comm, pow_mul, h]
    ring
  · intro q hq hdvd
    rw [fermat_sub_one] at hdvd ⊢
    have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd)
    subst hq2
    rw [two_pow_split n, Nat.mul_div_cancel_left _ (by norm_num), h]
    exact ZMod.neg_one_ne_one

/-- Necessity in Pépin's test: a Fermat prime `F n` with `n ≥ 1` satisfies the
residue condition, since `3` is a quadratic non-residue mod `F n`
(`F n ≡ 1 [MOD 4]` and `F n ≡ 2 [MOD 3]`, so quadratic reciprocity gives
`legendreSym (F n) 3 = legendreSym 3 2 = -1`). -/
