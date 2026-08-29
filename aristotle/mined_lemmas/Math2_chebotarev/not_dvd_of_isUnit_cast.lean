/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

/-- Auxiliary step: an automorphism `σ` of a field containing a primitive `n`-th root of unity
`ζ` sends `ζ` to `ζ ^ m` for some `m` that is invertible modulo `n`. -/

theorem not_dvd_of_isUnit_cast {n p : ℕ} (hp : p.Prime) (h : IsUnit ((p : ZMod n))) :
    ¬ p ∣ n := by
  intro hdvd
  have hcop : Nat.Coprime p n := (ZMod.isUnit_iff_coprime p n).mp h
  have : p ∣ 1 := hcop ▸ Nat.dvd_gcd dvd_rfl hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- **Chebotarev density theorem** (qualitative form) for cyclotomic extensions.

Let `K` be a field of characteristic zero containing a primitive `n`-th root of unity `ζ`,
and let `σ` be any element of the Galois group `Gal(K/ℚ)` (whose conjugacy classes are
singletons, since the Galois group of a cyclotomic extension is abelian).

Then there are infinitely many primes `p`, unramified (`p ∤ n`), whose Frobenius element
at `p` — characterized by the congruence `Frob_p (ζ) = ζ ^ p` — is exactly `σ`.

Equivalently: the set of primes whose Frobenius conjugacy class is the class of `σ`
is infinite. The proof reduces the Frobenius condition to a congruence condition
`p ≡ m (mod n)` and then applies Dirichlet's theorem on primes in arithmetic
progressions. -/
