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

namespace Brockian

/-- The `K2` Goldbach wheel property at modulus `m`:

every residue class `r` modulo `m` is represented as `p + q` with `p`, `q` prime, where moreover
the two primes may be taken arbitrarily large (larger than any prescribed bound `N`).

This is the "wheel" (residue-class) shadow of the binary Goldbach problem: it says that, modulo
`m`, no congruence obstruction can rule out a representation as a sum of two primes, uniformly in
the size of the primes used. -/

theorem isUnit_zmod_prime_pow_iff {p n : ℕ} (hp : Nat.Prime p) (hn : 0 < n) (x : ZMod (p ^ n)) :
    IsUnit x ↔ (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)) x ≠ 0 := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hx : ((x.val : ℕ) : ZMod (p ^ n)) = x := ZMod.natCast_rightInverse x
  rw [← hx, ZMod.isUnit_iff_coprime, map_natCast, Ne, ZMod.natCast_eq_zero_iff,
    Nat.coprime_pow_right_iff hn, Nat.coprime_comm, hp.coprime_iff_not_dvd]

/-- Odd prime power moduli split every residue into a sum of two units: one of `1 + (r - 1)` and
`2 + (r - 2)` works, since `1` and `2` are distinct nonzero residues modulo an odd prime. -/
