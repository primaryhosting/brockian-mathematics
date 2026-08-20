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

theorem splitsIntoUnits_mul {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : SplitsIntoUnits a) (hb : SplitsIntoUnits b) : SplitsIntoUnits (a * b) := by
  intro r
  set e := ZMod.chineseRemainder hab with he
  obtain ⟨c1, d1, hc1, hd1, h1⟩ := ha (e r).1
  obtain ⟨c2, d2, hc2, hd2, h2⟩ := hb (e r).2
  refine ⟨e.symm (c1, c2), e.symm (d1, d2), (Prod.isUnit_iff.mpr ⟨hc1, hc2⟩).map e.symm,
    (Prod.isUnit_iff.mpr ⟨hd1, hd2⟩).map e.symm, ?_⟩
  rw [← map_add]
  have hsum : ((c1, c2) + (d1, d2) : ZMod a × ZMod b) = e r := by
    rw [Prod.mk_add_mk, h1, h2]
  rw [hsum, e.symm_apply_apply]

/-- Every odd modulus splits every residue class into a sum of two units. -/
