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

/-- The *Goldbach wheel* of order `2` (`K2`) at modulus `m` for the target `n`:
the set of residues `r < m` such that both `r` and `n - r` (read modulo `m`) are
coprime to `m`.

If `n = p + q` is a Goldbach representation with both summands coprime to `m`,
then `p % m` necessarily lies in this set, so the wheel records exactly the
residue classes that such a representation of `n` is allowed to occupy modulo
`m` (see `Brockian.mem_goldbachWheelK2Residues_of_add`). -/

private theorem coprime_mod_left {a m : ℕ} (h : Nat.Coprime a m) : Nat.Coprime (a % m) m := by
  have h' : Nat.gcd m a = 1 := Nat.coprime_comm.mpr h
  rwa [Nat.gcd_rec] at h'

/-- Any representation `n = p + q` with `p`, `q` coprime to `m` puts `p % m`
on the wheel `GoldbachWheelK2Residues m n`. -/
