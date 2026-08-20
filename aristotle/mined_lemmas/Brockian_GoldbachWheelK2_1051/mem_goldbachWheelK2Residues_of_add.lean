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

theorem mem_goldbachWheelK2Residues_of_add {m p q : ℕ} (hm : 0 < m)
    (hp : Nat.Coprime p m) (hq : Nat.Coprime q m) :
    p % m ∈ GoldbachWheelK2Residues m (p + q) := by
  have hlt : p % m < m := Nat.mod_lt _ hm
  have hdm : p % m + m * (p / m) = p := Nat.mod_add_div p m
  have heq : p + q + m - p % m = m * (p / m) + q + m := by omega
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, coprime_mod_left hp, ?_⟩
  rw [heq, Nat.add_mod_right, Nat.mul_add_mod]
  exact coprime_mod_left hq

/-- The exact size of the `K2` Goldbach wheel at a prime modulus `m`: the wheel
consists of all residues except `0` and `n % m`. -/
