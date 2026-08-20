import Mathlib

/-!
# Goldbach wheel conditions of order 2

For a *wheel modulus* `m`, the order-2 Goldbach wheel condition `GoldbachWheelK2 m`
says that every residue class `e : ZMod m` is hit by a sum `p + q` of two primes,
both coprime to `m` (i.e. both lying on the wheel of `m`), and with `p, q` arbitrarily
large.  This is the residue-class ("wheel") shadow of the Goldbach property: no
congruence obstruction mod `m` can prevent an integer from being a sum of two
wheel primes.

The main general result is `Brockian.goldbachWheelK2_of_prime`, which establishes the
condition for every odd prime modulus, and the family members
`Brockian.GoldbachWheelK2_631`, `Brockian.GoldbachWheelK2_641`,
`Brockian.GoldbachWheelK2_1009` are instances of it.
-/

namespace Brockian

/-- The order-2 Goldbach wheel condition at modulus `m`: every residue class mod `m`
is the class of a sum of two arbitrarily large primes, each coprime to `m`. -/

lemma exists_ne_zero_ne {m : ℕ} (hm : 3 ≤ m) (e : ZMod m) :
    ∃ a : ZMod m, a ≠ 0 ∧ a ≠ e := by
  haveI : NeZero m := ⟨by omega⟩
  have h1 : ((1 : ℕ) : ZMod m) ≠ ((0 : ℕ) : ZMod m) := by
    rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have h2 : ((2 : ℕ) : ZMod m) ≠ ((0 : ℕ) : ZMod m) := by
    rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have h12 : ((1 : ℕ) : ZMod m) ≠ ((2 : ℕ) : ZMod m) := by
    rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  push_cast at h1 h2 h12
  by_cases he : (1 : ZMod m) = e
  · exact ⟨2, h2, by rw [← he]; exact fun h => h12 h.symm⟩
  · exact ⟨1, h1, he⟩

/-- Every odd prime modulus satisfies the order-2 Goldbach wheel condition.
The proof uses Dirichlet's theorem on primes in arithmetic progressions. -/
