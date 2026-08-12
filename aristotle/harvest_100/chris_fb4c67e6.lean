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
def GoldbachWheelK2Residues (m n : ℕ) : Finset ℕ :=
  (Finset.range m).filter fun r => Nat.Coprime r m ∧ Nat.Coprime ((n + m - r) % m) m

private theorem coprime_mod_left {a m : ℕ} (h : Nat.Coprime a m) : Nat.Coprime (a % m) m := by
  have h' : Nat.gcd m a = 1 := Nat.coprime_comm.mpr h
  rwa [Nat.gcd_rec] at h'

/-- Any representation `n = p + q` with `p`, `q` coprime to `m` puts `p % m`
on the wheel `GoldbachWheelK2Residues m n`. -/
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
theorem goldbachWheelK2Residues_card_of_prime {m : ℕ} (hm : Nat.Prime m) (n : ℕ) :
    (GoldbachWheelK2Residues m n).card = if m ∣ n then m - 1 else m - 2 := by
  have hm0 : 0 < m := hm.pos
  have hnm : n % m < m := Nat.mod_lt _ hm0
  have fact1 : ∀ r, r < m → (Nat.Coprime r m ↔ r ≠ 0) := by
    intro r hr
    rw [Nat.coprime_comm, hm.coprime_iff_not_dvd]
    constructor
    · rintro h rfl; exact h (dvd_zero m)
    · intro h hd; exact h (Nat.eq_zero_of_dvd_of_lt hd hr)
  have fact2 : ∀ r, r < m → (Nat.Coprime ((n + m - r) % m) m ↔ r ≠ n % m) := by
    intro r hr
    rw [Nat.coprime_comm, hm.coprime_iff_not_dvd, Nat.dvd_mod_iff dvd_rfl,
      ← Nat.modEq_iff_dvd' (by omega)]
    show ¬ (r % m = (n + m) % m) ↔ _
    rw [Nat.mod_eq_of_lt hr, Nat.add_mod_right]
  have hset : GoldbachWheelK2Residues m n = (Finset.range m) \ {0, n % m} := by
    ext r
    simp only [GoldbachWheelK2Residues, Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨hr, h1, h2⟩
      exact ⟨hr, (fact1 r hr).1 h1, (fact2 r hr).1 h2⟩
    · rintro ⟨hr, h1, h2⟩
      exact ⟨hr, (fact1 r hr).2 h1, (fact2 r hr).2 h2⟩
  have hsub : ({0, n % m} : Finset ℕ) ⊆ Finset.range m := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  rw [hset, Finset.card_sdiff_of_subset hsub, Finset.card_range]
  by_cases h : m ∣ n
  · rw [Nat.dvd_iff_mod_eq_zero.mp h, if_pos h]
    simp
  · have h0 : n % m ≠ 0 := fun hc => h (Nat.dvd_of_mod_eq_zero hc)
    rw [Finset.card_pair (Ne.symm h0), if_neg h]

/-- New wheel modulus for the `GoldbachWheelK2` family: `m = 1051`.
The wheel at modulus `1051` carries `1050` admissible residues when `1051 ∣ n`,
and `1049` admissible residues otherwise. -/
theorem GoldbachWheelK2_1051 (n : ℕ) :
    (GoldbachWheelK2Residues 1051 n).card = if 1051 ∣ n then 1050 else 1049 := by
  have hp : Nat.Prime 1051 := by norm_num
  simpa using goldbachWheelK2Residues_card_of_prime hp n

/-- In particular the wheel at modulus `1051` is never empty: no target `n` is
obstructed modulo `1051`. -/
theorem goldbachWheelK2_1051_nonempty (n : ℕ) :
    (GoldbachWheelK2Residues 1051 n).Nonempty := by
  rw [← Finset.card_pos, GoldbachWheelK2_1051]
  split <;> norm_num

end Brockian

