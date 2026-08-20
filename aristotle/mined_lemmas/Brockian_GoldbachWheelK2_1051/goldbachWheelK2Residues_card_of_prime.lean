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
