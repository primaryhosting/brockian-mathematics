/-
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
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
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- A finite set of nonnegative integers is *admissible* (in the Hardy–Littlewood /
Hensley–Richards sense) if for every prime `p` it fails to cover all residue classes
modulo `p`.  Equivalently, the singular series attached to the tuple is nonzero. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- Pigeonhole: a set with fewer than `p` elements cannot occupy every residue class
modulo `p`. -/
theorem exists_uncovered_residue (H : Finset ℕ) (p : ℕ) (hcard : H.card < p) :
    ∃ r < p, ∀ h ∈ H, h % p ≠ r := by
  have hlt : (H.image (fun x => x % p)).card < (Finset.range p).card := by
    calc (H.image (fun x => x % p)).card ≤ H.card := Finset.card_image_le
      _ < p := hcard
      _ = (Finset.range p).card := (Finset.card_range p).symm
  obtain ⟨r, hr, hrnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨r, Finset.mem_range.mp hr, ?_⟩
  intro h hh hcon
  exact hrnot (Finset.mem_image.mpr ⟨h, hh, hcon⟩)

/-- The primes below `141`. -/
def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103, 107, 109, 113, 127, 131, 137, 139]

theorem mem_smallPrimes {p : ℕ} (hp : p.Prime) (hle : p ≤ 140) : p ∈ smallPrimes := by
  revert hp
  revert hle
  revert p
  decide

/-- The admissible tuple obtained by sieving the window `[q0, q0 + d]` by all primes
below `141`, translated back to start at `0`. -/
def sieved (q0 d : ℕ) : Finset ℕ :=
  (Finset.range (d + 1)).filter (fun n => ∀ p ∈ smallPrimes, (q0 + n) % p ≠ 0)

theorem sieved_subset_range {q0 d h : ℕ} (hh : h ∈ sieved q0 d) : h ≤ d := by
  have := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
  omega

/-- Sieving by all primes below `141` produces an admissible set, provided the surviving
set is small enough that larger primes cannot be covered either. -/
theorem sieved_admissible (q0 d : ℕ) (hc : (sieved q0 d).card ≤ 140) :
    Admissible (sieved q0 d) := by
  intro p hp
  by_cases hple : p ≤ 140
  · have hppos : 0 < p := hp.pos
    refine ⟨(p - q0 % p) % p, Nat.mod_lt _ hppos, ?_⟩
    intro h hh hcon
    have hmem : p ∈ smallPrimes := mem_smallPrimes hp hple
    have hne : (q0 + h) % p ≠ 0 := (Finset.mem_filter.mp hh).2 p hmem
    apply hne
    have ha : q0 % p < p := Nat.mod_lt _ hppos
    rcases Nat.eq_zero_or_pos (q0 % p) with h0 | h0
    · have hz : (p - q0 % p) % p = 0 := by rw [h0, Nat.sub_zero, Nat.mod_self]
      rw [Nat.add_mod, h0, hcon, hz]
      simp
    · have hlt : p - q0 % p < p := by omega
      have hz : (p - q0 % p) % p = p - q0 % p := Nat.mod_eq_of_lt hlt
      rw [Nat.add_mod, hcon, hz]
      have hsum : q0 % p + (p - q0 % p) = p := by omega
      rw [hsum, Nat.mod_self]
  · exact exists_uncovered_residue _ _ (by omega)

/-- Packaging: from a computation of the cardinality of a sieved window and the fact
that both endpoints survive the sieve, we get an admissible tuple of diameter exactly
`d` and size at least `100`. -/
theorem sieved_witness (q0 d k : ℕ) (hk1 : 100 ≤ k) (hk2 : k ≤ 140)
    (hcard : (sieved q0 d).card = k)
    (h0 : 0 ∈ sieved q0 d) (hd : d ∈ sieved q0 d) :
    ∃ H : Finset ℕ, Admissible H ∧ 100 ≤ H.card ∧ 0 ∈ H ∧ d ∈ H ∧ ∀ h ∈ H, h ≤ d :=
  ⟨sieved q0 d, sieved_admissible q0 d (by omega), by omega, h0, hd,
    fun _ hh => sieved_subset_range hh⟩

theorem mem_sieved_zero (q0 d : ℕ) (h : ∀ p ∈ smallPrimes, (q0 + 0) % p ≠ 0) :
    0 ∈ sieved q0 d :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩

theorem mem_sieved_top (q0 d : ℕ) (h : ∀ p ∈ smallPrimes, (q0 + d) % p ≠ 0) :
    d ∈ sieved q0 d :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩

/-- **Singular series gaps in the range 1450–1460.**

For a gap `d` with `1450 ≤ d ≤ 1460`, there exists an admissible tuple of at least `100`
elements whose smallest element is `0` and whose largest element is `d` (i.e. an admissible
tuple of diameter exactly `d`) **if and only if** `d` is even.

The forward implication is the parity obstruction modulo `2`; the reverse implication is
witnessed, for each of the six even values, by an explicit sieved window. -/
theorem SingularSeriesGaps14501460 (d : ℕ) (hd1 : 1450 ≤ d) (hd2 : d ≤ 1460) :
    (∃ H : Finset ℕ, Admissible H ∧ 100 ≤ H.card ∧ 0 ∈ H ∧ d ∈ H ∧ ∀ h ∈ H, h ≤ d) ↔
      Even d := by
  constructor
  · rintro ⟨H, hAdm, -, h0, hdH, -⟩
    obtain ⟨r, hr2, hr⟩ := hAdm 2 Nat.prime_two
    interval_cases r
    · exact absurd rfl (hr 0 h0)
    · have := hr d hdH
      exact Nat.even_iff.mpr (by omega)
  · intro hev
    have hev' : d % 2 = 0 := Nat.even_iff.mp hev
    interval_cases d
    · exact sieved_witness 17761 1450 140 (by norm_num) (by norm_num) (by decide)
        (mem_sieved_zero _ _ (by decide)) (mem_sieved_top _ _ (by decide))
    · exact absurd hev' (by decide)
    · exact sieved_witness 17921 1452 139 (by norm_num) (by norm_num) (by decide)
        (mem_sieved_zero _ _ (by decide)) (mem_sieved_top _ _ (by decide))
    · exact absurd hev' (by decide)
    · exact sieved_witness 18233 1454 139 (by norm_num) (by norm_num) (by decide)
        (mem_sieved_zero _ _ (by decide)) (mem_sieved_top _ _ (by decide))
    · exact absurd hev' (by decide)
    · exact sieved_witness 17683 1456 140 (by norm_num) (by norm_num) (by decide)
        (mem_sieved_zero _ _ (by decide)) (mem_sieved_top _ _ (by decide))
    · exact absurd hev' (by decide)
    · exact sieved_witness 17749 1458 140 (by norm_num) (by norm_num) (by decide)
        (mem_sieved_zero _ _ (by decide)) (mem_sieved_top _ _ (by decide))
    · exact absurd hev' (by decide)
    · exact sieved_witness 18257 1460 140 (by norm_num) (by norm_num) (by decide)
        (mem_sieved_zero _ _ (by decide)) (mem_sieved_top _ _ (by decide))

end Brockian

