import Mathlib

namespace Brockian.ZumkellerNumbers

open Finset


lemma filter_odd_divisors {n k t : ℕ} (hn : n ≠ 0) (hkt : n = 2 ^ k * t) (hto : Odd t) :
    {d ∈ n.divisors | Odd d} = t.divisors := by
  have ht : t ≠ 0 := by
    rintro rfl; simp at hkt; exact hn hkt
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, hodd⟩
    refine ⟨?_, ht⟩
    rw [hkt] at hd
    have hcop : Nat.Coprime d (2 ^ k) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
    exact (Nat.Coprime.dvd_of_dvd_mul_left hcop hd)
  · rintro ⟨hd, -⟩
    refine ⟨⟨hd.trans ⟨2 ^ k, by rw [hkt]; ring⟩, hn⟩, hto.of_dvd_nat hd⟩

