import Mathlib
namespace Brockian.MsThue

/-- Pigeonhole step: there are more than `n` pairs `(i, j)` with `0 ≤ i, j ≤ √n`, so two
    distinct such pairs give the same value of `i - a * j` in `ZMod n`. -/

theorem thue_lemma (n a : ℕ) (hn : 1 < n) :
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ x.natAbs ≤ Nat.sqrt n ∧ y.natAbs ≤ Nat.sqrt n ∧
      (n : ℤ) ∣ (x - a * y) := by
  obtain ⟨p, q, hpq, h⟩ := thue_pigeonhole n a hn
  refine ⟨(p.1 : ℤ) - (q.1 : ℤ), (p.2 : ℤ) - (q.2 : ℤ), ?_, ?_, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    apply hpq
    have e1 : (p.1 : ℕ) = (q.1 : ℕ) := by exact_mod_cast sub_eq_zero.mp h1
    have e2 : (p.2 : ℕ) = (q.2 : ℕ) := by exact_mod_cast sub_eq_zero.mp h2
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  · have h1 : (p.1 : ℕ) ≤ Nat.sqrt n := Nat.lt_succ_iff.mp p.1.isLt
    have h2 : (q.1 : ℕ) ≤ Nat.sqrt n := Nat.lt_succ_iff.mp q.1.isLt
    omega
  · have h1 : (p.2 : ℕ) ≤ Nat.sqrt n := Nat.lt_succ_iff.mp p.2.isLt
    have h2 : (q.2 : ℕ) ≤ Nat.sqrt n := Nat.lt_succ_iff.mp q.2.isLt
    omega
  · have : (((((p.1 : ℤ) - (q.1 : ℤ)) - a * ((p.2 : ℤ) - (q.2 : ℤ))) : ℤ) : ZMod n) = 0 := by
      push_cast
      linear_combination h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp this

end Brockian.MsThue

