import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

open Finset

/-- `HasAPOfLength S k` says that the set `S` contains a `k`-term arithmetic progression
`a, a + d, …, a + (k-1) d` with positive common difference `d`. -/

theorem exists_shift_not_dvd (k M p : ℕ) (hp : p.Prime)
    (hMk : ∀ q : ℕ, q.Prime → q ≤ k → q ∣ M) :
    ∃ n : ℕ, ∀ i < k, ¬ p ∣ (n + i * M) := by
  by_cases hpM : p ∣ M
  · -- every `n + i * M` with `n = 1` is `≡ 1 [MOD p]`
    refine ⟨1, fun i _ h => ?_⟩
    have h1 : p ∣ 1 := by
      have := Nat.dvd_sub h (Dvd.dvd.mul_left hpM i)
      simpa using this
    exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp h1)
  · -- then `p > k`, and the `k` forbidden residues cannot exhaust `ZMod p`
    have hkp : k < p := by
      by_contra hle
      exact hpM (hMk p hp (not_lt.mp hle))
    haveI : Fact p.Prime := ⟨hp⟩
    set T : Finset (ZMod p) :=
      (Finset.range k).image (fun i : ℕ => -((i : ZMod p) * (M : ZMod p))) with hT
    have hcard : T.card < Fintype.card (ZMod p) := by
      have h1 : T.card ≤ k := le_trans (Finset.card_image_le) (by simp)
      have h2 : Fintype.card (ZMod p) = p := ZMod.card p
      omega
    obtain ⟨c, hc⟩ : ∃ c : ZMod p, c ∉ T := by
      by_contra hall
      push_neg at hall
      have : Finset.univ ⊆ T := fun x _ => hall x
      have := Finset.card_le_card this
      simp only [Finset.card_univ] at this
      omega
    refine ⟨c.val, fun i hi hdvd => hc ?_⟩
    have hzero : ((c.val + i * M : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    push_cast at hzero
    rw [ZMod.natCast_val, ZMod.cast_id] at hzero
    have hceq : c = -((i : ZMod p) * (M : ZMod p)) := by linear_combination hzero
    rw [hT, hceq]
    exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩

/-! ### The reduction -/

/-- **Green–Tao, reduced to Dickson's conjecture.**  Assuming Dickson's conjecture for
admissible shifts, the primes contain arbitrarily long arithmetic progressions: for every
`k` there are `a` and `d > 0` with `a + i * d` prime for all `i < k`.

The progression is produced with common difference `d = k !`, which is divisible by every
prime `≤ k`; this makes the shifts `i * k !` admissible (`exists_shift_not_dvd`).

Unconditionally, `Frontier.hasAP_le_ten` gives the base cases `k ≤ 10`. -/
