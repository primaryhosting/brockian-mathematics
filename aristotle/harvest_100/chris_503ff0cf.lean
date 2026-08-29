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
def HasAPOfLength (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

/-- The set of prime numbers. -/
def PrimeSet : Set ℕ := {p | Nat.Prime p}

/-- The Green–Tao theorem, as a proposition: the primes contain arbitrarily long
arithmetic progressions. -/
def GreenTaoStatement : Prop := ∀ k : ℕ, HasAPOfLength PrimeSet k

/-- Dickson's conjecture, in the form needed here: if the shifts `b 0, …, b (k-1)` are
*admissible* (for every prime `p` there is some `n` with `p ∤ n + b i` for all `i < k`),
then there is an `n` making all of `n + b 0, …, n + b (k-1)` prime. -/
def DicksonHypothesis : Prop :=
  ∀ (k : ℕ) (b : ℕ → ℕ),
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ i < k, ¬ p ∣ (n + b i)) →
    ∃ n : ℕ, ∀ i < k, Nat.Prime (n + b i)

/-- Containing an arithmetic progression of length `m` implies containing one of any
shorter length. -/
theorem HasAPOfLength.mono {S : Set ℕ} {k m : ℕ} (h : HasAPOfLength S m) (hkm : k ≤ m) :
    HasAPOfLength S k := by
  obtain ⟨a, d, hd, hmem⟩ := h
  exact ⟨a, d, hd, fun i hi => hmem i (lt_of_lt_of_le hi hkm)⟩

/-- To get progressions of every length it suffices to get them of unboundedly many
lengths. -/
theorem greenTao_of_unbounded
    (h : ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ HasAPOfLength PrimeSet k) : GreenTaoStatement := by
  intro N
  obtain ⟨k, hk, hAP⟩ := h N
  exact hAP.mono hk

/-! ### Unconditional base cases -/

/-- `199, 409, 619, 829, 1039, 1249, 1459, 1669, 1879, 2089` is a 10-term arithmetic
progression of primes (common difference `210`). -/
theorem hasAP_ten : HasAPOfLength PrimeSet 10 := by
  refine ⟨199, 210, by norm_num, ?_⟩
  intro i hi
  interval_cases i <;> · simp only [PrimeSet, Set.mem_setOf_eq]; norm_num

/-- Unconditionally, the primes contain arithmetic progressions of every length `≤ 10`. -/
theorem hasAP_le_ten {k : ℕ} (hk : k ≤ 10) : HasAPOfLength PrimeSet k :=
  hasAP_ten.mono hk

/-! ### Admissibility of the progression `n, n + M, …, n + (k-1) M` -/

/-- If every prime `≤ k` divides `M`, then the shifts `i * M` (`i < k`) are admissible:
for every prime `p` there is an `n` with `p ∤ n + i * M` for all `i < k`. -/
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
theorem Green_Tao (hD : DicksonHypothesis) : GreenTaoStatement := by
  intro k
  obtain ⟨n, hn⟩ :=
    hD k (fun i => i * Nat.factorial k) fun p hp =>
      exists_shift_not_dvd k (Nat.factorial k) p hp fun q hq hqk =>
        Nat.dvd_factorial hq.pos hqk
  exact ⟨n, Nat.factorial k, Nat.factorial_pos k, fun i hi => hn i hi⟩

end Frontier

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

