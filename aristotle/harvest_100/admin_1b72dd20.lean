import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancySpecialCases
import RequestProject.ErdosDiscrepancyMeasure

/-!
# The base case for completely multiplicative sequences

For a completely multiplicative `±1` sequence every homogeneous sum is `f d` times an
ordinary partial sum, so only the sums `S n = f 1 + ⋯ + f n` matter.  Tracking the four
values `f 2, f 3, f 5, f 7` shows that one of `S 4, S 6, S 8, S 10` must exceed `1` in
absolute value: for completely multiplicative sequences the length `10` already forces
discrepancy `2` (as opposed to `12` in general).
-/

namespace Frontier

/-- Unfolding the ordinary partial sums. -/
theorem homogSum_one_succ (f : ℕ → ℤ) (n : ℕ) :
    homogSum f 1 (n + 1) = homogSum f 1 n + f (n + 1) := by
  rw [homogSum_succ, mul_one]

private theorem cm_arith {a b c d : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    (h4 : (1 + a + b + a * a).natAbs ≤ 1)
    (h6 : (1 + a + b + a * a + c + a * b).natAbs ≤ 1)
    (h8 : (1 + a + b + a * a + c + a * b + d + a * (a * a)).natAbs ≤ 1) :
    1 < (1 + a + b + a * a + c + a * b + d + a * (a * a) + b * b + a * c).natAbs := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> norm_num at *

/-- **Base case for completely multiplicative sequences.**  Every completely
multiplicative `±1` sequence has an ordinary partial sum of absolute value at least `2`
among the first ten. -/
theorem completelyMultiplicative_exists_sum_gt_one {f : ℕ → ℤ}
    (hcm : CompletelyMultiplicative f) (hf : IsPMOne f) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 10 ∧ 1 < (homogSum f 1 n).natAbs := by
  -- the values forced by complete multiplicativity
  have e1 : f 1 = 1 := by
    have h11 : f 1 = f 1 * f 1 := by simpa using hcm 1 1 le_rfl le_rfl
    rcases hf 1 le_rfl with h | h
    · exact h
    · rw [h] at h11; norm_num at h11
  have e4 : f 4 = f 2 * f 2 := by simpa using hcm 2 2 (by norm_num) (by norm_num)
  have e6 : f 6 = f 2 * f 3 := by simpa using hcm 2 3 (by norm_num) (by norm_num)
  have e8 : f 8 = f 2 * (f 2 * f 2) := by
    have : f 8 = f 2 * f 4 := by simpa using hcm 2 4 (by norm_num) (by norm_num)
    rw [this, e4]
  have e9 : f 9 = f 3 * f 3 := by simpa using hcm 3 3 (by norm_num) (by norm_num)
  have e10 : f 10 = f 2 * f 5 := by simpa using hcm 2 5 (by norm_num) (by norm_num)
  -- the partial sums in terms of `f 2, f 3, f 5, f 7`
  have s4 : homogSum f 1 4 = 1 + f 2 + f 3 + f 2 * f 2 := by
    show f 1 + f 2 + f 3 + f 4 = _
    rw [e1, e4]
  have s6 : homogSum f 1 6 = 1 + f 2 + f 3 + f 2 * f 2 + f 5 + f 2 * f 3 := by
    show f 1 + f 2 + f 3 + f 4 + f 5 + f 6 = _
    rw [e1, e4, e6]
  have s8 : homogSum f 1 8 =
      1 + f 2 + f 3 + f 2 * f 2 + f 5 + f 2 * f 3 + f 7 + f 2 * (f 2 * f 2) := by
    show f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 = _
    rw [e1, e4, e6, e8]
  have s10 : homogSum f 1 10 =
      1 + f 2 + f 3 + f 2 * f 2 + f 5 + f 2 * f 3 + f 7 + f 2 * (f 2 * f 2)
        + f 3 * f 3 + f 2 * f 5 := by
    show f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 = _
    rw [e1, e4, e6, e8, e9, e10]
  -- one of the four sums must be large
  by_contra hcon
  push_neg at hcon
  have h4 := hcon 4 (by norm_num) (by norm_num)
  have h6 := hcon 6 (by norm_num) (by norm_num)
  have h8 := hcon 8 (by norm_num) (by norm_num)
  have h10 := hcon 10 (by norm_num) (by norm_num)
  rw [s4] at h4
  rw [s6] at h6
  rw [s8] at h8
  rw [s10] at h10
  have := cm_arith (hf 2 (by norm_num)) (hf 3 (by norm_num)) (hf 5 (by norm_num))
    (hf 7 (by norm_num)) h4 h6 h8
  omega

/-- **Every completely multiplicative `±1` sequence has discrepancy at least `2` already
inside `{1, …, 10}`.** -/
theorem two_le_discrepancyUpTo_ten_of_completelyMultiplicative {f : ℕ → ℤ}
    (hcm : CompletelyMultiplicative f) (hf : IsPMOne f) : 2 ≤ discrepancyUpTo f 10 := by
  obtain ⟨n, hn1, hn2, hlt⟩ := completelyMultiplicative_exists_sum_gt_one hcm hf
  exact le_trans hlt (le_discrepancyUpTo le_rfl hn1 (by simpa using hn2))

/-! ### Sharpness: an explicit completely multiplicative example of discrepancy `1`
up to `9` -/

/-- The completely multiplicative `±1` sequence with `f p = -1` for every prime `p ≠ 7`
and `f 7 = 1`. -/
def mulWitness (n : ℕ) : ℤ :=
  (-1) ^ (n.primeFactorsList.length + n.primeFactorsList.count 7)

theorem mulWitness_pm (n : ℕ) : mulWitness n = 1 ∨ mulWitness n = -1 := by
  rcases Nat.even_or_odd (n.primeFactorsList.length + n.primeFactorsList.count 7) with h | h
  · exact Or.inl (h.neg_one_pow)
  · exact Or.inr (h.neg_one_pow)

theorem mulWitness_pm_one : IsPMOne mulWitness := fun n _ => mulWitness_pm n

theorem mulWitness_completelyMultiplicative : CompletelyMultiplicative mulWitness := by
  intro a b ha hb
  have hperm := Nat.perm_primeFactorsList_mul (a := a) (b := b) (by omega) (by omega)
  have hlen : (a * b).primeFactorsList.length =
      a.primeFactorsList.length + b.primeFactorsList.length := by
    rw [hperm.length_eq, List.length_append]
  have hcount : (a * b).primeFactorsList.count 7 =
      a.primeFactorsList.count 7 + b.primeFactorsList.count 7 := by
    rw [hperm.count_eq, List.count_append]
  unfold mulWitness
  rw [hlen, hcount, show a.primeFactorsList.length + b.primeFactorsList.length +
      (a.primeFactorsList.count 7 + b.primeFactorsList.count 7) =
      (a.primeFactorsList.length + a.primeFactorsList.count 7) +
      (b.primeFactorsList.length + b.primeFactorsList.count 7) from by ring, pow_add]

theorem mulWitness_one : mulWitness 1 = 1 := by simp [mulWitness]

theorem mulWitness_prime {p : ℕ} (hp : p.Prime) :
    mulWitness p = if p = 7 then 1 else -1 := by
  unfold mulWitness
  rw [Nat.primeFactorsList_prime hp]
  by_cases h : p = 7 <;> simp [h]

theorem mulWitness_two : mulWitness 2 = -1 := by
  rw [mulWitness_prime (by norm_num)]; norm_num

theorem mulWitness_three : mulWitness 3 = -1 := by
  rw [mulWitness_prime (by norm_num)]; norm_num

theorem mulWitness_five : mulWitness 5 = -1 := by
  rw [mulWitness_prime (by norm_num)]; norm_num

theorem mulWitness_seven : mulWitness 7 = 1 := by
  rw [mulWitness_prime (by norm_num)]; norm_num

/-- The discrepancy of `mulWitness` is at most `1` inside `{1, …, 9}`. -/
theorem mulWitness_sum_le_one {n : ℕ} (hn : 1 ≤ n) (h9 : n ≤ 9) :
    (homogSum mulWitness 1 n).natAbs ≤ 1 := by
  have v1 : mulWitness 1 = 1 := mulWitness_one
  have v2 : mulWitness 2 = -1 := mulWitness_two
  have v3 : mulWitness 3 = -1 := mulWitness_three
  have v5 : mulWitness 5 = -1 := mulWitness_five
  have v7 : mulWitness 7 = 1 := mulWitness_seven
  have v4 : mulWitness 4 = 1 := by
    have := mulWitness_completelyMultiplicative 2 2 (by norm_num) (by norm_num)
    rw [v2] at this; simpa using this
  have v6 : mulWitness 6 = 1 := by
    have := mulWitness_completelyMultiplicative 2 3 (by norm_num) (by norm_num)
    rw [v2, v3] at this; simpa using this
  have v8 : mulWitness 8 = -1 := by
    have := mulWitness_completelyMultiplicative 2 4 (by norm_num) (by norm_num)
    rw [v2, v4] at this; simpa using this
  have v9 : mulWitness 9 = 1 := by
    have := mulWitness_completelyMultiplicative 3 3 (by norm_num) (by norm_num)
    rw [v3] at this; simpa using this
  have s1 : (homogSum mulWitness 1 1).natAbs ≤ 1 := by
    show (mulWitness 1).natAbs ≤ 1
    rw [v1]; decide
  have s2 : (homogSum mulWitness 1 2).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2).natAbs ≤ 1
    rw [v1, v2]; decide
  have s3 : (homogSum mulWitness 1 3).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3).natAbs ≤ 1
    rw [v1, v2, v3]; decide
  have s4 : (homogSum mulWitness 1 4).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3 + mulWitness 4).natAbs ≤ 1
    rw [v1, v2, v3, v4]; decide
  have s5 : (homogSum mulWitness 1 5).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3 + mulWitness 4 + mulWitness 5).natAbs ≤ 1
    rw [v1, v2, v3, v4, v5]; decide
  have s6 : (homogSum mulWitness 1 6).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3 + mulWitness 4 + mulWitness 5
      + mulWitness 6).natAbs ≤ 1
    rw [v1, v2, v3, v4, v5, v6]; decide
  have s7 : (homogSum mulWitness 1 7).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3 + mulWitness 4 + mulWitness 5
      + mulWitness 6 + mulWitness 7).natAbs ≤ 1
    rw [v1, v2, v3, v4, v5, v6, v7]; decide
  have s8 : (homogSum mulWitness 1 8).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3 + mulWitness 4 + mulWitness 5
      + mulWitness 6 + mulWitness 7 + mulWitness 8).natAbs ≤ 1
    rw [v1, v2, v3, v4, v5, v6, v7, v8]; decide
  have s9 : (homogSum mulWitness 1 9).natAbs ≤ 1 := by
    show (mulWitness 1 + mulWitness 2 + mulWitness 3 + mulWitness 4 + mulWitness 5
      + mulWitness 6 + mulWitness 7 + mulWitness 8 + mulWitness 9).natAbs ≤ 1
    rw [v1, v2, v3, v4, v5, v6, v7, v8, v9]; decide
  interval_cases n <;> assumption

/-- `mulWitness` has discrepancy `1` inside `{1, …, 9}`. -/
theorem discrepancyUpTo_mulWitness_nine : discrepancyUpTo mulWitness 9 ≤ 1 := by
  refine Finset.sup_le ?_
  rintro ⟨n, d⟩ hp
  simp only [Finset.mem_product, Finset.mem_Icc] at hp
  by_cases hle : n * d ≤ 9
  · rw [if_pos hle]
    have hnd : n ≤ 9 := le_trans (Nat.le_mul_of_pos_right n hp.2.1) hle
    rw [homogSum_completelyMultiplicative mulWitness_completelyMultiplicative hp.2.1 n,
      Int.natAbs_mul]
    have hsum := mulWitness_sum_le_one hp.1.1 hnd
    rcases mulWitness_pm d with h | h <;> rw [h] <;> simpa using hsum
  · rw [if_neg hle]
    exact Nat.zero_le _

/-- **The exact threshold for completely multiplicative sequences.**  `10` is the least `N`
such that every completely multiplicative `±1` sequence has discrepancy at least `2`
inside `{1, …, N}`. -/
theorem isLeast_completelyMultiplicative_threshold :
    IsLeast {N : ℕ | ∀ f : ℕ → ℤ, CompletelyMultiplicative f → IsPMOne f →
      2 ≤ discrepancyUpTo f N} 10 := by
  constructor
  · intro f hcm hf
    exact two_le_discrepancyUpTo_ten_of_completelyMultiplicative hcm hf
  · intro N hN
    by_contra hlt
    have h9 : N ≤ 9 := by omega
    have h1 : 2 ≤ discrepancyUpTo mulWitness N :=
      hN mulWitness mulWitness_completelyMultiplicative mulWitness_pm_one
    have h2 : discrepancyUpTo mulWitness N ≤ 1 :=
      le_trans (discrepancyUpTo_mono h9) discrepancyUpTo_mulWitness_nine
    omega

end Frontier

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `homogSum f d n = f d + f (2 * d) + ⋯ + f (n * d)`, the sum of `f` along the
initial segment of length `n` of the homogeneous arithmetic progression with
common difference `d`. -/
def homogSum (f : Nat → Int) (d : Nat) : Nat → Int
  | 0 => 0
  | 1 => f d
  | n + 2 => homogSum f d (n + 1) + f ((n + 2) * d)

/-- `f` is a `±1`-valued sequence (on the positive integers). -/
def IsPMOne (f : Nat → Int) : Prop := ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1

/-- **The Erdős discrepancy problem** (theorem of Tao): every `±1` sequence has
unbounded discrepancy along homogeneous arithmetic progressions, i.e. for every
bound `C` there are `d, n ≥ 1` with `|f d + f (2d) + ⋯ + f (nd)| > C`. -/
def ErdosDiscrepancyStatement : Prop :=
  ∀ f : Nat → Int, IsPMOne f → ∀ C : Nat,
    ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ C < (homogSum f d n).natAbs

/-! ### Auxiliary cancellation lemmas

If a partial sum of `±1`'s of even length is bounded by `1` in absolute value and all
earlier consecutive pairs already cancel, then the final pair cancels as well. -/

private theorem cancel2 {a b : Int} (hs : (a + b).natAbs ≤ 1)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) : b = -a := by omega

private theorem cancel4 {a b c d : Int} (hab : b = -a) (hs : (a + b + c + d).natAbs ≤ 1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1) : d = -c := by omega

private theorem cancel6 {a b c d e g : Int} (hab : b = -a) (hcd : d = -c)
    (hs : (a + b + c + d + e + g).natAbs ≤ 1)
    (he : e = 1 ∨ e = -1) (hg : g = 1 ∨ g = -1) : g = -e := by omega

private theorem cancel8 {a b c d e g h i : Int} (hab : b = -a) (hcd : d = -c) (heg : g = -e)
    (hs : (a + b + c + d + e + g + h + i).natAbs ≤ 1)
    (hh : h = 1 ∨ h = -1) (hi : i = 1 ∨ i = -1) : i = -h := by omega

private theorem cancel10 {a b c d e g h i j k : Int} (hab : b = -a) (hcd : d = -c) (heg : g = -e)
    (hhi : i = -h) (hs : (a + b + c + d + e + g + h + i + j + k).natAbs ≤ 1)
    (hj : j = 1 ∨ j = -1) (hk : k = 1 ∨ k = -1) : k = -j := by omega

/-- The eleven cancellation relations forced by a discrepancy-`1` sequence are
contradictory. -/
private theorem no_discrepancy_one {a1 a2 a3 a4 a6 a9 a10 a12 : Int}
    (v1 : a1 = 1 ∨ a1 = -1) (p12 : a2 = -a1) (p34 : a4 = -a3) (q24 : a4 = -a2)
    (r36 : a6 = -a3) (s612 : a12 = -a6) (r912 : a12 = -a9)
    (p910 : a10 = -a9) (q1012 : a12 = -a10) : False := by omega

/-- **Erdős discrepancy, the base case `C = 1`, in finitary form.**
For every `±1` sequence there are `d, n ≥ 1` with `n * d ≤ 12` and
`|f d + f (2d) + ⋯ + f (nd)| > 1`; that is, discrepancy at least `2` is already
forced by the twelve values `f 1, …, f 12`. -/
theorem erdos_discrepancy_le_twelve (f : Nat → Int) (hf : IsPMOne f) :
    ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ 12 ∧ 1 < (homogSum f d n).natAbs := by
  refine Classical.byContradiction fun hne => ?_
  have hcon : ∀ d n : Nat, 1 ≤ d → 1 ≤ n → n * d ≤ 12 → (homogSum f d n).natAbs ≤ 1 :=
    fun d n hd hn hnd => Nat.not_lt.mp fun hlt => hne ⟨d, n, hd, hn, hnd, hlt⟩
  -- the discrepancy bounds we use, with the sums expanded
  have b12 : (f 1 + f 2).natAbs ≤ 1 := hcon 1 2 (by decide) (by decide) (by decide)
  have b14 : (f 1 + f 2 + f 3 + f 4).natAbs ≤ 1 := hcon 1 4 (by decide) (by decide) (by decide)
  have b16 : (f 1 + f 2 + f 3 + f 4 + f 5 + f 6).natAbs ≤ 1 :=
    hcon 1 6 (by decide) (by decide) (by decide)
  have b18 : (f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8).natAbs ≤ 1 :=
    hcon 1 8 (by decide) (by decide) (by decide)
  have b110 : (f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10).natAbs ≤ 1 :=
    hcon 1 10 (by decide) (by decide) (by decide)
  have b22 : (f 2 + f 4).natAbs ≤ 1 := hcon 2 2 (by decide) (by decide) (by decide)
  have b24 : (f 2 + f 4 + f 6 + f 8).natAbs ≤ 1 := hcon 2 4 (by decide) (by decide) (by decide)
  have b26 : (f 2 + f 4 + f 6 + f 8 + f 10 + f 12).natAbs ≤ 1 :=
    hcon 2 6 (by decide) (by decide) (by decide)
  have b32 : (f 3 + f 6).natAbs ≤ 1 := hcon 3 2 (by decide) (by decide) (by decide)
  have b34 : (f 3 + f 6 + f 9 + f 12).natAbs ≤ 1 := hcon 3 4 (by decide) (by decide) (by decide)
  have b62 : (f 6 + f 12).natAbs ≤ 1 := hcon 6 2 (by decide) (by decide) (by decide)
  -- the values are `±1`
  have v1 := hf 1 (by decide)
  have v2 := hf 2 (by decide)
  have v3 := hf 3 (by decide)
  have v4 := hf 4 (by decide)
  have v5 := hf 5 (by decide)
  have v6 := hf 6 (by decide)
  have v7 := hf 7 (by decide)
  have v8 := hf 8 (by decide)
  have v9 := hf 9 (by decide)
  have v10 := hf 10 (by decide)
  have v12 := hf 12 (by decide)
  -- consecutive pairs cancel along the progression of difference `1`
  have p12 : f 2 = -f 1 := cancel2 b12 v1 v2
  have p34 : f 4 = -f 3 := cancel4 p12 b14 v3 v4
  have p56 : f 6 = -f 5 := cancel6 p12 p34 b16 v5 v6
  have p78 : f 8 = -f 7 := cancel8 p12 p34 p56 b18 v7 v8
  have p910 : f 10 = -f 9 := cancel10 p12 p34 p56 p78 b110 v9 v10
  -- pairs along the progression of difference `2`
  have q24 : f 4 = -f 2 := cancel2 b22 v2 v4
  have q68 : f 8 = -f 6 := cancel4 q24 b24 v6 v8
  have q1012 : f 12 = -f 10 := cancel6 q24 q68 b26 v10 v12
  -- pairs along the progressions of differences `3` and `6`
  have r36 : f 6 = -f 3 := cancel2 b32 v3 v6
  have r912 : f 12 = -f 9 := cancel4 r36 b34 v9 v12
  have s612 : f 12 = -f 6 := cancel2 b62 v6 v12
  -- writing `a = f 1`, these force both `f 12 = a` and `f 12 = -a`
  exact no_discrepancy_one v1 p12 p34 q24 r36 s612 r912 p910 q1012

/-- **Erdős discrepancy, the base case `C = 1`.**
Every `±1` sequence has discrepancy at least `2` along homogeneous arithmetic
progressions: there are `d, n ≥ 1` with `|f d + f (2d) + ⋯ + f (nd)| > 1`. -/
theorem erdos_discrepancy (f : Nat → Int) (hf : IsPMOne f) :
    ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ 1 < (homogSum f d n).natAbs :=
  match erdos_discrepancy_le_twelve f hf with
  | ⟨d, n, hd, hn, _, hlt⟩ => ⟨d, n, hd, hn, hlt⟩

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancyCompactness
import RequestProject.ErdosDiscrepancySharp
import RequestProject.ErdosDiscrepancySpecialCases
import RequestProject.ErdosDiscrepancyLogExample

/-!
# The discrepancy function

We package the results proved elsewhere in this project in terms of an explicit
discrepancy function

`discrepancyUpTo f N = max { |f d + f (2d) + ⋯ + f (nd)| : 1 ≤ d, 1 ≤ n, n * d ≤ N }`,

and restate:

* the Erdős discrepancy statement as "`discrepancyUpTo f` is unbounded for every `±1`
  sequence `f`";
* the proved base case: `2 ≤ discrepancyUpTo f 12` for every `±1` sequence;
* its sharpness: `discrepancyUpTo goodSeq 11 ≤ 1`;
* the logarithmic example: `discrepancyUpTo triSeq N ≤ log₃ N + 1`, while
  `discrepancyUpTo triSeq` is unbounded.
-/

namespace Frontier

open Finset

/-- The largest absolute value of a homogeneous partial sum of `f` inside `{1, …, N}`. -/
def discrepancyUpTo (f : ℕ → ℤ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).sup
    fun p => if p.1 * p.2 ≤ N then (homogSum f p.2 p.1).natAbs else 0

/-- Every homogeneous sum inside `{1, …, N}` is bounded by the discrepancy. -/
theorem le_discrepancyUpTo {f : ℕ → ℤ} {d n N : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (h : n * d ≤ N) : (homogSum f d n).natAbs ≤ discrepancyUpTo f N := by
  have hdN : d ≤ N := le_trans (Nat.le_mul_of_pos_left d hn) h
  have hnN : n ≤ N := le_trans (Nat.le_mul_of_pos_right n hd) h
  have hmem : (n, d) ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) := by
    simp [Finset.mem_product, hd, hn, hdN, hnN]
  have := Finset.le_sup (f := fun p : ℕ × ℕ =>
    if p.1 * p.2 ≤ N then (homogSum f p.2 p.1).natAbs else 0) hmem
  simpa [h] using this

/-- Conversely, a large discrepancy is witnessed by an actual homogeneous progression. -/
theorem exists_of_lt_discrepancyUpTo {f : ℕ → ℤ} {C N : ℕ} (h : C < discrepancyUpTo f N) :
    ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ N ∧ C < (homogSum f d n).natAbs := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [discrepancyUpTo] at h
  have hne : ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).Nonempty :=
    ⟨(1, 1), by simp [Finset.mem_product]; omega⟩
  obtain ⟨p, hp, hval⟩ := Finset.exists_mem_eq_sup _ hne
    (fun p : ℕ × ℕ => if p.1 * p.2 ≤ N then (homogSum f p.2 p.1).natAbs else 0)
  rw [discrepancyUpTo, hval] at h
  by_cases hle : p.1 * p.2 ≤ N
  · rw [if_pos hle] at h
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    exact ⟨p.2, p.1, hp.2.1, hp.1.1, hle, h⟩
  · rw [if_neg hle] at h
    omega

/-- The Erdős discrepancy statement, in terms of the discrepancy function. -/
theorem erdosDiscrepancyStatement_iff_discrepancyUpTo :
    ErdosDiscrepancyStatement ↔
      ∀ f : ℕ → ℤ, IsPMOne f → ∀ C : ℕ, ∃ N : ℕ, C < discrepancyUpTo f N := by
  constructor
  · intro h f hf C
    obtain ⟨d, n, hd, hn, hlt⟩ := h f hf C
    exact ⟨n * d, lt_of_lt_of_le hlt (le_discrepancyUpTo hd hn le_rfl)⟩
  · intro h f hf C
    obtain ⟨N, hN⟩ := h f hf C
    obtain ⟨d, n, hd, hn, _, hlt⟩ := exists_of_lt_discrepancyUpTo hN
    exact ⟨d, n, hd, hn, hlt⟩

/-- **Base case, in terms of the discrepancy function**: every `±1` sequence has
discrepancy at least `2` already within `{1, …, 12}`. -/
theorem two_le_discrepancyUpTo_twelve (f : ℕ → ℤ) (hf : IsPMOne f) :
    2 ≤ discrepancyUpTo f 12 := by
  obtain ⟨d, n, hd, hn, hnd, hlt⟩ := erdos_discrepancy_le_twelve f hf
  exact le_trans hlt (le_discrepancyUpTo hd hn hnd)

/-- **Sharpness**: the explicit sequence has discrepancy `1` within `{1, …, 11}`. -/
theorem discrepancyUpTo_goodSeq_eleven : discrepancyUpTo goodSeq 11 = 1 := by
  refine le_antisymm (Finset.sup_le ?_) ?_
  · rintro ⟨n, d⟩ hp
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    by_cases hle : n * d ≤ 11
    · rw [if_pos hle]
      exact goodSeq_discrepancy_le_one d n hp.2.1 hp.1.1 hle
    · rw [if_neg hle]
      exact Nat.zero_le 1
  · have : (homogSum goodSeq 1 1).natAbs ≤ discrepancyUpTo goodSeq 11 :=
      le_discrepancyUpTo le_rfl le_rfl (by norm_num)
    simpa [homogSum, goodSeq, goodPattern] using this

/-- **The logarithmic example**: the base-`3` sequence has discrepancy at most
`log₃ N + 1` within `{1, …, N}`. -/
theorem discrepancyUpTo_triSeq_le_log (N : ℕ) :
    discrepancyUpTo triSeq N ≤ Nat.log 3 N + 1 := by
  refine Finset.sup_le ?_
  rintro ⟨n, d⟩ hp
  simp only [Finset.mem_product, Finset.mem_Icc] at hp
  by_cases hle : n * d ≤ N
  · rw [if_pos hle]
    have hnN : n ≤ N := le_trans (Nat.le_mul_of_pos_right n hp.2.1) hle
    exact le_trans (triSeq_discrepancy_le_log hp.2.1 n)
      (by simpa using Nat.log_mono_right hnN)
  · rw [if_neg hle]
    exact Nat.zero_le _

/-- ... yet its discrepancy is unbounded. -/
theorem discrepancyUpTo_triSeq_unbounded (C : ℕ) : ∃ N : ℕ, C < discrepancyUpTo triSeq N := by
  obtain ⟨d, n, hd, hn, hlt⟩ := triSeq_unboundedDiscrepancy C
  exact ⟨n * d, lt_of_lt_of_le hlt (le_discrepancyUpTo hd hn le_rfl)⟩

/-- The discrepancy function is monotone in the length bound. -/
theorem discrepancyUpTo_mono {f : ℕ → ℤ} {M N : ℕ} (h : M ≤ N) :
    discrepancyUpTo f M ≤ discrepancyUpTo f N := by
  refine Finset.sup_le ?_
  rintro ⟨n, d⟩ hp
  simp only [Finset.mem_product, Finset.mem_Icc] at hp
  by_cases hle : n * d ≤ M
  · rw [if_pos hle]
    exact le_discrepancyUpTo hp.2.1 hp.1.1 (le_trans hle h)
  · rw [if_neg hle]
    exact Nat.zero_le _

/-- Every `±1` sequence has discrepancy at least `2` within `{1, …, N}` once `N ≥ 12`. -/
theorem two_le_discrepancyUpTo {f : ℕ → ℤ} (hf : IsPMOne f) {N : ℕ} (h : 12 ≤ N) :
    2 ≤ discrepancyUpTo f N :=
  le_trans (two_le_discrepancyUpTo_twelve f hf) (discrepancyUpTo_mono h)

/-- **The exact threshold for the base case.**  `12` is the least `N` such that *every*
`±1` sequence has discrepancy at least `2` inside `{1, …, N}`: it works, and it fails for
every smaller `N` because of the explicit sequence `goodSeq`. -/
theorem isLeast_discrepancy_two_bound :
    IsLeast {N : ℕ | ∀ f : ℕ → ℤ, IsPMOne f → 2 ≤ discrepancyUpTo f N} 12 := by
  constructor
  · intro f hf
    exact two_le_discrepancyUpTo_twelve f hf
  · intro N hN
    by_contra hlt
    have h11 : N ≤ 11 := by omega
    have h1 : 2 ≤ discrepancyUpTo goodSeq N := hN goodSeq goodSeq_pm_one
    have h2 : discrepancyUpTo goodSeq N ≤ 1 := by
      rw [← discrepancyUpTo_goodSeq_eleven]
      exact discrepancyUpTo_mono h11
    omega

/-- The finitary statement, in terms of the discrepancy function: for every bound `C`
there is a length `N` beyond which *every* `±1` sequence exceeds `C`. -/
theorem finiteErdosStatement_iff_discrepancyUpTo :
    FiniteErdosStatement ↔
      ∀ C : ℕ, ∃ N : ℕ, ∀ f : ℕ → ℤ, IsPMOne f → C < discrepancyUpTo f N := by
  constructor
  · intro h C
    obtain ⟨N, hN⟩ := h C
    refine ⟨N, fun f hf => ?_⟩
    obtain ⟨d, n, hd, hn, hnd, hlt⟩ := hN f hf
    exact lt_of_lt_of_le hlt (le_discrepancyUpTo hd hn hnd)
  · intro h C
    obtain ⟨N, hN⟩ := h C
    exact ⟨N, fun f hf => exists_of_lt_discrepancyUpTo (hN f hf)⟩

/-- **The Erdős discrepancy statement is equivalent to a uniform, finitary growth
statement for the discrepancy function.**  (The nontrivial implication is the compactness
argument of `Frontier.erdos_iff_finite`.) -/
theorem erdosDiscrepancyStatement_iff_uniform :
    ErdosDiscrepancyStatement ↔
      ∀ C : ℕ, ∃ N : ℕ, ∀ f : ℕ → ℤ, IsPMOne f → C < discrepancyUpTo f N :=
  erdos_iff_finite.trans finiteErdosStatement_iff_discrepancyUpTo

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancySpecialCases
import RequestProject.ErdosDiscrepancyMeasure

/-!
# Two remarks on the shape of the statement

* **A single progression is not enough.**  The alternating sequence has all its ordinary
  partial sums in `{0, 1}`, so the discrepancy along the progression of difference `1`
  stays bounded forever; the Erdős discrepancy statement really uses all differences `d`
  at once.  (Consistently with this, the alternating sequence is periodic, hence has
  unbounded discrepancy overall by `Frontier.unboundedDiscrepancy_of_periodic`: the
  progression of difference `2` is constant.)

* **Dilation.**  Replacing `f` by `n ↦ f (k * n)` turns the progression of difference `d`
  into the progression of difference `k * d`, so a dilation cannot have larger discrepancy
  than the original sequence (up to rescaling the length bound).
-/

namespace Frontier

/-! ### The alternating sequence -/

/-- The alternating `±1` sequence `1, -1, 1, -1, …`. -/
def altSeq (n : ℕ) : ℤ := if n % 2 = 1 then 1 else -1

theorem altSeq_pm_one : IsPMOne altSeq := by
  intro n _
  unfold altSeq
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The ordinary partial sums of the alternating sequence are `1, 0, 1, 0, …`. -/
theorem homogSum_altSeq_one (n : ℕ) :
    homogSum altSeq 1 n = if n % 2 = 1 then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [homogSum_succ, mul_one, ih]
      by_cases h : m % 2 = 1
      · have h' : (m + 1) % 2 = 0 := by omega
        simp [h, h', altSeq]
      · have h' : (m + 1) % 2 = 1 := by omega
        simp [h, h', altSeq]

/-- Along the progression of difference `1` the alternating sequence has discrepancy `1`
for every length: unboundedness in the Erdős discrepancy problem genuinely requires
varying the common difference. -/
theorem altSeq_sum_le_one (n : ℕ) : (homogSum altSeq 1 n).natAbs ≤ 1 := by
  rw [homogSum_altSeq_one]
  split <;> decide

/-- Nevertheless the alternating sequence has unbounded discrepancy: it is periodic, and
the progression of difference `2` is constant. -/
theorem altSeq_unboundedDiscrepancy : UnboundedDiscrepancy altSeq := by
  refine unboundedDiscrepancy_of_periodic (p := 2) (by norm_num) (fun n => ?_) altSeq_pm_one
  have h : (n + 2) % 2 = n % 2 := by omega
  simp [altSeq, h]

/-! ### Dilations -/

/-- Dilating a sequence by `k` turns the difference `d` into the difference `k * d`. -/
theorem homogSum_dilate (f : ℕ → ℤ) (k d n : ℕ) :
    homogSum (fun m => f (k * m)) d n = homogSum f (k * d) n := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [homogSum_succ, homogSum_succ, ih]
      congr 2
      ring

/-- A dilation has no larger discrepancy than the original sequence (after rescaling the
length bound). -/
theorem discrepancyUpTo_dilate_le (f : ℕ → ℤ) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    discrepancyUpTo (fun m => f (k * m)) N ≤ discrepancyUpTo f (k * N) := by
  refine Finset.sup_le ?_
  rintro ⟨n, d⟩ hp
  simp only [Finset.mem_product, Finset.mem_Icc] at hp
  by_cases hle : n * d ≤ N
  · rw [if_pos hle, homogSum_dilate]
    refine le_discrepancyUpTo (Nat.mul_pos hk hp.2.1) hp.1.1 ?_
    calc n * (k * d) = k * (n * d) := by ring
      _ ≤ k * N := Nat.mul_le_mul_left k hle
  · rw [if_neg hle]
    exact Nat.zero_le _

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib

/-!
# A Lean-checked reduction: the infinite and finite forms are equivalent

The Erdős discrepancy statement quantifies over infinite `±1` sequences.  Here we prove,
by a compactness (ultrafilter) argument, that it is equivalent to its finitary form:
for every bound `C` there is a *uniform* `N` such that every `±1` sequence already exceeds
the bound `C` on a homogeneous arithmetic progression contained in `{1, …, N}`.

This is the reduction that makes the problem amenable to finite search; the base case
`C = 1` proved in `Frontier.erdos_discrepancy_le_twelve` has `N = 12`.
-/

namespace Frontier

/-- The finitary form of the Erdős discrepancy statement. -/
def FiniteErdosStatement : Prop :=
  ∀ C : ℕ, ∃ N : ℕ, ∀ f : ℕ → ℤ, IsPMOne f →
    ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ N ∧ C < (homogSum f d n).natAbs

/-- A homogeneous partial sum only depends on the values of the sequence on `{1, …, n * d}`. -/
theorem homogSum_congr {f g : ℕ → ℤ} {d : ℕ} (hd : 1 ≤ d) :
    ∀ {n : ℕ}, (∀ k, 1 ≤ k → k ≤ n * d → f k = g k) → homogSum f d n = homogSum g d n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ m ih =>
      intro h
      have hpos : 1 ≤ (m + 1) * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
      rw [homogSum_succ, homogSum_succ, ih ?_, h ((m + 1) * d) hpos le_rfl]
      intro k hk1 hk2
      exact h k hk1 (hk2.trans (Nat.mul_le_mul_right d (Nat.le_succ m)))

/-- Easy direction: the finitary statement implies the infinite one. -/
theorem erdos_of_finite (h : FiniteErdosStatement) : ErdosDiscrepancyStatement := by
  intro f hf C
  obtain ⟨N, hN⟩ := h C
  obtain ⟨d, n, hd, hn, _, hlt⟩ := hN f hf
  exact ⟨d, n, hd, hn, hlt⟩

/-- Compactness direction: the infinite statement implies its finitary form.
The witness sequence is the ultrafilter limit, along a non-principal ultrafilter, of
sequences of low discrepancy on longer and longer initial segments. -/
theorem finite_of_erdos (h : ErdosDiscrepancyStatement) : FiniteErdosStatement := by
  classical
  intro C
  by_contra hcon
  push_neg at hcon
  -- for each `N`, a `±1` sequence with discrepancy `≤ C` inside `{1, …, N}`
  choose g hg1 hg2 using hcon
  let u : Ultrafilter ℕ := Filter.hyperfilter ℕ
  -- the ultrafilter limit of the sequences `g N`
  let f : ℕ → ℤ := fun k => if {N | g N k = 1} ∈ u then 1 else -1
  have hfval : ∀ k, f k = if {N | g N k = 1} ∈ u then 1 else -1 := fun _ => rfl
  have hf : IsPMOne f := by
    intro k _
    rw [hfval]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- each coordinate of `f` is the value of `g N` for `u`-most `N`
  have hA : ∀ k, 1 ≤ k → {N | g N k = f k} ∈ (u : Filter ℕ) := by
    intro k hk
    by_cases hmem : {N | g N k = 1} ∈ u
    · have hfk : f k = 1 := by rw [hfval]; exact if_pos hmem
      filter_upwards [Ultrafilter.mem_coe.mpr hmem] with N hN
      show g N k = f k
      rw [hfk]; exact hN
    · have hfk : f k = -1 := by rw [hfval]; exact if_neg hmem
      have hc : {N | g N k = 1}ᶜ ∈ (u : Filter ℕ) :=
        Ultrafilter.mem_coe.mpr (Ultrafilter.compl_mem_iff_notMem.mpr hmem)
      filter_upwards [hc] with N hN
      show g N k = f k
      rcases hg1 N k hk with hv | hv
      · exact absurd hv hN
      · rw [hfk]; exact hv
  -- hence for `u`-most `N` the sequence `g N` agrees with `f` on all of `{1, …, M}`
  have agree : ∀ M : ℕ, {N | ∀ k, 1 ≤ k → k ≤ M → g N k = f k} ∈ (u : Filter ℕ) := by
    intro M
    induction M with
    | zero =>
        filter_upwards with N k hk1 hk2
        exact absurd (hk1.trans hk2) (by decide)
    | succ m ih =>
        filter_upwards [ih, hA (m + 1) (Nat.le_add_left 1 m)] with N h1 h2 k hk1 hk2
        rcases Nat.lt_or_ge k (m + 1) with hlt | hge
        · exact h1 k hk1 (Nat.lt_succ_iff.mp hlt)
        · have : k = m + 1 := le_antisymm hk2 hge
          subst this; exact h2
  -- apply the infinite statement to the limit sequence `f`
  obtain ⟨d, n, hd, hn, hlt⟩ := h f hf C
  have hbig : {N : ℕ | n * d ≤ N} ∈ (u : Filter ℕ) := by
    refine Filter.hyperfilter_le_cofinite ?_
    rw [Filter.mem_cofinite]
    exact Set.Finite.subset (Set.finite_Iio (n * d)) fun x hx => by simpa using hx
  obtain ⟨N, hN1, hN2⟩ := Filter.nonempty_of_mem (Filter.inter_mem (agree (n * d)) hbig)
  have hsum : homogSum f d n = homogSum (g N) d n :=
    homogSum_congr hd fun k hk1 hk2 => (hN1 k hk1 hk2).symm
  have hle : (homogSum (g N) d n).natAbs ≤ C := hg2 N d n hd hn hN2
  omega

/-- **Lean-checked reduction.** The Erdős discrepancy statement is equivalent to its
finitary form. -/
theorem erdos_iff_finite : ErdosDiscrepancyStatement ↔ FiniteErdosStatement :=
  ⟨finite_of_erdos, erdos_of_finite⟩

/-- The finitary form of the base case: the uniform bound `N = 12` works for `C = 1`. -/
theorem finite_erdos_base_case :
    ∃ N : ℕ, ∀ f : ℕ → ℤ, IsPMOne f →
      ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ N ∧ 1 < (homogSum f d n).natAbs :=
  ⟨12, erdos_discrepancy_le_twelve⟩

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancyCompactness

/-!
# Classification of the discrepancy-one sequences of length eleven

`Frontier.erdos_discrepancy_le_twelve` shows that no `±1` sequence has discrepancy `1`
on all homogeneous progressions inside `{1, …, 12}`, and `Frontier.goodSeq` shows that
this fails for `11`.  Here we classify *all* the exceptional patterns: there are exactly
four `±1` patterns of length `11` with discrepancy `1`, namely two patterns and their
negatives; they agree on `{1, …, 10}` up to sign and are free at `11`.

The enumeration is a finite kernel computation over the `2 ^ 11` patterns.
-/

namespace Frontier

/-- All `±1` patterns of a given length. -/
def pmLists : ℕ → List (List ℤ)
  | 0 => [[]]
  | n + 1 => (pmLists n).flatMap fun l => [(1 : ℤ) :: l, (-1 : ℤ) :: l]

theorem mem_pmLists : ∀ L : List ℤ, (∀ x ∈ L, x = 1 ∨ x = -1) → L ∈ pmLists L.length := by
  intro L
  induction L with
  | nil => intro _; simp [pmLists]
  | cons x t ih =>
      intro h
      have ht : t ∈ pmLists t.length := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
      have hx : x = 1 ∨ x = -1 := h x (List.mem_cons_self ..)
      simp only [List.length_cons, pmLists, List.mem_flatMap]
      exact ⟨t, ht, by rcases hx with rfl | rfl <;> simp⟩

/-- The `±1` sequence read off from a pattern (index `k` uses the `(k-1)`-st entry). -/
def listSeq (L : List ℤ) (k : ℕ) : ℤ := L.getD (k - 1) 0

/-- Does a pattern have discrepancy at most `1` on all homogeneous progressions inside
`{1, …, 11}`? -/
def lowDisc (L : List ℤ) : Bool :=
  (List.range' 1 11).all fun d =>
    (List.range' 1 11).all fun n =>
      if n * d ≤ 11 then decide ((homogSum (listSeq L) d n).natAbs ≤ 1) else true

/-- The complete list of `±1` patterns of length `11` with discrepancy `1`. -/
theorem pmLists_filter_lowDisc :
    (pmLists 11).filter lowDisc =
      [[1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1],
       [-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, 1],
       [1, -1, -1, 1, -1, 1, 1, -1, -1, 1, -1],
       [-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1]] := by
  decide +kernel

/-- **Classification.**  A `±1` sequence with discrepancy `1` on every homogeneous
progression inside `{1, …, 11}` has one of exactly four patterns of initial values. -/
theorem discrepancy_one_classification (f : ℕ → ℤ) (hf : IsPMOne f)
    (h : ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n * d ≤ 11 → (homogSum f d n).natAbs ≤ 1) :
    [f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11] ∈
      [[(1 : ℤ), -1, -1, 1, -1, 1, 1, -1, -1, 1, 1],
       [-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, 1],
       [1, -1, -1, 1, -1, 1, 1, -1, -1, 1, -1],
       [-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1]] := by
  set L : List ℤ := [f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11] with hL
  -- the pattern is a `±1` pattern of length `11`
  have hmem : L ∈ pmLists 11 := by
    have hall : ∀ x ∈ L, x = 1 ∨ x = -1 := by
      intro x hx
      simp only [hL, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hf _ (by norm_num)
    have := mem_pmLists L hall
    simpa [hL] using this
  -- the values of the pattern are the values of `f`
  have hseq : ∀ k : ℕ, 1 ≤ k → k ≤ 11 → listSeq L k = f k := by
    intro k h1 h2
    interval_cases k <;> rfl
  -- the pattern has discrepancy at most `1`
  have hlow : lowDisc L = true := by
    simp only [lowDisc, List.all_eq_true]
    intro d hd n hn
    simp only [List.mem_range'_1] at hd hn
    by_cases hle : n * d ≤ 11
    · simp only [if_pos hle, decide_eq_true_eq]
      have hcong : homogSum (listSeq L) d n = homogSum f d n :=
        homogSum_congr hd.1 fun k hk1 hk2 => hseq k hk1 (le_trans hk2 hle)
      rw [hcong]
      exact h d n hd.1 hn.1 hle
    · simp [hle]
  -- hence the pattern occurs in the enumerated list
  have : L ∈ (pmLists 11).filter lowDisc := List.mem_filter.mpr ⟨hmem, hlow⟩
  rwa [pmLists_filter_lowDisc] at this

/-- The discrepancy-one patterns agree, up to a global sign, on `{1, …, 10}`. -/
theorem discrepancy_one_first_ten (f : ℕ → ℤ) (hf : IsPMOne f)
    (h : ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n * d ≤ 11 → (homogSum f d n).natAbs ≤ 1) :
    [f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10] = [1, -1, -1, 1, -1, 1, 1, -1, -1, 1] ∨
    [f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10] =
      [-1, 1, 1, -1, 1, -1, -1, 1, 1, -1] := by
  have := discrepancy_one_classification f hf h
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq] at this
  rcases this with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ |
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ |
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ |
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ <;>
    simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib

/-!
# Special cases and reductions for the Erdős discrepancy problem

We record:

* `Frontier.UnboundedDiscrepancy`, the per-sequence form of the statement, and the fact
  that the Erdős discrepancy statement is exactly "every `±1` sequence has unbounded
  discrepancy";
* the theorem for all sequences that are **eventually constant along some homogeneous
  progression** (the sums along that progression then grow linearly), and its corollaries
  for **eventually periodic** and **periodic** `±1` sequences;
* the reduction for **completely multiplicative** `±1` sequences: all homogeneous sums are
  of the form `f d * (f 1 + ⋯ + f n)`, so unbounded discrepancy is equivalent to
  unboundedness of the ordinary partial sums.
-/

namespace Frontier

/-- `f` has unbounded discrepancy along homogeneous arithmetic progressions. -/
def UnboundedDiscrepancy (f : ℕ → ℤ) : Prop :=
  ∀ C : ℕ, ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ C < (homogSum f d n).natAbs

/-- The Erdős discrepancy statement says exactly that every `±1` sequence has unbounded
discrepancy. -/
theorem erdosDiscrepancyStatement_iff :
    ErdosDiscrepancyStatement ↔ ∀ f : ℕ → ℤ, IsPMOne f → UnboundedDiscrepancy f := Iff.rfl

/-! ### Sequences that are eventually constant along a progression -/

/-- A homogeneous sum of `n` terms of a `±1` sequence has absolute value at most `n`. -/
theorem homogSum_natAbs_le {f : ℕ → ℤ} (hf : IsPMOne f) {d : ℕ} (hd : 1 ≤ d) :
    ∀ n : ℕ, (homogSum f d n).natAbs ≤ n := by
  intro n
  induction n with
  | zero => simp [homogSum]
  | succ m ih =>
      have hpos : 1 ≤ (m + 1) * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hv := hf ((m + 1) * d) hpos
      rw [homogSum_succ]
      omega

/-- If `f` is constant equal to `c` on the tail `{i * d : i ≥ M}` of a homogeneous
progression, its partial sums along that progression grow linearly. -/
theorem homogSum_eventually_constant {f : ℕ → ℤ} {d M : ℕ} {c : ℤ}
    (hconst : ∀ i, M ≤ i → 1 ≤ i → f (i * d) = c) :
    ∀ k : ℕ, homogSum f d (M + k) = homogSum f d M + k * c := by
  intro k
  induction k with
  | zero => simp
  | succ j ih =>
      have hstep : M + (j + 1) = (M + j) + 1 := by ring
      rw [hstep, homogSum_succ, ih, hconst (M + j + 1) (by omega) (by omega)]
      push_cast
      ring

/-- **Unbounded discrepancy for sequences eventually constant along a progression.** -/
theorem unboundedDiscrepancy_of_eventually_constant {f : ℕ → ℤ} (hf : IsPMOne f)
    {d M : ℕ} {c : ℤ} (hd : 1 ≤ d) (hc : c = 1 ∨ c = -1)
    (hconst : ∀ i, M ≤ i → 1 ≤ i → f (i * d) = c) : UnboundedDiscrepancy f := by
  intro C
  refine ⟨d, M + (C + M + 1), hd, by omega, ?_⟩
  have hA : (homogSum f d M).natAbs ≤ M := homogSum_natAbs_le hf hd M
  rw [homogSum_eventually_constant hconst]
  rcases hc with h | h <;> subst h <;> push_cast <;> omega

/-! ### Eventually periodic and periodic sequences -/

/-- An eventually periodic sequence is eventually constant along the progression whose
difference is the period. -/
theorem apply_mul_eventually_period {f : ℕ → ℤ} {p M : ℕ} (hp : 1 ≤ p)
    (hper : ∀ n, M ≤ n → f (n + p) = f n) :
    ∀ i, M + 1 ≤ i → 1 ≤ i → f (i * p) = f ((M + 1) * p) := by
  intro i hi _
  induction i with
  | zero => omega
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hi with h | h
      · rw [← h]
      · have hm : M + 1 ≤ m := by omega
        have hstep : (m + 1) * p = m * p + p := by ring
        have hMle : M ≤ m * p := le_trans (by omega) (Nat.le_mul_of_pos_right m hp)
        rw [hstep, hper (m * p) hMle, ih hm (by omega)]

/-- **The Erdős discrepancy statement holds for eventually periodic `±1` sequences.** -/
theorem unboundedDiscrepancy_of_eventually_periodic {f : ℕ → ℤ} {p M : ℕ} (hp : 1 ≤ p)
    (hper : ∀ n, M ≤ n → f (n + p) = f n) (hf : IsPMOne f) : UnboundedDiscrepancy f := by
  have hpos : 1 ≤ (M + 1) * p := Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact unboundedDiscrepancy_of_eventually_constant hf hp (hf ((M + 1) * p) hpos)
    (apply_mul_eventually_period hp hper)

/-- **The Erdős discrepancy statement holds for periodic `±1` sequences.** -/
theorem unboundedDiscrepancy_of_periodic {f : ℕ → ℤ} {p : ℕ} (hp : 1 ≤ p)
    (hper : ∀ n, f (n + p) = f n) (hf : IsPMOne f) : UnboundedDiscrepancy f :=
  unboundedDiscrepancy_of_eventually_periodic (M := 0) hp (fun n _ => hper n) hf

/-! ### Completely multiplicative sequences -/

/-- `f` is completely multiplicative (on positive arguments). -/
def CompletelyMultiplicative (f : ℕ → ℤ) : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → f (a * b) = f a * f b

/-- For a completely multiplicative sequence every homogeneous sum is a multiple of an
ordinary partial sum. -/
theorem homogSum_completelyMultiplicative {f : ℕ → ℤ} (h : CompletelyMultiplicative f)
    {d : ℕ} (hd : 1 ≤ d) : ∀ n : ℕ, homogSum f d n = f d * homogSum f 1 n := by
  intro n
  induction n with
  | zero => simp [homogSum]
  | succ m ih =>
      rw [homogSum_succ, homogSum_succ, ih, h (m + 1) d (by omega) hd, mul_one]
      ring

/-- **Reduction for completely multiplicative sequences.** Such a `±1` sequence has
unbounded discrepancy iff its ordinary partial sums `f 1 + ⋯ + f n` are unbounded. -/
theorem unboundedDiscrepancy_completelyMultiplicative_iff {f : ℕ → ℤ}
    (h : CompletelyMultiplicative f) (hf : IsPMOne f) :
    UnboundedDiscrepancy f ↔ ∀ C : ℕ, ∃ n : ℕ, 1 ≤ n ∧ C < (homogSum f 1 n).natAbs := by
  constructor
  · intro hU C
    obtain ⟨d, n, hd, hn, hlt⟩ := hU C
    refine ⟨n, hn, ?_⟩
    rw [homogSum_completelyMultiplicative h hd n, Int.natAbs_mul] at hlt
    rcases hf d hd with hv | hv <;> rw [hv] at hlt <;> simpa using hlt
  · intro hS C
    obtain ⟨n, hn, hlt⟩ := hS C
    exact ⟨1, n, le_rfl, hn, hlt⟩

/-! ### Invariance under changing finitely many values -/

/-- Two `±1` sequences that agree from `M` on have homogeneous sums differing by at most
`2 * M`. -/
theorem homogSum_sub_natAbs_le {f g : ℕ → ℤ} (hf : IsPMOne f) (hg : IsPMOne g)
    {M d : ℕ} (hd : 1 ≤ d) (h : ∀ k, M ≤ k → f k = g k) :
    ∀ n : ℕ, (homogSum f d n - homogSum g d n).natAbs ≤ 2 * min n M := by
  intro n
  induction n with
  | zero => simp [homogSum]
  | succ m ih =>
      have hle : m + 1 ≤ (m + 1) * d := Nat.le_mul_of_pos_right _ hd
      have hpos : 1 ≤ (m + 1) * d := le_trans (by omega) hle
      rw [homogSum_succ, homogSum_succ]
      by_cases hcase : M ≤ (m + 1) * d
      · have heq := h _ hcase
        omega
      · have h1 := hf ((m + 1) * d) hpos
        have h2 := hg ((m + 1) * d) hpos
        omega

/-- **Unbounded discrepancy only depends on the tail of a sequence**: changing finitely
many values of a `±1` sequence does not affect it. -/
theorem unboundedDiscrepancy_of_eventuallyEq {f g : ℕ → ℤ} (hf : IsPMOne f) (hg : IsPMOne g)
    {M : ℕ} (h : ∀ k, M ≤ k → f k = g k) (hU : UnboundedDiscrepancy f) :
    UnboundedDiscrepancy g := by
  intro C
  obtain ⟨d, n, hd, hn, hlt⟩ := hU (C + 2 * M)
  refine ⟨d, n, hd, hn, ?_⟩
  have hdiff := homogSum_sub_natAbs_le hf hg hd h n
  have hmin : 2 * min n M ≤ 2 * M := by omega
  omega

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy

/-!
# Sharpness of the base case

`Frontier.erdos_discrepancy` shows that every `±1` sequence has discrepancy at least `2`
along some homogeneous arithmetic progression, using only the twelve values `f 1, …, f 12`.
Here we show that twelve values are really needed: there is an explicit `±1` sequence whose
homogeneous partial sums are all bounded by `1` in absolute value as long as they stay
inside `{1, …, 11}`.
-/

namespace Frontier

/-- The pattern `goodPattern[k]` is the `k`-th term (`1 ≤ k ≤ 11`) of a `±1` sequence of
discrepancy `1` on `{1, …, 11}`; entry `0` is a dummy. -/
def goodPattern : List Int := [1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1]

/-- An explicit `±1` sequence with discrepancy `1` on the initial segment `{1, …, 11}`. -/
def goodSeq (n : ℕ) : Int := goodPattern.getD n 1

theorem goodSeq_pm_one : IsPMOne goodSeq := by
  intro n _
  by_cases h : n < 12
  · interval_cases n <;> decide
  · left
    have hlen : goodPattern.length ≤ n := by simp [goodPattern]; omega
    show goodPattern.getD n 1 = 1
    exact List.getD_eq_default _ _ hlen

/-- The explicit sequence has discrepancy at most `1` on every homogeneous arithmetic
progression contained in `{1, …, 11}`. -/
theorem goodSeq_discrepancy_le_one (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (h : n * d ≤ 11) :
    (homogSum goodSeq d n).natAbs ≤ 1 := by
  have hd' : d ≤ 11 := le_trans (Nat.le_mul_of_pos_left d hn) h
  have hn' : n ≤ 11 := le_trans (Nat.le_mul_of_pos_right n hd) h
  interval_cases d <;> interval_cases n <;> first | omega | decide

/-- **Sharpness of the base case.** There is a `±1` sequence all of whose homogeneous
partial sums lying inside `{1, …, 11}` are bounded by `1`; so the twelve values used in
`Frontier.erdos_discrepancy` cannot be reduced to eleven. -/
theorem erdos_discrepancy_base_sharp :
    ∃ g : ℕ → Int, IsPMOne g ∧
      ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n * d ≤ 11 → (homogSum g d n).natAbs ≤ 1 :=
  ⟨goodSeq, goodSeq_pm_one, goodSeq_discrepancy_le_one⟩

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

import Mathlib
import RequestProject.ErdosDiscrepancy

/-!
# Erdős discrepancy: Mathlib-idiomatic restatement

`RequestProject/ErdosDiscrepancy.lean` is written in pure Lean core (no imports), so it
uses a recursively defined partial sum `Frontier.homogSum` and `Int.natAbs`.  Here we
identify that partial sum with the Mathlib sum `∑ i ∈ Finset.Icc 1 n, f (i * d)` and
restate the proved base case using `|·|`.
-/

namespace Frontier

theorem homogSum_succ (f : ℕ → ℤ) (d n : ℕ) :
    homogSum f d (n + 1) = homogSum f d n + f ((n + 1) * d) := by
  cases n with
  | zero => simp [homogSum]
  | succ k => rfl

/-- `homogSum` is the sum of `f` over the homogeneous arithmetic progression
`d, 2d, …, nd`. -/
theorem homogSum_eq_sum (f : ℕ → ℤ) (d n : ℕ) :
    homogSum f d n = ∑ i ∈ Finset.Icc 1 n, f (i * d) := by
  induction n with
  | zero => simp [homogSum]
  | succ k ih =>
      rw [homogSum_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]

/-- **Erdős discrepancy, base case `C = 1`, in Mathlib notation.**
For every `±1`-valued sequence `f` there are `d, n ≥ 1` with
`|f d + f (2d) + ⋯ + f (nd)| ≥ 2`. -/
theorem erdos_discrepancy_sum (f : ℕ → ℤ) (hf : ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1) :
    ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ 2 ≤ |∑ i ∈ Finset.Icc 1 n, f (i * d)| := by
  obtain ⟨d, n, hd, hn, hlt⟩ := erdos_discrepancy f hf
  refine ⟨d, n, hd, hn, ?_⟩
  rw [← homogSum_eq_sum]
  have : (2 : ℤ) ≤ (homogSum f d n).natAbs := by exact_mod_cast hlt
  rwa [Int.abs_eq_natAbs]

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancySpecialCases

/-!
# An explicit `±1` sequence with slowly growing, but unbounded, discrepancy

The classical near-extremal example for the Erdős discrepancy problem is the `±1` sequence
determined by the base-`3` rule

* `f n = 1`  if `n ≡ 1 [MOD 3]`,
* `f n = -1` if `n ≡ 2 [MOD 3]`,
* `f (3 * n) = f n`.

Its partial sums satisfy `S (3 * m) = S m` and `S (3 * m + 1) = S m + 1`, so along the
indices `a k = (3 ^ (k + 1) - 1) / 2` the partial sum equals `k + 1`: the discrepancy of
this sequence is unbounded, but grows only logarithmically.

We prove here that this sequence is `±1`-valued and has unbounded discrepancy.
-/

namespace Frontier

/-- The base-`3` `±1` sequence described above. -/
def triSeq (n : ℕ) : ℤ :=
  if n % 3 = 1 then 1
  else if n % 3 = 2 then -1
  else if n = 0 then 1
  else triSeq (n / 3)
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero (by assumption)) (by norm_num)

theorem triSeq_mod_one {n : ℕ} (h : n % 3 = 1) : triSeq n = 1 := by
  rw [triSeq]; simp [h]

theorem triSeq_mod_two {n : ℕ} (h : n % 3 = 2) : triSeq n = -1 := by
  rw [triSeq]; simp [h]

theorem triSeq_three_mul (m : ℕ) : triSeq (3 * m) = triSeq m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; norm_num
  · rw [triSeq]
    have h0 : 3 * m % 3 = 0 := by omega
    have h1 : 3 * m ≠ 0 := by omega
    have h2 : 3 * m / 3 = m := by omega
    simp [h0, h1, h2]

theorem triSeq_pm (n : ℕ) : triSeq n = 1 ∨ triSeq n = -1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rw [triSeq]
      split
      · exact Or.inl rfl
      · split
        · exact Or.inr rfl
        · split
          · exact Or.inl rfl
          · exact ih (n / 3) (Nat.div_lt_self (Nat.pos_of_ne_zero (by assumption))
              (by norm_num))

theorem triSeq_pm_one : IsPMOne triSeq := fun n _ => triSeq_pm n

/-- The partial sums `S n = f 1 + ⋯ + f n` of the base-`3` sequence. -/
def triSum (n : ℕ) : ℤ := homogSum triSeq 1 n

theorem triSum_succ (n : ℕ) : triSum (n + 1) = triSum n + triSeq (n + 1) := by
  rw [triSum, triSum, homogSum_succ, mul_one]

/-- Along multiples of `3` the partial sums are unchanged. -/
theorem triSum_three_mul : ∀ m : ℕ, triSum (3 * m) = triSum m := by
  intro m
  induction m with
  | zero => rfl
  | succ j ih =>
      have h1 : triSeq (3 * j + 1) = 1 := triSeq_mod_one (by omega)
      have h2 : triSeq (3 * j + 2) = -1 := triSeq_mod_two (by omega)
      have h3 : triSeq (3 * j + 3) = triSeq (j + 1) := by
        rw [show 3 * j + 3 = 3 * (j + 1) from by ring, triSeq_three_mul]
      have e1 : triSum (3 * j + 1) = triSum (3 * j) + triSeq (3 * j + 1) := triSum_succ _
      have e2 : triSum (3 * j + 2) = triSum (3 * j + 1) + triSeq (3 * j + 2) := triSum_succ _
      have e3 : triSum (3 * j + 3) = triSum (3 * j + 2) + triSeq (3 * j + 3) := triSum_succ _
      have e4 : triSum (j + 1) = triSum j + triSeq (j + 1) := triSum_succ _
      rw [show 3 * (j + 1) = 3 * j + 3 from by ring, e3, e2, e1, ih, h1, h2, h3, e4]
      ring

/-- One step past a multiple of `3` the partial sum increases by one. -/
theorem triSum_three_mul_add_one (m : ℕ) : triSum (3 * m + 1) = triSum m + 1 := by
  rw [triSum_succ, triSum_three_mul, triSeq_mod_one (by omega)]

/-- The indices `a 0 = 1`, `a (k+1) = 3 * a k + 1` where the partial sums reach `k + 1`. -/
def triIdx : ℕ → ℕ
  | 0 => 1
  | k + 1 => 3 * triIdx k + 1

theorem triIdx_pos (k : ℕ) : 1 ≤ triIdx k := by
  cases k with
  | zero => exact le_rfl
  | succ j => show 1 ≤ 3 * triIdx j + 1; omega

/-- `a k = (3 ^ (k + 1) - 1) / 2`, so the index grows geometrically. -/
theorem two_mul_triIdx_add_one (k : ℕ) : 2 * triIdx k + 1 = 3 ^ (k + 1) := by
  induction k with
  | zero => norm_num [triIdx]
  | succ j ih =>
      have : triIdx (j + 1) = 3 * triIdx j + 1 := rfl
      rw [this]
      ring_nf
      ring_nf at ih
      omega

/-- The partial sum at the index `a k` equals `k + 1`. -/
theorem triSum_triIdx (k : ℕ) : triSum (triIdx k) = k + 1 := by
  induction k with
  | zero => rw [show triIdx 0 = 1 from rfl, triSum, homogSum]; norm_num [triSeq_mod_one]
  | succ j ih =>
      have hstep : triIdx (j + 1) = 3 * triIdx j + 1 := rfl
      rw [hstep, triSum_three_mul_add_one, ih]
      push_cast
      ring

/-- **The base-`3` sequence has unbounded discrepancy** (in fact logarithmically growing:
the partial sum at `(3 ^ (k+1) - 1) / 2` equals `k + 1`). -/
theorem triSeq_unboundedDiscrepancy : UnboundedDiscrepancy triSeq := by
  intro C
  refine ⟨1, triIdx C, le_rfl, triIdx_pos C, ?_⟩
  have h : homogSum triSeq 1 (triIdx C) = (C : ℤ) + 1 := triSum_triIdx C
  rw [h]
  omega

/-! ### The sequence is completely multiplicative -/

private theorem triSeq_mul_aux : ∀ s a b : ℕ, a + b = s → 1 ≤ a → 1 ≤ b →
    triSeq (a * b) = triSeq a * triSeq b := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
      intro a b hs ha hb
      by_cases h3a : a % 3 = 0
      · obtain ⟨a', rfl⟩ : ∃ a', a = 3 * a' := ⟨a / 3, by omega⟩
        have ha' : 1 ≤ a' := by omega
        rw [show 3 * a' * b = 3 * (a' * b) from by ring, triSeq_three_mul, triSeq_three_mul,
          ih (a' + b) (by omega) a' b rfl ha' hb]
      · by_cases h3b : b % 3 = 0
        · obtain ⟨b', rfl⟩ : ∃ b', b = 3 * b' := ⟨b / 3, by omega⟩
          have hb' : 1 ≤ b' := by omega
          rw [show a * (3 * b') = 3 * (a * b') from by ring, triSeq_three_mul, triSeq_three_mul,
            ih (a + b') (by omega) a b' rfl ha hb']
        · rcases (show a % 3 = 1 ∨ a % 3 = 2 by omega) with h1 | h1 <;>
            rcases (show b % 3 = 1 ∨ b % 3 = 2 by omega) with h2 | h2
          · have hab : (a * b) % 3 = 1 := by rw [Nat.mul_mod, h1, h2]
            rw [triSeq_mod_one hab, triSeq_mod_one h1, triSeq_mod_one h2]; norm_num
          · have hab : (a * b) % 3 = 2 := by rw [Nat.mul_mod, h1, h2]
            rw [triSeq_mod_two hab, triSeq_mod_one h1, triSeq_mod_two h2]; norm_num
          · have hab : (a * b) % 3 = 2 := by rw [Nat.mul_mod, h1, h2]
            rw [triSeq_mod_two hab, triSeq_mod_two h1, triSeq_mod_one h2]; norm_num
          · have hab : (a * b) % 3 = 1 := by rw [Nat.mul_mod, h1, h2]
            rw [triSeq_mod_one hab, triSeq_mod_two h1, triSeq_mod_two h2]; norm_num

/-- The base-`3` sequence is completely multiplicative. -/
theorem triSeq_completelyMultiplicative : CompletelyMultiplicative triSeq :=
  fun a b ha hb => triSeq_mul_aux (a + b) a b rfl ha hb

/-! ### The discrepancy of the base-`3` sequence grows only logarithmically -/

/-- Two steps past a multiple of `3` the partial sum is again unchanged. -/
theorem triSum_three_mul_add_two (m : ℕ) : triSum (3 * m + 2) = triSum m := by
  rw [show 3 * m + 2 = (3 * m + 1) + 1 from by ring, triSum_succ, triSum_three_mul_add_one,
    triSeq_mod_two (by omega)]
  ring

/-- Passing to `n / 3` decreases the partial sum by at most one, and never increases it. -/
theorem triSum_div_three (n : ℕ) :
    triSum (n / 3) ≤ triSum n ∧ triSum n ≤ triSum (n / 3) + 1 := by
  rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h | h
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m := ⟨n / 3, by omega⟩
    rw [show 3 * m / 3 = m from by omega, triSum_three_mul]
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 1 := ⟨n / 3, by omega⟩
    rw [show (3 * m + 1) / 3 = m from by omega, triSum_three_mul_add_one]
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 2 := ⟨n / 3, by omega⟩
    rw [show (3 * m + 2) / 3 = m from by omega, triSum_three_mul_add_two]
    omega

/-- The partial sums of the base-`3` sequence are nonnegative. -/
theorem triSum_nonneg : ∀ n : ℕ, 0 ≤ triSum n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact le_of_eq rfl
      · have hlt : n / 3 < n := Nat.div_lt_self hn (by norm_num)
        have := (triSum_div_three n).1
        have := ih (n / 3) hlt
        omega

/-- The partial sums of the base-`3` sequence are at most `log₃ n + 1`. -/
theorem triSum_le_log : ∀ n : ℕ, triSum n ≤ Nat.log 3 n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases Nat.lt_or_ge n 3 with hsmall | hbig
      · interval_cases n
        · norm_num [triSum, homogSum]
        · rw [show (1 : ℕ) = 0 + 1 from rfl, triSum_succ]
          norm_num [triSum, homogSum, triSeq_mod_one]
        · rw [show (2 : ℕ) = 3 * 0 + 2 from rfl, triSum_three_mul_add_two]
          norm_num [triSum, homogSum]
      · have hn : 0 < n := by omega
        have hlt : n / 3 < n := Nat.div_lt_self hn (by norm_num)
        have hlog : Nat.log 3 (n / 3) + 1 = Nat.log 3 n := by
          have h1 : Nat.log 3 (n / 3) = Nat.log 3 n - 1 := Nat.log_div_base 3 n
          have h2 : 0 < Nat.log 3 n := Nat.log_pos (by norm_num) hbig
          omega
        have h3 := (triSum_div_three n).2
        have h4 := ih (n / 3) hlt
        have : (Nat.log 3 (n / 3) : ℤ) + 1 = (Nat.log 3 n : ℤ) := by exact_mod_cast hlog
        omega

/-- **The discrepancy of the base-`3` sequence is at most `log₃ n + 1` on every homogeneous
arithmetic progression.**  Together with `triSeq_unboundedDiscrepancy` this shows that its
discrepancy is unbounded but of logarithmic order. -/
theorem triSeq_discrepancy_le_log {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    (homogSum triSeq d n).natAbs ≤ Nat.log 3 n + 1 := by
  rw [homogSum_completelyMultiplicative triSeq_completelyMultiplicative hd n, Int.natAbs_mul]
  have h1 : (0 : ℤ) ≤ triSum n := triSum_nonneg n
  have h2 : triSum n ≤ Nat.log 3 n + 1 := triSum_le_log n
  have h3 : (homogSum triSeq 1 n).natAbs ≤ Nat.log 3 n + 1 := by
    rw [show homogSum triSeq 1 n = triSum n from rfl]
    omega
  rcases triSeq_pm d with h | h <;> rw [h] <;> simpa using h3

end Frontier

