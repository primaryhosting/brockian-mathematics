/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
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

namespace Frontier

/-- The discrepancy sum of the sequence `f` along the homogeneous arithmetic progression
of common difference `d` and length `n`, i.e. `f d + f (2 d) + ... + f (n d)`. -/
def apSum (f : ℕ → ℤ) (d n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, f (i * d)

/-- `f` is a `±1`-sequence (indexed by the positive integers). -/
def IsPMOne (f : ℕ → ℤ) : Prop := ∀ n, 0 < n → f n = 1 ∨ f n = -1

/-- The full Erdős discrepancy statement (Tao's theorem): every `±1` sequence has
unbounded discrepancy along homogeneous arithmetic progressions. This `Prop` is stated
here for reference; the theorem proved below, `Frontier.erdos_discrepancy`, is the
`C = 1` case, i.e. the base case of this statement. -/
def UnboundedDiscrepancy : Prop :=
  ∀ f : ℕ → ℤ, IsPMOne f → ∀ C : ℤ, ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ C < |apSum f d n|

section Base

variable {f : ℕ → ℤ} (hf : IsPMOne f)
  (h : ∀ d n : ℕ, 0 < d → 0 < n → n * d ≤ 12 → |apSum f d n| ≤ 1)

include hf h

/-- Under a discrepancy bound of `1`, consecutive terms of any homogeneous progression
cancel: `f (2 d) = - f d`. -/
private lemma two_mul_eq (d : ℕ) (hd : 0 < d) (hb : 2 * d ≤ 12) : f (2 * d) = -f d := by
  have h2 := h d 2 hd (by norm_num) (by omega)
  have e : apSum f d 2 = f d + f (2 * d) := by
    simp [apSum, Finset.sum_Icc_succ_top]
  rcases hf d hd with h1 | h1 <;> rcases hf (2 * d) (by positivity) with h3 | h3 <;>
    rw [e, h1, h3] at h2 <;> simp_all

/-- Under a discrepancy bound of `1`, `f (3 d) = - f d`. -/
private lemma three_mul_eq (d : ℕ) (hd : 0 < d) (hb : 4 * d ≤ 12) : f (3 * d) = -f d := by
  have h4 := h d 4 hd (by norm_num) (by omega)
  have e : apSum f d 4 = f d + f (2 * d) + f (3 * d) + f (4 * d) := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have e2 : f (2 * d) = -f d := two_mul_eq hf h d hd (by omega)
  have e4 : f (4 * d) = -f (2 * d) := by
    have := two_mul_eq hf h (2 * d) (by positivity) (by omega)
    simpa [← Nat.mul_assoc] using this
  rw [e, e2, e4, e2] at h4
  have hsum : |f (3 * d) + f d| ≤ 1 := by
    have : f d + -f d + f (3 * d) + - -f d = f (3 * d) + f d := by ring
    rwa [this] at h4
  rcases hf d hd with h1 | h1 <;> rcases hf (3 * d) (by positivity) with h3 | h3 <;>
    rw [h1, h3] at hsum <;> simp_all

/-- Under a discrepancy bound of `1`, `f (5 d) = - f d`. -/
private lemma five_mul_eq (d : ℕ) (hd : 0 < d) (hb : 6 * d ≤ 12) : f (5 * d) = -f d := by
  have h6 := h d 6 hd (by norm_num) (by omega)
  have e : apSum f d 6 =
      f d + f (2 * d) + f (3 * d) + f (4 * d) + f (5 * d) + f (6 * d) := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have e2 : f (2 * d) = -f d := two_mul_eq hf h d hd (by omega)
  have e3 : f (3 * d) = -f d := three_mul_eq hf h d hd (by omega)
  have e4 : f (4 * d) = f d := by
    have := two_mul_eq hf h (2 * d) (by positivity) (by omega)
    rw [← Nat.mul_assoc] at this
    norm_num at this
    rw [this, e2, neg_neg]
  have e6 : f (6 * d) = f d := by
    have := two_mul_eq hf h (3 * d) (by positivity) (by omega)
    rw [← Nat.mul_assoc] at this
    norm_num at this
    rw [this, e3, neg_neg]
  rw [e, e2, e3, e4, e6] at h6
  have hsum : |f (5 * d) + f d| ≤ 1 := by
    have : f d + -f d + -f d + f d + f (5 * d) + f d = f (5 * d) + f d := by ring
    rwa [this] at h6
  rcases hf d hd with h1 | h1 <;> rcases hf (5 * d) (by positivity) with h5 | h5 <;>
    rw [h1, h5] at hsum <;> simp_all

/-- A `±1` sequence cannot have all homogeneous-progression discrepancies bounded by `1`. -/
private lemma not_bounded_by_one : False := by
  -- basic values, in terms of `a = f 1`
  have e2 : f 2 = -f 1 := by simpa using two_mul_eq hf h 1 one_pos (by norm_num)
  have e3 : f 3 = -f 1 := by simpa using three_mul_eq hf h 1 one_pos (by norm_num)
  have e5 : f 5 = -f 1 := by simpa using five_mul_eq hf h 1 one_pos (by norm_num)
  have e4 : f 4 = f 1 := by
    have := two_mul_eq hf h 2 (by norm_num) (by norm_num)
    norm_num at this
    rw [this, e2, neg_neg]
  have e6 : f 6 = f 1 := by
    have := two_mul_eq hf h 3 (by norm_num) (by norm_num)
    norm_num at this
    rw [this, e3, neg_neg]
  have e8 : f 8 = -f 1 := by
    have := two_mul_eq hf h 4 (by norm_num) (by norm_num)
    norm_num at this
    rw [this, e4]
  have e9 : f 9 = f 1 := by
    have := three_mul_eq hf h 3 (by norm_num) (by norm_num)
    norm_num at this
    rw [this, e3, neg_neg]
  have e10 : f 10 = f 1 := by
    have := two_mul_eq hf h 5 (by norm_num) (by norm_num)
    norm_num at this
    rw [this, e5, neg_neg]
  -- the length-8 progression forces `f 7 = f 1`
  have h8 := h 1 8 one_pos (by norm_num) (by norm_num)
  have E8 : apSum f 1 8 = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  rw [E8, e2, e3, e4, e5, e6, e8] at h8
  have hsum : |f 7 + -f 1| ≤ 1 := by
    have : f 1 + -f 1 + -f 1 + f 1 + -f 1 + f 1 + f 7 + -f 1 = f 7 + -f 1 := by ring
    rwa [this] at h8
  have e7 : f 7 = f 1 := by
    rcases hf 1 one_pos with h1 | h1 <;> rcases hf 7 (by norm_num) with h7 | h7 <;>
      rw [h1, h7] at hsum <;> simp_all
  -- now the length-10 progression has discrepancy `2`
  have h10 := h 1 10 one_pos (by norm_num) (by norm_num)
  have E10 : apSum f 1 10 =
      f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  rw [E10, e2, e3, e4, e5, e6, e7, e8, e9, e10] at h10
  have hfin : |2 * f 1| ≤ 1 := by
    have : f 1 + -f 1 + -f 1 + f 1 + -f 1 + f 1 + f 1 + -f 1 + f 1 + f 1 = 2 * f 1 := by ring
    rwa [this] at h10
  rcases hf 1 one_pos with h1 | h1 <;> rw [h1] at hfin <;> norm_num at hfin

end Base

/-- **Erdős discrepancy problem, base case `C = 1`.**
For every `±1` sequence `f` there are a positive common difference `d` and a positive
length `n`, with all the used indices at most `12`, such that the discrepancy
`|f d + f (2 d) + ⋯ + f (n d)|` exceeds `1`.
(The full statement of Tao's theorem, that the discrepancy is unbounded, is recorded
as `Frontier.UnboundedDiscrepancy`; this is its `C = 1` case, made quantitative.
The bound `12` is optimal, see `Frontier.erdos_discrepancy_sharp`.) -/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsPMOne f) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ n * d ≤ 12 ∧ 1 < |apSum f d n| := by
  by_contra hcon
  push_neg at hcon
  exact not_bounded_by_one hf (fun d n hd hn hb => hcon d n hd hn hb)

/-- The `C = 1` case of `Frontier.UnboundedDiscrepancy`: every bound `C ≤ 1` is exceeded
by some homogeneous-progression discrepancy of any `±1` sequence. -/
theorem exists_discrepancy_gt_of_le_one (f : ℕ → ℤ) (hf : IsPMOne f) (C : ℤ) (hC : C ≤ 1) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ C < |apSum f d n| := by
  obtain ⟨d, n, hd, hn, -, hlt⟩ := erdos_discrepancy f hf
  exact ⟨d, n, hd, hn, lt_of_le_of_lt hC hlt⟩

/-- The `±1` sequence `1, -1, -1, 1, -1, 1, 1, -1, -1, 1, -1` (extended by `1`), which
has discrepancy at most `1` on every homogeneous progression using indices `≤ 11`. -/
def sharpWitness : ℕ → ℤ
  | 1 => 1 | 2 => -1 | 3 => -1 | 4 => 1 | 5 => -1 | 6 => 1
  | 7 => 1 | 8 => -1 | 9 => -1 | 10 => 1 | 11 => -1 | _ => 1

lemma isPMOne_sharpWitness : IsPMOne sharpWitness := by
  intro n _
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => decide
  | (k + 12) => left; rfl

/-- The bound `12` in `Frontier.erdos_discrepancy` is optimal: there is a `±1` sequence
all of whose homogeneous-progression discrepancies using indices at most `11` are `≤ 1`. -/
theorem erdos_discrepancy_sharp :
    IsPMOne sharpWitness ∧
      ∀ d n : ℕ, 0 < d → 0 < n → n * d ≤ 11 → |apSum sharpWitness d n| ≤ 1 := by
  refine ⟨isPMOne_sharpWitness, ?_⟩
  intro d n hd hn hb
  have hd11 : d ≤ 11 := by nlinarith
  have hn11 : n ≤ 11 := by nlinarith
  interval_cases d <;> interval_cases n <;>
    first
      | omega
      | (simp only [apSum]; decide)

end Frontier

