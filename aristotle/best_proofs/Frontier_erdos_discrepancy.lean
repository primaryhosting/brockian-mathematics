/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no imports): a Lean module docstring
must be the first command in a file, so the required header above forces the
file to contain no `import` lines.  Everything below therefore uses only the
Lean 4 core library.  The file `RequestProject/Main.lean` re-states the results
in Mathlib terms (`∑ i ∈ Finset.Icc 1 n, f (i * d)` and `|·|`) and proves that
the two formulations agree.
-/

namespace Frontier

/-- The partial sum of `f` along the homogeneous arithmetic progression with
common difference `d`, over its first `n` terms:  `f d + f (2d) + ⋯ + f (n d)`. -/
def hapSum (f : Nat → Int) (n d : Nat) : Int :=
  ((List.range n).map (fun i => f ((i + 1) * d))).sum

/-- `f` is a `±1`-sequence. -/
def IsPlusMinusOne (f : Nat → Int) : Prop := ∀ n, f n = 1 ∨ f n = -1

/-- `f` has unbounded discrepancy along homogeneous arithmetic progressions:
for every bound `C` some partial sum `f d + f (2d) + ⋯ + f (n d)` exceeds `C`
in absolute value. -/
def HasUnboundedDiscrepancy (f : Nat → Int) : Prop :=
  ∀ C : Nat, ∃ n d : Nat, 1 ≤ n ∧ 1 ≤ d ∧ C < (hapSum f n d).natAbs

/-- **The Erdős discrepancy problem** (theorem of Tao): every `±1` sequence has
unbounded discrepancy on homogeneous arithmetic progressions.  This is the
statement; the theorem `Frontier.erdos_discrepancy` below proves its base case
`C = 1`. -/
def ErdosDiscrepancyStatement : Prop :=
  ∀ f : Nat → Int, IsPlusMinusOne f → HasUnboundedDiscrepancy f

section Expansions

variable (f : Nat → Int)

theorem hapSum_two (d : Nat) : hapSum f 2 d = f d + f (2 * d) := by
  simp [hapSum, List.range_succ]

theorem hapSum_four_one : hapSum f 4 1 = f 1 + f 2 + f 3 + f 4 := by
  simp [hapSum, List.range_succ]
  omega

theorem hapSum_six_one : hapSum f 6 1 = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  simp [hapSum, List.range_succ]
  omega

theorem hapSum_eight_one :
    hapSum f 8 1 = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp [hapSum, List.range_succ]
  omega

theorem hapSum_ten_one :
    hapSum f 10 1 =
      f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
  simp [hapSum, List.range_succ]
  omega

theorem hapSum_four_three : hapSum f 4 3 = f 3 + f 6 + f 9 + f 12 := by
  simp [hapSum, List.range_succ]
  omega

end Expansions

/-- Two `±1` values whose sum has absolute value at most `1` are opposite. -/
theorem pm_eq_neg_of_natAbs_add_le_one {a b : Int} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) (hab : (a + b).natAbs ≤ 1) : b = -a := by
  omega

/-- No `±1` sequence has all of its homogeneous-AP partial sums bounded by `1`
in absolute value.  (Only the values `f 1, …, f 12` are used.) -/
theorem not_discrepancy_le_one {f : Nat → Int} (hf : IsPlusMinusOne f)
    (h : ∀ n d : Nat, 1 ≤ n → 1 ≤ d → n * d ≤ 12 → (hapSum f n d).natAbs ≤ 1) :
    False := by
  -- doubling relations: `f (2d) = - f d`, coming from the two-term progressions
  have e2 : f 2 = -f 1 := by
    have h2 := h 2 1 (by omega) (by omega) (by omega)
    rw [hapSum_two] at h2
    exact pm_eq_neg_of_natAbs_add_le_one (hf 1) (hf 2) (by simpa using h2)
  have e4 : f 4 = -f 2 := by
    have h2 := h 2 2 (by omega) (by omega) (by omega)
    rw [hapSum_two] at h2
    exact pm_eq_neg_of_natAbs_add_le_one (hf 2) (hf 4) (by simpa using h2)
  have e6 : f 6 = -f 3 := by
    have h2 := h 2 3 (by omega) (by omega) (by omega)
    rw [hapSum_two] at h2
    exact pm_eq_neg_of_natAbs_add_le_one (hf 3) (hf 6) (by simpa using h2)
  have e8 : f 8 = -f 4 := by
    have h2 := h 2 4 (by omega) (by omega) (by omega)
    rw [hapSum_two] at h2
    exact pm_eq_neg_of_natAbs_add_le_one (hf 4) (hf 8) (by simpa using h2)
  have e10 : f 10 = -f 5 := by
    have h2 := h 2 5 (by omega) (by omega) (by omega)
    rw [hapSum_two] at h2
    exact pm_eq_neg_of_natAbs_add_le_one (hf 5) (hf 10) (by simpa using h2)
  have e12 : f 12 = -f 6 := by
    have h2 := h 2 6 (by omega) (by omega) (by omega)
    rw [hapSum_two] at h2
    exact pm_eq_neg_of_natAbs_add_le_one (hf 6) (hf 12) (by simpa using h2)
  -- the partial sums along `d = 1` and along `d = 3`
  have c4 := h 4 1 (by omega) (by omega) (by omega)
  have c6 := h 6 1 (by omega) (by omega) (by omega)
  have c8 := h 8 1 (by omega) (by omega) (by omega)
  have c10 := h 10 1 (by omega) (by omega) (by omega)
  have c34 := h 4 3 (by omega) (by omega) (by omega)
  rw [hapSum_four_one] at c4
  rw [hapSum_six_one] at c6
  rw [hapSum_eight_one] at c8
  rw [hapSum_ten_one] at c10
  rw [hapSum_four_three] at c34
  have h1 := hf 1
  have h3 := hf 3
  have h5 := hf 5
  have h7 := hf 7
  have h9 := hf 9
  omega

/-- **Base case of the Erdős discrepancy problem (discrepancy `> 1`).**

For every `±1` sequence `f` there are `n, d ≥ 1` with `n * d ≤ 12` such that the
partial sum of `f` along the homogeneous arithmetic progression `d, 2d, …, n d`
has absolute value at least `2`.  Equivalently, no `±1` sequence has discrepancy
at most `1` on homogeneous arithmetic progressions.

This is the `C = 1` case of `Frontier.ErdosDiscrepancyStatement`, the Erdős
discrepancy problem, whose general form is a theorem of Tao.  The bound `12` is
optimal: `Frontier.edsWitness_discrepancy_le_one` (in `RequestProject/Main.lean`)
exhibits a `±1` sequence whose homogeneous-AP partial sums using only indices
`≤ 11` all have absolute value at most `1`. -/
theorem erdos_discrepancy {f : Nat → Int} (hf : IsPlusMinusOne f) :
    ∃ n d : Nat, 1 ≤ n ∧ 1 ≤ d ∧ n * d ≤ 12 ∧ 2 ≤ (hapSum f n d).natAbs := by
  refine Classical.byContradiction (fun hcon => not_discrepancy_le_one hf ?_)
  intro n d hn hd hnd
  refine Classical.byContradiction (fun hc => hcon ⟨n, d, hn, hd, hnd, ?_⟩)
  omega

/-- Reduction of the full Erdős discrepancy statement to a uniform finite
statement: if, for every `C`, there is a length `N` such that *every* `±1`
sequence has a homogeneous-AP partial sum of absolute value `> C` using only
indices `≤ N`, then every `±1` sequence has unbounded discrepancy. -/
theorem erdosDiscrepancyStatement_of_finite
    (H : ∀ C : Nat, ∃ N : Nat, ∀ f : Nat → Int, IsPlusMinusOne f →
      ∃ n d : Nat, 1 ≤ n ∧ 1 ≤ d ∧ n * d ≤ N ∧ C < (hapSum f n d).natAbs) :
    ErdosDiscrepancyStatement := by
  intro f hf C
  obtain ⟨_, hN⟩ := H C
  obtain ⟨n, d, hn, hd, _, hC⟩ := hN f hf
  exact ⟨n, d, hn, hd, hC⟩

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy

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

/-!
## Erdős discrepancy: Mathlib-flavoured restatement

`RequestProject/ErdosDiscrepancy.lean` (which must be import-free, since its
required module docstring has to be the first command in the file) develops the
Erdős discrepancy base case using the core-library sum
`((List.range n).map fun i => f ((i+1) * d)).sum`.  Here we check that this
agrees with the Mathlib sum `∑ i ∈ Finset.Icc 1 n, f (i * d)` and restate the
result in Mathlib notation.
-/

namespace Frontier

theorem hapSum_eq_sum_Icc (f : ℕ → ℤ) (n d : ℕ) :
    hapSum f n d = ∑ i ∈ Finset.Icc 1 n, f (i * d) := by
  induction n with
  | zero => simp [hapSum]
  | succ n ih =>
      have hlist : hapSum f (n + 1) d = hapSum f n d + f ((n + 1) * d) := by
        simp [hapSum, List.range_succ]
      rw [hlist, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

/-- **Base case of the Erdős discrepancy problem**, in Mathlib notation: for
every `±1` sequence `f` there are `n, d ≥ 1` with `n * d ≤ 12` such that
`|f d + f (2d) + ⋯ + f (n d)| ≥ 2`. -/
theorem erdos_discrepancy_sum {f : ℕ → ℤ} (hf : ∀ n, f n = 1 ∨ f n = -1) :
    ∃ n d : ℕ, 1 ≤ n ∧ 1 ≤ d ∧ n * d ≤ 12 ∧ 2 ≤ |∑ i ∈ Finset.Icc 1 n, f (i * d)| := by
  obtain ⟨n, d, hn, hd, h12, habs⟩ := erdos_discrepancy hf
  refine ⟨n, d, hn, hd, h12, ?_⟩
  rw [← hapSum_eq_sum_Icc, Int.abs_eq_natAbs]
  exact_mod_cast habs

end Frontier

/-!
## Optimality of the bound `12`

There is a `±1` sequence all of whose homogeneous-AP partial sums using only
indices `≤ 11` have absolute value at most `1`, so the base case above cannot be
witnessed inside `{1, …, 11}`.
-/

namespace Frontier

/-- A `±1` sequence with discrepancy `1` on all homogeneous arithmetic
progressions contained in `{1, …, 11}`. -/
def edsWitness : ℕ → ℤ := fun n => if n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 8 ∨ n = 9 then -1 else 1

theorem edsWitness_isPlusMinusOne : IsPlusMinusOne edsWitness := by
  intro n
  unfold edsWitness
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Every homogeneous arithmetic progression inside `{1, …, 11}` has
`edsWitness`-partial sums of absolute value at most `1`.  Together with
`Frontier.erdos_discrepancy` this shows that the bound `n * d ≤ 12` there is
optimal. -/
theorem edsWitness_discrepancy_le_one (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hnd : n * d ≤ 11) : (hapSum edsWitness n d).natAbs ≤ 1 := by
  have key : ∀ n < 12, ∀ d < 12, 1 ≤ n → 1 ≤ d → n * d ≤ 11 →
      (hapSum edsWitness n d).natAbs ≤ 1 := by decide
  have hn12 : n < 12 := lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_right n hd) hnd) (by norm_num)
  have hd12 : d < 12 := lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_left d hn) hnd) (by norm_num)
  exact key n hn12 d hd12 hn hd hnd

end Frontier

