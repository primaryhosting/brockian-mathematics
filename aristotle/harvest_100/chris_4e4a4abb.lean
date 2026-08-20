/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header above
-- is written as a plain comment and repeated as a module docstring after the import.)

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A sequence `f : ℕ → ℤ` is a `±1` sequence if `f n ∈ {1, -1}` for every `n ≥ 1`
(the value `f 0` is irrelevant, since homogeneous arithmetic progressions only use
indices `i * d` with `i, d ≥ 1`). -/
def IsPMOne (f : ℕ → ℤ) : Prop := ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1

/-- The sum of `f` over the first `n` terms of the homogeneous arithmetic progression
of common difference `d`, i.e. `f d + f (2d) + ⋯ + f (nd)`. -/
def hapSum (f : ℕ → ℤ) (n d : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, f (i * d)

/-- The Erdős discrepancy problem (solved by Tao): every `±1` sequence has unbounded
discrepancy along homogeneous arithmetic progressions.  This is the statement; the
theorem `Frontier.erdos_discrepancy` below proves the base case `C = 1` of it, with
an explicit bound on the length of the progression involved. -/
def ErdosDiscrepancyStatement : Prop :=
  ∀ f : ℕ → ℤ, IsPMOne f → ∀ C : ℤ, ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ C < |hapSum f n d|

/-- **Erdős discrepancy, base case.**  Every `±1` sequence `f` admits a homogeneous
arithmetic progression `d, 2d, …, nd` contained in `{1, …, 12}` along which the
discrepancy is at least `2`; in particular the discrepancy of every `±1` sequence
exceeds `1`.  (The bound `12` is sharp: there are `±1` sequences of length `11` all of
whose homogeneous arithmetic progression sums lie in `{-1, 0, 1}`.) -/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsPMOne f) :
    ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ n * d ≤ 12 ∧ 2 ≤ |hapSum f n d| := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ n d : ℕ, 0 < n → 0 < d → n * d ≤ 12 →
      -1 ≤ hapSum f n d ∧ hapSum f n d ≤ 1 := by
    intro n d hn hd hnd
    have h := hcon n d hn hd hnd
    have : |hapSum f n d| ≤ 1 := by omega
    exact abs_le.mp this
  have ha := hf 1 (by norm_num)
  have hb := hf 2 (by norm_num)
  have hc := hf 3 (by norm_num)
  have hd := hf 4 (by norm_num)
  have he := hf 5 (by norm_num)
  have hff := hf 6 (by norm_num)
  have hg := hf 7 (by norm_num)
  have hh := hf 8 (by norm_num)
  have hi := hf 9 (by norm_num)
  have hj := hf 10 (by norm_num)
  have hk := hf 11 (by norm_num)
  have hl := hf 12 (by norm_num)
  have s2 := key 2 1 (by norm_num) (by norm_num) (by norm_num)
  have s4 := key 4 1 (by norm_num) (by norm_num) (by norm_num)
  have s6 := key 6 1 (by norm_num) (by norm_num) (by norm_num)
  have s8 := key 8 1 (by norm_num) (by norm_num) (by norm_num)
  have s10 := key 10 1 (by norm_num) (by norm_num) (by norm_num)
  have s12 := key 12 1 (by norm_num) (by norm_num) (by norm_num)
  have t2 := key 2 2 (by norm_num) (by norm_num) (by norm_num)
  have t4 := key 4 2 (by norm_num) (by norm_num) (by norm_num)
  have t6 := key 6 2 (by norm_num) (by norm_num) (by norm_num)
  have u4 := key 4 3 (by norm_num) (by norm_num) (by norm_num)
  have v2 := key 2 4 (by norm_num) (by norm_num) (by norm_num)
  have v3 := key 3 4 (by norm_num) (by norm_num) (by norm_num)
  norm_num [hapSum, Finset.sum_Icc_succ_top] at s2 s4 s6 s8 s10 s12 t2 t4 t6 u4 v2 v3
  omega

/-- Reformulation of the base case: every `±1` sequence has discrepancy `> 1`, i.e. the
statement `ErdosDiscrepancyStatement` holds for the constant `C = 1` (and hence for every
`C ≤ 1`). -/
theorem erdos_discrepancy_one (f : ℕ → ℤ) (hf : IsPMOne f) :
    ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ (1 : ℤ) < |hapSum f n d| := by
  obtain ⟨n, d, hn, hd, _, h⟩ := erdos_discrepancy f hf
  exact ⟨n, d, hn, hd, by omega⟩

/-- An explicit `±1` sequence whose first `11` entries are `+ - - + - + + - - + +`.
It witnesses the sharpness of the bound `12` in `Frontier.erdos_discrepancy`. -/
def seq11 : ℕ → ℤ := fun n => ([0, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1] : List ℤ).getD n 1

theorem isPMOne_seq11 : IsPMOne seq11 := by
  intro n hn
  rcases lt_or_ge n 12 with h | h
  · interval_cases n <;> decide
  · exact Or.inl (List.getD_eq_default _ _ (by simpa using h))

/-- **Sharpness of the bound `12`.**  All homogeneous arithmetic progressions contained in
`{1, …, 11}` have discrepancy at most `1` for the sequence `seq11`, so the conclusion of
`Frontier.erdos_discrepancy` fails if `12` is replaced by `11`. -/
theorem seq11_discrepancy_le_one (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hnd : n * d ≤ 11) :
    |hapSum seq11 n d| ≤ 1 := by
  have key : ∀ n ∈ Finset.Icc 1 11, ∀ d ∈ Finset.Icc 1 11, n * d ≤ 11 →
      |hapSum seq11 n d| ≤ 1 := by decide
  have hn' : n ≤ 11 := le_trans (Nat.le_mul_of_pos_right n hd) hnd
  have hd' : d ≤ 11 := le_trans (Nat.le_mul_of_pos_left d hn) hnd
  exact key n (Finset.mem_Icc.mpr ⟨hn, hn'⟩) d (Finset.mem_Icc.mpr ⟨hd, hd'⟩) hnd

/-- A Lean-checked reduction: to prove the full Erdős discrepancy statement it suffices to
prove it for natural-number bounds `C`, since the discrepancy bound is monotone in `C`. -/
theorem erdosDiscrepancyStatement_of_nat
    (H : ∀ f : ℕ → ℤ, IsPMOne f → ∀ C : ℕ, ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ (C : ℤ) < |hapSum f n d|) :
    ErdosDiscrepancyStatement := by
  intro f hf C
  obtain ⟨n, d, hn, hd, h⟩ := H f hf C.toNat
  refine ⟨n, d, hn, hd, lt_of_le_of_lt ?_ h⟩
  exact_mod_cast Int.self_le_toNat C

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

