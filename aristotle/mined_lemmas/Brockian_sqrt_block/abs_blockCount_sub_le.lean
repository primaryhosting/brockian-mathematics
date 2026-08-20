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

import Brockian.EquidistributionBVReduction

/-!
# Existence of an equidistributed sequence

This file exhibits an explicit sequence which is equidistributed mod one in the sense of
`Brockian.EquidistributionBVReduction.Equidistributed`, so that the hypotheses of
`Brockian.EquidistributionBVReduction.configCount_density_of_BV` are satisfiable.

The sequence is the concatenation of the uniform grids of odd sizes: the `k`-th block consists
of the `2k+1` points `0/(2k+1), 1/(2k+1), …, 2k/(2k+1)`, and it occupies the indices
`k² ≤ n < (k+1)²`.  Since `Nat.sqrt n = k` exactly on that range of indices, the sequence has the
closed form `gridSeq n = (n - (sqrt n)²) / (2 * sqrt n + 1)`.
-/

open scoped BigOperators
open scoped Classical
open Filter Set

namespace Brockian
namespace EquidistributionBVReduction

/-- The concatenation of the uniform grids of odd sizes: the block of indices
`k² ≤ n < (k+1)²` runs through the `2k+1` points `j / (2k+1)`. -/

lemma abs_blockCount_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {M : ℕ}
    (hM : 0 < M) : |(blockCount a b M : ℝ) - M * (b - a)| ≤ 1 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hfil : ((Finset.range M).filter (fun j : ℕ => ((j : ℝ) / M) ∈ Set.Ico a b))
      = Finset.Ico ⌈(M : ℝ) * a⌉₊ ⌈(M : ℝ) * b⌉₊ := by
    have hbM : ⌈(M : ℝ) * b⌉₊ ≤ M := by
      rw [Nat.ceil_le]; nlinarith
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Set.mem_Ico]
    constructor
    · rintro ⟨_, h1, h2⟩
      refine ⟨Nat.ceil_le.mpr ?_, Nat.lt_ceil.mpr ?_⟩
      · rw [le_div_iff₀ hM'] at h1; linarith
      · rw [div_lt_iff₀ hM'] at h2; linarith
    · rintro ⟨h1, h2⟩
      have h1' : (M : ℝ) * a ≤ j := Nat.ceil_le.mp h1
      have h2' : (j : ℝ) < (M : ℝ) * b := Nat.lt_ceil.mp h2
      refine ⟨lt_of_lt_of_le h2 hbM, ?_, ?_⟩
      · rw [le_div_iff₀ hM']; linarith
      · rw [div_lt_iff₀ hM']; linarith
  have hmono : ⌈(M : ℝ) * a⌉₊ ≤ ⌈(M : ℝ) * b⌉₊ := Nat.ceil_le_ceil (by nlinarith)
  rw [blockCount, hfil, Nat.card_Ico, Nat.cast_sub hmono]
  have h1 := Nat.le_ceil ((M : ℝ) * a)
  have h2 := Nat.le_ceil ((M : ℝ) * b)
  have h3 := Nat.ceil_lt_add_one (a := (M : ℝ) * a) (by positivity)
  have h4 := Nat.ceil_lt_add_one (a := (M : ℝ) * b) (by nlinarith)
  rw [abs_le]
  constructor <;> nlinarith

/-- The count over a full range of blocks is the sum of the block counts. -/
