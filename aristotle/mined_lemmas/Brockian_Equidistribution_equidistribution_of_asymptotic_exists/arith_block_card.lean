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

/-
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Brockian.Equidistribution

/-- Triangular numbers: `T m = 1 + 2 + ⋯ + m = m (m+1) / 2`. -/

lemma arith_block_card (L : ℕ) (hL : 0 < L) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |((((Finset.range L).filter (fun k : ℕ => ((k : ℝ) / L) ∈ Set.Ico a b)).card : ℝ)) -
      (b - a) * L| ≤ 1 := by
  have hLR : (0:ℝ) < (L:ℝ) := by exact_mod_cast hL
  have hset : ((Finset.range L).filter (fun k : ℕ => ((k : ℝ) / L) ∈ Set.Ico a b))
      = Finset.Ico ⌈a * L⌉₊ ⌈b * L⌉₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico, Finset.mem_Ico,
      Nat.ceil_le, Nat.lt_ceil]
    constructor
    · rintro ⟨hk, h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hLR] at h1; linarith
      · rw [div_lt_iff₀ hLR] at h2; linarith
    · rintro ⟨h1, h2⟩
      have hkL : (k:ℝ) < L := by nlinarith
      refine ⟨by exact_mod_cast hkL, ?_, ?_⟩
      · rw [le_div_iff₀ hLR]; linarith
      · rw [div_lt_iff₀ hLR]; linarith
  rw [hset, Nat.card_Ico]
  have hx : (0:ℝ) ≤ a * L := by positivity
  have hy : (0:ℝ) ≤ b * L := by nlinarith
  have hle : ⌈a * L⌉₊ ≤ ⌈b * L⌉₊ := Nat.ceil_le_ceil (by nlinarith)
  rw [Nat.cast_sub hle]
  have h1 := Nat.le_ceil (a * L)
  have h2 := Nat.le_ceil (b * L)
  have h3 := Nat.ceil_lt_add_one hx
  have h4 := Nat.ceil_lt_add_one hy
  rw [abs_le]
  constructor <;> nlinarith

