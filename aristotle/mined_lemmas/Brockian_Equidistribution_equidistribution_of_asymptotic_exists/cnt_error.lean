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

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian.Equidistribution

/-- A sequence `u : ℕ → ℝ` is *asymptotically equidistributed mod 1* if for every
subinterval `[a, b) ⊆ [0, 1]` the asymptotic density of the set of indices `n` with
`Int.fract (u n) ∈ [a, b)` exists and equals the length `b - a` of the interval. -/

lemma cnt_error (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (N : ℕ) :
    |(cnt x N : ℝ) - x * N| ≤ 2 * blk N := by
  obtain ⟨h1, h2⟩ := blk_spec N
  set K := blk N with hK
  set m := N - tri K with hm
  have hmK : m ≤ K := by rw [tri_succ] at h2; omega
  have hNsplit : N = tri K + m := by omega
  have hcnt : cnt x N = cnt x (tri K) + min m ⌈((K : ℝ) + 1) * x⌉₊ := by
    rw [hNsplit]; exact cnt_block_add x K m (by omega)
  have hNcast : (N : ℝ) = (tri K : ℝ) + (m : ℝ) := by
    rw [hNsplit]; push_cast; ring
  have hmain := cnt_tri_error x hx0 hx1 K
  have hmin1 : (min m ⌈((K : ℝ) + 1) * x⌉₊ : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.cast_le.mpr (min_le_left _ _)
  have hmin0 : (0 : ℝ) ≤ (min m ⌈((K : ℝ) + 1) * x⌉₊ : ℝ) := by positivity
  have hmk : (m : ℝ) ≤ (K : ℝ) := by exact_mod_cast hmK
  have hxm0 : (0 : ℝ) ≤ x * m := by positivity
  have hxm1 : x * (m : ℝ) ≤ (K : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have habs : |(min m ⌈((K : ℝ) + 1) * x⌉₊ : ℝ) - x * m| ≤ (K : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have hsplit : (cnt x N : ℝ) - x * N
      = ((cnt x (tri K) : ℝ) - x * tri K)
        + ((min m ⌈((K : ℝ) + 1) * x⌉₊ : ℝ) - x * m) := by
    rw [hcnt, hNcast]; push_cast; ring
  calc |(cnt x N : ℝ) - x * N|
      ≤ |((cnt x (tri K) : ℝ) - x * tri K)|
          + |((min m ⌈((K : ℝ) + 1) * x⌉₊ : ℝ) - x * m)| := by
        rw [hsplit]; exact abs_add_le _ _
    _ ≤ (K : ℝ) + (K : ℝ) := add_le_add hmain habs
    _ = 2 * K := by ring

