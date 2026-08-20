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
