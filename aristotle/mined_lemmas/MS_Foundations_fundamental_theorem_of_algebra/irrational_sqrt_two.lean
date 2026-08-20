import Mathlib
namespace MS.Foundations


theorem irrational_sqrt_two : Irrational (Real.sqrt 2) := _root_.irrational_sqrt_two

section ExpIrrational

open Nat Finset

/-- The `n`-th partial sum of the exponential series at `1`, i.e. `∑_{m < n+1} 1/m!`. -/
private noncomputable def expPartial (n : ℕ) : ℝ := ∑ m ∈ Finset.range (n + 1), (1 : ℝ) ^ m / m !

/-- `n! * (e - S_{n+1})` is strictly positive, since the exponential series has positive terms. -/
