import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-! ## Admissible tuples and the Hardy–Littlewood singular series

A finite set `H` of nonnegative integers is *admissible* if for every prime `p` the
elements of `H` do not cover all residue classes modulo `p`.  Equivalently, every local
factor of the Hardy–Littlewood singular series attached to `H` is positive.

The main result `Brockian.SingularSeriesGaps16021610` determines exactly which `d` in the
range `1602 ≤ d ≤ 1610` occur as the diameter of a (large) admissible tuple: precisely the
even ones, and for each of those we exhibit an explicit admissible tuple with at least
`145` elements whose smallest element is `0` and whose largest element is `d`.
-/

/-- `H` is an admissible tuple: for each prime `p` some residue class mod `p` is missed. -/

theorem singularSeriesFactor_pos (H : Finset ℕ) (hH : Admissible H) (p : ℕ) (hp : p.Prime) :
    0 < singularSeriesFactor H p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : 0 < 1 - ((H.image (fun x => x % p)).card : ℝ) / (p : ℝ) := by
    have := card_image_mod_lt H hH p hp
    have : ((H.image (fun x => x % p)).card : ℝ) < (p : ℝ) := by exact_mod_cast this
    rw [sub_pos, div_lt_one hppos]
    exact this
  have h2 : 0 < 1 - 1 / (p : ℝ) := by
    rw [sub_pos, div_lt_one hppos]
    linarith
  exact mul_pos h1 (zpow_pos h2 _)

/-! ### An explicit family of admissible tuples -/

/-- The odd primes below `212`, used as sieving primes. -/
