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
import Brockian.RieselCovering

/-!
# Riesel problem, Mathlib-facing statement

`Brockian.RieselCovering` must begin with a mandated header comment, which forces it to be
import-free (Lean requires `import`s to come first in a file).  This module imports Mathlib and
restates the main result using Mathlib's `Nat.Prime`.
-/

namespace Brockian
namespace RieselCovering


theorem RieselProblem : ∀ n : Nat, 1 ≤ n → ¬ IsPrimeNat (509203 * 2 ^ n - 1) := by
  intro n hn hprime
  have h2 : (2 : Nat) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hbig : 241 < 509203 * 2 ^ n - 1 := by simp only [Nat.pow_one] at h2; omega
  have step : ∀ p r : Nat, 1 < p → p ≤ 241 → p ∣ 16777215 →
      p ∣ 509203 * 2 ^ r - 1 → n = 24 * (n / 24) + r → False := by
    intro p r hp1 hple hp24 hr hnr
    have hd : p ∣ 509203 * 2 ^ n - 1 := by
      rw [hnr]; exact cover_dvd p r hp24 hr (n / 24)
    rcases hprime.2 p hd with h | h <;> omega
  have hcase : n % 24 = 0 ∨ n % 24 = 1 ∨ n % 24 = 2 ∨ n % 24 = 3 ∨ n % 24 = 4 ∨
      n % 24 = 5 ∨ n % 24 = 6 ∨ n % 24 = 7 ∨ n % 24 = 8 ∨ n % 24 = 9 ∨ n % 24 = 10 ∨
      n % 24 = 11 ∨ n % 24 = 12 ∨ n % 24 = 13 ∨ n % 24 = 14 ∨ n % 24 = 15 ∨ n % 24 = 16 ∨
      n % 24 = 17 ∨ n % 24 = 18 ∨ n % 24 = 19 ∨ n % 24 = 20 ∨ n % 24 = 21 ∨ n % 24 = 22 ∨
      n % 24 = 23 := by omega
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h
  · exact step 3 0 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 5 1 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 2 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 241 3 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 4 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 5 5 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 6 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 13 7 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 8 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 5 9 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 10 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 7 11 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 12 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 5 13 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 14 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 17 15 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 16 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 5 17 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 18 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 13 19 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 20 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 5 21 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 22 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 7 23 (by omega) (by omega) (by decide) (by decide) (by omega)

/-- `509203` is a Riesel number. -/
