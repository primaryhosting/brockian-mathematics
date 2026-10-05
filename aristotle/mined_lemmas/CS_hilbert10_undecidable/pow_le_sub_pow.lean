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
import RequestProject.H10.Factorial

/-!
# The product `∏_{k=1}^{y} (a + b*k)` is Diophantine

This is the last of the classical auxiliary Diophantine functions needed for the
Davis–Putnam–Robinson elimination of bounded universal quantifiers.

The idea is that modulo a large `N` coprime to `b`, one has
`∏_{k=1}^{y} (a + b k) ≡ b^y ∏_{k=1}^{y} (m + k) = b^y y! binom(m+y, y)`
where `m` is the residue `a * b⁻¹ mod N`.
-/

namespace H10

open Nat Finset Dioph

/-- `prodAB a b y = (a + b) * (a + 2b) * ⋯ * (a + y b)`. -/

theorem pow_le_sub_pow (a r : ℕ) : ∀ n : ℕ, r ^ (n + 1) ≤ (r - a) ^ (n + 1) + (n + 1) * a * r ^ n := by
  intro n
  induction n with
  | zero => simp; omega
  | succ n ih =>
    have h1 : r * r ^ (n + 1) ≤ r * ((r - a) ^ (n + 1) + (n + 1) * a * r ^ n) :=
      Nat.mul_le_mul_left _ ih
    have h2 : r * (r - a) ^ (n + 1) ≤ (r - a) ^ (n + 2) + a * r ^ (n + 1) := by
      have hle : r ≤ (r - a) + a := by omega
      calc r * (r - a) ^ (n + 1) ≤ ((r - a) + a) * (r - a) ^ (n + 1) :=
            Nat.mul_le_mul_right _ hle
        _ = (r - a) ^ (n + 2) + a * (r - a) ^ (n + 1) := by ring
        _ ≤ (r - a) ^ (n + 2) + a * r ^ (n + 1) := by
            have : (r - a) ^ (n + 1) ≤ r ^ (n + 1) := Nat.pow_le_pow_left (by omega) _
            exact Nat.add_le_add_left (Nat.mul_le_mul_left _ this) _
    calc r ^ (n + 2) = r * r ^ (n + 1) := by ring
      _ ≤ r * ((r - a) ^ (n + 1) + (n + 1) * a * r ^ n) := h1
      _ = r * (r - a) ^ (n + 1) + (n + 1) * a * (r * r ^ n) := by ring
      _ ≤ ((r - a) ^ (n + 2) + a * r ^ (n + 1)) + (n + 1) * a * r ^ (n + 1) := by
          have h3 : r * r ^ n = r ^ (n + 1) := by ring
          rw [h3]; exact Nat.add_le_add_right h2 _
      _ = (r - a) ^ (n + 2) + (n + 2) * a * r ^ (n + 1) := by ring

/-- For `r` large, `n ! = ⌊r ^ n / C(r, n)⌋`. -/
