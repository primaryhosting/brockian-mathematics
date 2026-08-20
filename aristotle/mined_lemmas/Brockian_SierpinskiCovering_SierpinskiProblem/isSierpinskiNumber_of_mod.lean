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
import Brockian.SierpinskiCovering

/-!
# Sierpiński numbers: Mathlib-flavoured restatement

`Brockian/SierpinskiCovering.lean` must be import-free (its mandated header comment has to
precede everything, and Lean requires `import` to come first), so it develops the covering
argument using only the core `Nat` API.  Here we restate its conclusions with the usual
Mathlib vocabulary: `Nat.Prime`, `Odd`, and `Set.Infinite`.
-/

namespace Brockian.SierpinskiCovering

/-- A composite number is not prime. -/

theorem isSierpinskiNumber_of_mod {k : Nat} (hodd : k % 2 = 1) (hbig : 73 < k)
    (hk : k % coverModulus = 78557 % coverModulus) : IsSierpinskiNumber k := by
  refine ⟨hodd, by omega, ?_⟩
  intro n hn
  have hc := coverCheck_mod n
  simp only [coverCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨_, _⟩, hp2⟩, hp73⟩, _⟩ := hc
  refine ⟨coverPrime (n % 36), Nat.dvd_of_mod_eq_zero (coverPrime_dvd hk n), by omega, ?_⟩
  have h1 : k * 2 ^ 1 ≤ k * 2 ^ n :=
    Nat.mul_le_mul_left k (Nat.pow_le_pow_right (by decide) hn)
  simp only [Nat.pow_one] at h1
  omega

/-- `78557` is a Sierpiński number. -/
