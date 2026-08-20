/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

open Finset Matrix

/-- `zeta a = exp (2πi a / 12)`, the `a`-th power of a primitive 12th root of unity. -/

lemma zeta_eq_one_iff {d : ℤ} : zeta d = 1 ↔ d % 12 = 0 := by
  rw [zeta, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hd : d = 12 * n := by
      field_simp at hn
      exact_mod_cast hn
    omega
  · intro hd
    refine ⟨d / 12, ?_⟩
    have hdd : d = 12 * (d / 12) := by omega
    have hc : ((d : ℂ)) = 12 * ((d / 12 : ℤ) : ℂ) := by
      exact_mod_cast congrArg (fun x : ℤ => (x : ℂ)) hdd
    rw [hc]
    ring

/-- `2 cos (2πm/12)` written in terms of roots of unity. -/
