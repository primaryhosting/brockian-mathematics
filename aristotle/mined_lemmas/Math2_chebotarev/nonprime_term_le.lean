/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open ArithmeticFunction Complex Filter Topology

/-! ### The analytic input: Λ-weighted density of a residue class -/

/-- The terms of the `L`-series of the von Mangoldt function restricted to a residue class,
evaluated at a real point, are real. -/

theorem nonprime_term_le (q : ℕ) (a : ZMod q) {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) ^ s
      ≤ (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) := by
  have hnum : 0 ≤ (if n.Prime then 0 else vonMangoldt.residueClass a n) := by
    split_ifs
    · exact le_refl 0
    · exact vonMangoldt.residueClass_nonneg a _
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp
    · norm_num [vonMangoldt.residueClass]
  · have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
    have hle : (n : ℝ) ≤ (n : ℝ) ^ s := by
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h2 hs
    exact div_le_div_of_nonneg_left hnum (by linarith) hle

