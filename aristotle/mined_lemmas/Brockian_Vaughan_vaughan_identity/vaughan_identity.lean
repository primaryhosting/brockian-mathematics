/-
# Vaughan Identity
Category: B Brockian Frontier
Target: Brockian.Vaughan.vaughan_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Vaughan Identity
Category: B Brockian Frontier
Target: Brockian.Vaughan.vaughan_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

namespace Brockian
namespace Vaughan

open ArithmeticFunction

/-- The truncation of an arithmetic function to arguments `≤ U`. -/

theorem vaughan_identity (U V : ℕ) :
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      truncLE V ArithmeticFunction.vonMangoldt
        + truncLE U ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
            ArithmeticFunction ℝ) * ArithmeticFunction.log
        - truncLE U ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
              ArithmeticFunction ℝ) * truncLE V ArithmeticFunction.vonMangoldt
            * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
        + truncGT U ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
              ArithmeticFunction ℝ) * truncGT V ArithmeticFunction.vonMangoldt
            * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) := by
  set A := truncLE U ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
    ArithmeticFunction ℝ) with hA
  set B := truncGT U ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
    ArithmeticFunction ℝ) with hB
  set C := truncLE V (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) with hC
  set D := truncGT V (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) with hD
  set Z := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) with hZ
  have e1 : ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
      * ArithmeticFunction.log = ArithmeticFunction.vonMangoldt :=
    ArithmeticFunction.moebius_mul_log_eq_vonMangoldt
  have e2 : A + B = ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
      ArithmeticFunction ℝ) := truncLE_add_truncGT _ _
  have e3 : C + D = (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) :=
    truncLE_add_truncGT _ _
  have e4 : ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) * Z = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  have e5 : (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) * Z =
      ArithmeticFunction.log := ArithmeticFunction.vonMangoldt_mul_zeta
  linear_combination (-1 : ArithmeticFunction ℝ) * e1
    + (C * Z - ArithmeticFunction.log) * e2 + (-(B * Z)) * e3 + C * e4 + (-B) * e5

end Vaughan
end Brockian

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

