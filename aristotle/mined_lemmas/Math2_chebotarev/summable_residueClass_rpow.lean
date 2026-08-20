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

theorem summable_residueClass_rpow (q : ℕ) (a : ZMod q) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => vonMangoldt.residueClass a n / (n : ℝ) ^ s) := by
  rw [← Complex.summable_ofReal]
  have h : LSeriesSummable (fun n => (vonMangoldt.residueClass a n : ℂ)) (s : ℂ) := by
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
    refine lt_of_le_of_lt (vonMangoldt.abscissaOfAbsConv_residueClass_le_one a) ?_
    simpa using (by exact_mod_cast hs : (1 : EReal) < ((s : ℝ) : EReal))
  exact h.congr fun n => lseriesTerm_residueClass_ofReal q a s n

/-- At a real point, the `L`-series of the von Mangoldt function restricted to a residue class
is the coercion of the corresponding real series. -/
