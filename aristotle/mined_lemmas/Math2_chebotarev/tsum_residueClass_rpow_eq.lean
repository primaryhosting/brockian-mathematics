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

theorem tsum_residueClass_rpow_eq (q : ℕ) [NeZero q] {a : ZMod q} (ha : IsUnit a) (s : ℝ)
    (hs : 1 < s) :
    (∑' n : ℕ, vonMangoldt.residueClass a n / (n : ℝ) ^ s)
      = (vonMangoldt.LFunctionResidueClassAux a (s : ℂ)).re + (q.totient : ℝ)⁻¹ / (s - 1) := by
  have h := vonMangoldt.eqOn_LFunctionResidueClassAux ha
    (show (s : ℂ) ∈ {s : ℂ | 1 < s.re} by simpa using hs)
  simp only [lseries_residueClass_ofReal] at h
  have h2 : ((((∑' n : ℕ, vonMangoldt.residueClass a n / (n : ℝ) ^ s : ℝ)) : ℂ)
      - ((q.totient : ℂ))⁻¹ / ((s : ℂ) - 1)).re
      = (∑' n : ℕ, vonMangoldt.residueClass a n / (n : ℝ) ^ s) - (q.totient : ℝ)⁻¹ / (s - 1) := by
    rw [show ((q.totient : ℂ))⁻¹ / ((s : ℂ) - 1) = (((q.totient : ℝ)⁻¹ / (s - 1) : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_sub, Complex.ofReal_re]
  rw [h, h2]; ring

/-- The auxiliary function is continuous at `s = 1` along the reals from the right. -/
