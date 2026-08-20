import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
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

namespace Chem

open scoped Matrix

/-! ### A primitive 14-th root of unity and the associated character -/

/-- A primitive 14-th root of unity. -/

theorem ee_add_ee_neg (k : Fin 14) :
    ee ((k : ℕ) : ℤ) + ee (-((k : ℕ) : ℤ)) = (lam k : ℂ) := by
  set θ : ℝ := 2 * Real.pi * ((k : ℕ) : ℝ) / 14 with hdef
  have h1 : ee ((k : ℕ) : ℤ) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [ee_eq_exp]
    norm_num [hdef]
  have h2 : ee (-((k : ℕ) : ℤ)) = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [ee_eq_exp]
    congr 1
    push_cast [hdef]
    ring
  rw [h1, h2, lam, ← hdef, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos,
    Complex.cos, ← neg_mul]
  ring

/-! ### Diagonalisation -/

/-- The (unnormalised) discrete Fourier transform matrix. -/
