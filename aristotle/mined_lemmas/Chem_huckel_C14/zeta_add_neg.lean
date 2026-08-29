import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph Matrix

namespace Chem

/-! ### Arithmetic in `Fin 14`

`Fin 14` carries the modular `+`, `-`, `*` and `-·` operations used by
`SimpleGraph.cycleGraph_adj`, but no `CommRing` instance is available for the numeral `14`,
so the handful of ring identities we need are checked by decision procedure. -/

section Fin14


lemma zeta_add_neg (k : Fin 14) : zeta k + zeta (-k) = lam k := by
  set x : ℝ := 2 * Real.pi * (k : ℕ) / 14 with hx
  have hzk : zeta k = Complex.exp ((x : ℂ) * Complex.I) := by
    rw [zeta, w, ← Complex.exp_nat_mul]
    congr 1
    push_cast [hx]
    ring
  have hprod : zeta (-k) * zeta k = 1 := by
    rw [← zeta_add, fin14_neg_add, zeta_zero]
  have hzmk : zeta (-k) = Complex.exp (-(x : ℂ) * Complex.I) := by
    have h1 : Complex.exp (-(x : ℂ) * Complex.I) * Complex.exp ((x : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      simp
    have hne : Complex.exp ((x : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    rw [hzk] at hprod
    exact mul_right_cancel₀ hne (hprod.trans h1.symm)
  rw [hzk, hzmk, ← Complex.two_cos, lam, Complex.ofReal_cos]

