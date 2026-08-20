import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

open Polynomial IntermediateField

namespace Math2

/-- A complex number is a *rational point* if it lies in the image of `ℚ`. -/

lemma belyiPoly_maps_unit_interval (a b : ℕ) {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ (belyiPoly a b).eval x ∧ (belyiPoly a b).eval x ≤ 1 := by
  have hx1 : (0:ℚ) ≤ 1 - x := by linarith
  have hev : (belyiPoly a b).eval x = belyiConst a b * (x ^ (a+1) * (1-x) ^ (b+1)) := by
    simp [belyiPoly]
  have hcpos : (0:ℚ) < belyiConst a b := belyiConst_pos a b
  refine ⟨by rw [hev]; positivity, ?_⟩
  have hR := amgm_bound (a+1) (b+1) (Nat.succ_pos a) (Nat.succ_pos b) (x:ℝ)
    (by exact_mod_cast h0) (by exact_mod_cast h1)
  push_cast at hR
  have hQ : x ^ (a+1) * (1-x) ^ (b+1) * ((a:ℚ) + b + 2) ^ (a + b + 2) ≤
      ((a:ℚ)+1) ^ (a+1) * ((b:ℚ)+1) ^ (b+1) := by
    have hcast : ((x ^ (a+1) * (1-x) ^ (b+1) * ((a:ℚ) + b + 2) ^ (a + b + 2) : ℚ) : ℝ) ≤
        ((((a:ℚ)+1) ^ (a+1) * ((b:ℚ)+1) ^ (b+1) : ℚ) : ℝ) := by
      push_cast
      calc ((x:ℝ) ^ (a+1) * (1-(x:ℝ)) ^ (b+1) * (((a:ℝ) + b + 2) ^ (a + b + 2)))
          = (x:ℝ) ^ (a+1) * (1-(x:ℝ)) ^ (b+1) * (((a:ℝ)+1) + ((b:ℝ)+1)) ^ ((a+1) + (b+1)) := by
            ring_nf
        _ ≤ ((a:ℝ)+1) ^ (a+1) * ((b:ℝ)+1) ^ (b+1) := hR
    exact_mod_cast hcast
  rw [hev, belyiConst, div_mul_eq_mul_div, div_le_one (by positivity)]
  nlinarith [hQ]


/-! ### Phase 2 : reducing a finite set of rationals to `{0,1}` -/

/-- Every rational number in `(0,1)` is the interior critical point of a Belyi polynomial. -/
