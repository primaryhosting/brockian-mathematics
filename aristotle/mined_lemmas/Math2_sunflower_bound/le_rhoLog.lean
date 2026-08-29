/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of sets is a *sunflower with core `c`* if any two distinct members of `S`
intersect exactly in `c`. -/

lemma le_rhoLog (C : ℝ) (hC : 2 ≤ C) (p k : ℕ) (hk : 1 ≤ k) : (p : ℝ) ≤ rhoLog C p k := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : Real.log 2 ≤ Real.log ((k : ℝ) + 1) := by
    apply Real.log_le_log (by norm_num)
    linarith
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have : (1 : ℝ) ≤ C * Real.log ((k : ℝ) + 1) := by nlinarith
  calc (p : ℝ) = (p : ℝ) * 1 := (mul_one _).symm
    _ ≤ (p : ℝ) * (C * Real.log ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_left this hp0
    _ = rhoLog C p k := by rw [rhoLog]; ring

/-!
### Random colourings

We encode a uniformly random colouring of a finite ground set `X` by `m` colours as a uniformly
random element of the finite set `X.pi (fun _ => univ)` of functions `∀ a ∈ X, Fin m`.
-/

/-- The `i`-th colour class of the colouring `f` of the ground set `X`. -/
