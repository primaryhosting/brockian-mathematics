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

theorem sunflower_bound_greedy (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) (F : Finset (Finset α))
    (hF : ∀ A ∈ F, A.card = k) (hcard : ((p : ℝ) * k) ^ k ≤ (F.card : ℝ)) :
    HasSunflower F p := by
  refine sunflower_of_spreadDisjoint (rho := fun p k => (p : ℝ) * k) ?_ ?_ spreadDisjoint_mul
    k p hp hk F hF hcard
  · intro p k k' hp hk' hkk'
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have : (k' : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkk'
    exact mul_le_mul_of_nonneg_left this hp0
  · intro p k hp hk
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith

/-- The threshold function of the improved sunflower bound: `rhoLog C p k = C * p * log (k+1)`.
(The shift by one only serves to make the function positive at `k = 1`; for `k ≥ 2` we have
`log (k+1) ≤ 2 * log k`, so this is the same bound up to the value of the constant.) -/
