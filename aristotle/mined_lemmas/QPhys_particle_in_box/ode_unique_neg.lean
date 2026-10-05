import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well of width `L`:
`Eₙ = n²π²ℏ²/(2mL²)`. -/

lemma ode_unique_neg {k : ℝ} (hk : k ≠ 0) {g g' g'' : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (heq : ∀ x, g'' x = -k ^ 2 * g x) (hg0 : g 0 = 0) (hg'0 : g' 0 = 0) :
    ∀ x, g x = 0 := by
  have hW : ∀ x, HasDerivAt (fun y => g' y ^ 2 + k ^ 2 * g y ^ 2) 0 x := by
    intro x
    have hA : HasDerivAt (fun y => g' y ^ 2) (2 * g' x * g'' x) x := by
      have h := (h2 x).pow 2
      convert h using 1
      push_cast; ring
    have hB : HasDerivAt (fun y => k ^ 2 * g y ^ 2) (k ^ 2 * (2 * g x * g' x)) x := by
      have h := ((h1 x).pow 2).const_mul (k ^ 2)
      convert h using 1
      push_cast; ring
    have h3 := hA.add hB
    have hE : 2 * g' x * g'' x + k ^ 2 * (2 * g x * g' x) = 0 := by
      rw [heq x]; ring
    rw [hE] at h3
    exact h3
  intro x
  have h := const_of_hasDerivAt_zero hW x
  rw [hg0, hg'0] at h
  simp at h
  have hk2 : 0 < k ^ 2 := by positivity
  have hg2 : g x ^ 2 = 0 := by nlinarith [sq_nonneg (g' x), sq_nonneg (g x)]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hg2

/-- Solutions of `ψ'' = -k²ψ` (`k ≠ 0`) vanishing at `0` are multiples of `sin (k x)`. -/
