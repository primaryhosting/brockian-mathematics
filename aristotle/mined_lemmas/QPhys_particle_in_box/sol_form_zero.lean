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

lemma sol_form_zero {f f' f'' : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt f (f' x) x) (h2 : ∀ x, HasDerivAt f' (f'' x) x)
    (heq : ∀ x, f'' x = 0) (hf0 : f 0 = 0) :
    ∀ x, f x = f' 0 * x := by
  set B := f' 0 with hB
  set g : ℝ → ℝ := fun x => f x - B * x with hg
  set g' : ℝ → ℝ := fun x => f' x - B with hg'
  have hd1 : ∀ x, HasDerivAt g (g' x) x := fun x => (h1 x).sub (hasDerivAt_lin B x)
  have hd2 : ∀ x, HasDerivAt g' (f'' x) x := fun x => (h2 x).sub_const B
  have hgeq : ∀ x, f'' x = (0 : ℝ) ^ 2 * g x := by intro x; rw [heq x]; ring
  have hg0 : g 0 = 0 := by simp [hg, hf0]
  have hg'0 : g' 0 = 0 := by simp [hg', hB]
  have hz := ode_unique_nonneg hd1 hd2 hgeq hg0 hg'0
  intro x
  have hx := hz x
  simp only [hg] at hx
  linarith

end Helpers

section Eigenstates

variable {hbar m L : ℝ} {n : ℕ}

/-- The stationary states solve the time-independent Schrödinger equation with energy `Eₙ`. -/
