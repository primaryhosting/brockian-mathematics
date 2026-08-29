import Mathlib
/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

namespace Frontier

variable {n : ℕ}

/-- The Euclidean pairing `⟨c, x⟩ = ∑ⱼ cⱼ xⱼ` on `Fin n → ℝ`. -/

lemma diophantine_one : Diophantine (fun _ : Fin 1 => (1 : ℝ)) 1 0 := by
  intro k hk
  have hk0 : k 0 ≠ 0 := by
    intro h
    exact hk (funext fun j => by fin_cases j; exact h)
  have h1 : (1 : ℝ) ≤ |(k 0 : ℝ)| := by
    have : (1 : ℤ) ≤ |k 0| := Int.one_le_abs (by simpa using hk0)
    exact_mod_cast (by exact_mod_cast this : ((1 : ℤ) : ℝ) ≤ ((|k 0| : ℤ) : ℝ))
  simpa [dotZR, dotRR, l1Norm, Real.rpow_zero] using h1

/-- The hypotheses of `kam_theorem` are satisfiable with a genuinely nonzero perturbation:
for `ε ≠ 0` the invariant torus really is deformed. -/
