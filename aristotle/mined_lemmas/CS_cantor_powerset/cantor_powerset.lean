/-
# Cantor Powerset
Category: Computer Science
Target: CS.cantor_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Cantor Powerset
Category: Computer Science
Target: CS.cantor_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- **Cantor's theorem**: for any type `A`, no function `f : A → Set A` is surjective,
i.e. there is no surjection from `A` onto its powerset `𝒫(A)`.
This is exactly Mathlib's `Function.cantor_surjective`. -/

theorem cantor_powerset {A : Type*} (f : A → Set A) : ¬ Function.Surjective f :=
  Function.cantor_surjective f

/-- Restatement: there does not exist a surjection from `A` onto `Set A`. -/
