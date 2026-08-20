import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

def MODfun (p : ℕ) : ∀ n : ℕ, Cube n → Bool := fun _ x => decide (p ∣ ones x)

end CS

/-
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Approx
import RequestProject.Counting
import RequestProject.Binom
import RequestProject.Aux

/-!
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

