import Mathlib

/-!
# Arrhenius Monotone
Category: Chemistry
Target: Chem.arrhenius_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The Arrhenius rate constant `k(T) = A * exp (-Ea / (R * T))`. -/

lemma arrhenius_exponent_lt {Ea R T₁ T₂ : ℝ} (hEa : 0 < Ea) (hR : 0 < R)
    (hT₁ : 0 < T₁) (hlt : T₁ < T₂) :
    -Ea / (R * T₁) < -Ea / (R * T₂) := by
  have h1 : 0 < R * T₁ := mul_pos hR hT₁
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_left hEa h1 (by nlinarith)

/-- **Arrhenius law is strictly increasing in temperature.**
For a positive pre-exponential factor `A`, positive activation energy `Ea` and positive
gas constant `R`, the rate `k(T) = A e^{-Ea/(R T)}` is strictly increasing on `T > 0`. -/
