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

def ColourEstimate (B : ℝ) : Prop :=
  ∀ (k m : ℕ), 2 ≤ k → 2 ≤ m → ∀ (X : Finset α) (S : Finset (Finset α)),
    (∀ A ∈ S, A ⊆ X) → (∀ A ∈ S, A.card = k) →
    IsSpread S k (B * m * Real.log (k + 1)) →
    (B * m * Real.log (k + 1)) ^ k ≤ (S.card : ℝ) →
    ∀ i : Fin m,
      ((colorings X m).filter (fun f => ∃ A ∈ S, A ⊆ colorClass X f i)).card * 2 >
        (colorings X m).card

/-- From the colour estimate, the spread-to-disjoint property for `rho = 2 B p log (k+1)`:
this is the probabilistic part of the Bell–Chueluecha–Warnke argument (partition the ground set
into `2p` colour classes and use linearity of expectation). -/
