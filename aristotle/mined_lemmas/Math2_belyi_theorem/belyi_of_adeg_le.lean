import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial
open scoped IntermediateField

namespace Math2

/-- A *Belyi map* (in the genus-zero, polynomial model): a nonconstant polynomial with
rational coefficients, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`.  Being a polynomial, such a map is totally
ramified over `∞`, so it is ramified only above `{0, 1, ∞}`. -/

theorem belyi_of_adeg_le : ∀ (d : ℕ) (S : Finset ℂ), (∀ s ∈ S, IsAlgebraic ℚ s) →
    (∀ s ∈ S, adeg s ≤ d) → BelyiFor (S : Set ℂ) := by
  intro d
  induction d with
  | zero =>
    intro S halg hdeg
    exact belyi_deg_le_one S halg fun s hs => le_trans (hdeg s hs) (by omega)
  | succ d ihd =>
    intro S halg hdeg
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact belyi_deg_le_one S halg hdeg
    · exact belyi_descent_step d ihd hd (S.filter (fun s => adeg s = d + 1)).card S halg hdeg
        le_rfl

/-- **Belyi's theorem** (the hard direction), in the genus-zero model: any finite set of
algebraic numbers can be sent into `{0, 1, ∞}` by a Belyi map. -/
