/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The cap-set bound: subsets of `𝔽₃ⁿ` with no three-term arithmetic progression have size
`o(3ⁿ)`.  This is the Croot–Lev–Pach / Ellenberg–Gijswijt theorem, proved here by the
polynomial method.
-/

open Finset

namespace Math2
namespace CapSet

instance factThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The field `𝔽₃`. -/
abbrev F := ZMod 3

/-- The vector space `𝔽₃ⁿ`. -/
abbrev V (n : ℕ) := Fin n → F

/-- Exponent vectors of reduced monomials: each exponent is `0`, `1` or `2`. -/
abbrev E (n : ℕ) := Fin n → Fin 3

/-- Total degree of a reduced monomial. -/

lemma deg_asub_add {n : ℕ} (a b : E n) (hle : ∀ i, (b i : ℕ) ≤ (a i : ℕ)) :
    deg b + deg (asub a b) = deg a := by
  unfold deg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h : ((asub a b) i : ℕ) = (a i : ℕ) - (b i : ℕ) := rfl
  rw [h]; have := hle i; omega

/-- Expansion of a monomial evaluated at a sum. -/
