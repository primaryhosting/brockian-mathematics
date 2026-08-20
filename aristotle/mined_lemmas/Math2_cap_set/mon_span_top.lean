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

lemma mon_span_top {n : ℕ} :
    (⊤ : Submodule F (V n → F)) ≤ Submodule.span F (Set.range (mon (n := n))) := by
  rintro f -
  have : f = ∑ c : V n, f c • (fun x => if x = c then (1 : F) else 0) := by
    funext x; simp [Finset.sum_apply, Finset.sum_ite_eq]
  rw [this]
  exact Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ (delta_mem_span c))

