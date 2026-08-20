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

lemma deg_flipE {n : ℕ} (a : E n) : deg (flipE a) + deg a = 2 * n := by
  unfold deg
  rw [← Finset.sum_add_distrib]
  have h : ∀ i : Fin n, ((flipE a) i : ℕ) + (a i : ℕ) = 2 := by
    intro i; have := (a i).isLt
    show 2 - (a i : ℕ) + (a i : ℕ) = 2
    omega
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  simp [mul_comm]

