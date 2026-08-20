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

lemma card_M_le_finrank_W (n d : ℕ) : (M n d).card ≤ Module.finrank F (W n d) := by
  have hli : LinearIndependent F (fun a : {a // a ∈ M n d} => mon (a : E n)) :=
    mon_linearIndependent.comp _ Subtype.val_injective
  have hrange : Set.range (fun a : {a // a ∈ M n d} => mon (a : E n))
      = mon '' (M n d : Set (E n)) := by
    ext f; constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, rfl⟩
  have := finrank_span_eq_card hli
  rw [hrange] at this
  rw [W, this, Fintype.card_coe]

end Basic

section CLP

/-- Truncated pointwise subtraction of exponent vectors. -/
