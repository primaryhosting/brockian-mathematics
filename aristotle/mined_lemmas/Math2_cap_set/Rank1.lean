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

def Rank1 (n e : ℕ) : Submodule F (V n × V n → F) where
  carrier := {h | ∃ w w' : E n → V n → F, ∀ p : V n × V n,
      h p = (∑ b ∈ M n e, mon b p.1 * w b p.2) + (∑ c ∈ M n e, w' c p.1 * mon c p.2)}
  add_mem' := by
    rintro h1 h2 ⟨w1, w1', e1⟩ ⟨w2, w2', e2⟩
    exact ⟨fun b y => w1 b y + w2 b y, fun c x => w1' c x + w2' c x, fun p => by
      rw [Pi.add_apply, e1, e2]; simp only [mul_add, add_mul, Finset.sum_add_distrib]; ring⟩
  zero_mem' := ⟨0, 0, fun p => by simp⟩
  smul_mem' := by
    rintro t h ⟨w, w', hw⟩
    refine ⟨fun b y => t * w b y, fun c x => t * w' c x, fun p => ?_⟩
    rw [Pi.smul_apply, hw, smul_eq_mul]
    simp only [mul_add, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun i _ => by ring)

