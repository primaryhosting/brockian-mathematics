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

lemma Rank1_right {n e : ℕ} {b' : E n} (hb : deg b' ≤ e) (t : F) (b : E n) :
    (fun p : V n × V n => t * (mon b p.1 * mon b' p.2)) ∈ Rank1 n e := by
  classical
  refine ⟨0, fun c'' => if c'' = b' then (fun x => t * mon b x) else 0, fun p => ?_⟩
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single b']
  · simp only [if_true]; ring
  · intro c _ hc; simp [hc]
  · intro hb''; exact absurd ((mem_M_iff b').2 hb) hb''

/-- Shifting: the linear map sending `P` to the two-variable function `(x, y) ↦ P (x + y)`. -/
