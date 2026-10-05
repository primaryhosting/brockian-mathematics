import Mathlib
/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## The cap set problem

We prove the Croot–Lev–Pach / Ellenberg–Gijswijt bound: a subset of `𝔽₃ⁿ` containing no
non-trivial three-term arithmetic progression has size `o(3ⁿ)`.
-/

namespace CapSet

open Finset

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Points of `𝔽₃ⁿ`. -/
abbrev Pt (n : ℕ) := Fin n → ZMod 3

/-- Exponent vectors of reduced monomials (each exponent is `0`, `1` or `2`). -/
abbrev Exp (n : ℕ) := Fin n → Fin 3

/-- The monomial function `x ↦ ∏ i, x i ^ α i` on `𝔽₃ⁿ`. -/

lemma mono_add_expand {n : ℕ} (α : Exp n) (x y : Pt n) :
    mono α (x + y) = ∑ β : Exp n, ∑ γ : Exp n, KK α β γ * mono β x * mono γ y := by
  have step1 : mono α (x + y)
      = ∏ i, ∑ p : Fin 3 × Fin 3, kk (α i) p.1 p.2 * x i ^ (p.1 : ℕ) * y i ^ (p.2 : ℕ) := by
    simp only [mono, Pi.add_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [kk_expand (α i) (x i) (y i), Fintype.sum_prod_type]
  have step2 : ∑ β : Exp n, ∑ γ : Exp n, KK α β γ * mono β x * mono γ y
      = ∑ q : Exp n × Exp n, KK α q.1 q.2 * mono q.1 x * mono q.2 y := by
    rw [Fintype.sum_prod_type]
  rw [step1, step2, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Fintype.sum_equiv
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin 3) (fun _ => Fin 3)) _ _ ?_
  intro P
  simp only [Equiv.arrowProdEquivProdArrow_apply, KK, mono]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-! ### The splitting lemma -/

/-- If `P` has degree at most `d ≤ 2e+1`, then `P (x + y)` splits into a part where the
`x`-monomials have degree at most `e` and a part where the `y`-monomials do. -/
