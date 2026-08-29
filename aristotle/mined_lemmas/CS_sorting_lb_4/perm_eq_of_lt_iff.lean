/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-- A comparison-based sorting algorithm for `n` elements, modelled as a binary
decision tree.  An internal node `node i j l r` compares the inputs at positions
`i` and `j`, descending into `l` if `a i < a j` and into `r` otherwise; a leaf
`leaf p` outputs the permutation `p`. -/
inductive CompTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n
  deriving Inhabited

namespace CompTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed by the algorithm, i.e. the
height of the decision tree. -/

theorem perm_eq_of_lt_iff {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (h : ∀ i j, (τ i < τ j ↔ σ i < σ j)) : τ = σ := by
  let e : Fin n ≃o Fin n :=
    { toEquiv := σ.symm.trans τ
      map_rel_iff' := by
        intro a b
        simp only [Equiv.trans_apply]
        constructor
        · intro hab
          by_contra hlt
          push_neg at hlt
          have := (h (σ.symm b) (σ.symm a)).2 (by simpa using hlt)
          omega
        · intro hab
          rcases eq_or_lt_of_le hab with rfl | hab
          · exact le_refl _
          · exact le_of_lt ((h (σ.symm a) (σ.symm b)).2 (by simpa using hab)) }
  have he : ∀ a, τ (σ.symm a) = a := by
    intro a
    have := DFunLike.congr_fun (Subsingleton.elim e (OrderIso.refl (Fin n))) a
    simpa [e] using this
  exact Equiv.ext fun i => by simpa using he (σ i)

/-- The hypothesis of `CS.sorting_lb_4` is satisfiable: correct comparison sorts
of 4 elements do exist, so the lower bound below is not vacuous. -/
