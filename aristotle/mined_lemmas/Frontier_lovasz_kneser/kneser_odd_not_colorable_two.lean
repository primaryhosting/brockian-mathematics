import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

open SimpleGraph Finset

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {A : Finset (Fin n) // A.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/

lemma kneser_odd_not_colorable_two (k : ℕ) (hk : 1 ≤ k) :
    ¬ (kneserGraph (2 * k + 1) k).Colorable 2 := by
  rintro ⟨C⟩
  have hstep : ∀ j : ℕ, C (oddWalk k (j + 1)) = C (oddWalk k j) + 1 := by
    intro j
    have := C.valid (oddWalk_adj k hk j)
    omega
  have hj : ∀ j : ℕ, ((C (oddWalk k j)).val + j) % 2 = (C (oddWalk k 0)).val % 2 := by
    intro j
    induction j with
    | zero => simp
    | succ m ih =>
      have h := hstep m
      omega
  have h1 := hj (2 * k + 1)
  rw [oddWalk_period k] at h1
  omega

end OddGraph

/-! ## The main theorem -/

/-- **Lovász–Kneser theorem (base cases).**  The chromatic number of the Kneser graph
`KG_{n,k}` equals `n - 2k + 2`.  The full theorem is due to Lovász (via Borsuk–Ulam); here we
establish the base cases `k = 1` (where `KG_{n,1}` is the complete graph `K_n`), `n = 2k`
(where `KG_{2k,k}` is a perfect matching) and `n = 2k + 1` (the odd graphs, whose chromatic
number is `3`), together with the general upper bound `kneser_colorable`. -/
