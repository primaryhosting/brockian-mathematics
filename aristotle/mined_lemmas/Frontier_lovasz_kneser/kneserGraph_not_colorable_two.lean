/-
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of an
`n`-element set. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/

lemma kneserGraph_not_colorable_two (k : ℕ) (hk : 1 ≤ k) :
    ¬ (kneserGraph (2 * k + 1) k).Colorable 2 := by
  rintro ⟨C⟩
  have hadj : ∀ i : ℕ, C (cycVertex k (i + k)) ≠ C (cycVertex k i) := by
    intro i
    refine C.valid ⟨?_, disjoint_cycBlock k i⟩
    intro h
    exact cycBlock_ne k i hk (congrArg Subtype.val h)
  have key : ∀ a b : Fin 2, a ≠ b → a = b + 1 := by decide
  have key2 : ∀ a : Fin 2, a + 1 + 1 = a := by decide
  have key3 : ∀ a : Fin 2, a ≠ a + 1 := by decide
  have hstep : ∀ m : ℕ, C (cycVertex k ((m + 1) * k)) = C (cycVertex k (m * k)) + 1 := by
    intro m
    refine key _ _ ?_
    have h1 : (m + 1) * k = m * k + k := by ring
    rw [h1]
    exact hadj (m * k)
  have hpar : ∀ m : ℕ, C (cycVertex k (m * k))
      = if m % 2 = 0 then C (cycVertex k 0) else C (cycVertex k 0) + 1 := by
    intro m
    induction m with
    | zero => simp
    | succ p ih =>
      rw [hstep p, ih]
      by_cases hp : p % 2 = 0
      · rw [if_pos hp, if_neg (by omega)]
      · rw [if_neg hp, if_pos (by omega), key2]
  have hfin := hpar (2 * k + 1)
  rw [if_neg (by omega)] at hfin
  have hveq : cycVertex k ((2 * k + 1) * k) = cycVertex k 0 :=
    Subtype.ext (cycBlock_period k)
  rw [hveq] at hfin
  exact key3 _ hfin

/-! ### Main theorem -/

/-- If `G` is `(m+1)`-colourable but not `m`-colourable, its chromatic number is `m + 1`. -/
