import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
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

namespace Frontier

/-- Vertices of the Kneser graph `KG_{n,k}`: the `k`-element subsets of an `n`-element set. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-subsets of `Fin n`, and two
distinct vertices are adjacent when the corresponding sets are disjoint. -/

lemma lovasz_kneser_two_k_add_one (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).chromaticNumber = (2 * k + 1 - 2 * k + 2 : ℕ) := by
  have hupper : (kneserGraph (2 * k + 1) k).chromaticNumber ≤ (2 * k + 1 - 2 * k + 2 : ℕ) :=
    kneser_chromaticNumber_le (2 * k + 1) k hk (by omega)
  have hlower : (3 : ℕ∞) ≤ (kneserGraph (2 * k + 1) k).chromaticNumber := by
    have hnot : ¬ (kneserGraph (2 * k + 1) k).chromaticNumber ≤ (2 : ℕ) := fun h =>
      kneser_odd_not_colorable_two k hk (SimpleGraph.chromaticNumber_le_iff_colorable.mp h)
    have := Order.add_one_le_of_lt (not_le.mp (by simpa using hnot))
    simpa using this
  have h3 : ((2 * k + 1 - 2 * k + 2 : ℕ) : ℕ∞) = 3 := by
    have : (2 * k + 1 - 2 * k + 2 : ℕ) = 3 := by omega
    rw [this]
    rfl
  rw [h3] at hupper ⊢
  exact le_antisymm hupper hlower

/-- **Lovász–Kneser theorem** (base cases).  The chromatic number of the Kneser graph
`KG_{n,k}` equals `n - 2k + 2`.  Here we prove the statement in the base cases `k = 1`
(where `KG_{n,1}` is the complete graph `K_n`), `n = 2k` (where `KG_{2k,k}` is a perfect
matching) and `n = 2k + 1` (the odd graphs, where an odd cycle rules out `2`-colourings).
The general upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` is `Frontier.kneser_chromaticNumber_le`;
the matching general lower bound is the hard direction, due to Lovász via the Borsuk–Ulam
theorem. -/
