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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are disjoint. -/

theorem kneser_chromaticNumber_two_mul_add_one (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).chromaticNumber = 3 := by
  have hupper : (kneserGraph (2 * k + 1) k).Colorable 3 := by
    have := kneser_colorable (2 * k + 1) k hk (by omega)
    have heq : 2 * k + 1 - 2 * k + 2 = 3 := by omega
    rwa [heq] at this
  have hle : (kneserGraph (2 * k + 1) k).chromaticNumber ≤ 3 := by
    exact_mod_cast SimpleGraph.chromaticNumber_le_iff_colorable.mpr hupper
  have hnot : ¬ ((kneserGraph (2 * k + 1) k).chromaticNumber ≤ 2) := by
    intro hcon
    exact kneser_not_colorable_two k hk
      (SimpleGraph.chromaticNumber_le_iff_colorable.mp (by exact_mod_cast hcon))
  have hge : (3 : ℕ∞) ≤ (kneserGraph (2 * k + 1) k).chromaticNumber := by
    have h2 : (2 : ℕ∞) < (kneserGraph (2 * k + 1) k).chromaticNumber := not_le.mp hnot
    have := Order.add_one_le_of_lt h2
    norm_num at this
    exact this
  exact le_antisymm hle hge

/-- **Lovász–Kneser theorem**, base cases.
The chromatic number of the Kneser graph `KG_{n,k}` equals `n - 2k + 2`,
proved here in the base cases `k = 1` (the complete graph `K_n`), `n = 2k`
(a perfect matching) and `n = 2k + 1` (the odd graphs). -/
