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

/-- The vertices of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are distinct and disjoint.  (For `k ≥ 1` the
distinctness condition is automatic; it is included only so that the relation is
irreflexive also in the degenerate case `k = 0`.) -/

theorem kneser_chromaticNumber_of_n_eq_two_mul_k (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k) k).chromaticNumber = (2 * k - 2 * k + 2 : ℕ) := by
  classical
  have hupper : (kneserGraph (2 * k) k).chromaticNumber ≤ (2 * k - 2 * k + 2 : ℕ) :=
    (kneser_colorable (2 * k) k hk le_rfl).chromaticNumber_le
  have hkn : k < 2 * k := by omega
  set i : Fin (2 * k) := ⟨k, hkn⟩ with hi
  have hcs : (Finset.Iio i).card = k := by simp [hi]
  have hct : (Finset.Ici i).card = k := by
    rw [Fin.card_Ici]
    show 2 * k - k = k
    omega
  set S : KneserVertex (2 * k) k := ⟨Finset.Iio i, hcs⟩ with hS
  set T : KneserVertex (2 * k) k := ⟨Finset.Ici i, hct⟩ with hT
  have hdisj : Disjoint (Finset.Iio i) (Finset.Ici i) :=
    Finset.disjoint_left.2 fun a ha hb =>
      absurd (Finset.mem_Ici.1 hb) (not_le.2 (Finset.mem_Iio.1 ha))
  have hST : S ≠ T := by
    intro h
    have h1 : (Finset.Iio i) = (Finset.Ici i) := congrArg Subtype.val h
    have h2 : i ∈ Finset.Ici i := Finset.mem_Ici.2 le_rfl
    rw [← h1] at h2
    exact absurd (Finset.mem_Iio.1 h2) (lt_irrefl i)
  have hlower : (2 : ℕ∞) ≤ (kneserGraph (2 * k) k).chromaticNumber :=
    SimpleGraph.two_le_chromaticNumber_of_adj (u := S) (v := T) ⟨hST, hdisj⟩
  have h2 : 2 * k - 2 * k + 2 = 2 := by omega
  rw [h2] at hupper ⊢
  exact le_antisymm hupper (by exact_mod_cast hlower)

/-!
### The odd case `n = 2k + 1`

Here `KG_{2k+1,k}` contains an odd cycle of length `2k+1` (the "cyclic intervals"
`{j, j+1, …, j+k-1}` taken modulo `2k+1`, joined in steps of `k`), so it is not
`2`-colorable and its chromatic number is `3 = (2k+1) - 2k + 2`.
-/

/-- The cyclic interval `{j, j+1, …, j+k-1}` of `Fin (2k+1)`, taken modulo `2k+1`. -/
