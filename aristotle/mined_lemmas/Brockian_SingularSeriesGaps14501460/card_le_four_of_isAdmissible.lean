/-
# Singular Series Gaps 14501460 — Mathlib formulation

Companion to `RequestProject/SingularSeriesGaps14501460.lean`.  The target theorem there is
stated in plain core Lean (its file has to start with a fixed header comment, which forbids
`import`s).  Here the same mathematical content is formalized in the idiomatic Mathlib way,
with tuples as `Finset ℤ`, primality as `Nat.Prime`, and residues in `ZMod p`.
-/

import Mathlib

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) when, for every prime `p`, the elements of `H` fail to cover
all residue classes modulo `p`.  Equivalently, the singular series attached to `H` is
nonzero. -/

theorem card_le_four_of_isAdmissible (H : Finset ℤ) (hsub : H ⊆ Finset.Icc (1450 : ℤ) 1460)
    (hadm : IsAdmissible H) : H.card ≤ 4 := by
  obtain ⟨r2, h2⟩ := hadm 2 Nat.prime_two
  obtain ⟨r3, h3⟩ := hadm 3 Nat.prime_three
  have key : H ⊆ (Finset.Icc (1450 : ℤ) 1460).filter
      (fun a : ℤ => ((a : ZMod 2) ≠ r2 ∧ (a : ZMod 3) ≠ r3)) := fun a ha =>
    Finset.mem_filter.mpr ⟨hsub ha, h2 a ha, h3 a ha⟩
  refine le_trans (Finset.card_le_card key) ?_
  have huniv : ∀ s2 : ZMod 2, ∀ s3 : ZMod 3, ((Finset.Icc (1450 : ℤ) 1460).filter
      (fun a : ℤ => ((a : ZMod 2) ≠ s2 ∧ (a : ZMod 3) ≠ s3))).card ≤ 4 := by decide
  exact huniv r2 r3

/-- **Singular series gaps 14501460 (Mathlib formulation).**

Inside the window `[1450, 1460]` there is an admissible tuple with four elements, and every
admissible tuple contained in that window has at most four elements; so the largest
admissible tuple in this gap range has exactly four elements. -/
