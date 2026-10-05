/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` only because Lean 4 does not allow a module
-- docstring to precede the `import` commands; the same header is repeated below verbatim.)

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Hückel (tight-binding) Hamiltonian of the cyclic polyene `C₁₈` is, up to the affine
normalisation `H = α + β A`, the adjacency matrix `A` of the cycle graph `C₁₈`.
We prove that a complex number `μ` is an eigenvalue of that adjacency matrix precisely when
`μ = 2 cos (2πk/18)` for some `k ∈ {0, …, 17}`.

The vertex type of `SimpleGraph.cycleGraph 18` is `Fin 18`, which is `ZMod 18`; all index
arithmetic below is therefore modulo `18`.
-/

namespace Chem

open Complex Matrix Finset

/-- A primitive 18-th root of unity. -/

lemma Adj_sum (f : ZMod 18 → ℂ) (j : ZMod 18) :
    ∑ l, Adj j l * f l = f (j - 1) + f (j + 1) := by
  have hset : (Finset.univ.filter (fun l : ZMod 18 => j - l = 1 ∨ l - j = 1)) = {j - 1, j + 1} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · left; linear_combination -h
      · right; linear_combination h
    · rintro (h | h)
      · left; rw [h]; ring
      · right; rw [h]; ring
  have hne : (j - 1) ≠ (j + 1) := by
    intro h
    have h2 : (2 : ZMod 18) = 0 := by linear_combination -h
    revert h2; decide
  calc ∑ l, Adj j l * f l
      = ∑ l ∈ Finset.univ.filter (fun l : ZMod 18 => j - l = 1 ∨ l - j = 1), f l := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl (fun l _ => by rw [Adj_apply]; split <;> simp)
    _ = f (j - 1) + f (j + 1) := by rw [hset, Finset.sum_pair hne]

/-- The diagonalisation identity `A · P = P · D`. -/
