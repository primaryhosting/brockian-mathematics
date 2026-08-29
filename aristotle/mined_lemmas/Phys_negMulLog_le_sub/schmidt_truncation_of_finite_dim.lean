import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` to be the very first command of a module, so the
requested header block appears immediately after the single `import Mathlib` line.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace Phys

/-! ## Elementary entropy inequalities -/

/-- Gibbs-type pointwise bound: for `x ≥ 0` and a reference weight `r > 0`,
`-x log x ≤ (r - x) - x log r`. -/

theorem schmidt_truncation_of_finite_dim (psi : Matrix A B ℂ) (hnorm : (psi * psiᴴ).trace = 1)
    (k : ℕ) :
    ∃ s : Finset A, s.card ≤ k ∧
      ∑ i ∈ sᶜ, schmidtSpectrum psi i ≤ ((Fintype.card A : ℝ) + 1) / ((k : ℝ) + 1) := by
  classical
  by_cases h : Fintype.card A ≤ k
  · refine ⟨Finset.univ, by simpa using h, ?_⟩
    simp only [Finset.compl_univ, Finset.sum_empty]
    positivity
  · refine ⟨∅, by simp, ?_⟩
    rw [Finset.compl_empty, sum_schmidtSpectrum psi hnorm]
    push_neg at h
    have hk : ((k : ℝ) + 1) ≤ (Fintype.card A : ℝ) + 1 := by
      have : (k : ℝ) ≤ (Fintype.card A : ℝ) := by exact_mod_cast h.le
      linarith
    rw [le_div_iff₀ (by positivity)]
    linarith

end Bipartite

/-! ## The one-dimensional area law -/

/--
**Area law for gapped one-dimensional systems (Hastings).**

Setting: a spin chain of `n` sites with local Hilbert space dimension `d`, cut into the left
block (sites `0, …, m-1`) and the right block (the remaining `n - m` sites).  A pure state of
the chain is a matrix `psi` indexed by the configurations of the two blocks, normalized by
`tr (psi psiᴴ) = 1`; its entanglement entropy across the cut is the von Neumann entropy of the
reduced density matrix `psi psiᴴ`.

Hypothesis (the gap input): for the ground state of a gapped local one-dimensional Hamiltonian,
truncating the Schmidt decomposition across any cut to `k` terms leaves a discarded weight that
tends to `0` at a rate `C/(k+1)` with a constant `C` fixed by the gap and the local dimension,
uniformly in the system size.  This is the analytic content supplied by Hastings' theorem and by
the approximate-ground-state-projector construction of Arad–Kitaev–Landau–Vazirani (which in
fact yields a faster, polynomially decaying truncation error); it is hypothesis `hdecay` below.

Conclusion (the area law): there is a single constant `K`, depending only on `C` and **not** on
the chain length `n`, the position `m` of the cut, or the total Hilbert space dimension, that
bounds the entanglement entropy across every cut of every such chain.  In one dimension the
boundary of a cut is a single point, so a size-independent constant bound is exactly the
statement of the area law.
-/
