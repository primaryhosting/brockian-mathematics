import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header block is required to be the first content of the file; Lean 4 requires
`import` statements to precede every other command, including module docstrings, so the
single `import Mathlib` line above is the only thing preceding it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Phys

/-! ## Shannon entropy of a finite spectrum -/

/-- Shannon (von Neumann) entropy of a finite family of probabilities. -/

lemma expSchmidtDecay_of_fintype {N d : ℕ} (psi : Config N d → ℂ) (L : ℕ)
    (hnorm : ∑ x, ‖psi x‖ ^ 2 = 1) {c : ℝ} (hc : 0 < c) :
    ExpSchmidtDecay psi L (Real.exp (c * (Fintype.card (LeftConfig N d L) : ℝ))) c := by
  classical
  refine ⟨fun a => ((Fintype.equivFin (LeftConfig N d L)) a : ℕ), ?_, ?_⟩
  · intro a a' h
    exact (Fintype.equivFin (LeftConfig N d L)).injective (Fin.ext h)
  · intro a
    have hle1 : cutSpectrum psi L a ≤ 1 := by
      rw [← sum_cutSpectrum psi L hnorm]
      exact Finset.single_le_sum (f := cutSpectrum psi L)
        (fun i _ => schmidtSpectrum_nonneg _ i) (Finset.mem_univ a)
    have hrank : (((Fintype.equivFin (LeftConfig N d L)) a : ℕ) : ℝ)
        ≤ (Fintype.card (LeftConfig N d L) : ℝ) := by
      exact_mod_cast ((Fintype.equivFin (LeftConfig N d L)) a).isLt.le
    have : (1 : ℝ) ≤ Real.exp (c * (Fintype.card (LeftConfig N d L) : ℝ))
        * Real.exp (-(c * (((Fintype.equivFin (LeftConfig N d L)) a : ℕ) : ℝ))) := by
      rw [← Real.exp_add]
      rw [Real.one_le_exp_iff]
      nlinarith
    linarith

/-- **Area law for gapped ground states in one dimension.**

For a normalized state `psi` of a one-dimensional chain of `N` sites with local
dimension `d`, whose Schmidt spectrum across the cut at position `L` decays
exponentially with constants `C, c` (the property produced by a spectral gap in
Hastings' theorem), the entanglement entropy across the cut is bounded by
`areaLawBound C c`.

The bound depends only on `C` and `c`; it is independent of the chain length `N`,
the local dimension `d` and, crucially, of the size `L` of the block.  This is exactly
the one-dimensional area law: entropy of a block is bounded by a constant, rather than
growing with the block's volume. -/
