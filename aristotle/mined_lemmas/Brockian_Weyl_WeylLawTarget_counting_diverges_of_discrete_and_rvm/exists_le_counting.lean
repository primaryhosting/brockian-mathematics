import Mathlib

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

/-
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Weyl-law style statement proved here: for a linear operator `T` on an infinite
dimensional real vector space (in particular on a real inner product space) whose spectrum is
*discrete* — every spectral subspace below a level is finite dimensional — and whose
eigensystem is *complete*, as furnished by the Rayleigh variational method (RVM), the
eigenvalue counting function `lam ↦ dim (span of eigenvectors with eigenvalue ≤ lam)`
diverges to `+∞`.

The final section exhibits an explicit model (the diagonal operator `f ↦ (n ↦ n * f n)` on
finitely supported real sequences) satisfying all the hypotheses, so the theorem is not
vacuous.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

section General

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- The low-lying spectral subspace: the span of all eigenvectors of `T` whose
eigenvalue is at most `lam`. -/

theorem exists_le_counting (T : Module.End ℝ H) (hinf : ¬ FiniteDimensional ℝ H)
    (hdisc : HasDiscreteSpectrum T) (hrvm : RVMComplete T) (k : ℕ) :
    ∃ lam : ℝ, k ≤ counting T lam := by
  -- Pick `k` linearly independent vectors; possible since `H` is infinite dimensional.
  have hrank : (k : Cardinal) ≤ Module.rank ℝ H := by
    have hlt : ¬ Module.rank ℝ H < Cardinal.aleph0 := by
      rw [Module.rank_lt_aleph0_iff]
      exact fun h => hinf h
    exact (Cardinal.natCast_lt_aleph0 (n := k)).le.trans (not_lt.mp hlt)
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank (R := ℝ) (M := H) (n := k) hrank
  -- Each of them lies in the span of finitely many eigenspaces.
  have hmem : ∀ i : Fin k, ∃ s : Finset ℝ, v i ∈ ⨆ c ∈ s, T.eigenspace c := by
    intro i
    have hmem' : v i ∈ ⨆ c : ℝ, T.eigenspace c := by rw [hrvm]; trivial
    exact Submodule.mem_iSup_iff_exists_finset.mp hmem'
  choose s hs using hmem
  -- Take a level above all the finitely many eigenvalues involved.
  obtain ⟨lam, hlam⟩ := (Finset.univ.biUnion s).exists_le
  refine ⟨lam, ?_⟩
  have hspan : Submodule.span ℝ (Set.range v) ≤ lowSpectrumSpan T lam := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hle : (⨆ c ∈ s i, T.eigenspace c) ≤ lowSpectrumSpan T lam :=
      iSup_le fun c => iSup_le fun (hc : c ∈ s i) =>
        le_iSup₂ (f := fun c (_ : c ≤ lam) => T.eigenspace c) c
          (hlam c (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hc⟩))
    exact hle (hs i)
  have hcard : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = k := by
    simpa using finrank_span_eq_card hv
  have : FiniteDimensional ℝ (lowSpectrumSpan T lam) := hdisc lam
  calc k = Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := hcard.symm
    _ ≤ counting T lam := Submodule.finrank_mono hspan

/-- **Weyl law: divergence of the eigenvalue counting function.**
If a linear operator `T` on an infinite dimensional real vector space (for instance a real
inner product space) has a discrete spectrum — every spectral subspace below a level is
finite dimensional — and a complete eigensystem, as furnished by the Rayleigh variational
method, then its eigenvalue counting function diverges to infinity. -/
