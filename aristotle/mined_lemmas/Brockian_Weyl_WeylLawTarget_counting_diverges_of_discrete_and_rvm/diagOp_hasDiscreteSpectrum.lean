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

theorem diagOp_hasDiscreteSpectrum : HasDiscreteSpectrum diagOp := by
  intro lam
  classical
  set N : ℕ := ⌈lam⌉₊ with hN
  set B : Set (ℕ →₀ ℝ) :=
    (fun m : ℕ => Finsupp.single m (1 : ℝ)) '' (Finset.range (N + 1) : Finset ℕ) with hB
  have hBfin : B.Finite := Set.Finite.image _ (Finset.range (N + 1)).finite_toSet
  have hfin : FiniteDimensional ℝ (Submodule.span ℝ B) :=
    FiniteDimensional.span_of_finite ℝ hBfin
  have hle : lowSpectrumSpan diagOp lam ≤ Submodule.span ℝ B := by
    refine iSup_le fun c => iSup_le fun (hc : c ≤ lam) => ?_
    intro f hf
    rw [Module.End.mem_eigenspace_iff] at hf
    -- every coordinate of `f` outside `{m | (m : ℝ) = c}` vanishes
    have hcoord : ∀ m : ℕ, (m : ℝ) ≠ c → f m = 0 := by
      intro m hm
      have h1 := congrArg (fun g : ℕ →₀ ℝ => g m) hf
      simp only [diagOp_apply, Finsupp.smul_apply, smul_eq_mul] at h1
      have hsub : ((m : ℝ) - c) * f m = 0 := by ring_nf; linarith [h1]
      rcases mul_eq_zero.mp hsub with h | h
      · exact absurd (by linarith [sub_eq_zero.mp h] : (m : ℝ) = c) hm
      · exact h
    have hsupp : ∀ m ∈ f.support, m ∈ Finset.range (N + 1) := by
      intro m hm
      have hfm : f m ≠ 0 := Finsupp.mem_support_iff.mp hm
      have hmc : (m : ℝ) = c := by
        by_contra hne
        exact hfm (hcoord m hne)
      have hmlam : (m : ℝ) ≤ lam := hmc ▸ hc
      have hmN : m ≤ N := by exact_mod_cast le_trans hmlam (Nat.le_ceil lam)
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hmN)
    -- expand `f` in the standard basis
    have hexp : f = f.sum fun m a => a • Finsupp.single m (1 : ℝ) := by
      conv_lhs => rw [← Finsupp.sum_single f]
      exact Finsupp.sum_congr fun m _ => by simp [Finsupp.smul_single]
    rw [hexp, Finsupp.sum]
    refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨m, by simpa using hsupp m hm, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

