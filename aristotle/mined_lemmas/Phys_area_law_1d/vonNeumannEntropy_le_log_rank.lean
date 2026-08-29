import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
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

namespace Phys

/-! ## Shannon entropy of a finite probability vector -/

/-- The Shannon entropy `-∑ pᵢ log pᵢ` of a finite family of reals. -/

theorem vonNeumannEntropy_le_log_rank {n : Type*} [Fintype n] [DecidableEq n]
    {rho : Matrix n n ℂ} (hpsd : rho.PosSemidef) (htr : rho.trace = 1)
    (D : ℕ) (hrank : rho.rank ≤ D) :
    vonNeumannEntropy rho ≤ Real.log D := by
  classical
  have hherm : rho.IsHermitian := hpsd.isHermitian
  have hev_nonneg : ∀ i, 0 ≤ hherm.eigenvalues i := fun i => hpsd.eigenvalues_nonneg i
  have hev_sum : ∑ i, hherm.eigenvalues i = 1 := by
    have := hherm.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h2 : ((∑ i, hherm.eigenvalues i : ℝ) : ℂ) = (1 : ℂ) := by
      rw [Complex.ofReal_sum]; exact this.symm
    exact_mod_cast h2
  have hcard : (Finset.univ.filter fun i => hherm.eigenvalues i ≠ 0).card ≤ D := by
    have h : rho.rank = Fintype.card {i // hherm.eigenvalues i ≠ 0} :=
      hherm.rank_eq_card_non_zero_eigs
    rw [Fintype.card_subtype] at h
    rw [h] at hrank
    exact hrank
  rw [vonNeumannEntropy, dif_pos hherm]
  exact shannonEntropy_le_log_of_card_support_le _ hev_nonneg hev_sum D hcard

/-! ## The 1D chain: cuts, Schmidt matricization and reduced density matrices -/

/-- Splitting of the configuration space of a chain of `N` sites with local dimension `d`
into the configurations of the left block `{0, …, x-1}` and of the right block. -/
