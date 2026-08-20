/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace Frontier
namespace KadisonSinger

/-! ## The setting

Let `H` be a complex Hilbert space with a distinguished orthonormal (Hilbert) basis `e : ι → H`.
The *diagonal* subalgebra `𝒟` (an atomic MASA in `B(H)`, isomorphic to `ℓ^∞(ι)`) consists of the
bounded operators that are diagonalised by the basis.  The Kadison–Singer problem asks whether
every pure state of `𝒟` extends *uniquely* to a state of `B(H)`; this was answered
affirmatively by Marcus, Spielman and Srivastava.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The rank-one orthogonal projection onto the line spanned by a unit vector `u`, i.e. `u u*`. -/

theorem kadison_singer_of_finite {ι H : Type*} [Fintype ι] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (e : HilbertBasis ι ℂ H)
    (psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (hpsi : KadisonSinger.IsState psi)
    (hpure : KadisonSinger.IsPureOnDiagonal e psi) :
    KadisonSinger.HasUniqueExtension e psi := by
  by_cases hatom : ∃ i, psi (KadisonSinger.rankOneProj (e i)) = 1
  · obtain ⟨i, hi⟩ := hatom
    exact (kadison_singer e i psi hpsi hi).2
  · exfalso
    have hzero : ∀ i, psi (KadisonSinger.rankOneProj (e i)) = 0 := by
      intro i
      rcases KadisonSinger.apply_rankOneProj_eq_zero_or_one hpure i with h0 | h1
      · exact h0
      · exact absurd ⟨i, h1⟩ hatom
    have hsum : psi (∑ i, KadisonSinger.rankOneProj (e i)) = 0 := by
      rw [map_sum]
      simp [hzero]
    rw [KadisonSinger.sum_rankOneProj e, hpsi.map_one] at hsum
    exact one_ne_zero hsum

/-! ## The Marcus–Spielman–Srivastava discrepancy theorem

The solution of the Kadison–Singer problem by Marcus, Spielman and Srivastava proceeds through
Weaver's discrepancy-theoretic reformulation `KS_2`: if finitely many vectors
`v₁, …, vₘ ∈ ℂ^d` form a resolution of the identity, `∑ᵢ vᵢ vᵢ* = I`, and each has small norm,
`‖vᵢ‖² ≤ ε`, then the index set can be split in two so that each half has spectral norm at most
`(1/√2 + √ε)²`.  We state this below and prove the one-dimensional base case, where the
statement reduces to a greedy partition of nonnegative reals summing to `1`. -/

namespace Weaver

/-- The rank-one positive semidefinite matrix `v v*`. -/
