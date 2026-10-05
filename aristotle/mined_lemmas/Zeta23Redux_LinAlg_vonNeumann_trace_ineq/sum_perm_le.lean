import Mathlib
/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- Two antitone functions monovary. -/

lemma sum_perm_le {a b mu nu : Fin d → ℝ} (hmu : Antitone mu) (hnu : Antitone nu)
    (pa pb : Equiv.Perm (Fin d)) (hma : mu = a ∘ pa) (hnb : nu = b ∘ pb)
    (σ : Equiv.Perm (Fin d)) : ∑ i, a i * b (σ i) ≤ ∑ i, mu i * nu i := by
  set τ : Equiv.Perm (Fin d) := pa.trans (σ.trans pb.symm) with hτ
  have key : ∑ i, a i * b (σ i) = ∑ k, mu k * nu (τ k) := by
    rw [← Equiv.sum_comp pa fun i => a i * b (σ i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : mu k = a (pa k) := by rw [hma]; rfl
    have h2 : nu (τ k) = b (σ (pa k)) := by rw [hnb]; simp [hτ]
    rw [h1, h2]
  rw [key]
  exact sum_mul_comp_perm_le hmu hnu τ

/-- The bilinear pairing of `a` and `b` against a doubly stochastic matrix is bounded by the
sorted pairing.  This is the Birkhoff step: a doubly stochastic matrix is a convex combination
of permutation matrices, and a linear functional bounded on the permutation matrices is bounded
on their convex hull. -/
