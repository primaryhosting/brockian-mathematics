/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Matrix Finset

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/

lemma normSq_unitary_mem_doublyStochastic {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (Matrix.of fun p q => Complex.normSq (W p q)) ∈ doublyStochastic ℝ (Fin d) := by
  have h1 : W * star W = 1 := Matrix.mem_unitaryGroup_iff.mp hW
  have h2 : star W * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hW
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, fun p => ?_, fun q => ?_⟩
  · have h := congrFun (congrFun h1 p) p
    simp [Matrix.mul_apply, Complex.mul_conj] at h
    exact_mod_cast h
  · have h := congrFun (congrFun h2 q) q
    simp [Matrix.mul_apply, mul_comm, Complex.mul_conj] at h
    exact_mod_cast h

/-- Birkhoff + rearrangement: a bilinear form of two antitone vectors against a doubly
stochastic matrix is bounded by the aligned pairing. -/
