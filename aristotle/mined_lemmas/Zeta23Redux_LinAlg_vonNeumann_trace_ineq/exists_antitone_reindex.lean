/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Finset

namespace Zeta23Redux.LinAlg

/-- Abel summation / Hardy–Littlewood–Pólya: if `m` is decreasing on `range d` and the partial
sums of `f` are dominated by those of `g`, with equal total sums, then `∑ m f ≤ ∑ m g`. -/

lemma exists_antitone_reindex {d : ℕ} (f : Fin d → ℝ) :
    ∃ s : Equiv.Perm (Fin d), Antitone (fun i => f (s i)) := by
  refine ⟨Tuple.sort (fun i => -f i), ?_⟩
  intro i j hij
  have h := Tuple.monotone_sort (fun i => -f i) hij
  simp only [Function.comp_apply] at h
  linarith

/-- Existence form of von Neumann's trace inequality: the decreasing eigenvalue listings always
exist, so the hypotheses of `vonNeumann_trace_ineq` are never vacuous. -/
