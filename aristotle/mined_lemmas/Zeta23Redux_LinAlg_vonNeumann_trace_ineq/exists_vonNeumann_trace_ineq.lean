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

theorem exists_vonNeumann_trace_ineq {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ mu nu : Fin d → ℝ, Antitone mu ∧ Antitone nu ∧
      (∃ sA : Equiv.Perm (Fin d), ∀ i, mu i = hA.eigenvalues (sA i)) ∧
      (∃ sB : Equiv.Perm (Fin d), ∀ i, nu i = hB.eigenvalues (sB i)) ∧
      (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  obtain ⟨sA, hsA⟩ := exists_antitone_reindex hA.eigenvalues
  obtain ⟨sB, hsB⟩ := exists_antitone_reindex hB.eigenvalues
  exact ⟨fun i => hA.eigenvalues (sA i), fun i => hB.eigenvalues (sB i), hsA, hsB,
    ⟨sA, fun _ => rfl⟩, ⟨sB, fun _ => rfl⟩,
    vonNeumann_trace_ineq hA hB _ _ sA sB (fun _ => rfl) (fun _ => rfl) hsA hsB⟩

end Zeta23Redux.LinAlg

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

