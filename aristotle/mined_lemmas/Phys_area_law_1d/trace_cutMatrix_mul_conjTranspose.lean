/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix ComplexOrder

namespace Phys

/-! ## Entropy of a finitely supported probability vector -/

/-- Shannon entropy of a real vector, `∑ -p i * log (p i)`. -/

theorem trace_cutMatrix_mul_conjTranspose {k m : ℕ} (psi : (Fin (k + m) → Fin d) → ℂ) :
    (cutMatrix psi * (cutMatrix psi)ᴴ).trace = ((∑ s, ‖psi s‖ ^ 2 : ℝ) : ℂ) := by
  have hsplit : (∑ s, ‖psi s‖ ^ 2 : ℝ)
      = ∑ u : Fin k → Fin d, ∑ v : Fin m → Fin d, ‖psi (Fin.append u v)‖ ^ 2 := by
    have h := Fintype.sum_equiv (Fin.appendEquiv k m)
      (fun p => ‖psi (Fin.append p.1 p.2)‖ ^ 2) (fun s => ‖psi s‖ ^ 2) (fun _ => rfl)
    rw [← h, Fintype.sum_prod_type]
  rw [hsplit]
  push_cast
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.conjTranspose_apply]
  show psi (Fin.append u v) * (starRingEnd ℂ) (psi (Fin.append u v)) = _
  rw [Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _

/-! ## The area law -/

/--
**Entanglement-entropy area law in one dimension.**

Hastings' theorem states that the ground state of a gapped local Hamiltonian on a 1D chain is
(approximated to any fixed accuracy by) a matrix product state whose bond dimension `D` depends
only on the spectral gap and the local dimension, not on the length of the chain. That is the
physical input, and it is encoded here as the hypothesis that the state is a matrix product
state of bond dimension `D`.

What is proved here is the resulting area law: for a normalized state on a chain of `k + m`
sites, the von Neumann entanglement entropy of the reduced density matrix of the left block,
across the cut between the first `k` and the last `m` sites, is at most `log D` — a constant
depending only on the bond dimension, and in particular independent of the sizes `k` and `m`
of the two blocks. Since the boundary of an interval in one dimension consists of a bounded
number of points, such a bound, uniform in the block sizes, is precisely the area law.
-/
