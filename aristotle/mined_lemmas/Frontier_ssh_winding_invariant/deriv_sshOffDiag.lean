/-
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
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

namespace Frontier

open Complex

/-!
## The Su–Schrieffer–Heeger (SSH) chain

The SSH model is a one-dimensional two-band tight-binding chain with alternating
intracell hopping `v` and intercell hopping `w`.  Its Bloch Hamiltonian is

`H(k) = Re(h k) • σₓ + Im(h k) • σ_y`,  where  `h k = v + w * exp (i k)`,

i.e. `H(k)` is purely off-diagonal (chiral / sublattice symmetry).  The spectrum is
`± |h k|`, so the chain is gapped exactly when `h k ≠ 0` for all `k`, which happens
precisely when `|v| ≠ |w|`.

The topological invariant is the winding number of the complex-valued loop
`k ↦ h k`, `k ∈ [0, 2π]`, around the origin:

`ν = (1 / (2 π i)) ∫₀^{2π} (d/dk) log (h k) dk = (1 / (2 π i)) ∫₀^{2π} h'(k) / h(k) dk`.
-/

/-- The off-diagonal entry of the SSH Bloch Hamiltonian:
`h(k) = v + w·e^{i k}`, for intracell hopping `v` and intercell hopping `w`. -/

theorem deriv_sshOffDiag (v w : ℝ) (k : ℝ) :
    deriv (fun t : ℝ => sshOffDiag v w t) k =
      Complex.I * (w : ℂ) * Complex.exp (k * Complex.I) := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I)
      (Complex.I) k := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := k)).mul_const Complex.I)
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((k : ℂ) * Complex.I) * Complex.I) k := h1.cexp
  have h3 : HasDerivAt (fun t : ℝ => sshOffDiag v w t)
      ((w : ℂ) * (Complex.exp ((k : ℂ) * Complex.I) * Complex.I)) k := by
    simpa [sshOffDiag] using (h2.const_mul (w : ℂ)).const_add ((v : ℂ))
  rw [h3.deriv]; ring

/-- The defining `[0, 2π]`-integral of `sshWinding` is the contour integral of
`z ↦ w / (v + w z)` over the unit circle. -/
