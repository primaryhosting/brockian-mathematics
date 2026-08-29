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

import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Boltzmann weight of state `i` for the Hamiltonian `E - f • A`, at inverse
temperature `β` and external field `f`. -/

lemma hasDerivAt_numerator (β : ℝ) (E A : ι → ℝ) (g : ι → ℝ) (f₀ : ℝ) :
    HasDerivAt (fun f => ∑ i, g i * boltz β E A f i)
      (∑ i, g i * (β * A i * boltz β E A f₀ i)) f₀ :=
  HasDerivAt.fun_sum (fun i _ => (hasDerivAt_boltz β E A f₀ i).const_mul (g i))

/-- **Fluctuation–dissipation theorem** (classical, static form).

For a finite classical system with unperturbed energies `E` and an observable `A`
coupled to an external field `f` (so the Hamiltonian is `E i - f * A i`), the
linear response of the equilibrium expectation value of `A` to the field, i.e.
the susceptibility `d⟨A⟩/df`, equals `β` times the equilibrium variance
`⟨A²⟩ - ⟨A⟩²` of `A`.  Dissipation (response) is thus determined by equilibrium
fluctuations. -/
