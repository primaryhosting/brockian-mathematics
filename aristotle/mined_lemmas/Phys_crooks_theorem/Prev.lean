/-
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
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

/-!
## Setting

A driven classical system with a finite state space `S` is observed at the `N + 1` times
`0, 1, …, N`.  The externally controlled protocol is encoded by the energy functions
`E k : S → ℝ` (`k : Fin (N+1)`), and the stochastic relaxation between consecutive times by
Markov weights `K k : S → S → ℝ` (`k : Fin N`), where `K k x y` is the weight of the jump
`x ↦ y` performed while the energy function is `E k.succ`.

The single physical input is *microscopic reversibility* (detailed balance) of each `K k`
with respect to the Boltzmann distribution of `E k.succ` at inverse temperature `β`.

A forward trajectory `x : Fin (N+1) → S` is drawn by sampling `x 0` from the equilibrium
distribution of `E 0` and then applying the kernels `K 0, K 1, …`.  The reverse experiment
starts from the equilibrium distribution of `E (Fin.last N)` and applies the same kernels in
the opposite order, `K (N-1), …, K 0`.

Work is the energy change performed at fixed state, heat the energy change caused by the
jumps.  The free energies are `F k = -β⁻¹ log (Z k)`.
-/

section

variable {S : Type*}

/-- Partition function of the energy function `E` at inverse temperature `beta`. -/

noncomputable def Prev [Fintype S] (beta : ℝ) (E : Fin (N + 1) → S → ℝ)
    (K : Fin N → S → S → ℝ) (y : Fin (N + 1) → S) : ℝ :=
  eqProb beta (E (Fin.last N)) (y 0) * ∏ k : Fin N, K k.rev (y k.castSucc) (y k.succ)

/-- Work performed on the system along the forward trajectory `x`: at each step the energy
function is switched from `E k` to `E k.succ` while the system sits in the state
`x k.castSucc`. -/
