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

/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Part I: an abstract twist (flux insertion) estimate

We model a quantum system on a finite configuration space `α`: states are functions
`ψ : α → ℂ`, the (squared) norm is `∑ c, ‖ψ c‖^2`, and a Hamiltonian is a matrix
`H : α → α → ℂ`.  `qf H ψ` is the energy expectation `⟪ψ, H ψ⟫` (real part).
-/

section Abstract

variable {α : Type*} [Fintype α]

/-- The energy expectation value `⟪ψ, H ψ⟫` (real part). -/

lemma theta_odd_jump (hn : Even n) (ψ : Conf n L → ℂ) (hsector : ∀ c, ψ c ≠ 0 → M2 c = 0)
    (c : Conf n L) (hc : ψ c ≠ 0) :
    ∃ m : ℤ, theta (sh c) - theta c = Real.pi * (2 * m + 1) := by
  obtain ⟨m, hm⟩ := w_odd hn (c 0)
  refine ⟨m, ?_⟩
  rw [theta_sh_sub c (hsector c hc), hm]
  push_cast
  ring

/-- **Lieb-Schultz-Mattis.**  Consider a periodic chain of `L` sites, each carrying `n = 2S+1`
states, with half-integral spin (`n` even), and a translation invariant nearest-neighbour
Hamiltonian `Hchain b` whose bond matrix `b` is hermitian and conserves the total magnetization.
Let `ψ` be a ground state of energy `E0` lying in the zero magnetization sector.  Then either
the ground state energy is degenerate (there is a second, orthogonal, ground state), or there is
an excited state orthogonal to `ψ` whose energy exceeds `E0` by at most `2π²(n-1)²B/L`, where
`B` bounds the row sums of the bond matrix.  In particular the gap above the ground state closes
at least as fast as `O(1/L)` as the chain length `L` grows. -/
