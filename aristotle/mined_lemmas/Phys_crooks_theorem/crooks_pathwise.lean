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

theorem crooks_pathwise (beta : ℝ) (hbeta : beta ≠ 0) (E : Fin (N + 1) → S → ℝ)
    (K : Fin N → S → S → ℝ) (hDB : DetailedBalance beta E K) (x : Fin (N + 1) → S) :
    Pfwd beta E K x =
      Real.exp (beta * (work E x - deltaF beta E)) * Prev beta E K (revTraj x) := by
  have hZ0 : (0:ℝ) < Zpart beta (E 0) := Zpart_pos _ _
  have hZN : (0:ℝ) < Zpart beta (E (Fin.last N)) := Zpart_pos _ _
  have hF : Real.exp (-beta * deltaF beta E) =
      Zpart beta (E (Fin.last N)) / Zpart beta (E 0) := by
    rw [deltaF]
    have : -beta * (-(1 / beta) * Real.log (Zpart beta (E (Fin.last N)) / Zpart beta (E 0)))
        = Real.log (Zpart beta (E (Fin.last N)) / Zpart beta (E 0)) := by
      field_simp
    rw [this, Real.exp_log (by positivity)]
  have hfirst := work_add_heat E x
  rw [Pfwd, prod_fwd_eq beta E K hDB x, Prev_revTraj]
  rw [eqProb, eqProb]
  have hexp : Real.exp (beta * (work E x - deltaF beta E)) =
      Real.exp (beta * work E x) * (Zpart beta (E (Fin.last N)) / Zpart beta (E 0)) := by
    rw [← hF, ← Real.exp_add]
    ring_nf
  rw [hexp]
  have hQ : Real.exp (-beta * E 0 (x 0)) * Real.exp (-beta * heat E x) =
      Real.exp (beta * work E x) * Real.exp (-beta * E (Fin.last N) (x (Fin.last N))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    linear_combination (-beta) * hfirst
  have habs : ∀ A B C D P Z0 ZN : ℝ, Z0 ≠ 0 → ZN ≠ 0 → A * B = C * D →
      A / Z0 * (P * B) = C * (ZN / Z0) * (D / ZN * P) := by
    intro A B C D P Z0 ZN h0 hN h
    field_simp
    linear_combination P * h
  exact habs _ _ _ _ _ _ _ hZ0.ne' hZN.ne' hQ

end Lemmas

section Main

variable {S : Type*} [Fintype S] [Nonempty S] {N : ℕ}

/-- Probability that the forward experiment produces work `w`. -/
