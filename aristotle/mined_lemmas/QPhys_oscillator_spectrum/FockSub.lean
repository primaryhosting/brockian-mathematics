import Mathlib

/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
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

set_option grind.warning false

namespace QPhys

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Hamiltonian `ℏω (a† a + ½)` of a one-dimensional quantum harmonic oscillator,
expressed through the annihilation operator `a` and the creation operator `ad = a†`. -/

def FockSub : Submodule ℂ Lsp where
  carrier := {x | {n | (x : ℕ → ℂ) n ≠ 0}.Finite}
  add_mem' := by
    intro x y hx hy
    refine Set.Finite.subset (hx.union hy) ?_
    intro n hn
    simp only [Set.mem_setOf_eq, lp.coeFn_add, Pi.add_apply] at hn
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    simp [hc.1, hc.2] at hn
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    refine Set.Finite.subset hx ?_
    intro n hn
    simp only [Set.mem_setOf_eq, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hn ⊢
    exact fun h => hn (by simp [h])

/-- Build an element of the Fock space from a finitely supported sequence. -/
