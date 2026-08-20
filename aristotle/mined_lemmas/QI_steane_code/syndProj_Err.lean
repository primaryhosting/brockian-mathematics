/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Basic setting: 7 qubits, computational basis indexed by bit strings -/

/-- Labels of the computational basis of `(ℂ²)^{⊗7}`: bit strings of length 7. -/
abbrev Bits := Fin 7 → ZMod 2

/-- Syndrome values: three bits (one per parity check of each CSS type). -/
abbrev Chk := Fin 3 → ZMod 2

/-- A state of the 7-qubit register, in the computational basis. -/
abbrev State := Bits → ℂ

/-- Mod-2 inner product of two bit strings. -/

lemma syndProj_Err (sz sx : Chk) (v w : Bits) (psi : State) (hpsi : IsCode psi) :
    syndProj sz sx (Err v w psi) = if sz = syn v ∧ sx = syn w then Err v w psi else 0 := by
  have hzf : ∀ k : Fin 3, zfacL (sz k) k (Err v w psi)
      = (if sz k = syn v k then (1 : ℂ) else 0) • Err v w psi :=
    fun k => zfacL_eigen _ _ _ _ (steane_syndrome_Z v w psi hpsi k)
  have hxf : ∀ k : Fin 3, xfacL (sx k) k (Err v w psi)
      = (if sx k = syn w k then (1 : ℂ) else 0) • Err v w psi :=
    fun k => xfacL_eigen _ _ _ _ (steane_syndrome_X v w psi hpsi k)
  simp only [syndProj, LinearMap.comp_apply, map_smul, hzf, hxf, smul_smul]
  by_cases h : sz = syn v ∧ sx = syn w
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    simp
  · rw [if_neg h]
    have hex : (∃ k : Fin 3, sz k ≠ syn v k) ∨ (∃ k : Fin 3, sx k ≠ syn w k) := by
      by_contra hc
      push_neg at hc
      exact h ⟨funext fun k => hc.1 k, funext fun k => hc.2 k⟩
    have hk3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    rcases hex with ⟨k, hk⟩ | ⟨k, hk⟩ <;> rcases hk3 k with rfl | rfl | rfl <;>
      rw [if_neg hk] <;> simp

/-- **The Steane code corrects an arbitrary single-qubit error.**
For an arbitrary error acting on qubit `i` (an arbitrary linear combination of the four
one-qubit Paulis at site `i`), each syndrome measurement outcome `(sz, sx)` projects the
corrupted state onto a state which, after the syndrome-determined recovery, is exactly
the original code state `ψ` up to the (outcome-probability) amplitude `c a b`. -/
