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

lemma creatFun_finite (x : FockSub) : {n | creatFun x n ≠ 0}.Finite := by
  refine Set.Finite.subset (Set.Finite.image (fun n : ℕ => n + 1) (fock_finite x)) ?_
  intro n hn
  match n with
  | 0 => simp [creatFun] at hn
  | (m + 1) =>
      simp only [Set.mem_setOf_eq, creatFun] at hn
      refine ⟨m, ?_, rfl⟩
      simp only [Set.mem_setOf_eq]
      intro h; simp [h] at hn

/-- The annihilation operator `a` on the Fock space. -/
