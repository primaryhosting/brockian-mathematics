import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

namespace Frontier

variable {n : ℕ}

/-- Pairing of an integer covector `k` with a real vector `x`: `⟪k, x⟫ = ∑ i, k i * x i`. -/

lemma partialDeriv_linear (ω : Fin n → ℝ) (j : Fin n) (I : Fin n → ℝ) (c : ℝ) :
    partialDeriv (fun y => (∑ i, ω i * y i) + c) j I = ω j := by
  have h : HasDerivAt (fun s => (∑ i, ω i * (Function.update I j s) i) + c) (ω j) (I j) := by
    have h0 : (fun s => (∑ i, ω i * (Function.update I j s) i) + c) =
        fun s => ω j * s + ((∑ i ∈ Finset.univ.erase j, ω i * I i) + c) := by
      funext s
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), Function.update_self]
      have : ∑ i ∈ Finset.univ.erase j, ω i * (Function.update I j s) i =
          ∑ i ∈ Finset.univ.erase j, ω i * I i :=
        Finset.sum_congr rfl (fun i hi => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
      rw [this]; ring
    rw [h0]
    simpa using ((hasDerivAt_id (I j)).const_mul (ω j)).add_const
      ((∑ i ∈ Finset.univ.erase j, ω i * I i) + c)
  rw [partialDeriv, h.deriv]

