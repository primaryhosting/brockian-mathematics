/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

An `[[n, k, d]]_q` quantum error-correcting code is a subspace `C` of the `n`-qudit space
`(ℂ^q)^{⊗ n}`, here modelled as `EuclideanSpace ℂ (Fin n → Fin q)` (functions on the set of
classical configurations), of dimension `q ^ k`, such that every set `A` of at most `d - 1`
sites is *correctable*, i.e. satisfies the Knill–Laflamme condition
`P E P = λ(E) P` for all operators `E` supported on `A` (equivalently, for all matrix units,
which is the form used below).

The main result `QI.quantum_singleton` is the quantum Singleton bound `n - k ≥ 2 (d - 1)`.

The proof is the rank version of the standard entropic argument: for two disjoint correctable
sets `A`, `B`, writing `K` for the dimension of the code, `r_A`, `r_B` for the ranks of the
reduced density matrices on `A`, `B` and `γ` for the configuration space of the remaining
sites, one has `K * r_A ≤ |γ| * r_B` and `K * r_B ≤ |γ| * r_A`, whence `K ≤ |γ|`.
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

open scoped ComplexConjugate
open Module (finrank)

namespace QI

noncomputable section Core

variable {X α β γ Ya Yb : Type*} [Fintype X] [Fintype α] [Fintype β] [Fintype γ]
  [Fintype Ya] [Fintype Yb]

/-- The slice of `f` along the cut `e : X ≃ α × Y` at the value `a`: the vector
`y ↦ f (e.symm (a, y))`. -/

lemma cutRank_pos (e : X ≃ α × Ya) (C : Submodule ℂ (EuclideanSpace ℂ X)) (hC : C ≠ ⊥) :
    0 < cutRank e C := by
  rcases Nat.eq_zero_or_pos (cutRank e C) with h | h
  · exfalso
    have hbot : (nullSp e C)ᗮ = ⊥ := Submodule.finrank_eq_zero.mp h
    have htop : nullSp e C = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hbot
    refine hC (le_bot_iff.mp fun f hf => ?_)
    have hslice : ∀ a, cutSlice e f a = 0 := by
      intro a
      have hu : (EuclideanSpace.single a (1 : ℂ)) ∈ nullSp e C := by rw [htop]; trivial
      have h0 := hu f hf
      ext y
      have h1 := congrArg (fun v : EuclideanSpace ℂ Ya => v y) h0
      simpa [psiv_apply, EuclideanSpace.single_apply] using h1
    have hf0 : f = 0 := by
      ext x
      have h1 := congrArg (fun v : EuclideanSpace ℂ Ya => v (e x).2) (hslice (e x).1)
      simpa [cutSlice] using h1
    exact Submodule.mem_bot ℂ |>.mpr hf0
  · exact h

/-- The key inequality: `dim C * rank(A-cut) ≤ |γ| * rank(B-cut)`. -/
