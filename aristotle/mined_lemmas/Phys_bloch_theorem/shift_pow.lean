/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Statement: Eigenstates of a periodic Hamiltonian are Bloch waves e^{ikx}u_k(x).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Phys

/-- Translation of a wave function by the lattice constant `a`: `(transl a f) x = f (x + a)`. -/

lemma shift_pow {A : ℝ} {c : ℂ} {f : ℝ → ℂ} (h : ∀ x, f (x + A) = c * f x) :
    ∀ (n : ℕ) (x : ℝ), f (x + n * A) = c ^ n * f x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ m ih =>
      intro x
      have : (x : ℝ) + (m + 1 : ℕ) * A = (x + m * A) + A := by push_cast; ring
      rw [this, h, ih, pow_succ]
      ring

/-- If a bounded, not identically zero function satisfies `f (x + A) = c * f x`,
then `‖c‖ ≤ 1`. -/
