/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 4000000

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma geom_sum_zeta_eq_eight (m : ℕ) (h : m % 8 = 0) :
    ∑ j : Fin 8, zeta ^ ((j : ℕ) * m) = 8 := by
  have hterm : ∀ j : Fin 8, zeta ^ ((j : ℕ) * m) = 1 := by
    intro j
    have : ((j : ℕ) * m) % 8 = 0 % 8 := by rw [Nat.mul_mod, h]; simp
    simpa using zeta_pow_mod _ 0 this
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  simp

