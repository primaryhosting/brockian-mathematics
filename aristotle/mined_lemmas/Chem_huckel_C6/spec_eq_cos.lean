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
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Matrix Polynomial SimpleGraph

namespace Chem

/-- The adjacency matrix of the cycle graph `C₆` (the Hückel matrix of benzene,
with `α = 0`, `β = 1`). -/

lemma spec_eq_cos (k : Fin 6) : spec k = 2 * Real.cos (2 * Real.pi * k / 6) := by
  have h3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  obtain ⟨n, hn⟩ := k
  interval_cases n
  · norm_num [spec]
  · rw [show (2 * Real.pi * ((⟨1, hn⟩ : Fin 6) : ℕ) / 6 : ℝ) = Real.pi / 3 by
      push_cast [Fin.val_mk]; ring]
    norm_num [spec, h3]
  · rw [show (2 * Real.pi * ((⟨2, hn⟩ : Fin 6) : ℕ) / 6 : ℝ) = Real.pi - Real.pi / 3 by
      push_cast [Fin.val_mk]; ring]
    norm_num [spec, Real.cos_pi_sub, h3]
  · rw [show (2 * Real.pi * ((⟨3, hn⟩ : Fin 6) : ℕ) / 6 : ℝ) = Real.pi by
      push_cast [Fin.val_mk]; ring]
    norm_num [spec, Real.cos_pi]
  · rw [show (2 * Real.pi * ((⟨4, hn⟩ : Fin 6) : ℕ) / 6 : ℝ) = Real.pi + Real.pi / 3 by
      push_cast [Fin.val_mk]; ring]
    norm_num [spec, Real.cos_add, Real.cos_pi, Real.sin_pi, h3]
  · rw [show (2 * Real.pi * ((⟨5, hn⟩ : Fin 6) : ℕ) / 6 : ℝ) = 2 * Real.pi - Real.pi / 3 by
      push_cast [Fin.val_mk]; ring]
    norm_num [spec, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, h3]

set_option maxHeartbeats 1000000 in
