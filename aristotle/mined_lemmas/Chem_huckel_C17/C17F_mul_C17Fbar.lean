/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; the same header is repeated below as the module docstring.)

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
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

namespace Chem

open Matrix Complex

/-- The adjacency matrix of the cycle graph `C₁₇` (the Hückel matrix of the cyclic
polyene, in units where the diagonal Coulomb integral is `0` and the resonance
integral is `1`), with vertices indexed by `ZMod 17`: `i` and `j` are adjacent iff
they differ by `1`. -/

lemma C17F_mul_C17Fbar : C17F * C17Fbar = (17 : ℂ) • (1 : Matrix (ZMod 17) (ZMod 17) ℂ) := by
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : ZMod 17, C17F j k * C17Fbar k l = chi ((j - l) * k) := by
    intro k
    rw [C17F, C17Fbar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [hterm, chi_sum]
  by_cases h : j = l
  · simp [h]
  · have hjl : j - l ≠ 0 := sub_ne_zero_of_ne h
    simp [hjl, h]

