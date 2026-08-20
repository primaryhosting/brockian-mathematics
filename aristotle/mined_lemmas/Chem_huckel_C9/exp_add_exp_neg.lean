import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede all other commands, including module
docstrings, so the required header comment appears immediately after the import.)
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₉`, with vertices indexed by `ZMod 9`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `9`. -/

lemma exp_add_exp_neg (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-((t : ℂ) * Complex.I))
      = 2 * (Real.cos t : ℂ) := by
  have h2 : -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [Complex.exp_mul_I, h2, Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- `ψ k + ψ (-k) = 2 cos (2πk/9)`. -/
