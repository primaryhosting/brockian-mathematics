import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires every `import` to precede any module docstring, so the header
-- comment above sits immediately after the single `import Mathlib` line.

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- The vertex space of the regular `n`-gon: complex-valued functions on the vertex
set `ZMod n`.  The dihedral group `D_n` acts on it through the rotation `ngonShift`
and the reflection `ngonRefl`. -/
abbrev NGon (n : ℕ) : Type := ZMod n → ℂ

/-- Rotation of the `n`-gon by `t` vertices, acting on functions by translation. -/

theorem PentagonPentagonIsotypicHigherN :
    (∀ (n : ℕ) [NeZero n] (j : ZMod n),
        (∀ t : ZMod n, ∀ f ∈ ngonIsotypic n j, ngonShift n t f ∈ ngonIsotypic n j) ∧
        (∀ f ∈ ngonIsotypic n j, ngonRefl n f ∈ ngonIsotypic n j) ∧
        (∀ f ∈ ngonIsotypic n j, ngonAdj n f = ((ngonEigen n j : ℝ) : ℂ) • f) ∧
        (j ≠ -j →
          LinearIndependent ℂ ![⇑(ngonChar n j), ⇑(ngonChar n (-j))] ∧
          Module.finrank ℂ (ngonIsotypic n j) = 2))
    ∧ ngonEigen 5 1 = (Real.sqrt 5 - 1) / 2
    ∧ ngonEigen 5 2 = -(1 + Real.sqrt 5) / 2 :=
  ⟨fun _ _ j =>
      ⟨fun t _ hf => ngonIsotypic_shift_mem j t hf,
       fun _ hf => ngonIsotypic_refl_mem j hf,
       fun _ hf => ngonAdj_isotypic j hf,
       fun hj => ⟨ngonChar_linearIndependent j hj, ngonIsotypic_finrank j hj⟩⟩,
    ngonEigen_five_one, ngonEigen_five_two⟩

end Brockian

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

