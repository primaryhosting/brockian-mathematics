/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-! ### Arithmetic in `ZMod 2` -/


theorem exists_uniform_spectral_gap_family :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      IsLeast {mu : ℝ | mu ≠ 0 ∧ ∃ f : Cube k → ℝ, f ≠ 0 ∧
        (hypercube k).lapMatrix ℝ *ᵥ f = mu • f} c :=
  ⟨2, two_pos, expander_uniform_gap_witness⟩

end Frontier.Spectral

