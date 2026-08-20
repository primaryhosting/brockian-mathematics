import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header block is required to be the first content of the file; Lean 4 requires
`import` statements to precede every other command, including module docstrings, so the
single `import Mathlib` line above is the only thing preceding it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Phys

/-! ## Shannon entropy of a finite spectrum -/

/-- Shannon (von Neumann) entropy of a finite family of probabilities. -/

def ExpSchmidtDecay {N d : ℕ} (psi : Config N d → ℂ) (L : ℕ) (C c : ℝ) : Prop :=
  ∃ rank : LeftConfig N d L → ℕ, Function.Injective rank ∧
    ∀ a, cutSpectrum psi L a ≤ C * Real.exp (-(c * rank a))

/-- The exponential-decay hypothesis is never vacuous: for a *fixed* finite chain and a
fixed cut, some pair of constants always works (with `C` growing with the dimension of
the block).  The mathematical content of the area law therefore lies in the *uniformity*
of the constants `C, c` over all chain lengths and all cut positions, which is what
`Phys.area_law_1d_uniform` below expresses. -/
