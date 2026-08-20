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

/-!
# Deutsch's algorithm

We model a two-qubit quantum register by its amplitude vector
`Bool × Bool → ℂ` (the computational basis is indexed by pairs of bits),
implement the Hadamard gates on each qubit and the phase-kickback oracle
`U_f |x,y⟩ = |x, y ⊕ f x⟩` as linear maps on this space, and prove that
Deutsch's algorithm — which queries the oracle exactly once — decides
whether `f : {0,1} → {0,1}` is constant or balanced with certainty.
-/

namespace QC

noncomputable section

/-- The state space of two qubits: amplitudes indexed by the computational basis. -/
abbrev State : Type := Bool × Bool → ℂ

/-- The sign `(-1)^b` of a bit. -/

lemma deutschState_apply (f : Bool → Bool) (b y : Bool) :
    deutschState f (b, y)
      = ((Real.sqrt 2 : ℂ)⁻¹) ^ 3 * sgn y * (sgn (f false) + sgn b * sgn (f true)) := by
  simp only [deutschState, H1, H2, oracle, init]
  cases b <;>
    cases hy : y <;>
      cases h0 : f false <;>
        cases h1 : f true <;>
          simp [sgn] <;> ring

