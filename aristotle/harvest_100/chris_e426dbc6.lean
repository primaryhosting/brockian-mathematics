/-
# Self Nonprediction
Category: Frontier Mind
Target: Frontier.self_nonprediction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib.Computability.PartrecCode

namespace Frontier

open Nat.Partrec Nat.Partrec.Code

/-- **Self nonprediction.**

No machine can always correctly predict its own next output before producing it.

Formalisation: machines are indices (`Nat.Partrec.Code`) for partial recursive functions, and a
*predictor* is any total computable map `predict : Code → ℕ` assigning to each machine the value it
is predicted to output.  Then some machine `c` refutes the predictor *about itself*: `c` halts on
every input, and its actual output `predict c + 1` differs from the prediction `predict c` that the
predictor makes about `c`.

The proof is the diagonal self-reference argument, using Kleene's second recursion theorem
(`Nat.Partrec.Code.fixed_point₂`): build the machine that consults the predictor about its own code
and then outputs something else. -/
theorem self_nonprediction {predict : Code → ℕ} (hp : Computable predict) :
    ∃ c : Code, ∀ n : ℕ, eval c n = Part.some (predict c + 1) ∧ predict c ∉ eval c n := by
  obtain ⟨c, hc⟩ :=
    fixed_point₂ (f := fun (c : Code) (_ : ℕ) => (Part.some (predict c + 1) : Part ℕ))
      (Computable₂.partrec₂
        ((Computable.succ.comp hp).comp Computable.fst))
  refine ⟨c, fun n => ⟨by rw [hc], ?_⟩⟩
  rw [hc]
  simp

end Frontier

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

