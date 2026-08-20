/-
/-!
# Fib Uniform Mod 5
Category: Cone Line
Target: Brockian.ConeLine.fib_uniform_mod5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace ConeLine

/-- Key intermediate lemma: the explicit list of Fibonacci residues mod 5 over one
Pisano period (the first 20 terms). -/

theorem fib_uniform_mod5 :
    (∀ r : Fin 5, ((Finset.range 20).filter (fun k => Nat.fib k % 5 = r.val)).card = 4)
      ∧ Nat.fib 20 % 5 = 0 ∧ Nat.fib 21 % 5 = 1 := by
  refine ⟨?_, fib_pisano20_seed⟩
  decide

end ConeLine
end Brockian

