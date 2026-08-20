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

lemma fib_pisano20_seed : Nat.fib 20 % 5 = 0 ∧ Nat.fib 21 % 5 = 1 := by
  constructor <;> rfl

/-- Fibonacci is uniformly distributed mod 5: within one Pisano period (20 terms),
each residue mod 5 occurs exactly 4 times.  We also record the Pisano-20 restart
`fib 20 ≡ 0`, `fib 21 ≡ 1` (mod 5). -/
