import Mathlib

/-!
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann
namespace Mertens

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`, where `μ` is the Möbius function. -/

private lemma moebius_mul_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    ArithmeticFunction.moebius (m * n) =
      ArithmeticFunction.moebius m * ArithmeticFunction.moebius n :=
  ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h

