import Mathlib

/-!
# Psi Two Le
Category: Frontier Wave 2 (deeper machinery)
Target: Chebyshev.psi_two_le
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chebyshev

open ArithmeticFunction

/-- Λ(4) = log 2, since 4 = 2². -/

theorem sum_vonMangoldt_Icc_four :
    ∑ n ∈ Finset.Icc 1 4, ArithmeticFunction.vonMangoldt n
      = 2 * Real.log 2 + Real.log 3 := by
  have h1 : ArithmeticFunction.vonMangoldt 1 = 0 :=
    ArithmeticFunction.vonMangoldt_apply_one
  have h2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; norm_num
  have h3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]; norm_num
  have h4 : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := vonMangoldt_four
  have hIcc : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  rw [hIcc]
  norm_num [Finset.sum_insert, h1, h2, h3, h4]
  ring

/-- The second Chebyshev function at `4`: `ψ(4) = ∑_{n ≤ 4} Λ(n) = log 12`. -/
