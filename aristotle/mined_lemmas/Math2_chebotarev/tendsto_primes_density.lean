/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
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

namespace Math2

open ArithmeticFunction Complex Filter Topology

/-! ### The analytic input: Λ-weighted density of a residue class -/

/-- The terms of the `L`-series of the von Mangoldt function restricted to a residue class,
evaluated at a real point, are real. -/

theorem tendsto_primes_density (q : ℕ) [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun s : ℝ => (s - 1) *
        ∑' n : ℕ, (if n.Prime then vonMangoldt.residueClass a n else 0) / (n : ℝ) ^ s)
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have hsub := (tendsto_residueClass_density q ha).sub (tendsto_nonprime_part q a)
  simp only [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (1 : ℝ) < s := hs
  have hsplit : ∑' n : ℕ, vonMangoldt.residueClass a n / (n : ℝ) ^ s
      = (∑' n : ℕ, (if n.Prime then vonMangoldt.residueClass a n else 0) / (n : ℝ) ^ s)
        + ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) ^ s := by
    rw [← Summable.tsum_add (summable_prime_rpow q a hs') (summable_nonprime_rpow q a hs'.le)]
    refine tsum_congr fun n => ?_
    by_cases hn : n.Prime <;> simp [hn]
  rw [hsplit]
  ring

/-! ### The Galois side: Frobenius elements of cyclotomic fields -/

/-- The `q`-th cyclotomic polynomial is irreducible over `ℚ`. -/
