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

theorem tendsto_nonprime_part (q : ℕ) (a : ZMod q) :
    Tendsto (fun s : ℝ => (s - 1) *
        ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) ^ s)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  set C : ℝ := ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ)
  have h1 : Tendsto (fun s : ℝ => (s - 1) * C) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa using tendsto_sub_one_nhdsGT.mul_const C
  refine squeeze_zero' (eventually_nhdsWithin_of_forall ?_) (eventually_nhdsWithin_of_forall ?_) h1
  · intro s hs
    have hs' : (1 : ℝ) < s := hs
    have hnn : 0 ≤ ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) ^ s :=
      tsum_nonneg fun n => nonprime_term_nonneg q a s n
    nlinarith [hnn]
  · intro s hs
    have hs' : (1 : ℝ) < s := hs
    have hle : ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) ^ s ≤ C :=
      Summable.tsum_le_tsum (nonprime_term_le q a hs'.le) (summable_nonprime_rpow q a hs'.le)
        (vonMangoldt.summable_residueClass_non_primes_div a)
    nlinarith [hle]

/-- **Dirichlet density of the primes in a residue class** (von Mangoldt weighted form). -/
