import Mathlib
/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the very first command in a file, so the header
comment appears immediately after it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace QPhys

open Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The degree-`N` homogeneous component of the product `exp a * exp b`. -/

lemma commutator_pow_eq_zero (hc : c = a * b - b * a) (hac : Commute a c) (hbc : Commute b c)
    {K : ℕ} (hK : a ^ K = 0) : c ^ K = 0 := by
  have key : ∀ i, i ≤ K → a ^ (K - i) * c ^ i = 0 := by
    intro i
    induction i with
    | zero => intro _; simp [hK]
    | succ i ih =>
      intro hi
      have ihz := ih (by omega)
      obtain ⟨n, hn⟩ : ∃ n, K - i = n + 1 := ⟨K - i - 1, by omega⟩
      rw [hn] at ihz
      have hn' : K - (i + 1) = n := by omega
      have hcb : Commute (c ^ i) b := hbc.symm.pow_left i
      have hac' : a ^ n * c ^ i = c ^ i * a ^ n := (hac.pow_pow n i).eq
      have e2 : c * a ^ n * c ^ i = c ^ (i + 1) * a ^ n := by
        rw [mul_assoc, hac', ← mul_assoc, ← pow_succ']
      have e1 : b * (a ^ (n + 1) * c ^ i)
          = a ^ (n + 1) * c ^ i * b - ((n : ℚ) + 1) • (c ^ (i + 1) * a ^ n) := by
        rw [← mul_assoc, mul_pow_succ_comm_of_central hc hac, sub_mul, smul_mul_assoc, e2,
          mul_assoc, hcb.symm.eq, ← mul_assoc]
      rw [ihz, mul_zero, zero_mul, zero_sub, eq_comm, neg_eq_zero] at e1
      have h0 : c ^ (i + 1) * a ^ n = 0 := by
        refine smul_left_cancel_rat (k := ((n : ℚ) + 1)) (by positivity) ?_
        rw [smul_zero]
        exact e1
      rw [hn', (hac.pow_pow n (i + 1)).eq, h0]
  simpa using key K le_rfl

