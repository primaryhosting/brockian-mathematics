/-
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.AKS.Algorithm
import RequestProject.AKS.Cost

/-!
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000

namespace CS

/-- **PRIMES is in P** (Agrawal–Kayal–Saxena).

`AKS.aksBool : ℕ → Bool` is an explicit, fully computable implementation of the AKS primality
test.  On input `n` it checks that `n ≥ 2`, that `n` is not a perfect power, that no `a ≤ r`
shares a nontrivial factor with `n`, and — unless `n ≤ r` — that the congruences
`(X + a)^n = X^n + a` hold in `(ZMod n)[X]/(X^r - 1)` for all `1 ≤ a ≤ ℓ`, where `r = AKS.rAlg n`
is the least modulus for which the multiplicative order of `n` exceeds `(bit length)^4` and
`ℓ = AKS.ellAlg n`.  The congruences are evaluated by repeated squaring in a computable
coefficient-vector model of the quotient ring.

`AKS.aksI : ℕ → Bool × ℕ` is the same algorithm instrumented with a counter: it is a structural
copy of every function involved, threading a count of the primitive operations performed
(see `RequestProject/AKS/Cost.lean` for the cost assigned to each leaf primitive: `r * r`
coefficient multiplications for one cyclic convolution, `bits n` for one `Nat.gcd`, and so on).
Costs are therefore measured in arithmetic operations on numbers of `O(log n)` bits, not in
bit operations.

The statement below records:

* **the instrumented algorithm computes the same answer** as the plain one;
* **correctness**: `AKS.aksBool` decides primality exactly;
* **polynomial running time**: on every input `n ≥ 2` the algorithm performs at most
  `(bit length of n) ^ 45` primitive operations;
* **polynomial size of the parameters**: `r ≤ 2 · (bit length)^12` and `ℓ ≤ 4 · (bit length)^7 + 2`.
-/

theorem ordMod_eq_orderOf (n r : ℕ) [NeZero r] : ordMod n r = orderOf ((n : ZMod r)) := by
  classical
  set x : ZMod r := (n : ZMod r) with hx
  set S := (Finset.Icc 1 r).filter (fun i => x ^ i = 1) with hS
  have hmemS : ∀ i, i ∈ S ↔ (1 ≤ i ∧ i ≤ r) ∧ x ^ i = 1 := by
    intro i
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
  rcases hmin : S.min with _ | m
  · -- `S` is empty
    have hSempty : S = ∅ := Finset.min_eq_top.mp hmin
    have : orderOf x = 0 := by
      by_contra hcon
      have hpos : 0 < orderOf x := Nat.pos_of_ne_zero hcon
      have hmem : orderOf x ∈ S := by
        rw [hmemS]
        exact ⟨⟨hpos, orderOf_le_mod r x⟩, pow_orderOf_eq_one x⟩
      rw [hSempty] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    rw [ordMod, ← hS, hmin, this]
    rfl
  · have hmemm : m ∈ S := Finset.mem_of_min hmin
    have hm := (hmemS m).mp hmemm
    have hpos : 0 < orderOf x := by
      rw [orderOf_pos_iff]
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm.1.1, hm.2⟩
    have hle : orderOf x ≤ m := orderOf_le_of_pow_eq_one hm.1.1 hm.2
    have hmem2 : orderOf x ∈ S := by
      rw [hmemS]
      exact ⟨⟨hpos, orderOf_le_mod r x⟩, pow_orderOf_eq_one x⟩
    have hge : m ≤ orderOf x := Finset.min_le_of_eq hmem2 hmin
    rw [ordMod, ← hS, hmin]
    simp only [Option.getD_some]
    omega

/-! ### Integer roots -/

/-- Auxiliary binary search for the integer `b`-th root of `n`. -/
