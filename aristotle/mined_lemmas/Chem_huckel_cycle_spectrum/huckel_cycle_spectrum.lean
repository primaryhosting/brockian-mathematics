/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- The Hückel (adjacency) matrix of the cycle graph `C n`, with vertices indexed by `ZMod n`:
vertex `i` is joined to `i + 1` and to `i - 1`.  For `n ≥ 3` this is exactly the adjacency matrix
of the simple cycle graph `C n`; for `n = 1, 2` it is the circulant matrix `S + S⁻¹` (`S` the
cyclic shift), which is the convention under which the Hückel spectrum formula holds. -/

theorem huckel_cycle_spectrum (n : ℕ) [NeZero n] (lam : ℂ) :
    (∃ v : ZMod n → ℂ, v ≠ 0 ∧ (cycleAdj n).mulVec v = lam • v) ↔
      ∃ k < n, lam = 2 * (Real.cos (2 * Real.pi * k / n) : ℂ) := by
  constructor
  · intro ⟨v, hv0, hv⟩
    by_contra hcon
    push_neg at hcon
    -- Fourier coefficients vanish
    have hcoef : ∀ t : ZMod n, ∑ j : ZMod n, v j * chi n (-(t * j)) = 0 := by
      intro t
      set c := ∑ j : ZMod n, v j * chi n (-(t * j)) with hc
      have key : lam * c = (chi n t + chi n (-t)) * c := by
        have h1 : lam * c = ∑ j : ZMod n, (v (j + 1) + v (j - 1)) * chi n (-(t * j)) := by
          rw [hc, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have := congrFun hv j
          rw [cycleAdj_mulVec] at this
          simp only [Pi.smul_apply, smul_eq_mul] at this
          rw [this]
          ring
        have h2 : ∑ j : ZMod n, v (j + 1) * chi n (-(t * j)) = chi n t * c := by
          have : ∀ j : ZMod n, v (j + 1) * chi n (-(t * j))
              = (fun j : ZMod n => v j * chi n (-(t * (j - 1)))) (j + 1) := by
            intro j; simp
          rw [Finset.sum_congr rfl (fun j _ => this j)]
          rw [Fintype.sum_equiv (Equiv.addRight (1 : ZMod n))
            (fun j => (fun j : ZMod n => v j * chi n (-(t * (j - 1)))) (j + 1))
            (fun j : ZMod n => v j * chi n (-(t * (j - 1)))) (fun j => rfl)]
          rw [hc, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have : -(t * (j - 1)) = t + -(t * j) := by ring
          rw [this, chi_add]
          ring
        have h3 : ∑ j : ZMod n, v (j - 1) * chi n (-(t * j)) = chi n (-t) * c := by
          have : ∀ j : ZMod n, v (j - 1) * chi n (-(t * j))
              = (fun j : ZMod n => v j * chi n (-(t * (j + 1)))) (j - 1) := by
            intro j; simp
          rw [Finset.sum_congr rfl (fun j _ => this j)]
          rw [Fintype.sum_equiv (Equiv.subRight (1 : ZMod n))
            (fun j => (fun j : ZMod n => v j * chi n (-(t * (j + 1)))) (j - 1))
            (fun j : ZMod n => v j * chi n (-(t * (j + 1)))) (fun j => rfl)]
          rw [hc, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have : -(t * (j + 1)) = -t + -(t * j) := by ring
          rw [this, chi_add]
          ring
        rw [h1]
        simp only [add_mul]
        rw [Finset.sum_add_distrib, h2, h3]
      have hne : lam ≠ chi n t + chi n (-t) := by
        rw [chi_add_chi_neg]
        exact hcon t.val (ZMod.val_lt t)
      have := sub_eq_zero.2 key
      rw [← sub_mul] at this
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hne
      · exact h
    -- Fourier inversion
    apply hv0
    funext j
    have hsum : (n : ℂ) * v j = 0 := by
      have expand : ∑ t : ZMod n, (∑ i : ZMod n, v i * chi n (-(t * i))) * chi n (t * j)
          = (n : ℂ) * v j := by
        have step1 : ∀ t : ZMod n, (∑ i : ZMod n, v i * chi n (-(t * i))) * chi n (t * j)
            = ∑ i : ZMod n, v i * chi n (t * (j - i)) := by
          intro t
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have : t * (j - i) = -(t * i) + t * j := by ring
          rw [this, chi_add]
          ring
        rw [Finset.sum_congr rfl (fun t _ => step1 t), Finset.sum_comm]
        have step2 : ∀ i : ZMod n, ∑ t : ZMod n, v i * chi n (t * (j - i))
            = v i * (if j - i = 0 then (n : ℂ) else 0) := by
          intro i; rw [← Finset.mul_sum, chi_orthogonality]
        rw [Finset.sum_congr rfl (fun i _ => step2 i)]
        rw [Finset.sum_eq_single j]
        · simp [mul_comm]
        · intro i _ hij
          have : j - i ≠ 0 := sub_ne_zero.2 (Ne.symm hij)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [← expand]
      refine Finset.sum_eq_zero (fun t _ => ?_)
      rw [hcoef t, zero_mul]
    have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
    simpa [hn] using hsum
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun a => chi n ((k : ZMod n) * a), ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp only [mul_zero, chi_zero, Pi.zero_apply] at this
      exact one_ne_zero this
    · funext i
      rw [cycleAdj_mulVec]
      have e1 : (k : ZMod n) * (i + 1) = (k : ZMod n) * i + (k : ZMod n) := by ring
      have e2 : (k : ZMod n) * (i - 1) = (k : ZMod n) * i + (-(k : ZMod n)) := by ring
      rw [e1, e2, chi_add, chi_add]
      have hval : ((k : ZMod n)).val = k := ZMod.val_cast_of_lt hk
      have := chi_add_chi_neg n (k : ZMod n)
      rw [hval] at this
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_add, this]
      ring

end Chem

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

