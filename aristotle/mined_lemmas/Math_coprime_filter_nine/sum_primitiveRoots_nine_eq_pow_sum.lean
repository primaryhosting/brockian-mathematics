import Mathlib

/-!
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The set of exponents `i < 9` with `gcd i 9 = 1`. -/

lemma sum_primitiveRoots_nine_eq_pow_sum {ζ : ℂ} (h : IsPrimitiveRoot ζ 9) :
    ∑ z ∈ primitiveRoots 9 ℂ, z
      = ∑ i ∈ (Finset.range 9).filter (fun i => Nat.Coprime i 9), ζ ^ i := by
  refine (Finset.sum_bij (fun i _ => ζ ^ i) ?_ ?_ ?_ ?_).symm
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    exact (mem_primitiveRoots (by norm_num)).2 (h.pow_of_coprime a ha.2)
  · intro a ha b hb H
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    exact h.pow_inj ha.1 hb.1 H
  · intro z hz
    rw [mem_primitiveRoots (by norm_num), h.isPrimitiveRoot_iff] at hz
    obtain ⟨i, hi, hic, rfl⟩ := hz
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hic⟩, rfl⟩
  · intro a _
    rfl

/-- The sum of the primitive 9-th roots of unity equals `μ(9) = 0`. -/
