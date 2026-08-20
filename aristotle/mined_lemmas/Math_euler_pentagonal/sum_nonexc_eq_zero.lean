import Mathlib
/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
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

namespace Math

/-- The smallest element of a finite set of naturals (junk value `0` if empty). -/

lemma sum_nonExc_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    ∑ s ∈ (D n).filter (fun s => ¬ isExc s), (-1 : ℤ) ^ s.card = 0 := by
  have key : ∀ s ∈ (D n).filter (fun s => ¬ isExc s),
      0 ∉ franklin s ∧ (∑ i ∈ franklin s, i) = n ∧
        ((franklin s).card + 1 = s.card ∨ s.card + 1 = (franklin s).card) ∧
        ¬ isExc (franklin s) ∧ franklin (franklin s) = s := by
    intro s hs
    obtain ⟨h0, hne, hsum, hexc⟩ := mem_filter_props hn hs
    obtain ⟨a, b, c, d, e⟩ := franklin_props h0 hne hexc
    exact ⟨a, by rw [b, hsum], c, d, e⟩
  have g_mem : ∀ s (hs : s ∈ (D n).filter (fun s => ¬ isExc s)),
      franklin s ∈ (D n).filter (fun s => ¬ isExc s) := by
    intro s hs
    obtain ⟨a, b, _, d, _⟩ := key s hs
    rw [Finset.mem_filter, mem_D_iff]
    exact ⟨⟨a, b⟩, d⟩
  refine Finset.sum_involution (fun s _ => franklin s) (fun s hs => ?_) (fun s hs _ => ?_)
    g_mem (fun s hs => ?_)
  · show (-1 : ℤ) ^ s.card + (-1 : ℤ) ^ (franklin s).card = 0
    exact neg_one_pow_add (Or.symm (key s hs).2.2.1)
  · show franklin s ≠ s
    intro hcon
    have := (key s hs).2.2.1
    rw [hcon] at this
    omega
  · exact (key s hs).2.2.2.2

/-! ### The exceptional partitions -/

