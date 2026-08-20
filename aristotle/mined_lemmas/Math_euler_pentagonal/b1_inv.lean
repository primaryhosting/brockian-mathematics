/-
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
Euler's pentagonal number theorem.

We prove that the coefficient of `q^n` in the (truncated) product `∏_{i=1}^{N} (1 - q^i)`
(for any `N ≥ n`, so that the coefficient has already stabilised) equals
`∑_{k ∈ ℤ} (-1)^k [n = k(3k-1)/2]`.

The proof is Franklin's involution on partitions into distinct parts.
-/

namespace Math

open Finset

/-! ### Basic combinatorial gadgets -/

/-- `runLen s t` is the length of the maximal run `t, t-1, t-2, …` of consecutive
elements of `s` ending at `t`. -/

lemma b1_inv (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : mnf s ≤ df s) (hexc : ¬ IsExc s) :
    franklin (b1img s) = s := by
  classical
  have hmx : mnf s ≤ mxf s := mnf_le (mxf_mem hne)
  have hmem : mnf s ∈ s := mnf_mem hne
  have htop : mxf s - mnf s + 1 ∈ s := b1_top_mem h0 hne hb
  have hlt : mnf s < mxf s - mnf s + 1 := b1_mnf_lt_top h0 hne hb hexc
  have htop' : mxf s - mnf s + 1 ∈ s.erase (mnf s) :=
    Finset.mem_erase.2 ⟨by omega, htop⟩
  have hnot : mxf s + 1 ∉ (s.erase (mnf s)).erase (mxf s - mnf s + 1) := by
    intro h
    have hs : mxf s + 1 ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
    have := le_mxf hs
    omega
  have hbr := b1_branch h0 hne hb hexc
  rw [franklin, if_neg (by omega), b2img, b1_df h0 hne hb hexc, b1_mxf]
  have herase : (b1img s).erase (mxf s + 1) = (s.erase (mnf s)).erase (mxf s - mnf s + 1) := by
    rw [b1img, Finset.erase_insert hnot]
  rw [herase]
  have heq : mxf s + 1 - mnf s = mxf s - mnf s + 1 := by omega
  rw [heq, Finset.insert_erase htop', Finset.insert_erase hmem]

end Branch1

/-! ### Branch 2 of Franklin's involution: `run < min` -/

section Branch2

variable {s : Finset ℕ}

