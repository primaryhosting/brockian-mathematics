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

set_option grind.warning false

namespace Chem

open Polynomial Complex

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The cycle graph `C₁₃`, on the vertex set `ZMod 13`, where `i` and `j` are adjacent
iff they differ by `1`. -/

theorem huckel_C13_eigenvector (k : ℕ) (hk : k < 13) :
    ∃ v : ZMod 13 → ℂ, v ≠ 0 ∧
      adjC13.mulVec v = ((2 * Real.cos (2 * Real.pi * (k : ℝ) / 13) : ℝ) : ℂ) • v := by
  refine ⟨evec (k : ZMod 13), ?_, ?_⟩
  · intro h
    have h0 : evec (k : ZMod 13) 0 = 0 := by rw [h]; rfl
    exact ee_ne_zero _ h0
  · have hval : ((k : ZMod 13)).val = k := ZMod.val_natCast_of_lt hk
    have := mulVec_evec (k : ZMod 13)
    rwa [eval13, hval] at this

/-- The spectrum of the adjacency matrix of `C₁₃` is the set of numbers `2 cos (2πk/13)`. -/
