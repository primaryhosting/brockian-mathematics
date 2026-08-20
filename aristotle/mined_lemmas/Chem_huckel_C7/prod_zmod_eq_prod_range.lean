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

namespace Chem

open Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₇`, with vertices indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `±1` mod `7`. -/

private lemma prod_zmod_eq_prod_range {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ k : ZMod 7, f k.val = ∏ n ∈ Finset.range 7, f n := by
  refine Finset.prod_nbij' (fun k => k.val) (fun n => (n : ZMod 7)) ?_ ?_ ?_ ?_ ?_
  · intro k _
    simpa [Finset.mem_range] using ZMod.val_lt k
  · intro n _
    exact Finset.mem_univ _
  · intro k _
    simp [ZMod.natCast_val, ZMod.cast_id]
  · intro n hn
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)
  · intro k _
    rfl

/-- **Hückel theory for `C₇`**: the characteristic polynomial of the adjacency matrix of the
cycle graph `C₇` is `∏_{k=0}^{6} (X - 2 cos (2πk/7))`, i.e. the adjacency eigenvalues of `C₇`,
counted with multiplicity, are `2 cos (2πk/7)` for `k = 0, …, 6`. -/
