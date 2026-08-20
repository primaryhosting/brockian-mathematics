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

namespace Frontier

/-! ## Gibbs' inequality (nonnegativity of relative entropy) -/

/-- Gibbs' inequality on a finite index type: the relative entropy (Kullback–Leibler
divergence) of two probability distributions is nonnegative, provided `p` is absolutely
continuous with respect to `q`. -/

theorem exists_disconnected_system :
    ∃ (M : System Bool Bool) (A : Finset Bool),
      A ∈ System.Bipartitions Bool ∧ M.Disconnected A := by
  refine ⟨⟨fun _ _ _ => 1 / 2, by norm_num, by intro _ _; simp⟩, {true}, ⟨⟨true, by simp⟩, ?_⟩,
    ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩
  intro h
  have : (false : Bool) ∈ ({true} : Finset Bool) := h ▸ Finset.mem_univ false
  simp at this

end Frontier

