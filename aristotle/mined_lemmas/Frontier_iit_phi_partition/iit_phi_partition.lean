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

theorem iit_phi_partition {V S : Type*} [Fintype V] [DecidableEq V] [Fintype S] [Nonempty S]
    (M : System V S) {A : Finset V} (hA : A ∈ System.Bipartitions V)
    (hdis : M.Disconnected A) (s : V → S) :
    M.Phi s = 0 := by
  have hlb : ∀ x ∈ {x : ℝ | ∃ A ∈ System.Bipartitions V, x = M.EI A s}, 0 ≤ x := by
    rintro x ⟨B, -, rfl⟩
    exact M.EI_nonneg B s
  have hmem : (0 : ℝ) ∈ {x : ℝ | ∃ A ∈ System.Bipartitions V, x = M.EI A s} :=
    ⟨A, hA, (M.EI_eq_zero_of_disconnected hdis s).symm⟩
  refine le_antisymm ?_ ?_
  · exact csInf_le ⟨0, fun x hx => hlb x hx⟩ hmem
  · exact le_csInf ⟨0, hmem⟩ hlb

/-- The hypotheses of `Frontier.iit_phi_partition` are satisfiable: there is a genuine
two-element system together with a bipartition along which it is disconnected. -/
