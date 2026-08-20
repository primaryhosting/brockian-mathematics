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

noncomputable def EI (M : System V S) (A : Finset V) (s : V → S) : ℝ :=
  ∑ s' : V → S, M.prob s s' * Real.log (M.prob s s' / M.cutProb A s s')

/-- The set of bipartitions of the system: nonempty proper subsets `A` of the set of nodes,
each one standing for the bipartition `{A, Aᶜ}`. -/
