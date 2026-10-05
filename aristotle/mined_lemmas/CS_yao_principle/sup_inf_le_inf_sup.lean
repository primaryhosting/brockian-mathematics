/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is repeated as a module docstring below; Lean requires `import`
-- to precede any module docstring.)

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
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

namespace CS

variable {A I : Type*}

/-- The expected cost of the randomized algorithm given by the distribution `p` over the
(deterministic) algorithms `A`, run on the input `i`. -/

lemma sup_inf_le_inf_sup (cost : A → I → ℝ) :
    ⨆ q : stdSimplex ℝ I, ⨅ a, distCost cost a (q : I → ℝ) ≤
      ⨅ p : stdSimplex ℝ A, ⨆ i, randCost cost (p : A → ℝ) i := by
  refine ciSup_le fun q => le_ciInf fun p => ?_
  have h1 : (⨅ a, distCost cost a (q : I → ℝ)) ≤ ∑ a, (p : A → ℝ) a * distCost cost a q :=
    le_convex_comb p.2 fun a => ciInf_le (bddBelow_distCost cost (q : I → ℝ)) a
  have h2 : ∑ i, (q : I → ℝ) i * randCost cost (p : A → ℝ) i ≤ ⨆ i, randCost cost (p : A → ℝ) i :=
    convex_comb_le q.2 fun i => le_ciSup (bddAbove_randCost cost (p : A → ℝ)) i
  rw [exchange] at h2
  exact h1.trans h2

/-- **Yao's minimax principle**: for a finite set `A` of deterministic algorithms and a finite set
`I` of inputs with cost matrix `cost`, the randomized complexity (the least, over distributions `p`
over algorithms, of the worst-case expected cost) equals the distributional complexity (the
greatest, over distributions `q` over inputs, of the best expected cost of a deterministic
algorithm). -/
