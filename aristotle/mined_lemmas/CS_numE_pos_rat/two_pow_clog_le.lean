/-
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header
-- above is repeated below as the module docstring.)

import Mathlib

/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
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

/-- A *constraint graph* over the alphabet `Fin q`: a finite (multi)graph on the vertex
set `Fin numV` with `numE` edges, each edge carrying a binary constraint on the values
assigned to its endpoints.  This is the combinatorial object manipulated throughout
Dinur's proof of the PCP theorem. -/
structure ConstraintGraph (q : ℕ) where
  /-- number of vertices -/
  numV : ℕ
  /-- number of edges -/
  numE : ℕ
  /-- the endpoints of each edge -/
  edge : Fin numE → Fin numV × Fin numV
  /-- the constraint attached to each edge -/
  sat : Fin numE → (Fin q → Fin q → Bool)
  /-- constraint graphs have at least one edge -/
  edge_pos : 0 < numE

variable {q : ℕ} [NeZero q]

/-- The set of edges violated by an assignment `σ`. -/

lemma two_pow_clog_le (m : ℕ) (hm : 0 < m) : 2 ^ (Nat.clog 2 m) ≤ 2 * m := by
  rcases Nat.eq_or_lt_of_le hm with h | h
  · simp [← h]
  · have h1 : 2 ^ (Nat.clog 2 m - 1) < m :=
      Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have hclog : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by norm_num) h
    calc 2 ^ (Nat.clog 2 m) = 2 * 2 ^ (Nat.clog 2 m - 1) := by
          rw [← pow_succ']
          congr 1
          omega
      _ ≤ 2 * m := by omega

/--
**Dinur's gap amplification proof of the PCP theorem.**

Dinur's proof of the PCP theorem consists of a deep combinatorial *amplification step*
(preprocessing, graph powering and composition with an assignment tester), which produces
from any constraint graph `G` over a fixed alphabet a constraint graph `A G` over the same
alphabet such that

* `A G` has size at most `C` times the size of `G` (`hsize`),
* `A G` is satisfiable whenever `G` is (`hsat`),
* the UNSAT value doubles, unless it has already reached the constant `α` (`hamp`),

together with the *iteration argument* formalized here: applying the amplification step
`⌈log₂ (numE G)⌉` times turns any constraint graph into one of polynomial size whose UNSAT
value exhibits the constant gap `α` — satisfiable instances stay satisfiable, and
unsatisfiable instances become "`α`-far" from satisfiable.  This gap version of constraint
satisfaction is exactly the PCP theorem in its equivalent CSP formulation.

Here the amplification step is taken as a hypothesis (`A`, `hsize`, `hsat`, `hamp`) and the
iteration argument is proved, including the explicit polynomial size bound
`(2 · numE G) ^ t · numE G`, where `2 ^ t` bounds the blow-up constant `C`.
-/
