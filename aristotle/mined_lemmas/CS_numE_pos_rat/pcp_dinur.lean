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

theorem pcp_dinur
    (A : ConstraintGraph q → ConstraintGraph q) (C α : ℚ)
    (hC : 1 ≤ C) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (t : ℕ) (hCt : C ≤ 2 ^ t)
    (hsize : ∀ G : ConstraintGraph q, ((A G).numE : ℚ) ≤ C * (G.numE : ℚ))
    (hsat : ∀ G : ConstraintGraph q, unsat G = 0 → unsat (A G) = 0)
    (hamp : ∀ G : ConstraintGraph q, min (2 * unsat G) α ≤ unsat (A G))
    (G : ConstraintGraph q) :
    ∃ H : ConstraintGraph q,
      H = A^[Nat.clog 2 G.numE] G ∧
      (unsat G = 0 → unsat H = 0) ∧
      (0 < unsat G → α ≤ unsat H) ∧
      ((H.numE : ℚ) ≤ (2 * (G.numE : ℚ)) ^ t * (G.numE : ℚ)) := by
  classical
  set k : ℕ := Nat.clog 2 G.numE with hk
  refine ⟨A^[k] G, rfl, ?_, ?_, ?_⟩
  · intro h; exact iterate_sat A hsat k G h
  · intro hpos
    have hamp' : min ((2 : ℚ) ^ k * unsat G) α ≤ unsat (A^[k] G) :=
      iterate_amp A α hα0 hamp k G
    have hlow : 1 / (G.numE : ℚ) ≤ unsat G := one_div_numE_le_unsat G hpos
    have hpow : (G.numE : ℚ) ≤ (2 : ℚ) ^ k := by
      have : G.numE ≤ 2 ^ k := Nat.le_pow_clog (by norm_num) _
      exact_mod_cast this
    have hmpos : (0 : ℚ) < (G.numE : ℚ) := numE_pos_rat G
    have : (1 : ℚ) ≤ 2 ^ k * unsat G := by
      have h1 : (2 : ℚ) ^ k * (1 / (G.numE : ℚ)) ≤ 2 ^ k * unsat G := by
        have : (0:ℚ) ≤ (2:ℚ) ^ k := by positivity
        nlinarith
      have h2 : (1 : ℚ) ≤ (2 : ℚ) ^ k * (1 / (G.numE : ℚ)) := by
        rw [mul_one_div, le_div_iff₀ hmpos]
        linarith [hpow]
      linarith
    have : α ≤ min ((2:ℚ) ^ k * unsat G) α := le_min (by linarith) le_rfl
    linarith [hamp', this]
  · have h1 : ((A^[k] G).numE : ℚ) ≤ C ^ k * (G.numE : ℚ) := iterate_size A C hC hsize k G
    have hCk : C ^ k ≤ (2 * (G.numE : ℚ)) ^ t := by
      have hC0 : (0:ℚ) ≤ C := by linarith
      have h2 : C ^ k ≤ ((2:ℚ) ^ t) ^ k := pow_le_pow_left₀ hC0 hCt k
      have h3 : ((2:ℚ) ^ t) ^ k = ((2:ℚ) ^ k) ^ t := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have h4 : (2:ℚ) ^ k ≤ 2 * (G.numE : ℚ) := by
        have := two_pow_clog_le G.numE G.edge_pos
        have : ((2 ^ k : ℕ) : ℚ) ≤ ((2 * G.numE : ℕ) : ℚ) := by exact_mod_cast this
        push_cast at this
        linarith
      have h5 : ((2:ℚ) ^ k) ^ t ≤ (2 * (G.numE : ℚ)) ^ t :=
        pow_le_pow_left₀ (by positivity) h4 t
      calc C ^ k ≤ ((2:ℚ) ^ t) ^ k := h2
        _ = ((2:ℚ) ^ k) ^ t := h3
        _ ≤ (2 * (G.numE : ℚ)) ^ t := h5
    have hmpos : (0 : ℚ) ≤ (G.numE : ℚ) := le_of_lt (numE_pos_rat G)
    calc ((A^[k] G).numE : ℚ) ≤ C ^ k * (G.numE : ℚ) := h1
      _ ≤ (2 * (G.numE : ℚ)) ^ t * (G.numE : ℚ) := by nlinarith


/-!
### The PCP reading: a two-query verifier

Given a constraint graph `H`, the associated verifier picks one of the `numE` edges
uniformly at random (using `⌈log₂ numE⌉` random bits), queries the two symbols of the
purported proof `σ : Fin numV → Fin q` sitting at the endpoints of that edge, and accepts
iff the constraint of that edge is satisfied.  Its acceptance probability is `accProb`.
-/

omit [NeZero q] in
/-- The probability that the two-query verifier accepts the proof `σ`. -/
