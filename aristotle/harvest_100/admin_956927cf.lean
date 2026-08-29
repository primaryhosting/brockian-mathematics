/-
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- A *constraint graph* over the alphabet `α`: a finite vertex set `Fin numVerts`
together with a list of edges, each carrying a binary constraint on `α`.  This is the
combinatorial object (a binary CSP instance) manipulated by Dinur's proof of the PCP
theorem. -/
structure ConstraintGraph (α : Type) where
  /-- Number of vertices; the vertex set is `Fin numVerts`. -/
  numVerts : ℕ
  /-- The edges, each with its constraint. -/
  edges : List (Fin numVerts × Fin numVerts × (α → α → Bool))

namespace ConstraintGraph

variable {α : Type}

/-- The size of a constraint graph is its number of edges. -/
def size (G : ConstraintGraph α) : ℕ := G.edges.length

/-- The number of edges of `G` violated by the assignment `f`. -/
def unsatCount (G : ConstraintGraph α) (f : Fin G.numVerts → α) : ℕ :=
  G.edges.countP (fun e => !(e.2.2 (f e.1) (f e.2.1)))

/-- The fraction of edges of `G` violated by the assignment `f`. -/
def unsatFrac (G : ConstraintGraph α) (f : Fin G.numVerts → α) : ℚ :=
  (G.unsatCount f : ℚ) / (G.size : ℚ)

theorem unsatFrac_nonneg (G : ConstraintGraph α) (f : Fin G.numVerts → α) :
    0 ≤ G.unsatFrac f := by
  unfold unsatFrac
  positivity

/-- `UNSAT(G)`: the minimum, over all assignments, of the fraction of violated edges. -/
noncomputable def unsat [Fintype α] [Nonempty α] (G : ConstraintGraph α) : ℚ :=
  Finset.univ.inf' Finset.univ_nonempty G.unsatFrac

variable [Fintype α] [Nonempty α]

theorem unsat_nonneg (G : ConstraintGraph α) : 0 ≤ G.unsat :=
  Finset.le_inf' _ _ fun f _ => G.unsatFrac_nonneg f

/-- The minimum defining `UNSAT(G)` is attained by some assignment. -/
theorem exists_unsat_eq (G : ConstraintGraph α) :
    ∃ f : Fin G.numVerts → α, G.unsat = G.unsatFrac f := by
  obtain ⟨f, -, hf⟩ :=
    Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin G.numVerts → α)) G.unsatFrac
  exact ⟨f, hf⟩

/-- A constraint graph with no edges is (vacuously) satisfiable. -/
theorem size_pos_of_unsat_pos (G : ConstraintGraph α) (h : 0 < G.unsat) : 0 < G.size := by
  rcases Nat.eq_zero_or_pos G.size with hs | hs
  · obtain ⟨f, hf⟩ := G.exists_unsat_eq
    rw [hf] at h
    unfold unsatFrac at h
    rw [hs] at h
    simp at h
  · exact hs

/-- If a constraint graph is unsatisfiable, then at least one of its `size G` edges
is violated by every assignment, so `UNSAT(G) ≥ 1 / size G`. -/
theorem one_div_size_le_unsat (G : ConstraintGraph α) (h : 0 < G.unsat) :
    1 / (G.size : ℚ) ≤ G.unsat := by
  obtain ⟨f, hf⟩ := G.exists_unsat_eq
  rw [hf] at h ⊢
  unfold unsatFrac at h ⊢
  have hm : (0 : ℚ) < (G.size : ℚ) := by
    have := G.size_pos_of_unsat_pos (by rw [hf]; exact h)
    exact_mod_cast this
  have hk : (1 : ℚ) ≤ (G.unsatCount f : ℚ) := by
    by_contra hcon
    push_neg at hcon
    have h0 : G.unsatCount f = 0 := by
      have : (G.unsatCount f : ℚ) < 1 := hcon
      exact Nat.lt_one_iff.mp (by exact_mod_cast this)
    rw [h0] at h
    simp at h
  gcongr

end ConstraintGraph

open ConstraintGraph

/-! ### Sanity checks: the `UNSAT` value is not degenerate. -/

/-- A satisfiable instance: one vertex, one self-loop with the constraint `x = x`. -/
def satExample : ConstraintGraph Bool :=
  ⟨1, [(0, 0, fun x y => decide (x = y))]⟩

/-- An unsatisfiable instance: one vertex, one self-loop with the constraint `x ≠ x`. -/
def unsatExample : ConstraintGraph Bool :=
  ⟨1, [(0, 0, fun x y => decide (x ≠ y))]⟩

theorem satExample_unsat_eq_zero : satExample.unsat = 0 := by
  have h : ∀ f : Fin satExample.numVerts → Bool, satExample.unsatFrac f = 0 := by
    intro f
    simp [unsatFrac, unsatCount, satExample, ConstraintGraph.size]
  refine le_antisymm ?_ satExample.unsat_nonneg
  obtain ⟨f⟩ : Nonempty (Fin satExample.numVerts → Bool) := inferInstance
  calc satExample.unsat ≤ satExample.unsatFrac f :=
        Finset.inf'_le _ (Finset.mem_univ f)
    _ = 0 := h f

theorem unsatExample_unsat_eq_one : unsatExample.unsat = 1 := by
  have h : ∀ f : Fin unsatExample.numVerts → Bool, unsatExample.unsatFrac f = 1 := by
    intro f
    simp [unsatFrac, unsatCount, unsatExample, ConstraintGraph.size]
  refine le_antisymm ?_ ?_
  · obtain ⟨f⟩ : Nonempty (Fin unsatExample.numVerts → Bool) := inferInstance
    calc unsatExample.unsat ≤ unsatExample.unsatFrac f :=
          Finset.inf'_le _ (Finset.mem_univ f)
      _ = 1 := h f
  · exact Finset.le_inf' _ _ fun f _ => le_of_eq (h f).symm

/-- Non-vacuity check for the hypotheses of `CS.pcp_dinur`: for every gap constant
`0 < a ≤ 1` there really is an operation on constraint graphs satisfying the three
assumptions of the amplification lemma (with `C = 1`).  (Of course the interest of
Dinur's actual amplification lemma lies in the *efficient computability* of `amp`,
which is not modelled here; this lemma only certifies that the hypotheses below are
consistent, so that `CS.pcp_dinur` is not vacuously true.) -/
theorem amplification_hypotheses_consistent (a : ℚ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∃ amp : ConstraintGraph Bool → ConstraintGraph Bool,
      (∀ G : ConstraintGraph Bool, (amp G).size ≤ 1 * G.size) ∧
      (∀ G : ConstraintGraph Bool, G.unsat = 0 → (amp G).unsat = 0) ∧
      (∀ G : ConstraintGraph Bool, min a (2 * G.unsat) ≤ (amp G).unsat) := by
  classical
  refine ⟨fun G => if G.unsat = 0 then G else unsatExample, ?_, ?_, ?_⟩
  · intro G
    show (if G.unsat = 0 then G else unsatExample).size ≤ 1 * G.size
    by_cases h : G.unsat = 0
    · simp [h]
    · have hpos : 0 < G.unsat := lt_of_le_of_ne G.unsat_nonneg (Ne.symm h)
      have hs : 1 ≤ G.size := G.size_pos_of_unsat_pos hpos
      rw [if_neg h, one_mul]
      simpa [unsatExample, ConstraintGraph.size] using hs
  · intro G h
    show (if G.unsat = 0 then G else unsatExample).unsat = 0
    simp [h]
  · intro G
    show min a (2 * G.unsat) ≤ (if G.unsat = 0 then G else unsatExample).unsat
    by_cases h : G.unsat = 0
    · simp [h, min_eq_right (le_of_lt ha0)]
    · rw [if_neg h, unsatExample_unsat_eq_one]
      exact le_trans (min_le_left _ _) ha1

/-- **Dinur's gap amplification proof of the PCP theorem** (gap-CSP form).

Assume the *amplification lemma*, the technical heart of Dinur's proof (obtained there by
combining preprocessing/expanderization, graph powering and composition with an inner
verifier): there are constants `C` and `a > 0` and an operation `amp` on constraint
graphs over the fixed finite alphabet `α` such that for every constraint graph `G`

* `size (amp G) ≤ C * size G`  (linear size blow-up),
* `amp G` is satisfiable whenever `G` is  (completeness),
* `UNSAT (amp G) ≥ min a (2 * UNSAT G)`  (the unsatisfiability value doubles until it
  reaches the constant `a`).

Then the PCP theorem in its gap form follows: there is a reduction `red` with polynomial
size blow-up which maps satisfiable constraint graphs to satisfiable ones, and maps
unsatisfiable constraint graphs to graphs with `UNSAT ≥ a`, i.e. graphs in which every
assignment violates at least a constant fraction `a` of the constraints.

The reduction is obtained by iterating `amp` logarithmically many times. -/
theorem pcp_dinur {α : Type} [Fintype α] [Nonempty α]
    (C : ℕ) (a : ℚ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (amp : ConstraintGraph α → ConstraintGraph α)
    (hsize : ∀ G : ConstraintGraph α, (amp G).size ≤ C * G.size)
    (hcomplete : ∀ G : ConstraintGraph α, G.unsat = 0 → (amp G).unsat = 0)
    (hgap : ∀ G : ConstraintGraph α, min a (2 * G.unsat) ≤ (amp G).unsat) :
    ∃ (K d : ℕ) (red : ConstraintGraph α → ConstraintGraph α),
      ∀ G : ConstraintGraph α,
        (red G).size ≤ K * G.size ^ d ∧
        (G.unsat = 0 → (red G).unsat = 0) ∧
        (0 < G.unsat → a ≤ (red G).unsat) := by
  -- Size blow-up of `t`-fold iteration.
  have hiter_size : ∀ (t : ℕ) (H : ConstraintGraph α), (amp^[t] H).size ≤ C ^ t * H.size := by
    intro t
    induction t with
    | zero => intro H; simp
    | succ t ih =>
        intro H
        rw [Function.iterate_succ_apply]
        calc (amp^[t] (amp H)).size ≤ C ^ t * (amp H).size := ih _
          _ ≤ C ^ t * (C * H.size) := Nat.mul_le_mul_left _ (hsize H)
          _ = C ^ (t + 1) * H.size := by ring
  -- Completeness is preserved by iteration.
  have hiter_comp : ∀ (t : ℕ) (H : ConstraintGraph α), H.unsat = 0 → (amp^[t] H).unsat = 0 := by
    intro t
    induction t with
    | zero => intro H h; simpa using h
    | succ t ih =>
        intro H h
        rw [Function.iterate_succ_apply]
        exact ih _ (hcomplete H h)
  -- The unsatisfiability value doubles at each step, until it reaches `a`.
  have hiter_gap : ∀ (t : ℕ) (H : ConstraintGraph α),
      min a (2 ^ t * H.unsat) ≤ (amp^[t] H).unsat := by
    intro t
    induction t with
    | zero => intro H; simp
    | succ t ih =>
        intro H
        rw [Function.iterate_succ_apply]
        refine le_trans ?_ (ih (amp H))
        have hu : 0 ≤ H.unsat := H.unsat_nonneg
        have hpow : (0 : ℚ) < 2 ^ t := by positivity
        have hpow1 : (1 : ℚ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
        have h1 : min a (2 * H.unsat) ≤ (amp H).unsat := hgap H
        rcases le_or_gt (2 * H.unsat) a with hc | hc
        · have : 2 * H.unsat ≤ (amp H).unsat := le_trans (le_min hc le_rfl) h1
          have : 2 ^ t * (2 * H.unsat) ≤ 2 ^ t * (amp H).unsat := by
            exact mul_le_mul_of_nonneg_left this (le_of_lt hpow)
          refine min_le_min le_rfl ?_
          calc (2 : ℚ) ^ (t + 1) * H.unsat = 2 ^ t * (2 * H.unsat) := by ring
            _ ≤ 2 ^ t * (amp H).unsat := this
        · have hae : a ≤ (amp H).unsat := by
            rwa [min_eq_left (le_of_lt hc)] at h1
          have : a ≤ 2 ^ t * (amp H).unsat := by
            calc a = 1 * a := (one_mul a).symm
              _ ≤ 2 ^ t * (amp H).unsat := by
                  exact mul_le_mul hpow1 hae (le_of_lt ha0) (by positivity)
          exact le_trans (min_le_left _ _) (le_min le_rfl this)
  -- The reduction: iterate `amp` about `log₂ (size G)` times.
  set b : ℕ := Nat.log 2 C + 1 with hb
  refine ⟨C, b + 1, fun G => amp^[Nat.log 2 G.size + 1] G, ?_⟩
  intro G
  set m : ℕ := G.size with hm
  set L : ℕ := Nat.log 2 m with hL
  refine ⟨?_, ?_, ?_⟩
  · -- polynomial size blow-up
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · have := hiter_size (L + 1) G
      rw [← hm, hm0] at this
      simpa [hm0] using this
    · have hCb : C ≤ 2 ^ b := le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) C)
      have h2L : 2 ^ L ≤ m := Nat.pow_log_le_self 2 hm0.ne'
      have hCL : C ^ L ≤ m ^ b := by
        calc C ^ L ≤ (2 ^ b) ^ L := Nat.pow_le_pow_left hCb L
          _ = (2 ^ L) ^ b := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
          _ ≤ m ^ b := Nat.pow_le_pow_left h2L b
      calc (amp^[L + 1] G).size ≤ C ^ (L + 1) * m := hiter_size (L + 1) G
        _ = C * (C ^ L * m) := by ring
        _ ≤ C * (m ^ b * m) := by
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hCL)
        _ = C * m ^ (b + 1) := by ring
  · intro h
    exact hiter_comp (L + 1) G h
  · intro h
    have hmpos : 0 < m := G.size_pos_of_unsat_pos h
    have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hmpos
    have h1m : 1 / (m : ℚ) ≤ G.unsat := G.one_div_size_le_unsat h
    have hlt : (m : ℚ) < 2 ^ (L + 1) := by
      have : m < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
      exact_mod_cast this
    have hbig : a ≤ 2 ^ (L + 1) * G.unsat := by
      have h2 : (m : ℚ) * (1 / (m : ℚ)) ≤ 2 ^ (L + 1) * G.unsat := by
        have hp : (0 : ℚ) < 2 ^ (L + 1) := by positivity
        exact mul_le_mul (le_of_lt hlt) h1m (by positivity) (le_of_lt hp)
      rw [mul_one_div, div_self (ne_of_gt hmQ)] at h2
      exact le_trans ha1 h2
    have := hiter_gap (L + 1) G
    rwa [min_eq_left hbig] at this

/-- **PCP theorem, verifier form**, as a corollary of `CS.pcp_dinur`.

Under the same amplification hypotheses there is a polynomial-size reduction `red` such
that, for the two-query verifier which picks a uniformly random edge of `red G`
(`O(log (size G))` random bits), reads the values of the proof `f` at its two endpoints
(2 queries) and accepts iff the constraint of that edge is satisfied:

* if `G` is satisfiable, some proof is accepted with probability `1`
  (its rejection probability `unsatFrac` is `0`);
* if `G` is unsatisfiable, every proof is rejected with probability at least `a`. -/
theorem pcp_dinur_verifier {α : Type} [Fintype α] [Nonempty α]
    (C : ℕ) (a : ℚ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (amp : ConstraintGraph α → ConstraintGraph α)
    (hsize : ∀ G : ConstraintGraph α, (amp G).size ≤ C * G.size)
    (hcomplete : ∀ G : ConstraintGraph α, G.unsat = 0 → (amp G).unsat = 0)
    (hgap : ∀ G : ConstraintGraph α, min a (2 * G.unsat) ≤ (amp G).unsat) :
    ∃ (K d : ℕ) (red : ConstraintGraph α → ConstraintGraph α),
      ∀ G : ConstraintGraph α,
        (red G).size ≤ K * G.size ^ d ∧
        (G.unsat = 0 → ∃ f : Fin (red G).numVerts → α, (red G).unsatFrac f = 0) ∧
        (0 < G.unsat → ∀ f : Fin (red G).numVerts → α, a ≤ (red G).unsatFrac f) := by
  obtain ⟨K, d, red, hred⟩ := pcp_dinur C a ha0 ha1 amp hsize hcomplete hgap
  refine ⟨K, d, red, fun G => ⟨(hred G).1, ?_, ?_⟩⟩
  · intro h
    obtain ⟨f, hf⟩ := (red G).exists_unsat_eq
    exact ⟨f, by rw [← hf, (hred G).2.1 h]⟩
  · intro h f
    exact le_trans ((hred G).2.2 h) (Finset.inf'_le _ (Finset.mem_univ f))

end CS

