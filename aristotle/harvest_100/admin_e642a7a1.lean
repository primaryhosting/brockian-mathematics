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

/-
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Dinur's gap amplification and the PCP theorem (CSP form)

This file formalizes the combinatorial skeleton of Irit Dinur's proof of the PCP theorem.

We model a *constraint graph* as a finite nonempty list of binary constraints over a finite
alphabet `Fin (q+1)`, with variables indexed by `Fin n`.  For an assignment `a` the quantity
`unsatWith G a` is the fraction of constraints violated by `a`, and `unsat G` is the minimum
of this quantity over all assignments (the *unsat value*, or gap, of `G`).

Dinur's key technical result is the *gap amplification step*: there are a fixed alphabet size
`q0`, a constant `C` and a constant `α > 0` such that every constraint graph `G` over
`Fin (q0+1)` can be transformed into a constraint graph `step G` over the same alphabet with

* `size (step G) ≤ C * size G`   (linear blow-up),
* `min (2 * unsat G) α ≤ unsat (step G)`  (the gap doubles, until it reaches `α`),
* `unsat G = 0 → unsat (step G) = 0`  (perfect completeness is preserved).

This is packaged as the structure `CS.Amplifier`.  The main theorem `CS.pcp_dinur` shows how
the PCP theorem, in its equivalent "gap constraint satisfaction" form, follows: iterating the
amplification step `O(log (size G))` many times yields, in polynomial size, a constraint graph
whose gap is either `0` (if `G` is satisfiable) or at least the absolute constant `α`.

The efficiency (polynomial-time computability) of the reduction is *not* modelled here -- only
its size behaviour; correspondingly `CS.Amplifier` is a purely combinatorial hypothesis, and
`CS.amplifier_nonempty` records that it is consistent (so the main theorem is not vacuous).
-/

namespace CS

/-- A *constraint graph*: `n` variables taking values in the alphabet `Fin (q+1)`, together with
a nonempty list of binary constraints, each given by a pair of variables and a boolean relation
on the alphabet. -/
structure ConstraintGraph where
  /-- number of variables -/
  n : ℕ
  /-- the alphabet is `Fin (q+1)` -/
  q : ℕ
  /-- the list of constraints -/
  edges : List (Fin n × Fin n × (Fin (q + 1) → Fin (q + 1) → Bool))
  /-- there is at least one constraint -/
  edges_ne : edges ≠ []

namespace ConstraintGraph

/-- The size of a constraint graph is its number of constraints. -/
def size (G : ConstraintGraph) : ℕ := G.edges.length

lemma size_pos (G : ConstraintGraph) : 0 < G.size :=
  List.length_pos_iff.mpr G.edges_ne

/-- The fraction of constraints of `G` violated by the assignment `a`. -/
def unsatWith (G : ConstraintGraph) (a : Fin G.n → Fin (G.q + 1)) : ℚ :=
  (G.edges.countP (fun e => ! e.2.2 (a e.1) (a e.2.1)) : ℚ) / G.size

/-- The *unsat value* (gap) of a constraint graph: the minimum over all assignments of the
fraction of violated constraints. -/
def unsat (G : ConstraintGraph) : ℚ :=
  Finset.univ.inf' Finset.univ_nonempty G.unsatWith

lemma unsatWith_nonneg (G : ConstraintGraph) (a : Fin G.n → Fin (G.q + 1)) :
    0 ≤ G.unsatWith a := by
  unfold unsatWith
  positivity

lemma unsat_nonneg (G : ConstraintGraph) : 0 ≤ G.unsat :=
  Finset.le_inf' _ _ (fun a _ => G.unsatWith_nonneg a)

lemma unsat_le (G : ConstraintGraph) (a : Fin G.n → Fin (G.q + 1)) : G.unsat ≤ G.unsatWith a :=
  Finset.inf'_le _ (Finset.mem_univ a)

/-- The minimum defining `unsat` is attained. -/
lemma exists_unsat_eq (G : ConstraintGraph) : ∃ a, G.unsat = G.unsatWith a := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty) G.unsatWith
  exact ⟨a, ha⟩

lemma unsatWith_eq_zero_iff (G : ConstraintGraph) (a : Fin G.n → Fin (G.q + 1)) :
    G.unsatWith a = 0 ↔ ∀ e ∈ G.edges, e.2.2 (a e.1) (a e.2.1) = true := by
  unfold unsatWith
  rw [div_eq_zero_iff]
  have hs : (G.size : ℚ) ≠ 0 := by exact_mod_cast (G.size_pos).ne'
  simp only [hs, or_false, Nat.cast_eq_zero, List.countP_eq_zero]
  exact ⟨fun h e he => by simpa using h e he, fun h e he => by simpa using h e he⟩

lemma inv_size_le_unsatWith (G : ConstraintGraph) (a : Fin G.n → Fin (G.q + 1))
    (h : G.unsatWith a ≠ 0) : 1 / (G.size : ℚ) ≤ G.unsatWith a := by
  unfold unsatWith at h ⊢
  have hs : (0:ℚ) < G.size := by exact_mod_cast G.size_pos
  rw [div_le_div_iff_of_pos_right hs]
  have h1 : G.edges.countP (fun e => ! e.2.2 (a e.1) (a e.2.1)) ≠ 0 := by
    intro hc; apply h; rw [hc]; simp
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h1

/-- If the gap of `G` is nonzero then it is at least `1 / size G`: the gap is a fraction with
denominator the number of constraints. -/
lemma inv_size_le_unsat (G : ConstraintGraph) (h : G.unsat ≠ 0) :
    1 / (G.size : ℚ) ≤ G.unsat := by
  obtain ⟨a, ha⟩ := G.exists_unsat_eq
  rw [ha] at h ⊢
  exact G.inv_size_le_unsatWith a h

/-- `G` is satisfiable exactly when its gap vanishes. -/
lemma unsat_eq_zero_iff (G : ConstraintGraph) :
    G.unsat = 0 ↔
      ∃ a : Fin G.n → Fin (G.q + 1), ∀ e ∈ G.edges, e.2.2 (a e.1) (a e.2.1) = true := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := G.exists_unsat_eq
    exact ⟨a, (G.unsatWith_eq_zero_iff a).mp (ha ▸ h)⟩
  · rintro ⟨a, ha⟩
    have h2 := G.unsat_le a
    rw [(G.unsatWith_eq_zero_iff a).mpr ha] at h2
    exact le_antisymm h2 G.unsat_nonneg

/-- The acceptance probability of the canonical two-query PCP verifier attached to `G`: it picks
a uniformly random constraint of `G`, queries the values that the alleged proof `a` assigns to the
two variables involved, and accepts iff the constraint is satisfied. -/
def accProb (G : ConstraintGraph) (a : Fin G.n → Fin (G.q + 1)) : ℚ :=
  (G.edges.countP (fun e => e.2.2 (a e.1) (a e.2.1)) : ℚ) / G.size

lemma accProb_eq_one_sub_unsatWith (G : ConstraintGraph) (a : Fin G.n → Fin (G.q + 1)) :
    G.accProb a = 1 - G.unsatWith a := by
  have hs : (G.size : ℚ) ≠ 0 := by exact_mod_cast (G.size_pos).ne'
  have hlen : G.size
      = G.edges.countP (fun e => e.2.2 (a e.1) (a e.2.1))
        + G.edges.countP (fun e => ! e.2.2 (a e.1) (a e.2.1)) := by
    have := List.length_eq_countP_add_countP (l := G.edges)
      (fun e => e.2.2 (a e.1) (a e.2.1))
    simpa [size, Bool.not_eq_true'] using this
  have hlen' : (G.size : ℚ)
      = (G.edges.countP (fun e => e.2.2 (a e.1) (a e.2.1)) : ℚ)
        + (G.edges.countP (fun e => ! e.2.2 (a e.1) (a e.2.1)) : ℚ) := by
    exact_mod_cast hlen
  unfold accProb unsatWith
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hs]
  exact hlen'.symm

/-- If every assignment violates the same fraction `c` of constraints, then the gap is `c`. -/
lemma unsat_eq_of_const (G : ConstraintGraph) (c : ℚ) (h : ∀ a, G.unsatWith a = c) :
    G.unsat = c := by
  refine le_antisymm ?_ (Finset.le_inf' _ _ (fun a _ => (h a).ge))
  have h0 := G.unsat_le (fun _ => 0)
  rwa [h] at h0

end ConstraintGraph

/-- A *gap amplification step* in the sense of Dinur: a size-linear transformation of constraint
graphs over a fixed alphabet which preserves perfect completeness and doubles the gap, until the
gap reaches the absolute constant `alpha`. -/
structure Amplifier where
  /-- the fixed alphabet size (alphabet `Fin (q0+1)`) -/
  q0 : ℕ
  /-- the linear size blow-up constant -/
  C : ℕ
  /-- the absolute constant that the gap is amplified to -/
  alpha : ℚ
  /-- `alpha` is positive -/
  alpha_pos : 0 < alpha
  /-- the amplification step -/
  step : ConstraintGraph → ConstraintGraph
  /-- the step preserves the alphabet -/
  step_alphabet : ∀ G, G.q = q0 → (step G).q = q0
  /-- the step blows up the size by at most a constant factor -/
  step_size : ∀ G, (step G).size ≤ C * G.size
  /-- the step doubles the gap, up to the ceiling `alpha` -/
  step_gap : ∀ G, G.q = q0 → min (2 * G.unsat) alpha ≤ (step G).unsat
  /-- the step preserves satisfiability -/
  step_complete : ∀ G, G.unsat = 0 → (step G).unsat = 0

namespace Amplifier

variable (A : Amplifier)

lemma iterate_alphabet (k : ℕ) (G : ConstraintGraph) (hG : G.q = A.q0) :
    (A.step^[k] G).q = A.q0 := by
  induction k with
  | zero => simpa using hG
  | succ k ih => rw [Function.iterate_succ_apply']; exact A.step_alphabet _ ih

lemma iterate_size (k : ℕ) (G : ConstraintGraph) :
    (A.step^[k] G).size ≤ A.C ^ k * G.size := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc (A.step (A.step^[k] G)).size
          ≤ A.C * (A.step^[k] G).size := A.step_size _
        _ ≤ A.C * (A.C ^ k * G.size) := Nat.mul_le_mul_left _ ih
        _ = A.C ^ (k + 1) * G.size := by ring

lemma iterate_complete (k : ℕ) (G : ConstraintGraph) (hG : G.unsat = 0) :
    (A.step^[k] G).unsat = 0 := by
  induction k with
  | zero => simpa using hG
  | succ k ih => rw [Function.iterate_succ_apply']; exact A.step_complete _ ih

/-- Iterating the amplification step `k` times multiplies the gap by `2^k`, up to the
ceiling `alpha`. -/
lemma iterate_gap (k : ℕ) (G : ConstraintGraph) (hG : G.q = A.q0) :
    min (2 ^ k * G.unsat) A.alpha ≤ (A.step^[k] G).unsat := by
  induction k with
  | zero => simp only [pow_zero, one_mul, Function.iterate_zero_apply]; exact min_le_left _ _
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine le_trans ?_ (A.step_gap _ (A.iterate_alphabet k G hG))
      rcases le_total (2 ^ k * G.unsat) A.alpha with h | h
      · rw [min_eq_left h] at ih
        refine le_min (min_le_of_left_le ?_) (min_le_right _ _)
        have hrw : (2:ℚ) ^ (k + 1) * G.unsat = 2 * (2 ^ k * G.unsat) := by ring
        rw [hrw]; linarith
      · refine le_trans (min_le_right _ _) ?_
        rw [min_eq_right h] at ih
        exact le_min (by linarith [A.alpha_pos]) le_rfl

end Amplifier

/-- An elementary arithmetic bound: `C ^ (log₂ N)` is polynomially bounded in `N`. -/
lemma pow_log_le_pow (C N : ℕ) : C ^ Nat.log 2 N ≤ (N + 1) ^ (Nat.log 2 C + 1) := by
  have h2 : (2:ℕ) ^ Nat.log 2 N ≤ N + 1 := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · simp [hN]
    · exact le_trans (Nat.pow_log_le_self 2 hN.ne') (Nat.le_succ N)
  have hC : C ≤ 2 ^ (Nat.log 2 C + 1) := (Nat.lt_pow_succ_log_self (by norm_num) C).le
  calc C ^ Nat.log 2 N ≤ (2 ^ (Nat.log 2 C + 1)) ^ Nat.log 2 N := Nat.pow_le_pow_left hC _
    _ = (2 ^ Nat.log 2 N) ^ (Nat.log 2 C + 1) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (N + 1) ^ (Nat.log 2 C + 1) := Nat.pow_le_pow_left h2 _

/-- **The PCP theorem in gap-CSP form, via Dinur's gap amplification.**

Given a gap amplification step `A` (Dinur's main technical lemma), there are constants `c`, `d`
such that every constraint graph `G` over the alphabet `Fin (A.q0 + 1)` can be transformed into a
constraint graph `G'` over the same alphabet, of size at most `c * (size G + 1) ^ d`, such that

* if `G` is satisfiable then so is `G'` (perfect completeness), and
* if `G` is unsatisfiable then *every* assignment to `G'` violates at least an `A.alpha` fraction
  of its constraints (soundness with an absolute constant gap).

Thus deciding satisfiability of constraint graphs reduces, in polynomial size, to distinguishing
satisfiable instances from instances with constant gap: the PCP theorem. -/
theorem pcp_dinur (A : Amplifier) :
    ∃ c d : ℕ, ∀ G : ConstraintGraph, G.q = A.q0 →
      ∃ G' : ConstraintGraph,
        G'.q = A.q0 ∧
        G'.size ≤ c * (G.size + 1) ^ d ∧
        (G.unsat = 0 → G'.unsat = 0) ∧
        (G.unsat ≠ 0 → A.alpha ≤ G'.unsat) := by
  set a : ℕ := ⌈A.alpha⌉₊ with ha
  set d : ℕ := Nat.log 2 A.C + 1 with hd
  refine ⟨A.C * (a + 1) ^ d, d + 1, ?_⟩
  intro G hG
  set m : ℕ := G.size with hm
  set N : ℕ := ⌈A.alpha * m⌉₊ with hN
  set k : ℕ := Nat.log 2 N + 1 with hk
  refine ⟨A.step^[k] G, A.iterate_alphabet k G hG, ?_, ?_, ?_⟩
  · -- size bound
    have h1 : (A.step^[k] G).size ≤ A.C ^ k * m := A.iterate_size k G
    have h2 : A.C ^ k = A.C * A.C ^ Nat.log 2 N := by rw [hk, pow_succ]; ring
    have h3 : A.C ^ Nat.log 2 N ≤ (N + 1) ^ d := pow_log_le_pow A.C N
    have hNa : N ≤ a * m := by
      rw [hN, Nat.ceil_le]
      push_cast
      exact mul_le_mul_of_nonneg_right (Nat.le_ceil A.alpha) (by positivity)
    have h4 : N + 1 ≤ (a + 1) * (m + 1) := by nlinarith [hNa, Nat.zero_le a, Nat.zero_le m]
    calc (A.step^[k] G).size ≤ A.C ^ k * m := h1
      _ = A.C * A.C ^ Nat.log 2 N * m := by rw [h2]
      _ ≤ A.C * (N + 1) ^ d * m := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
      _ ≤ A.C * ((a + 1) * (m + 1)) ^ d * (m + 1) := by
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h4 _))
            (Nat.le_succ m)
      _ = A.C * (a + 1) ^ d * ((m + 1) ^ d * (m + 1)) := by rw [Nat.mul_pow]; ring
      _ = A.C * (a + 1) ^ d * (m + 1) ^ (d + 1) := by ring
  · -- completeness
    exact fun h => A.iterate_complete k G h
  · -- soundness
    intro h
    have hgap := A.iterate_gap k G hG
    have hmpos : (0:ℚ) < m := by exact_mod_cast G.size_pos
    have hu : 1 / (m:ℚ) ≤ G.unsat := G.inv_size_le_unsat h
    -- `2 ^ k` exceeds `A.alpha * m`
    have hNlt : (N:ℚ) < 2 ^ k := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
      exact_mod_cast this
    have hle : A.alpha * m ≤ (N:ℚ) := by
      rw [hN]; exact_mod_cast Nat.le_ceil (A.alpha * m)
    have hkey : A.alpha ≤ 2 ^ k * G.unsat := by
      have h1 : A.alpha * m ≤ (2:ℚ) ^ k := le_of_lt (lt_of_le_of_lt hle hNlt)
      have h2 : (2:ℚ) ^ k * (1 / m) ≤ 2 ^ k * G.unsat := by
        have : (0:ℚ) < 2 ^ k := by positivity
        exact mul_le_mul_of_nonneg_left hu this.le
      have h3 : A.alpha ≤ (2:ℚ) ^ k * (1 / m) := by
        rw [mul_one_div, le_div_iff₀ hmpos]
        exact h1
      linarith
    rw [min_eq_right hkey] at hgap
    exact hgap

/-- **The PCP theorem, verifier formulation.**

Restating `CS.pcp_dinur` in terms of the canonical two-query verifier attached to a constraint
graph: satisfiability of constraint graphs reduces, with polynomial size blow-up, to a promise
problem for a verifier that reads only two symbols of the proof and has perfect completeness and
soundness error at most `1 - A.alpha`. -/
theorem pcp_dinur_verifier (A : Amplifier) :
    ∃ c d : ℕ, ∀ G : ConstraintGraph, G.q = A.q0 →
      ∃ G' : ConstraintGraph,
        G'.q = A.q0 ∧
        G'.size ≤ c * (G.size + 1) ^ d ∧
        ((∃ a : Fin G.n → Fin (G.q + 1), ∀ e ∈ G.edges, e.2.2 (a e.1) (a e.2.1) = true) →
          ∃ a' : Fin G'.n → Fin (G'.q + 1), G'.accProb a' = 1) ∧
        ((¬ ∃ a : Fin G.n → Fin (G.q + 1), ∀ e ∈ G.edges, e.2.2 (a e.1) (a e.2.1) = true) →
          ∀ a' : Fin G'.n → Fin (G'.q + 1), G'.accProb a' ≤ 1 - A.alpha) := by
  obtain ⟨c, d, hcd⟩ := pcp_dinur A
  refine ⟨c, d, fun G hG => ?_⟩
  obtain ⟨G', hq, hsize, hcomp, hsound⟩ := hcd G hG
  refine ⟨G', hq, hsize, ?_, ?_⟩
  · intro hsat
    have h0 : G'.unsat = 0 := hcomp (G.unsat_eq_zero_iff.mpr hsat)
    obtain ⟨a', ha'⟩ := G'.exists_unsat_eq
    refine ⟨a', ?_⟩
    rw [G'.accProb_eq_one_sub_unsatWith a', ← ha', h0, sub_zero]
  · intro hunsat a'
    have h0 : G.unsat ≠ 0 := fun h => hunsat (G.unsat_eq_zero_iff.mp h)
    have h1 : A.alpha ≤ G'.unsatWith a' := le_trans (hsound h0) (G'.unsat_le a')
    rw [G'.accProb_eq_one_sub_unsatWith a']
    linarith

/-- A one-variable, one-constraint instance whose single constraint is unsatisfiable. -/
def badGraph : ConstraintGraph := ⟨1, 0, [(0, 0, fun _ _ => false)], by simp⟩

/-- A one-variable, one-constraint instance whose single constraint is trivially satisfied. -/
def satGraph : ConstraintGraph := ⟨1, 0, [(0, 0, fun _ _ => true)], by simp⟩

lemma unsat_badGraph : badGraph.unsat = 1 := by
  refine ConstraintGraph.unsat_eq_of_const _ _ (fun a => ?_)
  simp [ConstraintGraph.unsatWith, ConstraintGraph.size, badGraph]

lemma unsat_satGraph : satGraph.unsat = 0 := by
  refine ConstraintGraph.unsat_eq_of_const _ _ (fun a => ?_)
  simp [ConstraintGraph.unsatWith, ConstraintGraph.size, satGraph]

/-- The hypothesis of `CS.pcp_dinur` is consistent: gap amplification steps exist (as purely
combinatorial objects; the content of Dinur's theorem, not modelled here, is that one exists
which is moreover computable in polynomial time). -/
lemma amplifier_nonempty : Nonempty Amplifier := by
  refine ⟨{ q0 := 0, C := 1, alpha := 1, alpha_pos := one_pos,
            step := fun G => if G.unsat = 0 then satGraph else badGraph,
            step_alphabet := ?_, step_size := ?_, step_gap := ?_, step_complete := ?_ }⟩
  · intro G _
    by_cases h : G.unsat = 0 <;> simp [h, satGraph, badGraph]
  · intro G
    have hG : 1 ≤ G.size := G.size_pos
    rcases eq_or_ne G.unsat 0 with h | h
    · rw [if_pos h]
      simpa [satGraph, ConstraintGraph.size] using hG
    · rw [if_neg h]
      simpa [badGraph, ConstraintGraph.size] using hG
  · intro G _
    rcases eq_or_ne G.unsat 0 with h | h
    · rw [if_pos h, unsat_satGraph, h]
      simp
    · rw [if_neg h, unsat_badGraph]
      exact min_le_right _ _
  · intro G h
    simp [h, unsat_satGraph]

end CS

