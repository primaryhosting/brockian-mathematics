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

/-!
## Constraint graphs (binary CSPs)

Dinur's proof of the PCP theorem is phrased in terms of *constraint graphs*: binary
constraint satisfaction problems whose variables are the vertices of a graph and whose
constraints sit on the edges.  We model such an instance by

* a number `n` of variables, indexed by `Fin n`;
* an alphabet `Fin q` with `q > 0`;
* a list `cs` of constraints, each a triple `(u, v, R)` with `u v : Fin n` and
  `R : Fin q → Fin q → Bool`.

An assignment is a map `Fin n → Fin q`, and the *unsat value* `UNSAT G` is the minimum,
over all assignments, of the fraction of constraints that are violated.
-/

/-- A binary constraint satisfaction instance ("constraint graph"): `n` variables taking
values in an alphabet of size `q > 0`, subject to a list of binary constraints. -/
structure ConstraintGraph where
  /-- Number of variables. -/
  n : ℕ
  /-- Size of the alphabet. -/
  q : ℕ
  /-- The alphabet is nonempty. -/
  hq : 0 < q
  /-- The list of constraints, each relating two variables. -/
  cs : List (Fin n × Fin n × (Fin q → Fin q → Bool))

namespace ConstraintGraph

variable (G : ConstraintGraph)

/-- The "all-zero" assignment; it exists because the alphabet is nonempty. -/
def baseAssign : Fin G.n → Fin G.q := fun _ => ⟨0, G.hq⟩

/-- The size of a constraint graph: number of variables plus number of constraints. -/
def size : ℕ := G.n + G.cs.length

/-- Whether an assignment satisfies a given constraint. -/
def satC (a : Fin G.n → Fin G.q) (c : Fin G.n × Fin G.n × (Fin G.q → Fin G.q → Bool)) :
    Bool := c.2.2 (a c.1) (a c.2.1)

/-- The number of constraints violated by an assignment. -/
def unsatCount (a : Fin G.n → Fin G.q) : ℕ := G.cs.countP (fun c => !(G.satC a c))

/-- The fraction of constraints violated by an assignment (defined to be `0` when there
are no constraints). -/
def unsatFrac (a : Fin G.n → Fin G.q) : ℚ := (G.unsatCount a : ℚ) / (G.cs.length : ℚ)

/-- The set of achievable unsat fractions is nonempty. -/
lemma image_unsatFrac_nonempty :
    (Finset.univ.image (G.unsatFrac)).Nonempty :=
  ⟨G.unsatFrac G.baseAssign, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

/-- `UNSAT G` is the minimum over all assignments of the fraction of violated constraints.
This is the quantity that Dinur's gap amplification step doubles. -/
noncomputable def UNSAT : ℚ :=
  (Finset.univ.image (G.unsatFrac)).min' G.image_unsatFrac_nonempty

/-- An instance is satisfiable if some assignment satisfies all constraints. -/
def Satisfiable : Prop := ∃ a : Fin G.n → Fin G.q, ∀ c ∈ G.cs, G.satC a c = true

variable {G}

lemma unsatCount_le (a : Fin G.n → Fin G.q) : G.unsatCount a ≤ G.cs.length :=
  List.countP_le_length

lemma unsatFrac_nonneg (a : Fin G.n → Fin G.q) : 0 ≤ G.unsatFrac a := by
  unfold unsatFrac
  positivity

lemma unsatFrac_le_one (a : Fin G.n → Fin G.q) : G.unsatFrac a ≤ 1 := by
  unfold unsatFrac
  rcases Nat.eq_zero_or_pos G.cs.length with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast unsatCount_le a

/-- `UNSAT G` is attained by some assignment. -/
lemma exists_unsatFrac_eq_UNSAT : ∃ a : Fin G.n → Fin G.q, G.UNSAT = G.unsatFrac a := by
  have h := Finset.min'_mem _ G.image_unsatFrac_nonempty
  rw [Finset.mem_image] at h
  obtain ⟨a, -, ha⟩ := h
  exact ⟨a, ha.symm⟩

lemma UNSAT_le (a : Fin G.n → Fin G.q) : G.UNSAT ≤ G.unsatFrac a :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))

lemma UNSAT_nonneg (G : ConstraintGraph) : 0 ≤ G.UNSAT := by
  obtain ⟨a, ha⟩ := (exists_unsatFrac_eq_UNSAT (G := G))
  rw [ha]; exact unsatFrac_nonneg a

lemma UNSAT_le_one (G : ConstraintGraph) : G.UNSAT ≤ 1 :=
  le_trans (UNSAT_le G.baseAssign) (unsatFrac_le_one _)

/-- Perfect completeness: the unsat value vanishes exactly on satisfiable instances. -/
lemma UNSAT_eq_zero_iff : G.UNSAT = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (exists_unsatFrac_eq_UNSAT (G := G))
    rcases Nat.eq_zero_or_pos G.cs.length with hm | hm
    · refine ⟨G.baseAssign, ?_⟩
      intro c hc
      exact absurd (List.length_pos_of_mem hc) (by omega)
    · refine ⟨a, ?_⟩
      have hne : (G.cs.length : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h0 : G.unsatFrac a = 0 := ha.symm.trans h
      rw [unsatFrac, div_eq_zero_iff] at h0
      have hz : G.unsatCount a = 0 := by
        rcases h0 with h0 | h0
        · exact_mod_cast h0
        · exact absurd h0 hne
      unfold unsatCount at hz
      rw [List.countP_eq_zero] at hz
      intro c hc
      have := hz c hc
      simpa using this
  · rintro ⟨a, ha⟩
    have hz : G.unsatCount a = 0 := by
      unfold unsatCount
      rw [List.countP_eq_zero]
      intro c hc
      simp [ha c hc]
    have : G.unsatFrac a = 0 := by simp [unsatFrac, hz]
    exact le_antisymm (this ▸ UNSAT_le a) G.UNSAT_nonneg

/-- If the unsat value is positive then there is at least one constraint. -/
lemma cs_length_pos_of_UNSAT_pos (h : 0 < G.UNSAT) : 0 < G.cs.length := by
  by_contra hc
  have hlen : G.cs.length = 0 := by omega
  have : G.unsatFrac G.baseAssign = 0 := by simp [unsatFrac, hlen]
  exact absurd (le_trans (UNSAT_le G.baseAssign) (le_of_eq this)) (by linarith)

/-- The key "discreteness" fact used to start the amplification: a nonzero unsat value is
at least the reciprocal of the number of constraints. -/
lemma one_div_le_UNSAT (h : 0 < G.UNSAT) : 1 / (G.cs.length : ℚ) ≤ G.UNSAT := by
  obtain ⟨a, ha⟩ := (exists_unsatFrac_eq_UNSAT (G := G))
  have hm : 0 < G.cs.length := cs_length_pos_of_UNSAT_pos h
  have hmQ : (0 : ℚ) < (G.cs.length : ℚ) := by exact_mod_cast hm
  have hpos : 0 < (G.unsatCount a : ℚ) / (G.cs.length : ℚ) := by
    rw [← unsatFrac, ← ha]; exact h
  have hc1 : 1 ≤ (G.unsatCount a : ℚ) := by
    by_contra hcon
    push_neg at hcon
    have : G.unsatCount a = 0 := by
      have : (G.unsatCount a : ℚ) < 1 := hcon
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    simp [this] at hpos
  rw [ha, unsatFrac]
  exact (div_le_div_iff_of_pos_right hmQ).mpr hc1

end ConstraintGraph

open ConstraintGraph

/-!
## Dinur's gap amplification, iterated

Dinur's *Main Lemma* provides, for a fixed alphabet size `q₀`, a transformation `amp` of
constraint graphs with:

* linear size blow-up: `size (amp G) ≤ C * size G`;
* perfect completeness: `amp G` is satisfiable whenever `G` is;
* gap amplification: `UNSAT (amp G) ≥ min (2 * UNSAT G) α` for a fixed constant `α > 0`.

The PCP theorem follows by iterating `amp` a logarithmic number of times.  The lemmas
below carry out this iteration, and `CS.pcp_dinur` records the resulting statement.
-/

section Amplification

variable (amp : ConstraintGraph → ConstraintGraph) (C : ℕ) (α : ℚ)

/-- Iterating the size bound. -/
lemma size_iterate_le (hsize : ∀ G, size (amp G) ≤ C * size G) (k : ℕ) (G : ConstraintGraph) :
    size (amp^[k] G) ≤ C ^ k * size G := by
  induction k generalizing G with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      calc size (amp^[k] (amp G)) ≤ C ^ k * size (amp G) := ih _
        _ ≤ C ^ k * (C * size G) := by
              exact Nat.mul_le_mul_left _ (hsize G)
        _ = C ^ (k + 1) * size G := by ring

/-- Iterating perfect completeness. -/
lemma UNSAT_iterate_eq_zero (hcomp : ∀ G, UNSAT G = 0 → UNSAT (amp G) = 0)
    (k : ℕ) (G : ConstraintGraph) (hG : UNSAT G = 0) : UNSAT (amp^[k] G) = 0 := by
  induction k generalizing G with
  | zero => simpa using hG
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ (hcomp G hG)

/-- Iterating the gap amplification step: after `k` rounds the gap has been doubled `k`
times, capped at the constant `α`. -/
lemma UNSAT_iterate_ge (hα : 0 ≤ α)
    (hgap : ∀ G, min (2 * UNSAT G) α ≤ UNSAT (amp G))
    (k : ℕ) (G : ConstraintGraph) :
    min (2 ^ k * UNSAT G) α ≤ UNSAT (amp^[k] G) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine le_trans ?_ (hgap (amp^[k] G))
      have hpow : (2 : ℚ) ^ (k + 1) * UNSAT G = 2 * (2 ^ k * UNSAT G) := by ring
      rw [le_min_iff]
      refine ⟨?_, min_le_right _ _⟩
      rcases le_total ((2 : ℚ) ^ k * UNSAT G) α with h | h
      · rw [min_eq_left h] at ih
        have h1 : min ((2 : ℚ) ^ (k + 1) * UNSAT G) α ≤ 2 ^ (k + 1) * UNSAT G :=
          min_le_left _ _
        linarith
      · rw [min_eq_right h] at ih
        have h1 : min ((2 : ℚ) ^ (k + 1) * UNSAT G) α ≤ α := min_le_right _ _
        linarith

end Amplification

/-!
## The PCP theorem via gap amplification
-/

/--
**Dinur's gap-amplification proof of the PCP theorem.**

Assume Dinur's *Main Lemma*: there are a constant alphabet size `q₀`, a size-blow-up
constant `C`, a gap constant `α > 0`, and a transformation `amp` of binary constraint
graphs such that for every instance `G`:

* `amp G` uses the fixed alphabet `Fin q₀`;
* `size (amp G) ≤ C * size G` (linear size blow-up);
* `amp G` is satisfiable whenever `G` is (perfect completeness);
* `UNSAT (amp G) ≥ min (2 * UNSAT G, α)` (gap amplification).

Then, for every constraint graph `G` and every `k` with `α * size G ≤ 2 ^ k` — i.e. for
`k` logarithmic in the size of `G` — one obtains an instance `G'` over the fixed alphabet
`Fin q₀` of size at most `C ^ (k+1) * size G` (polynomial in `size G`, since `k` is
logarithmic) which is satisfiable if `G` is, and whose unsat value is at least the
constant `α` whenever `G` is unsatisfiable.

This is exactly the gap-CSP form of the PCP theorem: deciding satisfiability of `G`
reduces to distinguishing `UNSAT G' = 0` from `UNSAT G' ≥ α`, a constant gap.
-/
theorem pcp_dinur
    (q₀ C : ℕ) (α : ℚ) (hα : 0 < α)
    (amp : ConstraintGraph → ConstraintGraph)
    (hq : ∀ G : ConstraintGraph, (amp G).q = q₀)
    (hsize : ∀ G : ConstraintGraph, size (amp G) ≤ C * size G)
    (hcomp : ∀ G : ConstraintGraph, UNSAT G = 0 → UNSAT (amp G) = 0)
    (hgap : ∀ G : ConstraintGraph, min (2 * UNSAT G) α ≤ UNSAT (amp G))
    (G : ConstraintGraph) (k : ℕ) (hk : α * (size G : ℚ) ≤ 2 ^ k) :
    ∃ G' : ConstraintGraph,
      G'.q = q₀ ∧
      size G' ≤ C ^ (k + 1) * size G ∧
      (G.Satisfiable → G'.Satisfiable) ∧
      (¬ G.Satisfiable → α ≤ UNSAT G') := by
  refine ⟨amp^[k + 1] G, ?_, ?_, ?_, ?_⟩
  · rw [Function.iterate_succ_apply']
    exact hq _
  · exact size_iterate_le amp C hsize (k + 1) G
  · intro hS
    rw [← UNSAT_eq_zero_iff] at hS ⊢
    exact UNSAT_iterate_eq_zero amp hcomp (k + 1) G hS
  · intro hS
    have hpos : 0 < UNSAT G := by
      rcases lt_or_eq_of_le G.UNSAT_nonneg with h | h
      · exact h
      · exact absurd (UNSAT_eq_zero_iff.mp h.symm) hS
    -- `UNSAT G ≥ 1 / (number of constraints) ≥ 1 / size G`
    have hmpos : 0 < G.cs.length := cs_length_pos_of_UNSAT_pos hpos
    have hlen_le : (G.cs.length : ℚ) ≤ (size G : ℚ) := by
      have : G.cs.length ≤ size G := by unfold size; omega
      exact_mod_cast this
    have hsizepos : (0 : ℚ) < (size G : ℚ) := by
      have : 0 < size G := by unfold size; omega
      exact_mod_cast this
    have hone : 1 / (size G : ℚ) ≤ UNSAT G := by
      refine le_trans ?_ (one_div_le_UNSAT hpos)
      exact one_div_le_one_div_of_le (by exact_mod_cast hmpos) hlen_le
    -- hence `2 ^ (k+1) * UNSAT G ≥ α`
    have hbig : α ≤ 2 ^ (k + 1) * UNSAT G := by
      have h1 : α ≤ 2 ^ k * (1 / (size G : ℚ)) := by
        rw [mul_one_div, le_div_iff₀ hsizepos]
        linarith [hk]
      have h2 : (2 : ℚ) ^ k * (1 / (size G : ℚ)) ≤ 2 ^ k * UNSAT G := by
        have h2k : (0:ℚ) ≤ 2 ^ k := by positivity
        exact mul_le_mul_of_nonneg_left hone h2k
      have h3 : (2 : ℚ) ^ k * UNSAT G ≤ 2 ^ (k + 1) * UNSAT G := by
        have hU : (0:ℚ) ≤ UNSAT G := G.UNSAT_nonneg
        have h2k : (0:ℚ) ≤ 2 ^ k := by positivity
        have e : (2:ℚ) ^ (k + 1) * UNSAT G = 2 ^ k * UNSAT G + 2 ^ k * UNSAT G := by ring
        nlinarith
      linarith
    have := UNSAT_iterate_ge amp α (le_of_lt hα) hgap (k + 1) G
    rw [min_eq_right hbig] at this
    exact this

/--
The same conclusion with an explicit, logarithmic number of amplification rounds:
`k = ⌈log₂ ⌈α · size G⌉⌉`.  Since the size grows by a factor `C` per round, the resulting
instance has size `C ^ O(log (size G)) · size G`, i.e. polynomial in `size G`.
-/
theorem pcp_dinur_log_rounds
    (q₀ C : ℕ) (α : ℚ) (hα : 0 < α)
    (amp : ConstraintGraph → ConstraintGraph)
    (hq : ∀ G : ConstraintGraph, (amp G).q = q₀)
    (hsize : ∀ G : ConstraintGraph, size (amp G) ≤ C * size G)
    (hcomp : ∀ G : ConstraintGraph, UNSAT G = 0 → UNSAT (amp G) = 0)
    (hgap : ∀ G : ConstraintGraph, min (2 * UNSAT G) α ≤ UNSAT (amp G))
    (G : ConstraintGraph) :
    ∃ G' : ConstraintGraph,
      G'.q = q₀ ∧
      size G' ≤ C ^ (Nat.clog 2 ⌈α * (size G : ℚ)⌉₊ + 1) * size G ∧
      (G.Satisfiable → G'.Satisfiable) ∧
      (¬ G.Satisfiable → α ≤ UNSAT G') := by
  refine pcp_dinur q₀ C α hα amp hq hsize hcomp hgap G _ ?_
  calc α * (size G : ℚ) ≤ (⌈α * (size G : ℚ)⌉₊ : ℚ) := Nat.le_ceil _
    _ ≤ ((2 ^ Nat.clog 2 ⌈α * (size G : ℚ)⌉₊ : ℕ) : ℚ) := by
        exact_mod_cast Nat.le_pow_clog one_lt_two _
    _ = 2 ^ Nat.clog 2 ⌈α * (size G : ℚ)⌉₊ := by push_cast; ring

end CS

