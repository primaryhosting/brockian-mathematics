/-
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
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

namespace Frontier

/-- An *information partition* of a (finite) state space `Ω`: to each state `ω` it assigns the
cell `cell ω` of states that the agent cannot distinguish from `ω`.  The two axioms say that
`ω` always lies in its own cell and that the cells genuinely form a partition (two cells that
meet are equal). -/
structure InfoPartition (Ω : Type*) [DecidableEq Ω] where
  /-- The information cell of a state. -/
  cell : Ω → Finset Ω
  /-- Every state belongs to its own cell. -/
  mem_cell : ∀ ω : Ω, ω ∈ cell ω
  /-- Cells that overlap coincide, so the cells form a partition of `Ω`. -/
  cell_eq_of_mem : ∀ ω ω' : Ω, ω' ∈ cell ω → cell ω' = cell ω

/-- **Key aggregation lemma.**  Let `M` be a set of states that is a union of cells of the
information partition `cell` (i.e. `M` is closed under `cell`).  If on every cell inside `M`
the conditional weight of `E` equals `q` (written multiplicatively as
`p (E ∩ C) = q * p C`), then the same holds for `M` itself.

This is the "the posterior is a weighted average of the posteriors on the cells" step of
Aumann's argument. -/
theorem sum_inter_eq_of_cells
    {Ω : Type*} [DecidableEq Ω] (p : Ω → ℝ) (I : InfoPartition Ω) (E : Finset Ω) (q : ℝ) :
    ∀ (n : ℕ) (M : Finset Ω), M.card ≤ n → (∀ ω ∈ M, I.cell ω ⊆ M) →
      (∀ ω ∈ M, ∑ x ∈ I.cell ω ∩ E, p x = q * ∑ x ∈ I.cell ω, p x) →
      ∑ x ∈ M ∩ E, p x = q * ∑ x ∈ M, p x := by
  intro n
  induction n with
  | zero =>
      intro M hcard _ _
      have hM : M = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst hM
      simp
  | succ n ih =>
      intro M hcard hclosed hpost
      rcases Finset.eq_empty_or_nonempty M with hM | ⟨ω, hω⟩
      · subst hM; simp
      · set C : Finset Ω := I.cell ω with hC
        have hCM : C ⊆ M := hclosed ω hω
        set M' : Finset Ω := M \ C with hM'
        -- `ω` is removed, so the cardinality strictly drops
        have hωC : ω ∈ C := I.mem_cell ω
        have hcard' : M'.card ≤ n := by
          have h1 : M'.card < M.card := by
            apply Finset.card_lt_card
            refine ⟨Finset.sdiff_subset, ?_⟩
            intro hsub
            have := hsub hω
            simp [hM', hωC] at this
          omega
        -- `M'` is again closed under the partition
        have hclosed' : ∀ ω' ∈ M', I.cell ω' ⊆ M' := by
          intro ω' hω' x hx
          have hω'M : ω' ∈ M := (Finset.mem_sdiff.mp hω').1
          have hω'C : ω' ∉ C := (Finset.mem_sdiff.mp hω').2
          have hxM : x ∈ M := hclosed ω' hω'M hx
          refine Finset.mem_sdiff.mpr ⟨hxM, ?_⟩
          intro hxC
          -- if `x ∈ C` then `cell ω' = cell x = C`, so `ω' ∈ C`, contradiction
          have h1 : I.cell x = C := I.cell_eq_of_mem ω x hxC
          have h2 : I.cell x = I.cell ω' := I.cell_eq_of_mem ω' x hx
          exact hω'C (h1 ▸ h2 ▸ I.mem_cell ω')
        have hpost' : ∀ ω' ∈ M', ∑ x ∈ I.cell ω' ∩ E, p x = q * ∑ x ∈ I.cell ω', p x :=
          fun ω' hω' => hpost ω' (Finset.mem_sdiff.mp hω').1
        have hIH : ∑ x ∈ M' ∩ E, p x = q * ∑ x ∈ M', p x := ih M' hcard' hclosed' hpost'
        -- split the sums over `M` into the cell `C` and the rest `M'`
        have hsplit : ∑ x ∈ M', p x + ∑ x ∈ C, p x = ∑ x ∈ M, p x :=
          Finset.sum_sdiff hCM
        have hCE : C ∩ E ⊆ M ∩ E := Finset.inter_subset_inter_right hCM
        have hset : (M ∩ E) \ (C ∩ E) = M' ∩ E := by
          ext x
          simp only [hM', Finset.mem_sdiff, Finset.mem_inter]
          tauto
        have hsplitE : ∑ x ∈ M' ∩ E, p x + ∑ x ∈ C ∩ E, p x = ∑ x ∈ M ∩ E, p x := by
          rw [← hset]; exact Finset.sum_sdiff hCE
        rw [← hsplitE, hIH, hpost ω hω, ← hsplit]
        ring

/-- **Aumann's agreement theorem** (finite, combinatorial form).

Two agents share a common prior `p` on a finite state space `Ω`, and each has an information
partition `I₁`, `I₂`.  Let `M` be a *common-knowledge event*: a set of states closed under both
partitions (equivalently, a cell of the meet of the two partitions).  Suppose that throughout
`M` agent 1's posterior probability of the event `E` is constantly `q₁` and agent 2's is
constantly `q₂` — i.e. the posteriors are common knowledge.  If `M` has positive prior
probability, then `q₁ = q₂`: the agents cannot agree to disagree.

Posteriors are the genuine conditional probabilities `p (E ∩ cell ω) / p (cell ω)`, and each
cell inside `M` is assumed to have positive prior probability so that conditioning is
meaningful.  No normalisation `∑ p = 1` is required: the argument only uses additivity of `p`,
so the statement is given for an arbitrary common weighting `p`. -/
theorem aumann_agreement
    {Ω : Type*} [DecidableEq Ω] (p : Ω → ℝ)
    (I₁ I₂ : InfoPartition Ω) (E M : Finset Ω)
    -- `M` is common knowledge: it is a union of cells of each agent
    (hM₁ : ∀ ω ∈ M, I₁.cell ω ⊆ M) (hM₂ : ∀ ω ∈ M, I₂.cell ω ⊆ M)
    -- conditioning is well defined
    (hpos₁ : ∀ ω ∈ M, 0 < ∑ x ∈ I₁.cell ω, p x) (hpos₂ : ∀ ω ∈ M, 0 < ∑ x ∈ I₂.cell ω, p x)
    (hMpos : 0 < ∑ x ∈ M, p x)
    -- the posteriors are common knowledge on `M`
    (q₁ q₂ : ℝ)
    (hq₁ : ∀ ω ∈ M, (∑ x ∈ I₁.cell ω ∩ E, p x) / (∑ x ∈ I₁.cell ω, p x) = q₁)
    (hq₂ : ∀ ω ∈ M, (∑ x ∈ I₂.cell ω ∩ E, p x) / (∑ x ∈ I₂.cell ω, p x) = q₂) :
    q₁ = q₂ := by
  have hmul₁ : ∀ ω ∈ M, ∑ x ∈ I₁.cell ω ∩ E, p x = q₁ * ∑ x ∈ I₁.cell ω, p x := by
    intro ω hω
    have h := hq₁ ω hω
    field_simp [(hpos₁ ω hω).ne'] at h
    linarith [h]
  have hmul₂ : ∀ ω ∈ M, ∑ x ∈ I₂.cell ω ∩ E, p x = q₂ * ∑ x ∈ I₂.cell ω, p x := by
    intro ω hω
    have h := hq₂ ω hω
    field_simp [(hpos₂ ω hω).ne'] at h
    linarith [h]
  have h1 : ∑ x ∈ M ∩ E, p x = q₁ * ∑ x ∈ M, p x :=
    sum_inter_eq_of_cells p I₁ E q₁ M.card M le_rfl hM₁ hmul₁
  have h2 : ∑ x ∈ M ∩ E, p x = q₂ * ∑ x ∈ M, p x :=
    sum_inter_eq_of_cells p I₂ E q₂ M.card M le_rfl hM₂ hmul₂
  have : q₁ * ∑ x ∈ M, p x = q₂ * ∑ x ∈ M, p x := by rw [← h1, ← h2]
  exact mul_right_cancel₀ hMpos.ne' this

/-! ### A non-vacuity witness

We exhibit a concrete situation in which all the hypotheses of `Frontier.aumann_agreement`
hold with genuinely *different* information partitions and a non-trivial posterior:
four equally likely states, agent 1 knows only whether the state lies in `{0,1}` or `{2,3}`,
agent 2 knows only whether it lies in `{0,3}` or `{1,2}`, and `E = {0,2}`.  Both posteriors
are `1/2` everywhere, and the theorem indeed returns `1/2 = 1/2`. -/

namespace Example

/-- Agent 1's information partition of `Fin 4`: the cells are `{0,1}` and `{2,3}`. -/
def cell₁ : Fin 4 → Finset (Fin 4) := fun ω => if ω.val < 2 then {0, 1} else {2, 3}

/-- Agent 2's information partition of `Fin 4`: the cells are `{0,3}` and `{1,2}`. -/
def cell₂ : Fin 4 → Finset (Fin 4) := fun ω => if ω = 0 ∨ ω = 3 then {0, 3} else {1, 2}

/-- Agent 1's partition, packaged as an `InfoPartition`. -/
def part₁ : InfoPartition (Fin 4) where
  cell := cell₁
  mem_cell := by decide
  cell_eq_of_mem := by decide

/-- Agent 2's partition, packaged as an `InfoPartition`. -/
def part₂ : InfoPartition (Fin 4) where
  cell := cell₂
  mem_cell := by decide
  cell_eq_of_mem := by decide

/-- All hypotheses of `Frontier.aumann_agreement` are satisfiable with distinct partitions
and a non-trivial common posterior value `1/2`. -/
example :
    (1 : ℝ) / 2 = 1 / 2 := by
  refine aumann_agreement (p := fun _ => (1 / 4 : ℝ)) part₁ part₂ {0, 2} Finset.univ
    (fun _ _ => Finset.subset_univ _) (fun _ _ => Finset.subset_univ _) ?_ ?_ ?_ (1 / 2) (1 / 2)
    ?_ ?_
  · intro ω _
    have h : (part₁.cell ω).card = 2 := by revert ω; decide
    rw [Finset.sum_const, h]; norm_num
  · intro ω _
    have h : (part₂.cell ω).card = 2 := by revert ω; decide
    rw [Finset.sum_const, h]; norm_num
  · rw [Finset.sum_const, Finset.card_univ]; norm_num
  · intro ω _
    have h : (part₁.cell ω ∩ ({0, 2} : Finset (Fin 4))).card = 1 ∧ (part₁.cell ω).card = 2 := by
      revert ω; decide
    rw [Finset.sum_const, Finset.sum_const, h.1, h.2]; norm_num
  · intro ω _
    have h : (part₂.cell ω ∩ ({0, 2} : Finset (Fin 4))).card = 1 ∧ (part₂.cell ω).card = 2 := by
      revert ω; decide
    rw [Finset.sum_const, Finset.sum_const, h.1, h.2]; norm_num

end Example

end Frontier

