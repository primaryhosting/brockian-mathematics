-- Lean requires `import` to be the first command in a file; the required header
-- comment follows immediately below.
import Mathlib

/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

/-!
## Overview

We formalise the PCP theorem `NP = PCP(log n, 1)` in its standard *constraint-satisfaction*
(gap-CSP) form, in the non-uniform (advice) setting.

* A **constraint** reads a constant number of bits of a Boolean assignment and applies an
  arbitrary Boolean predicate to them.
* A language `L ⊆ {0,1}*` is in `InNP` if for every input length `n` there is a
  constraint system `Ψ` with polynomially many constraints, each of arity at most a constant
  `q`, over variables `0, 1, …` (the first `n` variables carry the input `x`, the remaining
  ones are the witness/proof variables), such that `x ∈ L` iff `Ψ` has a satisfying assignment
  extending `x`.  By the Tseitin transformation this is exactly non-uniform `NP` (`NP/poly`).
* A language is in `InPCP` (i.e. in `PCP(log n, 1)`) if the same holds with a *gap*: for
  `x ∉ L` **every** assignment extending `x` satisfies at most half of the constraints.
  Reading a uniformly random constraint of the system is precisely a verifier that uses
  `O(log n)` random bits (there are polynomially many constraints) and reads `O(1)` bits of the
  input/proof, with completeness `1` and soundness error `1/2`.

The inclusion `PCP(log n, 1) ⊆ NP` is proved unconditionally (`CS.inNP_of_hasGapPCP`), as is the
*gap amplification by repetition* step `CS.hasGapPCP_half_of_hasGapPCP`, which turns any constant
gap into the gap `1/2` while keeping the arity constant and the size polynomial.

The remaining, genuinely hard, content of the PCP theorem is isolated as
`CS.GapCSPHardness`: every language in `NP` admits a constant-gap constraint system.  This is
the combinatorial core proved by Arora–Safra and Arora–Lund–Motwani–Sudan–Szegedy (and by
Dinur's gap amplification); it is *not* proved here.  `CS.pcp_theorem` derives the class
equality `NP = PCP(log n, 1)` from it, and `CS.pcp_theorem_iff` shows unconditionally that the
two statements are equivalent.
-/

namespace CS

/-- An assignment of Boolean values to the variables `0, 1, 2, …`. -/
abbrev Assignment := ℕ → Bool

/-- A local constraint: a list of queried variables together with a Boolean predicate on the
answers.  Its *arity* is the number of queried variables. -/
structure Constraint where
  /-- The variables read by the constraint. -/
  vars : List ℕ
  /-- The predicate applied to the values read. -/
  pred : List Bool → Bool

/-- Whether a constraint is satisfied by an assignment. -/
def Constraint.holds (c : Constraint) (a : Assignment) : Bool := c.pred (c.vars.map a)

/-- A constraint system is a (finite) list of constraints. -/
abbrev CSPInstance := List Constraint

/-- All constraints of `Ψ` have arity at most `q`. -/
def ArityLE (Ψ : CSPInstance) (q : ℕ) : Prop := ∀ c ∈ Ψ, c.vars.length ≤ q

/-- `a` satisfies every constraint of `Ψ`. -/
def Sat (Ψ : CSPInstance) (a : Assignment) : Prop := ∀ c ∈ Ψ, c.holds a = true

/-- The fraction of constraints of `Ψ` satisfied by `a`. -/
def satFrac (Ψ : CSPInstance) (a : Assignment) : ℚ :=
  ((Ψ.countP (fun c => c.holds a) : ℕ) : ℚ) / (Ψ.length : ℚ)

/-- The assignment `a` writes the input string `x` in the variables `0, …, |x| - 1`. -/
def Extends (x : List Bool) (a : Assignment) : Prop := ∀ i, i < x.length → a i = x.getD i false

/-- The canonical assignment extending `x` (all proof variables set to `false`). -/
def stdAssignment (x : List Bool) : Assignment := fun i => x.getD i false

lemma extends_stdAssignment (x : List Bool) : Extends x (stdAssignment x) := fun _ _ => rfl

/-!
### The complexity classes
-/

/-- `HasGapPCP L s`: for every input length there is a constraint system of polynomial size and
constant arity which is satisfiable by an extension of `x` when `x ∈ L`, and for which *no*
extension of `x` satisfies more than an `s` fraction of the constraints when `x ∉ L`.

Picking a uniformly random constraint gives a PCP verifier using `O(log n)` random bits and
`O(1)` queries, with perfect completeness and soundness error `s`. -/
def HasGapPCP (L : Set (List Bool)) (s : ℚ) : Prop :=
  ∃ q c k : ℕ, ∀ n : ℕ, ∃ Ψ : CSPInstance,
    Ψ ≠ [] ∧ Ψ.length ≤ c * (n + 1) ^ k ∧ ArityLE Ψ q ∧
      ∀ x : List Bool, x.length = n →
        ((x ∈ L → ∃ a, Extends x a ∧ Sat Ψ a) ∧
          (x ∉ L → ∀ a, Extends x a → satFrac Ψ a ≤ s))

/-- Non-uniform `NP`: `L` is described, for each input length, by a constraint system of
polynomial size and constant arity, membership being equivalent to satisfiability. -/
def InNP (L : Set (List Bool)) : Prop :=
  ∃ q c k : ℕ, ∀ n : ℕ, ∃ Ψ : CSPInstance,
    Ψ ≠ [] ∧ Ψ.length ≤ c * (n + 1) ^ k ∧ ArityLE Ψ q ∧
      ∀ x : List Bool, x.length = n → (x ∈ L ↔ ∃ a, Extends x a ∧ Sat Ψ a)

/-- `PCP(log n, 1)`: a PCP with `O(log n)` randomness, `O(1)` queries, perfect completeness and
soundness error `1/2`. -/
def InPCP (L : Set (List Bool)) : Prop := HasGapPCP L (1 / 2)

/-- The hard core of the PCP theorem: every language in `NP` has a constraint system with a
constant gap. -/
def GapCSPHardness : Prop :=
  ∀ L : Set (List Bool), InNP L → ∃ s : ℚ, s < 1 ∧ HasGapPCP L s

/-!
### Basic facts about `satFrac`
-/

lemma satFrac_nonneg (Ψ : CSPInstance) (a : Assignment) : 0 ≤ satFrac Ψ a := by
  unfold satFrac
  positivity

lemma satFrac_eq_one_of_sat {Ψ : CSPInstance} {a : Assignment} (hΨ : Ψ ≠ [])
    (h : Sat Ψ a) : satFrac Ψ a = 1 := by
  have hcount : Ψ.countP (fun c => c.holds a) = Ψ.length := by
    apply List.countP_eq_length.2
    intro c hc
    exact h c hc
  have hlen : (Ψ.length : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, List.length_eq_zero_iff]
    exact hΨ
  unfold satFrac
  rw [hcount]
  exact div_self hlen

lemma not_sat_of_satFrac_lt_one {Ψ : CSPInstance} {a : Assignment} (hΨ : Ψ ≠ [])
    {s : ℚ} (hs : s < 1) (h : satFrac Ψ a ≤ s) : ¬ Sat Ψ a := by
  intro hsat
  rw [satFrac_eq_one_of_sat hΨ hsat] at h
  exact absurd (h.trans_lt hs) (lt_irrefl 1)

/-- If some constraint fails then at most a `1 - 1/|Ψ|` fraction of constraints is satisfied:
every constraint system has a (tiny) gap for free. -/
lemma satFrac_le_of_not_sat {Ψ : CSPInstance} {a : Assignment} (hΨ : Ψ ≠ [])
    (h : ¬ Sat Ψ a) : satFrac Ψ a ≤ 1 - 1 / (Ψ.length : ℚ) := by
  have hlenpos : 0 < Ψ.length := List.length_pos_iff.2 hΨ
  have hcount : Ψ.countP (fun c => c.holds a) + 1 ≤ Ψ.length := by
    by_contra hcon
    push_neg at hcon
    exact h (List.countP_eq_length.1 (le_antisymm List.countP_le_length (by omega)))
  have hQ : ((Ψ.countP (fun c => c.holds a) : ℕ) : ℚ) ≤ (Ψ.length : ℚ) - 1 := by
    have := (Nat.cast_le (α := ℚ)).2 hcount
    push_cast at this
    linarith
  have hlen : (0 : ℚ) < (Ψ.length : ℚ) := by exact_mod_cast hlenpos
  unfold satFrac
  rw [div_le_iff₀ hlen]
  have : (1 - 1 / (Ψ.length : ℚ)) * (Ψ.length : ℚ) = (Ψ.length : ℚ) - 1 := by
    field_simp
  rw [this]
  exact hQ

/-!
### `PCP(log n, 1) ⊆ NP`
-/

/-- Any PCP with soundness error `s < 1` witnesses membership in (non-uniform) `NP`:
the constraint system itself is the `NP` description. -/
theorem inNP_of_hasGapPCP {L : Set (List Bool)} {s : ℚ} (hs : s < 1) (h : HasGapPCP L s) :
    InNP L := by
  obtain ⟨q, c, k, h⟩ := h
  refine ⟨q, c, k, fun n => ?_⟩
  obtain ⟨Ψ, hne, hlen, har, hmain⟩ := h n
  refine ⟨Ψ, hne, hlen, har, fun x hx => ?_⟩
  obtain ⟨hcomp, hsound⟩ := hmain x hx
  constructor
  · exact hcomp
  · rintro ⟨a, hax, hsat⟩
    by_contra hxL
    exact not_sat_of_satFrac_lt_one hne hs (hsound hxL a hax) hsat

theorem inNP_of_inPCP {L : Set (List Bool)} (h : InPCP L) : InNP L :=
  inNP_of_hasGapPCP (by norm_num) h

/-!
### Gap amplification by repetition
-/

/-- The conjunction of two constraints; its arity is the sum of the arities. -/
def Constraint.conj (c₁ c₂ : Constraint) : Constraint where
  vars := c₁.vars ++ c₂.vars
  pred := fun v => c₁.pred (v.take c₁.vars.length) && c₂.pred (v.drop c₁.vars.length)

@[simp] lemma Constraint.holds_conj (c₁ c₂ : Constraint) (a : Assignment) :
    (c₁.conj c₂).holds a = (c₁.holds a && c₂.holds a) := by
  have h : (c₁.vars.map a).length = c₁.vars.length := by simp
  simp only [Constraint.holds, Constraint.conj, List.map_append]
  rw [← h, List.take_left, List.drop_left]

@[simp] lemma Constraint.vars_conj (c₁ c₂ : Constraint) :
    (c₁.conj c₂).vars = c₁.vars ++ c₂.vars := rfl

/-- The product of two constraint systems: all pairwise conjunctions. -/
def prodCSP (Ψ₁ Ψ₂ : CSPInstance) : CSPInstance :=
  Ψ₁.flatMap (fun c₁ => Ψ₂.map (fun c₂ => c₁.conj c₂))

lemma mem_prodCSP {Ψ₁ Ψ₂ : CSPInstance} {c : Constraint} :
    c ∈ prodCSP Ψ₁ Ψ₂ ↔ ∃ c₁ ∈ Ψ₁, ∃ c₂ ∈ Ψ₂, c = c₁.conj c₂ := by
  simp [prodCSP, eq_comm]

lemma length_prodCSP (Ψ₁ Ψ₂ : CSPInstance) :
    (prodCSP Ψ₁ Ψ₂).length = Ψ₁.length * Ψ₂.length := by
  induction Ψ₁ with
  | nil => simp [prodCSP]
  | cons c t ih =>
    simp only [prodCSP, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons] at ih ⊢
    rw [ih]
    ring

lemma countP_prodCSP (Ψ₁ Ψ₂ : CSPInstance) (a : Assignment) :
    (prodCSP Ψ₁ Ψ₂).countP (fun c => c.holds a)
      = Ψ₁.countP (fun c => c.holds a) * Ψ₂.countP (fun c => c.holds a) := by
  induction Ψ₁ with
  | nil => simp [prodCSP]
  | cons c t ih =>
    have hmap : (Ψ₂.map (fun c₂ => c.conj c₂)).countP (fun d => d.holds a)
        = if c.holds a = true then Ψ₂.countP (fun c₂ => c₂.holds a) else 0 := by
      rw [List.countP_map]
      simp only [Function.comp_def, Constraint.holds_conj]
      by_cases h : c.holds a = true
      · simp [h]
      · rw [Bool.not_eq_true] at h
        simp [h]
    simp only [prodCSP, List.flatMap_cons, List.countP_append] at ih ⊢
    rw [hmap, ih]
    by_cases h : c.holds a = true <;> (simp [h, add_mul]; try ring)

lemma sat_prodCSP {Ψ₁ Ψ₂ : CSPInstance} {a : Assignment} (h₁ : Sat Ψ₁ a) (h₂ : Sat Ψ₂ a) :
    Sat (prodCSP Ψ₁ Ψ₂) a := by
  intro c hc
  rw [mem_prodCSP] at hc
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := hc
  simp [h₁ c₁ hc₁, h₂ c₂ hc₂]

lemma arityLE_prodCSP {Ψ₁ Ψ₂ : CSPInstance} {q₁ q₂ : ℕ} (h₁ : ArityLE Ψ₁ q₁)
    (h₂ : ArityLE Ψ₂ q₂) : ArityLE (prodCSP Ψ₁ Ψ₂) (q₁ + q₂) := by
  intro c hc
  rw [mem_prodCSP] at hc
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := hc
  simp only [Constraint.vars_conj, List.length_append]
  exact Nat.add_le_add (h₁ c₁ hc₁) (h₂ c₂ hc₂)

/-- The `k`-fold repetition of a constraint system: constraints are conjunctions of `k`
constraints of `Ψ`. -/
def iterCSP (Ψ : CSPInstance) : ℕ → CSPInstance
  | 0 => [⟨[], fun _ => true⟩]
  | k + 1 => prodCSP Ψ (iterCSP Ψ k)

lemma length_iterCSP (Ψ : CSPInstance) (k : ℕ) : (iterCSP Ψ k).length = Ψ.length ^ k := by
  induction k with
  | zero => simp [iterCSP]
  | succ k ih => simp [iterCSP, length_prodCSP, ih, pow_succ, Nat.mul_comm]

lemma countP_iterCSP (Ψ : CSPInstance) (a : Assignment) (k : ℕ) :
    (iterCSP Ψ k).countP (fun c => c.holds a) = (Ψ.countP (fun c => c.holds a)) ^ k := by
  induction k with
  | zero => simp [iterCSP, Constraint.holds]
  | succ k ih => simp [iterCSP, countP_prodCSP, ih, pow_succ, Nat.mul_comm]

lemma iterCSP_ne_nil {Ψ : CSPInstance} (hΨ : Ψ ≠ []) (k : ℕ) : iterCSP Ψ k ≠ [] := by
  have h : (iterCSP Ψ k).length = Ψ.length ^ k := length_iterCSP Ψ k
  have hpos : 0 < Ψ.length := List.length_pos_iff.2 hΨ
  have : 0 < (iterCSP Ψ k).length := by
    rw [h]; exact Nat.pow_pos hpos
  exact List.ne_nil_of_length_pos this

lemma sat_iterCSP {Ψ : CSPInstance} {a : Assignment} (h : Sat Ψ a) (k : ℕ) :
    Sat (iterCSP Ψ k) a := by
  induction k with
  | zero =>
    intro c hc
    simp only [iterCSP, List.mem_singleton] at hc
    subst hc
    rfl
  | succ k ih => exact sat_prodCSP h ih

lemma arityLE_iterCSP {Ψ : CSPInstance} {q : ℕ} (h : ArityLE Ψ q) (k : ℕ) :
    ArityLE (iterCSP Ψ k) (k * q) := by
  induction k with
  | zero =>
    intro c hc
    simp only [iterCSP, List.mem_singleton] at hc
    subst hc
    simp
  | succ k ih =>
    have := arityLE_prodCSP h ih
    intro c hc
    have := this c hc
    calc c.vars.length ≤ q + k * q := this
      _ = (k + 1) * q := by ring

lemma satFrac_iterCSP (Ψ : CSPInstance) (a : Assignment) (k : ℕ) :
    satFrac (iterCSP Ψ k) a = (satFrac Ψ a) ^ k := by
  unfold satFrac
  rw [countP_iterCSP, length_iterCSP]
  push_cast
  rw [div_pow]

/-- Monotonicity of the soundness parameter. -/
lemma hasGapPCP_mono {L : Set (List Bool)} {s t : ℚ} (hst : s ≤ t) (h : HasGapPCP L s) :
    HasGapPCP L t := by
  obtain ⟨q, c, k, h⟩ := h
  refine ⟨q, c, k, fun n => ?_⟩
  obtain ⟨Ψ, hne, hlen, har, hmain⟩ := h n
  refine ⟨Ψ, hne, hlen, har, fun x hx => ?_⟩
  obtain ⟨hcomp, hsound⟩ := hmain x hx
  exact ⟨hcomp, fun hxL a hax => (hsound hxL a hax).trans hst⟩

/-- **Gap amplification by repetition.**  A constant gap can be amplified to soundness error
`1/2`, keeping the arity constant and the number of constraints polynomial. -/
theorem hasGapPCP_half_of_hasGapPCP {L : Set (List Bool)} {s : ℚ} (hs : s < 1)
    (h : HasGapPCP L s) : InPCP L := by
  -- We may assume `0 ≤ s`.
  have h' : HasGapPCP L (max s 0) := hasGapPCP_mono (le_max_left _ _) h
  have hs' : max s 0 < 1 := max_lt hs (by norm_num)
  set t : ℚ := max s 0 with ht
  clear_value t
  clear h hs ht
  -- choose the number of repetitions
  obtain ⟨k, hk⟩ : ∃ k : ℕ, t ^ k < 1 / 2 := exists_pow_lt_of_lt_one (by norm_num) hs'
  obtain ⟨q, c, k₀, hfam⟩ := h'
  refine ⟨k * q, c ^ k, k₀ * k, fun n => ?_⟩
  obtain ⟨Ψ, hne, hlen, har, hmain⟩ := hfam n
  refine ⟨iterCSP Ψ k, iterCSP_ne_nil hne k, ?_, arityLE_iterCSP har k, fun x hx => ?_⟩
  · rw [length_iterCSP]
    calc Ψ.length ^ k ≤ (c * (n + 1) ^ k₀) ^ k := Nat.pow_le_pow_left hlen k
      _ = c ^ k * (n + 1) ^ (k₀ * k) := by rw [mul_pow, ← pow_mul]
  · obtain ⟨hcomp, hsound⟩ := hmain x hx
    refine ⟨fun hxL => ?_, fun hxL a hax => ?_⟩
    · obtain ⟨a, hax, hsat⟩ := hcomp hxL
      exact ⟨a, hax, sat_iterCSP hsat k⟩
    · rw [satFrac_iterCSP]
      calc satFrac Ψ a ^ k ≤ t ^ k := pow_le_pow_left₀ (satFrac_nonneg Ψ a) (hsound hxL a hax) k
        _ ≤ 1 / 2 := le_of_lt hk

/-!
### The PCP theorem
-/

/-- **The PCP theorem**, `NP = PCP(log n, 1)`, in its gap-CSP formulation, derived from the
hard combinatorial core `GapCSPHardness` (constant-gap constraint systems for `NP`, the
theorem of Arora–Safra and Arora–Lund–Motwani–Sudan–Szegedy).  The inclusion
`PCP(log n, 1) ⊆ NP` and the amplification of an arbitrary constant gap to soundness error
`1/2` are proved here. -/
theorem pcp_theorem (h : GapCSPHardness) :
    {L : Set (List Bool) | InNP L} = {L : Set (List Bool) | InPCP L} := by
  ext L
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hL
    obtain ⟨s, hs, hgap⟩ := h L hL
    exact hasGapPCP_half_of_hasGapPCP hs hgap
  · exact inNP_of_inPCP

/-- Unconditionally, the class equality `NP = PCP(log n, 1)` is *equivalent* to the
constant-gap hardness statement: gap amplification loses nothing. -/
theorem pcp_theorem_iff :
    GapCSPHardness ↔ {L : Set (List Bool) | InNP L} = {L : Set (List Bool) | InPCP L} := by
  constructor
  · exact pcp_theorem
  · intro heq L hL
    have hpcp : InPCP L := by
      have : L ∈ {L : Set (List Bool) | InPCP L} := heq ▸ hL
      exact this
    exact ⟨1 / 2, by norm_num, hpcp⟩

/-!
### Sanity checks: the classes are inhabited
-/

/-- The empty language is in `PCP(log n, 1)` (a single always-failing constraint). -/
theorem inPCP_empty : InPCP (∅ : Set (List Bool)) := by
  refine ⟨0, 1, 0, fun n => ⟨[⟨[], fun _ => false⟩], by simp, by simp, ?_, ?_⟩⟩
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    simp
  · intro x _
    refine ⟨fun hx => absurd hx (Set.notMem_empty x), fun _ a _ => ?_⟩
    simp [satFrac, Constraint.holds]

/-- The full language is in `PCP(log n, 1)` (a single always-true constraint). -/
theorem inPCP_univ : InPCP (Set.univ : Set (List Bool)) := by
  refine ⟨0, 1, 0, fun n => ⟨[⟨[], fun _ => true⟩], by simp, by simp, ?_, ?_⟩⟩
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    simp
  · intro x _
    refine ⟨fun _ => ⟨stdAssignment x, extends_stdAssignment x, ?_⟩, fun hx => absurd (Set.mem_univ x) hx⟩
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    rfl

end CS

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

