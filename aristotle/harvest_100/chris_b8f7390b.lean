import Mathlib

/-!
# A formal model of an isolation engine

This file develops a small but complete formal model of the "isolation engine" of a
*privilege-controlled architecture* (`PCA`).

An `Engine` is a (possibly infinite) transition system on a type of machine states
together with a distinguished set of *trusted* states (the isolation boundary).
A *privilege escape* from a state `s` is the existence of a run of the engine starting
at `s` and ending outside the isolation boundary.

The main results are:

* `PCA.Isolation.priv_escape_monotone` — escapes are monotone along refinement: making
  the engine more permissive (more transitions, fewer trusted states) can only create
  escapes, never remove them.
* `PCA.Isolation.isolation_sound` / `PCA.Isolation.isolation_complete` — an inductive
  invariant contained in the isolation boundary is a sound *and* complete certificate of
  the absence of privilege escapes.
* `PCA.Isolation.escapeCheck_iff` — for a finite-state engine the explicit reachability
  computation `escapeCheck` decides privilege escape: it is sound and complete with
  respect to the relational semantics.
-/

namespace PCA.Isolation

universe u

/-- An isolation engine on a state space `σ`: a transition relation `step` describing the
runs the engine permits, together with the set `trusted` of states that lie inside the
isolation boundary. -/
structure Engine (σ : Type u) where
  /-- The transitions the engine permits. -/
  step : σ → σ → Prop
  /-- The isolation boundary: the states considered privilege-safe. -/
  trusted : Set σ

variable {σ : Type u}

/-- `Reach e s t` says that the engine `e` admits a (possibly empty) run from `s` to `t`. -/
def Reach (e : Engine σ) : σ → σ → Prop :=
  Relation.ReflTransGen e.step

theorem Reach.refl (e : Engine σ) (s : σ) : Reach e s s :=
  Relation.ReflTransGen.refl

theorem Reach.tail {e : Engine σ} {s t u : σ} (h : Reach e s t) (h' : e.step t u) :
    Reach e s u :=
  Relation.ReflTransGen.tail h h'

theorem Reach.trans {e : Engine σ} {s t u : σ} (h : Reach e s t) (h' : Reach e t u) :
    Reach e s u :=
  Relation.ReflTransGen.trans h h'

/-- A *privilege escape* from `s`: some run of the engine leaves the isolation boundary. -/
def PrivEscape (e : Engine σ) (s : σ) : Prop :=
  ∃ t, Reach e s t ∧ t ∉ e.trusted

/-- `Refines e₁ e₂` says that `e₂` is at least as permissive as `e₁`: it allows all the
transitions `e₁` allows and its isolation boundary is no larger. -/
structure Refines (e₁ e₂ : Engine σ) : Prop where
  /-- Every transition of `e₁` is a transition of `e₂`. -/
  step_le : ∀ a b, e₁.step a b → e₂.step a b
  /-- The isolation boundary of `e₂` is contained in that of `e₁`. -/
  trusted_subset : e₂.trusted ⊆ e₁.trusted

theorem Refines.refl (e : Engine σ) : Refines e e :=
  ⟨fun _ _ h => h, fun _ h => h⟩

theorem Refines.trans {e₁ e₂ e₃ : Engine σ} (h₁ : Refines e₁ e₂) (h₂ : Refines e₂ e₃) :
    Refines e₁ e₃ :=
  ⟨fun a b h => h₂.step_le a b (h₁.step_le a b h), fun _ h => h₁.trusted_subset (h₂.trusted_subset h)⟩

theorem reach_mono {e₁ e₂ : Engine σ} (h : Refines e₁ e₂) {s t : σ} (hst : Reach e₁ s t) :
    Reach e₂ s t :=
  Relation.ReflTransGen.mono (fun a b hab => h.step_le a b hab) hst

/-- **Monotonicity of privilege escape.** If `e₂` refines `e₁` in the sense that it permits
more transitions and trusts fewer states, then every privilege escape of `e₁` is a privilege
escape of `e₂`. -/
theorem priv_escape_monotone {e₁ e₂ : Engine σ} (h : Refines e₁ e₂) {s : σ}
    (hs : PrivEscape e₁ s) : PrivEscape e₂ s := by
  obtain ⟨t, hreach, hout⟩ := hs
  exact ⟨t, reach_mono h hreach, fun hmem => hout (h.trusted_subset hmem)⟩

/-- The contrapositive reading: an engine with no escapes stays escape-free under
hardening. -/
theorem no_priv_escape_antitone {e₁ e₂ : Engine σ} (h : Refines e₁ e₂) {s : σ}
    (hs : ¬ PrivEscape e₂ s) : ¬ PrivEscape e₁ s :=
  fun hesc => hs (priv_escape_monotone h hesc)

/-! ### Inductive invariants: soundness and completeness -/

/-- `Inductive e I` says that `I` is closed under the transitions of `e`. -/
def Inductive (e : Engine σ) (I : Set σ) : Prop :=
  ∀ a ∈ I, ∀ b, e.step a b → b ∈ I

theorem reach_mem_of_inductive {e : Engine σ} {I : Set σ} (hI : Inductive e I) {s t : σ}
    (hs : s ∈ I) (h : Reach e s t) : t ∈ I := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact hI _ ih _ hstep

/-- **Soundness of the invariant method.** An inductive invariant containing `s` and
contained in the isolation boundary certifies the absence of privilege escapes. -/
theorem isolation_sound {e : Engine σ} {I : Set σ} {s : σ} (hI : Inductive e I)
    (hsub : I ⊆ e.trusted) (hs : s ∈ I) : ¬ PrivEscape e s := by
  rintro ⟨t, hreach, hout⟩
  exact hout (hsub (reach_mem_of_inductive hI hs hreach))

/-- **Completeness of the invariant method.** If there is no privilege escape from `s`,
then such an inductive invariant exists (namely the reachable set). -/
theorem isolation_complete {e : Engine σ} {s : σ} (h : ¬ PrivEscape e s) :
    ∃ I : Set σ, s ∈ I ∧ Inductive e I ∧ I ⊆ e.trusted := by
  refine ⟨{t | Reach e s t}, Reach.refl e s, ?_, ?_⟩
  · intro a ha b hab
    exact Reach.tail ha hab
  · intro t ht
    by_contra hout
    exact h ⟨t, ht, hout⟩

/-- The invariant method characterises absence of escapes exactly. -/
theorem no_priv_escape_iff_exists_inductive {e : Engine σ} {s : σ} :
    ¬ PrivEscape e s ↔ ∃ I : Set σ, s ∈ I ∧ Inductive e I ∧ I ⊆ e.trusted :=
  ⟨isolation_complete, fun ⟨_, hs, hI, hsub⟩ => isolation_sound hI hsub hs⟩

/-! ### A decision procedure for finite-state engines -/

variable {σ : Type u} [Fintype σ] [DecidableEq σ]

/-- A finite-state presentation of an isolation engine: successors are given by a finite
set and the isolation boundary is a `Finset`. -/
structure FinEngine (σ : Type u) [Fintype σ] [DecidableEq σ] where
  /-- The successor states of a given state. -/
  next : σ → Finset σ
  /-- The isolation boundary. -/
  trusted : Finset σ

/-- The relational semantics of a finite-state engine. -/
def FinEngine.toEngine (e : FinEngine σ) : Engine σ where
  step a b := b ∈ e.next a
  trusted := ↑e.trusted

/-- One step of the reachability computation. -/
def FinEngine.expand (e : FinEngine σ) (S : Finset σ) : Finset σ :=
  S ∪ S.biUnion e.next

/-- The set of states reachable from `s`, computed by iterating `expand` enough times. -/
def FinEngine.reachFinset (e : FinEngine σ) (s : σ) : Finset σ :=
  (e.expand)^[Fintype.card σ] {s}

/-- The escape checker: is some reachable state outside the isolation boundary? -/
def FinEngine.escapeCheck (e : FinEngine σ) (s : σ) : Bool :=
  ¬ (e.reachFinset s ⊆ e.trusted)

theorem FinEngine.subset_expand (e : FinEngine σ) (S : Finset σ) : S ⊆ e.expand S :=
  Finset.subset_union_left

theorem FinEngine.expand_mono (e : FinEngine σ) {S T : Finset σ} (h : S ⊆ T) :
    e.expand S ⊆ e.expand T :=
  Finset.union_subset_union h (Finset.biUnion_subset_biUnion_of_subset_left _ h)

theorem FinEngine.iterate_subset_succ (e : FinEngine σ) (S : Finset σ) (k : ℕ) :
    (e.expand)^[k] S ⊆ (e.expand)^[k + 1] S := by
  rw [Function.iterate_succ_apply']
  exact e.subset_expand _

theorem FinEngine.subset_iterate (e : FinEngine σ) (S : Finset σ) (k : ℕ) :
    S ⊆ (e.expand)^[k] S := by
  induction k with
  | zero => simp
  | succ k ih => exact ih.trans (e.iterate_subset_succ S k)

/-- If the iteration is stationary at step `j`, it stays stationary. -/
theorem FinEngine.iterate_eq_of_fixed (e : FinEngine σ) (S : Finset σ) {j : ℕ}
    (hj : (e.expand)^[j] S = (e.expand)^[j + 1] S) (m : ℕ) :
    (e.expand)^[j + m] S = (e.expand)^[j] S := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hstep : (e.expand)^[j + (m + 1)] S = e.expand ((e.expand)^[j + m] S) :=
        Function.iterate_succ_apply' e.expand (j + m) S
      rw [hstep, ih, ← Function.iterate_succ_apply' e.expand j, ← hj]

/-- Until the iteration becomes stationary its cardinality grows by at least one each step. -/
theorem FinEngine.card_iterate_ge (e : FinEngine σ) (S : Finset σ) (k : ℕ)
    (h : ∀ j < k, (e.expand)^[j] S ≠ (e.expand)^[j + 1] S) :
    S.card + k ≤ ((e.expand)^[k] S).card := by
  induction k with
  | zero => simp
  | succ k ih =>
      have ihk : S.card + k ≤ ((e.expand)^[k] S).card :=
        ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
      have hlt : ((e.expand)^[k] S).card < ((e.expand)^[k + 1] S).card :=
        Finset.card_lt_card ⟨e.iterate_subset_succ S k, fun hsub =>
          h k (Nat.lt_succ_self k)
            (Finset.Subset.antisymm (e.iterate_subset_succ S k) hsub)⟩
      omega

/-- Everything produced by the iteration is genuinely reachable. -/
theorem FinEngine.mem_iterate_reach (e : FinEngine σ) (s : σ) (k : ℕ) {t : σ}
    (ht : t ∈ (e.expand)^[k] {s}) : Reach e.toEngine s t := by
  induction k generalizing t with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Finset.mem_singleton] at ht
      subst ht
      exact Reach.refl _ _
  | succ k ih =>
      rw [Function.iterate_succ_apply'] at ht
      simp only [FinEngine.expand, Finset.mem_union, Finset.mem_biUnion] at ht
      rcases ht with ht | ⟨a, ha, hta⟩
      · exact ih ht
      · exact Reach.tail (ih ha) hta

/-- The iteration reaches a fixed point after at most `Fintype.card σ` steps. -/
theorem FinEngine.expand_reachFinset (e : FinEngine σ) (s : σ) :
    e.expand (e.reachFinset s) = e.reachFinset s := by
  set n := Fintype.card σ with hn
  have hex : ∃ j < n, (e.expand)^[j] {s} = (e.expand)^[j + 1] {s} := by
    by_contra hcon
    push_neg at hcon
    have hcard := e.card_iterate_ge {s} n (fun j hj => hcon j hj)
    have hle : ((e.expand)^[n] {s}).card ≤ n := by
      simpa [hn] using Finset.card_le_univ ((e.expand)^[n] {s})
    simp only [Finset.card_singleton] at hcard
    omega
  obtain ⟨j, hjn, hj⟩ := hex
  have hnj : n = j + (n - j) := by omega
  have hfix : (e.expand)^[n] {s} = (e.expand)^[j] {s} := by
    rw [hnj]; exact e.iterate_eq_of_fixed {s} hj (n - j)
  show e.expand ((e.expand)^[n] {s}) = (e.expand)^[n] {s}
  rw [hfix, ← Function.iterate_succ_apply' e.expand j, ← hj]

theorem FinEngine.self_mem_reachFinset (e : FinEngine σ) (s : σ) : s ∈ e.reachFinset s :=
  e.subset_iterate {s} (Fintype.card σ) (Finset.mem_singleton_self s)

/-- Membership in the computed set is exactly reachability. -/
theorem FinEngine.mem_reachFinset_iff (e : FinEngine σ) (s t : σ) :
    t ∈ e.reachFinset s ↔ Reach e.toEngine s t := by
  constructor
  · intro ht
    exact e.mem_iterate_reach s (Fintype.card σ) ht
  · intro ht
    induction ht with
    | refl => exact e.self_mem_reachFinset s
    | tail _ hstep ih =>
        rw [← e.expand_reachFinset s]
        simp only [FinEngine.expand, Finset.mem_union, Finset.mem_biUnion]
        exact Or.inr ⟨_, ih, hstep⟩

/-- **Soundness and completeness of the escape checker.** -/
theorem escapeCheck_iff (e : FinEngine σ) (s : σ) :
    e.escapeCheck s = true ↔ PrivEscape e.toEngine s := by
  have hcheck : (e.escapeCheck s = true) ↔ ¬ (e.reachFinset s ⊆ e.trusted) := by
    simp [FinEngine.escapeCheck]
  rw [hcheck, Finset.not_subset]
  constructor
  · rintro ⟨t, ht, hnt⟩
    exact ⟨t, (e.mem_reachFinset_iff s t).1 ht, by simpa [FinEngine.toEngine] using hnt⟩
  · rintro ⟨t, ht, hnt⟩
    exact ⟨t, (e.mem_reachFinset_iff s t).2 ht, by simpa [FinEngine.toEngine] using hnt⟩

/-- Privilege escape is decidable for finite-state engines. -/
instance (e : FinEngine σ) (s : σ) : Decidable (PrivEscape e.toEngine s) :=
  decidable_of_iff _ (escapeCheck_iff e s)

/-! ### A worked example

A three-state engine: state `0` is the sandboxed task, state `1` an intermediate
privileged helper and state `2` the (untrusted) kernel. Only states `0` and `1` are
trusted, and the engine allows `0 → 1 → 2`, so the sandbox can escape. Hardening the
engine by removing the transition `1 → 2` removes the escape. -/
section Example

/-- The permissive engine `0 → 1 → 2` with `{0, 1}` trusted. -/
def leakyEngine : FinEngine (Fin 3) where
  next i := if i = 0 then {1} else if i = 1 then {2} else ∅
  trusted := {0, 1}

/-- The hardened engine: the transition `1 → 2` has been removed. -/
def hardenedEngine : FinEngine (Fin 3) where
  next i := if i = 0 then {1} else ∅
  trusted := {0, 1}

example : PrivEscape leakyEngine.toEngine 0 := by decide

example : ¬ PrivEscape hardenedEngine.toEngine 0 := by decide

/-- The leaky engine is indeed more permissive than the hardened one, and monotonicity
therefore transports the escape from the hardened engine — it has none — rather than the
other way round. -/
theorem hardened_refines_leaky : Refines hardenedEngine.toEngine leakyEngine.toEngine := by
  constructor
  · intro a b h
    fin_cases a <;>
      simp_all [FinEngine.toEngine, hardenedEngine, leakyEngine]
  · intro x hx
    exact hx

end Example

end PCA.Isolation

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

