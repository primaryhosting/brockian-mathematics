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

/-!
# Tightened Predicate Refines Original
Category: Proof-Carrying Apps
Target: PCA.Isolation.tightened_predicate_refines_original
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

universe u

/-- Syntax of the isolation engine's access predicates over a state type `σ`.

An `AccessPred σ` describes when a request in state `s : σ` is permitted.
The language is monotone (no negation): `grant` always permits, `deny` never
permits, `atom p` consults a primitive check `p`, and `both`/`either` are
conjunction and disjunction of sub-policies. -/
inductive AccessPred (σ : Type u) : Type u
  | grant : AccessPred σ
  | deny : AccessPred σ
  | atom : (σ → Prop) → AccessPred σ
  | both : AccessPred σ → AccessPred σ → AccessPred σ
  | either : AccessPred σ → AccessPred σ → AccessPred σ

namespace AccessPred

/-- Denotational semantics of an access predicate: the set of states it permits. -/
def eval {σ : Type u} : AccessPred σ → σ → Prop
  | grant, _ => True
  | deny, _ => False
  | atom p, s => p s
  | both a b, s => eval a s ∧ eval b s
  | either a b, s => eval a s ∨ eval b s

/-- `Refines q p` says that policy `q` is at least as restrictive as policy `p`:
every state permitted by `q` is permitted by `p`. -/
def Refines {σ : Type u} (q p : AccessPred σ) : Prop :=
  ∀ s, eval q s → eval p s

/-- The isolation engine's tightening transformation: push an extra guard `g`
into every leaf of the policy `p`. -/
def tighten {σ : Type u} (g : AccessPred σ) : AccessPred σ → AccessPred σ
  | grant => g
  | deny => deny
  | atom p => both (atom p) g
  | both a b => both (tighten g a) (tighten g b)
  | either a b => either (tighten g a) (tighten g b)

end AccessPred

open AccessPred

/-- **Soundness of tightening.** The tightened policy refines the original one:
anything the tightened policy permits was already permitted before tightening.
Proved by structural induction on the policy. -/
theorem tightened_predicate_refines_original {σ : Type u} (g p : AccessPred σ) :
    Refines (tighten g p) p := by
  intro s
  induction p with
  | grant => intro _; exact trivial
  | deny => intro hs; exact hs
  | atom q => intro hs; exact hs.1
  | both a b iha ihb => intro hs; exact ⟨iha hs.1, ihb hs.2⟩
  | either a b iha ihb =>
      rintro (h | h)
      · exact Or.inl (iha h)
      · exact Or.inr (ihb h)

/-- **The guard is enforced.** Every state permitted by the tightened policy
also satisfies the guard `g`. -/
theorem tightened_predicate_enforces_guard {σ : Type u} (g p : AccessPred σ) :
    Refines (tighten g p) g := by
  intro s
  induction p with
  | grant => intro hs; exact hs
  | deny => intro hs; exact hs.elim
  | atom q => intro hs; exact hs.2
  | both a b iha _ => intro hs; exact iha hs.1
  | either a b iha ihb =>
      rintro (h | h)
      · exact iha h
      · exact ihb h

/-- **Completeness of tightening.** Anything permitted by the original policy
that also satisfies the guard is still permitted after tightening. -/
theorem tightened_predicate_complete {σ : Type u} (g p : AccessPred σ) (s : σ)
    (hg : eval g s) : eval p s → eval (tighten g p) s := by
  induction p with
  | grant => intro _; exact hg
  | deny => intro hp; exact hp.elim
  | atom q => intro hp; exact ⟨hp, hg⟩
  | both a b iha ihb => intro hp; exact ⟨iha hp.1, ihb hp.2⟩
  | either a b iha ihb =>
      rintro (h | h)
      · exact Or.inl (iha h)
      · exact Or.inr (ihb h)

/-- Exact characterization of the tightened policy: it permits precisely the
states permitted by the original policy that additionally satisfy the guard. -/
theorem eval_tighten_iff {σ : Type u} (g p : AccessPred σ) (s : σ) :
    eval (tighten g p) s ↔ eval p s ∧ eval g s :=
  ⟨fun h => ⟨tightened_predicate_refines_original g p s h,
             tightened_predicate_enforces_guard g p s h⟩,
   fun h => tightened_predicate_complete g p s h.2 h.1⟩

/-- Refinement is transitive, so iterated tightening keeps refining the original. -/
theorem Refines.trans' {σ : Type u} {a b c : AccessPred σ}
    (hab : Refines a b) (hbc : Refines b c) : Refines a c :=
  fun s h => hbc s (hab s h)

/-- Tightening twice still refines the original policy. -/
theorem tighten_tighten_refines_original {σ : Type u} (g₁ g₂ p : AccessPred σ) :
    Refines (tighten g₂ (tighten g₁ p)) p :=
  Refines.trans' (tightened_predicate_refines_original g₂ (tighten g₁ p))
    (tightened_predicate_refines_original g₁ p)

end PCA.Isolation

