/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

/-- A single component of a resource path (e.g. one segment of `"/etc/ssl/certs"`). -/
abbrev Component := String

/-- The actions an application may attempt on a resource. -/
inductive Action where
  | read : Action
  | write : Action
  | exec : Action
  deriving DecidableEq, Repr

/-- A capability grants `action` on every resource under the path prefix `path`. -/
structure Capability where
  action : Action
  path : List Component
  deriving DecidableEq, Repr

/-- A request made by the application: an `action` on the resource at `path`. -/
structure Request where
  action : Action
  path : List Component
  deriving DecidableEq, Repr

/-- The isolation scope of an application: the list of capabilities it was granted. -/
abbrev Scope := List Capability

/-- Declarative semantics of the isolation engine: a request is *in scope* when some granted
capability matches its action and its path prefixes the requested resource path. -/
def InScope (s : Scope) (r : Request) : Prop :=
  ∃ c ∈ s, c.action = r.action ∧ c.path <+: r.path

instance instDecidableInScope (s : Scope) (r : Request) : Decidable (InScope s r) :=
  inferInstanceAs (Decidable (∃ c ∈ s, c.action = r.action ∧ c.path <+: r.path))

/-! ## The compiled representation: a prefix trie -/

mutual

/-- A prefix trie over path components. `node b f` accepts here iff `b` is `true`. -/
inductive Trie where
  | node : Bool → Forest → Trie
  deriving Repr

/-- An association list of child tries, keyed by path component. -/
inductive Forest where
  | nil : Forest
  | cons : Component → Trie → Forest → Forest
  deriving Repr

end

namespace Trie

/-- The trie accepting nothing. -/
def empty : Trie := .node false .nil

end Trie

mutual

/-- `t.accepts r` walks the resource path `r` through the trie `t`, accepting as soon as it
reaches an accepting node. -/
def Trie.accepts : Trie → List Component → Bool
  | .node a _, [] => a
  | .node a f, x :: xs => a || Forest.accepts f x xs

/-- `Forest.accepts f x xs` looks `x` up in the forest `f` and continues with `xs`. -/
def Forest.accepts : Forest → Component → List Component → Bool
  | .nil, _, _ => false
  | .cons k t rest, x, xs => if k = x then Trie.accepts t xs else Forest.accepts rest x xs

end

mutual

/-- Insert a granted path prefix into the trie. -/
def Trie.insert : Trie → List Component → Trie
  | .node _ f, [] => .node true f
  | .node a f, x :: xs => .node a (Forest.insert f x xs)

/-- Insert `x :: xs` into a forest of children. -/
def Forest.insert : Forest → Component → List Component → Forest
  | .nil, x, xs => .cons x (Trie.insert Trie.empty xs) .nil
  | .cons k t rest, x, xs =>
      if k = x then .cons k (Trie.insert t xs) rest else .cons k t (Forest.insert rest x xs)

end

/-- Compile a list of granted path prefixes into a trie. -/
def Trie.ofList (ps : List (List Component)) : Trie :=
  ps.foldl Trie.insert Trie.empty

/-! ## Correctness of the compiled representation -/

@[simp] theorem Trie.empty_accepts (r : List Component) : Trie.empty.accepts r = false := by
  cases r <;> simp [Trie.empty, Trie.accepts, Forest.accepts]

theorem Trie.insert_accepts :
    ∀ (p : List Component) (t : Trie) (r : List Component),
      (t.insert p).accepts r = (t.accepts r || decide (p <+: r)) := by
  intro p
  induction p with
  | nil =>
      intro t r
      cases t with
      | node a f =>
          cases r <;> simp [Trie.insert, Trie.accepts]
  | cons y ys ih =>
      have hf : ∀ (f : Forest) (x : Component) (xs : List Component),
          Forest.accepts (Forest.insert f y ys) x xs
            = (Forest.accepts f x xs || (decide (y = x) && decide (ys <+: xs))) := by
        intro f
        induction f using Forest.rec (motive_1 := fun _ => True) with
        | node => trivial
        | nil =>
            intro x xs
            by_cases h : y = x <;>
              simp [Forest.insert, Forest.accepts, h, ih Trie.empty xs]
        | cons k t rest _ ihf =>
            intro x xs
            by_cases hky : k = y
            · subst hky
              by_cases h : k = x
              · simp [Forest.insert, Forest.accepts, h, ih t xs]
              · simp [Forest.insert, Forest.accepts, h]
            · by_cases h : k = x
              · have hxy : ¬ x = y := fun hh => hky (h.trans hh)
                have hyx : ¬ y = x := fun hh => hxy hh.symm
                simp [Forest.insert, Forest.accepts, h, hxy, hyx]
              · simp [Forest.insert, Forest.accepts, h, hky, ihf x xs]
      intro t r
      cases t with
      | node a f =>
          cases r with
          | nil => simp [Trie.insert, Trie.accepts]
          | cons x xs =>
              simp only [Trie.insert, Trie.accepts, hf f x xs]
              by_cases h : y = x
              · subst h
                simp [List.cons_prefix_cons, Bool.or_assoc]
              · simp [List.cons_prefix_cons, h]

theorem Trie.foldl_insert_accepts :
    ∀ (ps : List (List Component)) (t : Trie) (r : List Component),
      (ps.foldl Trie.insert t).accepts r = (t.accepts r || decide (∃ p ∈ ps, p <+: r)) := by
  intro ps
  induction ps with
  | nil => intro t r; simp
  | cons p ps ih =>
      intro t r
      simp only [List.foldl_cons, ih (t.insert p) r, Trie.insert_accepts p t r,
        List.mem_cons]
      by_cases h : p <+: r
      · simp [h]
      · simp [h]

/-- The compiled trie accepts exactly the resource paths covered by one of the granted
prefixes. -/
theorem Trie.ofList_accepts (ps : List (List Component)) (r : List Component) :
    (Trie.ofList ps).accepts r = decide (∃ p ∈ ps, p <+: r) := by
  simp [Trie.ofList, Trie.foldl_insert_accepts]

/-! ## The isolation engine -/

/-- Compile a scope into one trie per action. -/
def encode (s : Scope) (a : Action) : Trie :=
  Trie.ofList (s.filterMap (fun c => if c.action = a then some c.path else none))

/-- The runtime check performed by the isolation engine on a request. -/
def check (s : Scope) (r : Request) : Bool :=
  (encode s r.action).accepts r.path

/-- **Soundness and completeness of the in-scope encoding.**
The compiled isolation engine accepts a request exactly when the request is in scope
according to the declarative capability semantics. -/
theorem in_scope_encoding_sound (s : Scope) (r : Request) :
    check s r = true ↔ InScope s r := by
  simp only [check, encode, Trie.ofList_accepts, decide_eq_true_eq, InScope,
    List.mem_filterMap]
  constructor
  · rintro ⟨p, ⟨c, hc, hcp⟩, hpr⟩
    by_cases h : c.action = r.action
    · rw [if_pos h, Option.some.injEq] at hcp
      exact ⟨c, hc, h, hcp ▸ hpr⟩
    · simp [h] at hcp
  · rintro ⟨c, hc, hact, hpr⟩
    exact ⟨c.path, ⟨c, hc, by simp [hact]⟩, hpr⟩

/-- **Soundness of rejection.** The engine rejects a request exactly when no granted
capability covers it. -/
theorem check_eq_false_iff (s : Scope) (r : Request) :
    check s r = false ↔ ¬ InScope s r := by
  rw [← in_scope_encoding_sound]
  simp

/-! ## Sanity checks: the engine is neither always-accepting nor always-rejecting -/

/-- A scope granting read access under `/etc/ssl` and write access under `/tmp`. -/
def sampleScope : Scope :=
  [ { action := Action.read, path := ["etc", "ssl"] },
    { action := Action.write, path := ["tmp"] } ]

example : check sampleScope { action := Action.read, path := ["etc", "ssl", "certs"] } = true := by
  rw [in_scope_encoding_sound]; decide

example : check sampleScope { action := Action.write, path := ["etc", "ssl", "certs"] } = false := by
  rw [check_eq_false_iff]; decide

example : check sampleScope { action := Action.read, path := ["etc"] } = false := by
  rw [check_eq_false_iff]; decide

example : check sampleScope { action := Action.write, path := ["tmp", "a", "b"] } = true := by
  rw [in_scope_encoding_sound]; decide

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

