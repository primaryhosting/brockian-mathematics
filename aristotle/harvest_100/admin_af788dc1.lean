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
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports.  The header comment above is a *module docstring*, which Lean
parses as a command; consequently no `import` line may follow it.  The
development below is therefore self-contained in core Lean.  The reachability
relation `PCA.Isolation.Reaches` defined here is the reflexive-transitive
closure of the reference relation, i.e. the exact analogue of Mathlib's
`Relation.ReflTransGen`; the two directions of the main theorem correspond to
the induction principles `Relation.ReflTransGen.head_induction_on` /
`Relation.ReflTransGen.tail` there.  A Mathlib-based restatement, proved by
transporting along an equivalence with `Relation.ReflTransGen`, is given in
`RequestProject/PCA/IsolationMathlib.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Isolation

universe u v

variable {V : Type u} {D : Type v}

/-- Reflexive-transitive closure of the reference relation `edge`:
`Reaches edge a b` holds when `b` can be reached from `a` by following a finite
(possibly empty) chain of heap references. -/
inductive Reaches (edge : V → V → Prop) : V → V → Prop
  | refl (a : V) : Reaches edge a a
  | tail {a b c : V} : Reaches edge a b → edge b c → Reaches edge a c

/-- One expansion step of the isolation engine's worklist: keep everything already
discovered and add every heap node directly referenced from a discovered node. -/
def step (edge : V → V → Prop) (S : V → Prop) : V → Prop :=
  fun w => S w ∨ ∃ u, S u ∧ edge u w

/-- The set of heap nodes the isolation engine has discovered after `n` expansion
steps, starting from the externally visible `roots` (the isolation boundary). -/
def iter (edge : V → V → Prop) (roots : V → Prop) : Nat → V → Prop
  | 0 => roots
  | n + 1 => step edge (iter edge roots n)

/-- Declarative reachability model: the nodes reachable from the boundary roots
by following any finite chain of references. -/
def Reach (edge : V → V → Prop) (roots : V → Prop) (w : V) : Prop :=
  ∃ r, roots r ∧ Reaches edge r w

/-- A node is *unowned* when the ownership map assigns it no owning domain,
i.e. its owner is `null`. -/
def Unowned (owner : V → Option D) (w : V) : Prop :=
  owner w = none

/-- The isolation engine reports a *null escape* when, at some stage of its
iterative exploration outward from the boundary roots, it discovers an unowned
node. -/
def NullEscape (edge : V → V → Prop) (roots : V → Prop) (owner : V → Option D) : Prop :=
  ∃ n : Nat, ∃ w, iter edge roots n w ∧ Unowned owner w

/-- Soundness of the exploration: everything the engine discovers at stage `n` is
genuinely reachable from the roots. -/
theorem iter_imp_reach (edge : V → V → Prop) (roots : V → Prop) :
    ∀ (n : Nat) (w : V), iter edge roots n w → Reach edge roots w := by
  intro n
  induction n with
  | zero => exact fun w hw => ⟨w, hw, Reaches.refl w⟩
  | succ n ih =>
    rintro w (hw | ⟨u, hu, huw⟩)
    · exact ih w hw
    · obtain ⟨r, hr, hru⟩ := ih u hu
      exact ⟨r, hr, hru.tail huw⟩

/-- Completeness of the exploration: everything reachable from the roots is
discovered by the engine at some finite stage. -/
theorem reach_imp_iter (edge : V → V → Prop) (roots : V → Prop) (w : V)
    (hw : Reach edge roots w) : ∃ n : Nat, iter edge roots n w := by
  obtain ⟨r, hr, hrw⟩ := hw
  induction hrw with
  | refl => exact ⟨0, hr⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, Or.inr ⟨_, hn, hbc⟩⟩

/-- The engine's iterative exploration computes exactly the reachable set. -/
theorem iter_exists_iff_reach (edge : V → V → Prop) (roots : V → Prop) (w : V) :
    (∃ n : Nat, iter edge roots n w) ↔ Reach edge roots w :=
  ⟨fun ⟨n, hn⟩ => iter_imp_reach edge roots n w hn, reach_imp_iter edge roots w⟩

/-- **Soundness and completeness of the isolation engine's null-escape check.**
The engine reports a null escape across the isolation boundary if and only if
some unowned (null-owner) node is reachable from the boundary roots in the heap
reference graph. -/
theorem null_escape_iff_unowned_reachable
    (edge : V → V → Prop) (roots : V → Prop) (owner : V → Option D) :
    NullEscape edge roots owner ↔ ∃ w, Reach edge roots w ∧ Unowned owner w := by
  constructor
  · rintro ⟨n, w, hw, hnull⟩
    exact ⟨w, iter_imp_reach edge roots n w hw, hnull⟩
  · rintro ⟨w, hw, hnull⟩
    obtain ⟨n, hn⟩ := reach_imp_iter edge roots w hw
    exact ⟨n, w, hn, hnull⟩

end PCA.Isolation

import Mathlib
import RequestProject.PCA.Isolation

/-!
# Mathlib restatement of the null-escape criterion

The core development in `RequestProject/PCA/Isolation.lean` is self-contained
(its mandated header is a module docstring, after which Lean forbids `import`
lines).  Here we connect it to Mathlib: the reachability relation used there is
literally `Relation.ReflTransGen`, and the main theorem is restated with
Mathlib's `Set` API.

Mathlib lemmas used: `Relation.ReflTransGen.refl`, `Relation.ReflTransGen.tail`,
`Relation.ReflTransGen.head`, `Set.mem_iUnion`, `Set.Subset.antisymm`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Isolation

universe u v

variable {V : Type u} {D : Type v}

/-- The bespoke closure `PCA.Isolation.Reaches` agrees with Mathlib's
`Relation.ReflTransGen`. -/
theorem reaches_iff_reflTransGen (edge : V → V → Prop) (a b : V) :
    Reaches edge a b ↔ Relation.ReflTransGen edge a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail hbc
  · intro h
    induction h with
    | refl => exact Reaches.refl a
    | tail _ hbc ih => exact ih.tail hbc

/-- Set-valued version of the engine's discovered frontier after `n` steps. -/
def iterSet (edge : V → V → Prop) (roots : Set V) (n : Nat) : Set V :=
  {w | iter edge (· ∈ roots) n w}

/-- Set-valued reachable set, phrased with `Relation.ReflTransGen`. -/
def reachSet (edge : V → V → Prop) (roots : Set V) : Set V :=
  {w | ∃ r ∈ roots, Relation.ReflTransGen edge r w}

/-- The engine's iterative exploration computes exactly the reachable set,
in Mathlib's `Set` language. -/
theorem iUnion_iterSet_eq_reachSet (edge : V → V → Prop) (roots : Set V) :
    (⋃ n : Nat, iterSet edge roots n) = reachSet edge roots := by
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hw
    obtain ⟨r, hr, hrw⟩ := iter_imp_reach edge (· ∈ roots) n w hn
    exact ⟨r, hr, (reaches_iff_reflTransGen edge r w).1 hrw⟩
  · rintro w ⟨r, hr, hrw⟩
    obtain ⟨n, hn⟩ :=
      reach_imp_iter edge (· ∈ roots) w ⟨r, hr, (reaches_iff_reflTransGen edge r w).2 hrw⟩
    exact Set.mem_iUnion.2 ⟨n, hn⟩

/-- Mathlib-flavoured restatement: the isolation engine signals a null escape iff
some node with `null` owner lies in the `Relation.ReflTransGen`-reachable set of
the boundary roots. -/
theorem null_escape_iff_unowned_reachable_set
    (edge : V → V → Prop) (roots : Set V) (owner : V → Option D) :
    NullEscape edge (· ∈ roots) owner ↔
      ∃ w ∈ reachSet edge roots, owner w = none := by
  rw [null_escape_iff_unowned_reachable]
  constructor
  · rintro ⟨w, ⟨r, hr, hrw⟩, hnull⟩
    exact ⟨w, ⟨r, hr, (reaches_iff_reflTransGen edge r w).1 hrw⟩, hnull⟩
  · rintro ⟨w, ⟨r, hr, hrw⟩, hnull⟩
    exact ⟨w, ⟨r, hr, (reaches_iff_reflTransGen edge r w).2 hrw⟩, hnull⟩

end PCA.Isolation

