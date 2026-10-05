/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

/-! ## Policies

The isolation engine of a proof-carrying application reasons about *isolation
policies*: propositional constraints over atomic capabilities (permissions,
resource handles, ...).  A *state* of the machine is an assignment of a Boolean
truth value to every capability. -/

/-- Atomic capabilities are indexed by natural numbers. -/
abbrev Cap := Nat

/-- A machine state: which capabilities are currently granted. -/
abbrev State := Cap → Bool

/-- Isolation policies. -/
inductive Policy where
  | tt : Policy
  | ff : Policy
  | atom : Cap → Policy
  | neg : Policy → Policy
  | and : Policy → Policy → Policy
  | or : Policy → Policy → Policy
  deriving DecidableEq, Repr

namespace Policy

/-- Boolean semantics of a policy in a state. -/
def eval (s : State) : Policy → Bool
  | tt => true
  | ff => false
  | atom c => s c
  | neg p => !(eval s p)
  | and p q => (eval s p) && (eval s q)
  | or p q => (eval s p) || (eval s q)

@[simp] theorem eval_tt (s : State) : eval s tt = true := rfl
@[simp] theorem eval_ff (s : State) : eval s ff = false := rfl
@[simp] theorem eval_atom (s : State) (c : Cap) : eval s (atom c) = s c := rfl
@[simp] theorem eval_neg (s : State) (p : Policy) : eval s (neg p) = !(eval s p) := rfl
@[simp] theorem eval_and (s : State) (p q : Policy) :
    eval s (and p q) = ((eval s p) && (eval s q)) := rfl
@[simp] theorem eval_or (s : State) (p q : Policy) :
    eval s (or p q) = ((eval s p) || (eval s q)) := rfl

/-- The satisfaction relation: `Models s p` says that state `s` is a model of
the policy `p`. -/
def Models (s : State) (p : Policy) : Prop := eval s p = true

@[simp] theorem models_iff {p : Policy} {s : State} : Models s p ↔ eval s p = true := Iff.rfl

/-! ## Negation normal form -/

/-- `nnfAux b p` is the negation normal form of `p` (when `b = false`) or of
`¬ p` (when `b = true`). -/
def nnfAux : Bool → Policy → Policy
  | false, tt => tt
  | true, tt => ff
  | false, ff => ff
  | true, ff => tt
  | false, atom c => atom c
  | true, atom c => neg (atom c)
  | b, neg p => nnfAux (!b) p
  | false, and p q => and (nnfAux false p) (nnfAux false q)
  | true, and p q => or (nnfAux true p) (nnfAux true q)
  | false, or p q => or (nnfAux false p) (nnfAux false q)
  | true, or p q => and (nnfAux true p) (nnfAux true q)

/-- Negation normal form of a policy. -/
def nnf (p : Policy) : Policy := nnfAux false p

theorem eval_nnfAux (s : State) (p : Policy) :
    ∀ b : Bool, eval s (nnfAux b p) = (if b then !(eval s p) else eval s p) := by
  induction p with
  | tt => intro b; cases b <;> simp [nnfAux]
  | ff => intro b; cases b <;> simp [nnfAux]
  | atom c => intro b; cases b <;> simp [nnfAux]
  | neg p ih => intro b; cases b <;> simp [nnfAux, ih]
  | and p q ihp ihq => intro b; cases b <;> simp [nnfAux, ihp, ihq]
  | or p q ihp ihq => intro b; cases b <;> simp [nnfAux, ihp, ihq]

/-- Negation normal form preserves the semantics. -/
@[simp] theorem eval_nnf (s : State) (p : Policy) : eval s (nnf p) = eval s p := by
  simpa [nnf] using eval_nnfAux s p false

/-- A *literal*: a capability or a negated capability, or a constant. -/
def IsLiteral : Policy → Bool
  | tt => true
  | ff => true
  | atom _ => true
  | neg (atom _) => true
  | _ => false

/-- A policy is in negation normal form when every negation is applied to an
atomic capability. -/
def IsNNF : Policy → Bool
  | tt => true
  | ff => true
  | atom _ => true
  | neg (atom _) => true
  | neg _ => false
  | and p q => IsNNF p && IsNNF q
  | or p q => IsNNF p && IsNNF q

theorem isNNF_nnfAux (p : Policy) : ∀ b : Bool, IsNNF (nnfAux b p) = true := by
  induction p with
  | tt => intro b; cases b <;> simp [nnfAux, IsNNF]
  | ff => intro b; cases b <;> simp [nnfAux, IsNNF]
  | atom c => intro b; cases b <;> simp [nnfAux, IsNNF]
  | neg p ih => intro b; cases b <;> simp [nnfAux, ih]
  | and p q ihp ihq => intro b; cases b <;> simp [nnfAux, IsNNF, ihp, ihq]
  | or p q ihp ihq => intro b; cases b <;> simp [nnfAux, IsNNF, ihp, ihq]

theorem isNNF_nnf (p : Policy) : IsNNF (nnf p) = true := isNNF_nnfAux p false

/-! ## The disjunction split

The isolation engine cannot execute a policy containing a disjunction directly:
it must *split* it into a finite family of disjunction-free branches, each of
which is analysed in isolation.  `split` performs this splitting, distributing
conjunction over disjunction. -/

/-- Split a policy into a list of disjunction-free branches. -/
def split : Policy → List Policy
  | or p q => split p ++ split q
  | and p q => (split p).flatMap (fun a => (split q).map (fun b => and a b))
  | tt => [tt]
  | ff => [ff]
  | atom c => [atom c]
  | neg p => [neg p]

/-- A policy contains no disjunction (outside of the scope of a negation). -/
def IsDisjFree : Policy → Bool
  | tt => true
  | ff => true
  | atom _ => true
  | neg _ => true
  | and p q => IsDisjFree p && IsDisjFree q
  | or _ _ => false

/-- A *cube*: a conjunction of literals. -/
def IsCube : Policy → Bool
  | and p q => IsCube p && IsCube q
  | p => IsLiteral p

end Policy

open Policy

/-! ### Soundness and completeness of the split -/

/-- **Main theorem.** Splitting a policy into isolated, disjunction-free
branches preserves its semantics exactly: a state satisfies the policy if and
only if it satisfies one of the branches. -/
theorem disjunction_split_preserves_semantics (s : State) (p : Policy) :
    eval s p = true ↔ ∃ b ∈ split p, eval s b = true := by
  induction p with
  | tt => simp [split]
  | ff => simp [split]
  | atom c => simp [split]
  | neg p => simp [split]
  | or p q ihp ihq =>
      simp only [eval_or, Bool.or_eq_true, split, List.mem_append]
      constructor
      · rintro (h | h)
        · obtain ⟨b, hb, hb'⟩ := ihp.mp h; exact ⟨b, Or.inl hb, hb'⟩
        · obtain ⟨b, hb, hb'⟩ := ihq.mp h; exact ⟨b, Or.inr hb, hb'⟩
      · rintro ⟨b, hb | hb, hb'⟩
        · exact Or.inl (ihp.mpr ⟨b, hb, hb'⟩)
        · exact Or.inr (ihq.mpr ⟨b, hb, hb'⟩)
  | and p q ihp ihq =>
      simp only [eval_and, Bool.and_eq_true, split, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨a, ha, ha'⟩ := ihp.mp h1
        obtain ⟨c, hc, hc'⟩ := ihq.mp h2
        exact ⟨Policy.and a c, ⟨a, ha, c, hc, rfl⟩, by simp [ha', hc']⟩
      · rintro ⟨b, ⟨a, ha, c, hc, rfl⟩, hb'⟩
        simp only [eval_and, Bool.and_eq_true] at hb'
        exact ⟨ihp.mpr ⟨a, ha, hb'.1⟩, ihq.mpr ⟨c, hc, hb'.2⟩⟩

/-- Soundness: every branch of the split implies the original policy. -/
theorem split_sound (s : State) (p b : Policy) (hb : b ∈ split p)
    (h : eval s b = true) : eval s p = true :=
  (disjunction_split_preserves_semantics s p).mpr ⟨b, hb, h⟩

/-- Completeness: every model of the policy is a model of some branch. -/
theorem split_complete (s : State) (p : Policy) (h : eval s p = true) :
    ∃ b ∈ split p, eval s b = true :=
  (disjunction_split_preserves_semantics s p).mp h

/-- Satisfaction form: the models of a policy are exactly the states modelling
one of its branches. -/
theorem models_iff_exists_branch (s : State) (p : Policy) :
    Models s p ↔ ∃ b ∈ split p, Models s b :=
  disjunction_split_preserves_semantics s p

/-! ### Structural guarantees on the branches -/

/-- The split of a policy is never empty. -/
theorem split_ne_nil (p : Policy) : split p ≠ [] := by
  induction p with
  | tt => simp [split]
  | ff => simp [split]
  | atom c => simp [split]
  | neg p => simp [split]
  | or p q ihp _ => simp [split, ihp]
  | and p q ihp ihq =>
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ ihp
      obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ ihq
      have hmem : Policy.and a c ∈ split (Policy.and p q) := by
        simp only [split, List.mem_flatMap, List.mem_map]
        exact ⟨a, ha, c, hc, rfl⟩
      exact List.ne_nil_of_mem hmem

/-- Every branch produced by the split is disjunction free. -/
theorem split_disjFree (p : Policy) : ∀ b ∈ split p, IsDisjFree b = true := by
  induction p with
  | tt => simp [split, IsDisjFree]
  | ff => simp [split, IsDisjFree]
  | atom c => simp [split, IsDisjFree]
  | neg p => simp [split, IsDisjFree]
  | or p q ihp ihq =>
      intro b hb
      rcases List.mem_append.mp hb with h | h
      · exact ihp b h
      · exact ihq b h
  | and p q ihp ihq =>
      intro b hb
      simp only [split, List.mem_flatMap, List.mem_map] at hb
      obtain ⟨a, ha, c, hc, rfl⟩ := hb
      simp [IsDisjFree, ihp a ha, ihq c hc]

/-- On a policy in negation normal form, every branch is a cube: a conjunction
of literals. -/
theorem split_isCube_of_isNNF (p : Policy) (hp : IsNNF p = true) :
    ∀ b ∈ split p, IsCube b = true := by
  induction p with
  | tt => simp [split, IsCube, IsLiteral]
  | ff => simp [split, IsCube, IsLiteral]
  | atom c => simp [split, IsCube, IsLiteral]
  | neg p =>
      intro b hb
      simp only [split, List.mem_singleton] at hb
      subst hb
      cases p <;> simp_all [IsNNF, IsCube, IsLiteral]
  | or p q ihp ihq =>
      simp only [IsNNF, Bool.and_eq_true] at hp
      intro b hb
      rcases List.mem_append.mp hb with h | h
      · exact ihp hp.1 b h
      · exact ihq hp.2 b h
  | and p q ihp ihq =>
      simp only [IsNNF, Bool.and_eq_true] at hp
      intro b hb
      simp only [split, List.mem_flatMap, List.mem_map] at hb
      obtain ⟨a, ha, c, hc, rfl⟩ := hb
      simp [IsCube, ihp hp.1 a ha, ihq hp.2 c hc]

/-! ## The isolation pipeline -/

/-- The isolation engine: normalise, then split into isolated branches. -/
def isolate (p : Policy) : List Policy := split (nnf p)

/-- **Correctness of the isolation engine.** The isolation pipeline produces a
nonempty family of cubes whose union of models is exactly the model set of the
original policy. -/
theorem isolate_correct (p : Policy) :
    isolate p ≠ [] ∧
    (∀ b ∈ isolate p, IsCube b = true) ∧
    (∀ s : State, eval s p = true ↔ ∃ b ∈ isolate p, eval s b = true) := by
  refine ⟨split_ne_nil _, split_isCube_of_isNNF _ (isNNF_nnf p), fun s => ?_⟩
  rw [← eval_nnf s p]
  exact disjunction_split_preserves_semantics s (nnf p)

/-! ## Sanity checks -/

section Examples

/-- `(c₀ ∨ c₁) ∧ c₂` splits into the two isolated branches `c₀ ∧ c₂` and
`c₁ ∧ c₂`. -/
example :
    split (Policy.and (Policy.or (Policy.atom 0) (Policy.atom 1)) (Policy.atom 2)) =
      [Policy.and (Policy.atom 0) (Policy.atom 2),
       Policy.and (Policy.atom 1) (Policy.atom 2)] := by
  decide

/-- Negation normal form pushes negations down to the capabilities. -/
example :
    nnf (Policy.neg (Policy.and (Policy.atom 0) (Policy.atom 1))) =
      Policy.or (Policy.neg (Policy.atom 0)) (Policy.neg (Policy.atom 1)) := by
  decide

end Examples

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

