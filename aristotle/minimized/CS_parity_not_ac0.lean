import RequestProject.Basic

/-!
# Unbounded fan-in Boolean circuits, the class `AC⁰`, and `PARITY`

A `Circuit n` is a Boolean circuit on `n` inputs built from constants, input
variables, negations, and *unbounded fan-in* `AND`/`OR` gates.

* `Circuit.depth` counts the maximal number of `AND`/`OR` gates on a root-to-leaf
  path (negations are free, as is standard for `AC⁰`).
* `Circuit.size` counts the number of `AND`/`OR` gates.

`InAC0 f` says that the family `f` is computed by circuits of some fixed depth and
polynomial size.  Making negations free and not counting them in the size only
makes the class larger, hence the lower bound proved later stronger.
-/

namespace CS

/-- Boolean circuits with unbounded fan-in `AND`/`OR` gates. -/
inductive Circuit (n : ℕ) where
  | const : Bool → Circuit n
  | var : Fin n → Circuit n
  | neg : Circuit n → Circuit n
  | or : (m : ℕ) → (Fin m → Circuit n) → Circuit n
  | and : (m : ℕ) → (Fin m → Circuit n) → Circuit n

namespace Circuit

/-- The Boolean function computed by a circuit. -/

def eval {n : ℕ} : Circuit n → Bits n → Bool
  | const b, _ => b
  | var i, x => x i
  | neg c, x => !(eval c x)
  | or _ f, x => decide (∃ i, eval (f i) x = true)
  | and _ f, x => decide (∀ i, eval (f i) x = true)

/-- The depth of a circuit: the maximal number of `AND`/`OR` gates on a path. -/

def depth {n : ℕ} : Circuit n → ℕ
  | const _ => 0
  | var _ => 0
  | neg c => depth c
  | or _ f => 1 + Finset.univ.sup (fun i => depth (f i))
  | and _ f => 1 + Finset.univ.sup (fun i => depth (f i))

/-- The size of a circuit: the number of `AND`/`OR` gates. -/

def size {n : ℕ} : Circuit n → ℕ
  | const _ => 0
  | var _ => 0
  | neg c => size c
  | or _ f => 1 + ∑ i, size (f i)
  | and _ f => 1 + ∑ i, size (f i)

def InAC0 (f : (n : ℕ) → Bits n → Bool) : Prop :=
  ∃ d c : ℕ, ∀ n : ℕ, ∃ C : Circuit n, C.depth ≤ d ∧ C.size ≤ (n + 2) ^ c ∧
    ∀ x, C.eval x = f n x

/-- The parity function. -/

def parity (n : ℕ) (x : Bits n) : Bool :=
  decide (Odd ((Finset.univ.filter (fun i => x i = true)).card))

theorem or_in_ac0 : InAC0 (fun _n x => decide (∃ i, x i = true)) := by
  refine ⟨1, 0, fun n => ⟨Circuit.or n (fun i => Circuit.var i), ?_, ?_, ?_⟩⟩
  · simp
  · simp
  · intro x; simp

/-- **PARITY is not in `AC⁰`** (Razborov–Smolensky / Håstad).

There is no family of constant-depth, polynomial-size, unbounded fan-in Boolean
circuits computing the parity function. -/
