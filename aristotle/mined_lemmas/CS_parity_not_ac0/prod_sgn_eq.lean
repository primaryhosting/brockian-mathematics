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

lemma prod_sgn_eq {n : ℕ} (x : Bits n) (s : Finset (Fin n)) :
    (∏ i ∈ s, sgn (x i)) = (-1 : ZMod 3) ^ ((s.filter (fun i => x i = true)).card) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.filter_insert]
      by_cases hxa : x a = true
      · have : a ∉ s.filter (fun i => x i = true) := fun h => ha (Finset.mem_filter.1 h).1
        rw [if_pos hxa, Finset.card_insert_of_notMem this]
        simp [sgn, hxa]
        ring
      · have hxa' : x a = false := by simpa using hxa
        rw [if_neg hxa]
        simp [sgn, hxa']

/-- The `±1`-encoding of parity is the full monomial. -/
