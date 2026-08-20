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

lemma card_rows_filter {m ℓ : ℕ} (P : (Fin m → ZMod 3) → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter (fun c => ∀ j, P (c j))).card
      = ((Finset.univ : Finset (Fin m → ZMod 3)).filter P).card ^ ℓ := by
  classical
  have : ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter (fun c => ∀ j, P (c j)))
      = Fintype.piFinset (fun _ : Fin ℓ => (Finset.univ : Finset (Fin m → ZMod 3)).filter P) := by
    ext c
    simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset]
  simp

/-- Approximating an unbounded fan-in `OR` of `0/1`-valued low degree functions. -/
