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

lemma mon_mul {n : ℕ} (T U : Finset (Fin n)) : mon T * mon U = mon (symmDiff T U) := by
  funext x
  set a : Fin n → ZMod 3 := fun i => sgn (x i) with ha
  have d1 : Disjoint (T \ U) (T ∩ U) := by
    simp [Finset.disjoint_left]; tauto
  have d2 : Disjoint (U \ T) (T ∩ U) := by
    simp [Finset.disjoint_left]; tauto
  have d3 : Disjoint (T \ U) (U \ T) := by
    simp [Finset.disjoint_left]; tauto
  have e1 : (∏ i ∈ T, a i) = (∏ i ∈ T \ U, a i) * ∏ i ∈ T ∩ U, a i := by
    rw [← Finset.prod_union d1]
    congr 1
    ext i; by_cases h : i ∈ U <;> simp [h]
  have e2 : (∏ i ∈ U, a i) = (∏ i ∈ U \ T, a i) * ∏ i ∈ T ∩ U, a i := by
    rw [← Finset.prod_union d2]
    congr 1
    ext i; by_cases h : i ∈ T <;> simp [h]
  have e3 : (∏ i ∈ symmDiff T U, a i) = (∏ i ∈ T \ U, a i) * ∏ i ∈ U \ T, a i := by
    rw [← Finset.prod_union d3]; rfl
  have hsq : (∏ i ∈ T ∩ U, a i) * (∏ i ∈ T ∩ U, a i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun i _ => sgn_sq (x i))
  show (∏ i ∈ T, a i) * (∏ i ∈ U, a i) = ∏ i ∈ symmDiff T U, a i
  rw [e1, e2, e3]
  calc (∏ i ∈ T \ U, a i) * (∏ i ∈ T ∩ U, a i) * ((∏ i ∈ U \ T, a i) * ∏ i ∈ T ∩ U, a i)
      = ((∏ i ∈ T \ U, a i) * (∏ i ∈ U \ T, a i)) *
        ((∏ i ∈ T ∩ U, a i) * (∏ i ∈ T ∩ U, a i)) := by ring
    _ = (∏ i ∈ T \ U, a i) * ∏ i ∈ U \ T, a i := by rw [hsq]; ring

