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

lemma card_filter_card_le (N K : ℕ) :
    ((Finset.univ : Finset (Finset (Fin N))).filter (fun T => T.card ≤ K)).card
      = ∑ k ∈ Finset.range (K + 1), N.choose k := by
  classical
  have hmaps : Set.MapsTo Finset.card
      (((Finset.univ : Finset (Finset (Fin N))).filter (fun T => T.card ≤ K)) : Set (Finset (Fin N)))
      ((Finset.range (K + 1) : Finset ℕ) : Set ℕ) := by
    intro T hT
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hT
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_range] at hk
  have hset : ({T ∈ {T ∈ (Finset.univ : Finset (Finset (Fin N))) | T.card ≤ K} | T.card = k})
      = Finset.powersetCard k (Finset.univ : Finset (Fin N)) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ]
    omega
  rw [hset, Finset.card_powersetCard]
  simp

/-- Half of the binomial coefficients of `2m` sum to at most `4^m / 2`. -/
