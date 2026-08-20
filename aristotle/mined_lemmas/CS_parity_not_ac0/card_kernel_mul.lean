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

lemma card_kernel_mul {m : ℕ} (a : Fin m → ZMod 3) (i₀ : Fin m) (h : a i₀ = 1) :
    3 * ((Finset.univ : Finset (Fin m → ZMod 3)).filter
      (fun v => ∑ i, v i * a i = 0)).card = 3 ^ m := by
  classical
  set φ : (Fin m → ZMod 3) → ZMod 3 := fun v => ∑ i, v i * a i with hφ
  have hshift : ∀ (v : Fin m → ZMod 3) (t : ZMod 3),
      φ (v + fun i => if i = i₀ then t else 0) = φ v + t := by
    intro v t
    simp only [hφ, Pi.add_apply]
    have e1 : ∀ i : Fin m, (v i + if i = i₀ then t else 0) * a i
        = v i * a i + (if i = i₀ then t * a i else 0) := by
      intro i
      by_cases hi : i = i₀
      · simp [hi]; ring
      · simp [hi]
    rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq' Finset.univ i₀ (fun i => t * a i)]
    simp [h]
  have hcard : ∀ t : ZMod 3,
      ((Finset.univ : Finset (Fin m → ZMod 3)).filter (fun v => φ v = t)).card
      = ((Finset.univ : Finset (Fin m → ZMod 3)).filter (fun v => φ v = 0)).card := by
    intro t
    apply Finset.card_bij (fun v _ => v + fun i => if i = i₀ then -t else 0)
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [hshift v (-t), hv]; ring
    · intro v _ w _ hvw
      exact add_right_cancel hvw
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨w + fun i => if i = i₀ then t else 0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hshift w t, hw]; ring
      · funext i; by_cases hi : i = i₀ <;> simp [hi]
  have htotal : ∑ t : ZMod 3,
      ((Finset.univ : Finset (Fin m → ZMod 3)).filter (fun v => φ v = t)).card = 3 ^ m := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := φ) (fun v _ => Finset.mem_univ _)]
    simp [Finset.card_univ, ZMod.card]
  have hgoal : (Finset.univ.filter (fun v : Fin m → ZMod 3 => ∑ i, v i * a i = 0))
      = Finset.univ.filter (fun v => φ v = 0) := rfl
  rw [hgoal, ← htotal, Finset.sum_congr rfl (fun t _ => hcard t), Finset.sum_const,
    Finset.card_univ, ZMod.card, smul_eq_mul]

/-- Counting matrices all of whose rows lie in a fixed set of vectors. -/
