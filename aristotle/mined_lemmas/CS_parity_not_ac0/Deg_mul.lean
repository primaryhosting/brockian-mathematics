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

lemma Deg_mul {n k k' : ℕ} {f g : Fn n} (hf : f ∈ Deg n k) (hg : g ∈ Deg n k') :
    f * g ∈ Deg n (k + k') := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      simp only [monSet, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter] at hf
      obtain ⟨T, ⟨-, hT⟩, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          simp only [monSet, Finset.coe_image, Set.mem_image, Finset.mem_coe,
            Finset.mem_filter] at hg
          obtain ⟨U, ⟨-, hU⟩, rfl⟩ := hg
          rw [mon_mul]
          exact mon_mem_Deg (le_trans (card_symmDiff_le T U) (Nat.add_le_add hT hU))
      | zero => simp
      | add g₁ g₂ _ _ ih₁ ih₂ =>
          have : mon T * (g₁ + g₂) = mon T * g₁ + mon T * g₂ := by ring
          rw [this]; exact Submodule.add_mem _ ih₁ ih₂
      | smul a g _ ih =>
          have : mon T * (a • g) = a • (mon T * g) := by
            funext x; simp [Pi.smul_apply]; ring
          rw [this]; exact Submodule.smul_mem _ _ ih
  | zero => simp
  | add f₁ f₂ _ _ ih₁ ih₂ =>
      have : (f₁ + f₂) * g = f₁ * g + f₂ * g := by ring
      rw [this]; exact Submodule.add_mem _ ih₁ ih₂
  | smul a f _ ih =>
      have : (a • f) * g = a • (f * g) := by
        funext x; simp [Pi.smul_apply]; ring
      rw [this]; exact Submodule.smul_mem _ _ ih

