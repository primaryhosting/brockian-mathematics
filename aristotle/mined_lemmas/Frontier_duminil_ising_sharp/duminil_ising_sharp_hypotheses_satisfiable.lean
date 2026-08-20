/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-! ## The finite-volume Ising model -/

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The real spin value `±1` attached to a Boolean spin variable. -/

theorem duminil_ising_sharp_hypotheses_satisfiable :
    (∀ β, β < (0:ℝ) → ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      ∀ n, twoPoint β (fun _ _ : Bool => (0:ℝ)) true (fun _ => 0) n ≤ C * Real.exp (-a * n)) ∧
    (∀ β, (0:ℝ) ≤ β → (1:ℝ) * (β - 0) ≤ id β) ∧
    (∀ x y : Bool, x ≠ y → corr 0 (fun _ _ : Bool => (0:ℝ)) x y = 0) := by
  have hne : (Finset.univ.filter (fun v : Bool => (0:ℕ) = 0)).Nonempty := ⟨true, by simp⟩
  have hzero : ∀ (β : ℝ) (n : ℕ), n ≠ 0 →
      twoPoint β (fun _ _ : Bool => (0:ℝ)) true (fun _ => 0) n = 0 := by
    intro β n hn
    rw [twoPoint, dif_neg]
    simp [Ne.symm hn]
  refine duminil_ising_sharp (fun _ _ : Bool => (0:ℝ)) true (fun _ => 0) 0 1 id (fun _ => 1)
    ?_ ?_ rfl (Continuous.continuousOn continuous_id) (fun β _ => hasDerivAt_id β)
    (fun β _ => le_refl 1)
  · intro β n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      rw [twoPoint, dif_pos hne]
      refine le_trans ?_ (Finset.le_sup' (fun v => corr β (fun _ _ : Bool => (0:ℝ)) true v)
        (show true ∈ Finset.univ.filter (fun v : Bool => (0:ℕ) = 0) by simp))
      rw [corr_self]
      norm_num
    · rw [hzero β n (by omega)]
  · intro β _
    exact ⟨1, le_refl 1, 0, by norm_num, fun n => by rw [hzero β (n+1) (by omega)]; norm_num⟩

end Frontier

