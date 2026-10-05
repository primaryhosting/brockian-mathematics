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
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- `iter f t g` is the `t`-fold iterate `f^[t] g`. -/
def iter {G : Type u} (f : G → G) : Nat → G → G
  | 0, g => g
  | t + 1, g => f (iter f t g)

@[simp] theorem iter_zero {G : Type u} (f : G → G) (g : G) : iter f 0 g = g := rfl

@[simp] theorem iter_succ {G : Type u} (f : G → G) (t : Nat) (g : G) :
    iter f (t + 1) g = f (iter f t g) := rfl

/-- For every `m ≥ 1` there is a power of two in the interval `[m, 2 * m)`;
this is what makes the number of amplification rounds logarithmic. -/
theorem exists_pow_two_ge (m : Nat) (hm : 1 ≤ m) : ∃ t : Nat, m ≤ 2 ^ t ∧ 2 ^ t < 2 * m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact ⟨0, by omega, by omega⟩
    · obtain ⟨t, h1, h2⟩ := ih h
      by_cases hc : m + 1 ≤ 2 ^ t
      · exact ⟨t, hc, by omega⟩
      · have hEq : 2 ^ t = m := by omega
        refine ⟨t + 1, ?_, ?_⟩ <;> rw [Nat.pow_succ] <;> omega

/-- Doubling the scaled unsat value: `2 ^ (t + 1) * u = 2 * (2 ^ t * u)`. -/
theorem two_pow_succ_mul (t u : Nat) : 2 ^ (t + 1) * u = 2 * (2 ^ t * u) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ t) 2, Nat.mul_assoc]

section Dinur

variable {G : Type u}

/-- **Amplification.**  If one step of Dinur's transformation at least doubles the
unsat value (until the target value `gap` is reached), then `t` steps multiply it by
`2 ^ t` (until `gap` is reached). -/
theorem unsat_iter_lower_bound (unsat : G → Nat) (amplify : G → G) (gap : Nat)
    (hamplify : ∀ g, min gap (2 * unsat g) ≤ unsat (amplify g)) :
    ∀ (t : Nat) (g : G), min gap (2 ^ t * unsat g) ≤ unsat (iter amplify t g) := by
  intro t
  induction t with
  | zero => intro g; simp; omega
  | succ t ih =>
    intro g
    have hstep : min gap (2 * unsat (iter amplify t g)) ≤ unsat (iter amplify (t + 1) g) := by
      rw [iter_succ]; exact hamplify _
    have ihg := ih g
    rcases Nat.le_total gap (2 ^ t * unsat g) with h | h
    · have hgap : gap ≤ unsat (iter amplify t g) := by omega
      omega
    · have hdouble : 2 ^ (t + 1) * unsat g ≤ 2 * unsat (iter amplify t g) := by
        rw [two_pow_succ_mul]; omega
      omega

/-- **Completeness** is preserved by iterating the amplification step. -/
theorem unsat_iter_zero (unsat : G → Nat) (amplify : G → G)
    (hcomplete : ∀ g, unsat g = 0 → unsat (amplify g) = 0) :
    ∀ (t : Nat) (g : G), unsat g = 0 → unsat (iter amplify t g) = 0 := by
  intro t
  induction t with
  | zero => intro g hg; simpa using hg
  | succ t ih => intro g hg; rw [iter_succ]; exact hcomplete _ (ih g hg)

/-- **Size blow-up** after `t` steps is at most `C ^ t`. -/
theorem size_iter_le (size : G → Nat) (amplify : G → G) (C : Nat)
    (hsize : ∀ g, size (amplify g) ≤ C * size g) :
    ∀ (t : Nat) (g : G), size (iter amplify t g) ≤ C ^ t * size g := by
  intro t
  induction t with
  | zero => intro g; simp
  | succ t ih =>
    intro g
    rw [iter_succ]
    calc size (amplify (iter amplify t g)) ≤ C * size (iter amplify t g) := hsize _
      _ ≤ C * (C ^ t * size g) := Nat.mul_le_mul_left _ (ih g)
      _ = C ^ (t + 1) * size g := by
          rw [Nat.pow_succ, Nat.mul_comm (C ^ t) C, Nat.mul_assoc]

/--
**Dinur's gap amplification yields the PCP theorem** (abstract combinatorial form).

`G` is a type of constraint systems.  Each `g : G` has a `size` (number of constraints)
and an *unsatisfiability value* — the fraction of constraints violated by a best
assignment — which is recorded here in scaled integer form: the true value is
`unsat g / D` for a fixed denominator `D ≥ 1`.  Likewise the target constant gap is
`gap / D`.

The hypotheses are exactly the properties of one round of Dinur's transformation:

* `hsize`     : the size grows by at most a constant factor `C`;
* `hcomplete` : perfect completeness is preserved (satisfiable stays satisfiable);
* `hamplify`  : the unsat value at least doubles, until the constant `gap / D` is reached;
* `hsound`    : an unsatisfiable system violates at least one constraint, i.e. its unsat
                value `unsat g / D` is at least `1 / size g`.

Conclusion: for every size bound `n ≥ 1` there is a round count `t` that is only
*logarithmic* in `n` (witnessed by `2 ^ t ≤ 2 * (gap * n) + 1`), so that the total size
blow-up `C ^ t` is polynomial in `n`, and after `t` rounds every system of size at most
`n` is transformed into one that

* is still perfectly satisfiable if the original was, and
* otherwise has unsat value at least the *constant* `gap / D`.

This constant-gap, polynomial-size reduction is precisely the content of the PCP
theorem as obtained by Dinur's gap-amplification argument.
-/
theorem pcp_dinur {G : Type u} (size : G → Nat) (unsat : G → Nat) (amplify : G → G)
    (D C gap : Nat) (hD : 1 ≤ D)
    (hsize : ∀ g, size (amplify g) ≤ C * size g)
    (hcomplete : ∀ g, unsat g = 0 → unsat (amplify g) = 0)
    (hamplify : ∀ g, min gap (2 * unsat g) ≤ unsat (amplify g))
    (hsound : ∀ g, 0 < unsat g → D ≤ size g * unsat g)
    (n : Nat) (hn : 1 ≤ n) :
    ∃ t : Nat, 2 ^ t ≤ 2 * (gap * n) + 1 ∧
      ∀ g : G, size g ≤ n →
        size (iter amplify t g) ≤ C ^ t * n ∧
        (unsat g = 0 → unsat (iter amplify t g) = 0) ∧
        (0 < unsat g → gap ≤ unsat (iter amplify t g)) := by
  -- Choose `t` with `gap * n ≤ 2 ^ t < 2 * (gap * n) + 1`.
  obtain ⟨t, hge, hlt⟩ : ∃ t : Nat, gap * n ≤ 2 ^ t ∧ 2 ^ t ≤ 2 * (gap * n) + 1 := by
    rcases Nat.eq_zero_or_pos (gap * n) with h | h
    · exact ⟨0, by omega, by omega⟩
    · obtain ⟨t, h1, h2⟩ := exists_pow_two_ge (gap * n) h
      exact ⟨t, h1, by omega⟩
  refine ⟨t, hlt, ?_⟩
  intro g hg
  refine ⟨?_, unsat_iter_zero unsat amplify hcomplete t g, ?_⟩
  · exact Nat.le_trans (size_iter_le size amplify C hsize t g) (Nat.mul_le_mul_left _ hg)
  · intro hpos
    -- The unsat value of `g` is at least `1 / n`, so after `t` rounds it exceeds `gap / D`.
    have hkey : gap ≤ 2 ^ t * unsat g := by
      have h1 : D ≤ size g * unsat g := hsound g hpos
      have h2 : size g * unsat g ≤ n * unsat g := Nat.mul_le_mul_right _ hg
      have h3 : n * gap ≤ 2 ^ t * D := by
        calc n * gap = gap * n := Nat.mul_comm _ _
          _ ≤ 2 ^ t := hge
          _ = 2 ^ t * 1 := (Nat.mul_one _).symm
          _ ≤ 2 ^ t * D := Nat.mul_le_mul_left _ hD
      have h4 : n * gap ≤ n * (2 ^ t * unsat g) := by
        calc n * gap ≤ 2 ^ t * D := h3
          _ ≤ 2 ^ t * (n * unsat g) := Nat.mul_le_mul_left _ (Nat.le_trans h1 h2)
          _ = n * (2 ^ t * unsat g) := by
              rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (2 ^ t) n]
      exact Nat.le_of_mul_le_mul_left h4 hn
    have hlb := unsat_iter_lower_bound unsat amplify gap hamplify t g
    omega

end Dinur

/-- Non-vacuity check: the hypotheses of `pcp_dinur` are simultaneously satisfiable with a
strictly positive target gap (here `gap / D = 4`, `C = 2`), so the theorem is not vacuous. -/
example : ∃ (size unsat : Nat → Nat) (amplify : Nat → Nat) (D C gap : Nat),
    1 ≤ D ∧ 0 < gap ∧
    (∀ g, size (amplify g) ≤ C * size g) ∧
    (∀ g, unsat g = 0 → unsat (amplify g) = 0) ∧
    (∀ g, min gap (2 * unsat g) ≤ unsat (amplify g)) ∧
    (∀ g, 0 < unsat g → D ≤ size g * unsat g) := by
  refine ⟨fun g => 2 ^ g, fun g => min 4 (2 ^ g), fun g => g + 1, 1, 2, 4,
    Nat.le_refl 1, by omega, ?_, ?_, ?_, ?_⟩
  · intro g
    show 2 ^ (g + 1) ≤ 2 * 2 ^ g
    rw [Nat.pow_succ]; omega
  · intro g hg
    have h1 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
    simp only [] at hg
    omega
  · intro g
    show min 4 (2 * min 4 (2 ^ g)) ≤ min 4 (2 ^ (g + 1))
    rw [Nat.pow_succ]; omega
  · intro g _
    show 1 ≤ 2 ^ g * min 4 (2 ^ g)
    have h1 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
    have : 1 * 1 ≤ 2 ^ g * min 4 (2 ^ g) := Nat.mul_le_mul h1 (by omega)
    omega

end CS

