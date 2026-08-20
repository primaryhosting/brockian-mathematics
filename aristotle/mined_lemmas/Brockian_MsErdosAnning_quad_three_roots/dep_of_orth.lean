import Mathlib

/-!
# The Erdős–Anning theorem

An infinite set of points in the Euclidean plane whose pairwise distances are all integers
must be collinear.

## Proof outline

Assume `S` is infinite with integral pairwise distances and pick `A ≠ B` in `S`.  If some
`C ∈ S` is off the line `AB`, then `A`, `B`, `C` form a non-degenerate triangle.  For every
`P ∈ S` the two differences `dist P A - dist P B` and `dist P A - dist P C` are integers
bounded in absolute value by `dist A B` and `dist A C` respectively, so only finitely many
pairs of values occur (`finite_of_not_collinear`).  The heart of the argument (`key`) shows
that three *distinct* points cannot share the same pair of differences: writing
`⟪P - A, B - A⟫` in terms of the distances (`inner_formula`) shows that all such points lie
on a common line `A + p + x • q` with `x = dist P A`, and `‖p + x • q‖ = x` can hold for at
most two values of `x` unless `p = 0` and `‖q‖ = 1` (`key_p_zero`), in which case `B - A`
and `C - A` are both multiples of `q`, contradicting non-collinearity.  Hence `S` would be
finite, a contradiction.
-/

namespace Brockian.MsErdosAnning

open scoped RealInnerProductSpace

/-! ### Auxiliary algebraic lemmas -/

/-- A real quadratic with three distinct roots is identically zero. -/

lemma dep_of_orth {u w z : EuclideanSpace ℝ (Fin 2)} (hu : u ≠ 0)
    (h1 : ⟪u, w⟫ = 0) (h2 : ⟪u, z⟫ = 0) :
    ∃ s t : ℝ, ¬ (s = 0 ∧ t = 0) ∧ s • w = t • z := by
  by_cases hw : w = 0
  · exact ⟨1, 0, by simp, by simp [hw]⟩
  by_cases hz : z = 0
  · exact ⟨0, 1, by simp, by simp [hz]⟩
  -- Both w ≠ 0 and z ≠ 0
  -- Use components: for u = ⟨u₁, u₂⟩, w = ⟨w₁, w₂⟩, we have u₁ * w₁ + u₂ * w₂ = 0
  set u₁ := u 0 with hu1_def
  set u₂ := u 1 with hu2_def
  set w₁ := w 0 with hw1_def
  set w₂ := w 1 with hw2_def
  set z₁ := z 0 with hz1_def
  set z₂ := z 1 with hz2_def
  have huw : u₁ * w₁ + u₂ * w₂ = 0 := by simp [inner] at h1; linarith
  have huz : u₁ * z₁ + u₂ * z₂ = 0 := by simp [inner] at h2; linarith
  -- Case split on whether z₁ ≠ 0
  by_cases hz₁_nonzero : z₁ ≠ 0
  · -- Use s = z₁, t = w₁
    use z₁, w₁
    constructor
    · intro ⟨hz₁, hw₁⟩; exact hz₁_nonzero hz₁
    · -- Show z₁ • w = w₁ • z
      ext i
      fin_cases i
      · simp; ring
      · -- Need: z₁ * w₂ = w₁ * z₂
        -- From huw: u₁ * w₁ + u₂ * w₂ = 0, so u₁ * w₁ = -u₂ * w₂
        -- From huz: u₁ * z₁ + u₂ * z₂ = 0, so u₁ * z₁ = -u₂ * z₂
        -- Multiply first by z₂: u₁ * w₁ * z₂ = -u₂ * w₂ * z₂
        -- Multiply second by w₂: u₁ * z₁ * w₂ = -u₂ * z₂ * w₂
        -- These are equal, so u₁ * w₁ * z₂ = u₁ * z₁ * w₂
        have key : u₁ * w₁ * z₂ = u₁ * z₁ * w₂ := by
          have eq1 : u₁ * w₁ = -u₂ * w₂ := by linarith
          have eq2 : u₁ * z₁ = -u₂ * z₂ := by linarith
          calc u₁ * w₁ * z₂ = (-u₂ * w₂) * z₂ := by rw [eq1]
            _ = -u₂ * w₂ * z₂ := by ring
            _ = -u₂ * z₂ * w₂ := by ring
            _ = (u₁ * z₁) * w₂ := by rw [eq2]
            _ = u₁ * z₁ * w₂ := by ring
        have hcross : w₁ * z₂ = z₁ * w₂ := by
          by_cases hu₁ : u₁ = 0
          · -- If u₁ = 0, then u₂ ≠ 0, so from huw/huz: w₂ = 0 and z₂ = 0
            have hu₂ : u₂ ≠ 0 := fun hu₂_zero => hu (by
              ext i; fin_cases i <;> [exact hu1_def.symm.trans hu₁; exact hu2_def.symm.trans hu₂_zero])
            have huw' : u₂ * w₂ = 0 := by rw [hu₁, zero_mul, zero_add] at huw; exact huw
            have huz' : u₂ * z₂ = 0 := by rw [hu₁, zero_mul, zero_add] at huz; exact huz
            have hw₂_zero : w₂ = 0 := (mul_eq_zero.mp huw').resolve_left hu₂
            have hz₂_zero : z₂ = 0 := (mul_eq_zero.mp huz').resolve_left hu₂
            simp [hw₂_zero, hz₂_zero]
          · -- If u₁ ≠ 0, cancel u₁ from key
            have key' : u₁ * (w₁ * z₂) = u₁ * (z₁ * w₂) := by linarith
            exact mul_left_cancel₀ hu₁ key'
        simp; linarith
  · -- z₁ = 0, so z₂ ≠ 0 (since z ≠ 0)
    simp only [not_not] at hz₁_nonzero
    have hz₂_nonzero : z₂ ≠ 0 := by
      intro hz₂_zero
      exact hz (by ext i; fin_cases i <;> [exact hz1_def.symm.trans hz₁_nonzero; exact hz2_def.symm.trans hz₂_zero])
    -- Use s = z₂, t = w₂
    use z₂, w₂
    constructor
    · intro ⟨hz₂, hw₂⟩; exact hz₂_nonzero hz₂
    · -- Show z₂ • w = w₂ • z
      -- Since z₁ = 0 and z₂ ≠ 0, from huz: u₂ * z₂ = 0, so u₂ = 0
      -- From huw: u₁ * w₁ = 0, and since u ≠ 0, u₁ ≠ 0, so w₁ = 0
      have hu₂ : u₂ = 0 := by
        have huz' : u₂ * z₂ = 0 := by rw [hz₁_nonzero] at huz; ring_nf at huz; exact huz
        exact (mul_eq_zero.mp huz').resolve_right hz₂_nonzero
      have hu₁ : u₁ ≠ 0 := by
        intro hu₁_zero
        exact hu (by ext i; fin_cases i <;> [exact hu1_def.symm.trans hu₁_zero; exact hu2_def.symm.trans hu₂])
      have hw₁ : w₁ = 0 := by
        have huw' : u₁ * w₁ = 0 := by rw [hu₂, zero_mul, add_zero] at huw; exact huw
        exact (mul_eq_zero.mp huw').resolve_left hu₁
      ext i
      fin_cases i
      · show z₂ * w 0 = w₂ * z 0
        rw [hw1_def.symm, hz1_def.symm, hw₁, hz₁_nonzero]; ring
      · show z₂ * w 1 = w₂ * z 1
        ring

/-- If `B - A` and `C - A` are parallel then `A`, `B`, `C` are collinear. -/
