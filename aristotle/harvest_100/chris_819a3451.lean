/-
# Hadwiger Nelson 5
Category: Frontier — Moonshot
Target: Frontier.hadwiger_nelson_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is a plain block comment; it is repeated as a docstring below.)

import Mathlib

/-!
# Hadwiger Nelson 5
Category: Frontier — Moonshot
Target: Frontier.hadwiger_nelson_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## Unit-distance colourings

A colouring of a metric space `X` by `k` colours is *proper* (for the unit-distance
graph on `X`) when no two points at distance exactly `1` receive the same colour.
The chromatic number of `X` is `≥ k + 1` exactly when no proper `k`-colouring exists.
-/

/-- `c : X → Fin k` is a proper colouring of the unit-distance graph on the metric
space `X`: points at distance `1` get distinct colours. -/
def ProperUnitColouring {X : Type*} [MetricSpace X] {k : ℕ} (c : X → Fin k) : Prop :=
  ∀ p q : X, dist p q = 1 → c p ≠ c q

/-! ### Coordinate formulas for distances -/

private theorem dist_plane (a b a' b' : ℝ) :
    dist (⟨a, b⟩ : ℂ) ⟨a', b'⟩ = Real.sqrt ((a - a') ^ 2 + (b - b') ^ 2) := by
  rw [Complex.dist_eq_re_im]

private theorem dist_space (a b c a' b' c' : ℝ) :
    dist (!₂[a, b, c] : EuclideanSpace ℝ (Fin 3)) !₂[a', b', c'] =
      Real.sqrt ((a - a') ^ 2 + (b - b') ^ 2 + (c - c') ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_three, Real.dist_eq, sq_abs]

/-! ### Elementary colour-counting facts -/

/-- With three colours: if `a ≠ b` and both `p` and `q` avoid the colours `a` and `b`,
then `p = q`. -/
private theorem fin3_forced :
    ∀ a b p q : Fin 3, a ≠ b → p ≠ a → p ≠ b → q ≠ a → q ≠ b → p = q := by decide

/-- With four colours: if `a, b, c` are pairwise distinct and both `p` and `q` avoid
all three, then `p = q`. -/
private theorem fin4_forced :
    ∀ a b c p q : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      p ≠ a → p ≠ b → p ≠ c → q ≠ a → q ≠ b → q ≠ c → p = q := by decide

/-!
## The plane: `χ(ℝ²) ≥ 4`

We use the Moser spindle, realised in `ℂ` with explicit coordinates.  The two
"rhombus" gadgets `{P₀, A, B, T}` and `{P₁, A', B', T}` each force their two apexes
to share a colour under any proper `3`-colouring; since `P₀` and `P₁` are at distance
`1` this is a contradiction.
-/

section Plane

private noncomputable def r3 : ℝ := Real.sqrt 3
private noncomputable def r11 : ℝ := Real.sqrt 11

private theorem r3_sq : r3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private theorem r11_sq : r11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)

/-- Origin of the spindle. -/
private noncomputable def P0 : ℂ := ⟨0, 0⟩
/-- The point at distance `1` from `P0` whose colour we compare. -/
private noncomputable def P1 : ℂ := ⟨1, 0⟩
/-- The common apex of the two rhombi, at distance `√3` from both `P0` and `P1`. -/
private noncomputable def PT : ℂ := ⟨1 / 2, r11 / 2⟩
/-- First side vertex of the rhombus `P0–PT`. -/
private noncomputable def PA : ℂ := ⟨1 / 4 - r3 * r11 / 12, r11 / 4 + r3 / 12⟩
/-- Second side vertex of the rhombus `P0–PT`. -/
private noncomputable def PB : ℂ := ⟨1 / 4 + r3 * r11 / 12, r11 / 4 - r3 / 12⟩
/-- First side vertex of the rhombus `P1–PT`. -/
private noncomputable def PA' : ℂ := ⟨3 / 4 - r3 * r11 / 12, r11 / 4 - r3 / 12⟩
/-- Second side vertex of the rhombus `P1–PT`. -/
private noncomputable def PB' : ℂ := ⟨3 / 4 + r3 * r11 / 12, r11 / 4 + r3 / 12⟩

private theorem sqrt_one_of (e : ℝ) (h : e = 1) : Real.sqrt e = 1 := by
  rw [h, Real.sqrt_one]

/-- Closes each of the eleven unit-distance verifications in the plane. -/
local macro "plane_dist" : tactic =>
  `(tactic| (rw [dist_plane]
             apply sqrt_one_of
             ring_nf
             try simp only [r3_sq, r11_sq]
             try ring_nf
             try norm_num))

private theorem d_P0_P1 : dist P0 P1 = 1 := by
  unfold P0 P1; plane_dist

private theorem d_P0_PA : dist P0 PA = 1 := by
  unfold P0 PA; plane_dist

private theorem d_P0_PB : dist P0 PB = 1 := by
  unfold P0 PB; plane_dist

private theorem d_PA_PB : dist PA PB = 1 := by
  unfold PA PB; plane_dist

private theorem d_PT_PA : dist PT PA = 1 := by
  unfold PT PA; plane_dist

private theorem d_PT_PB : dist PT PB = 1 := by
  unfold PT PB; plane_dist

private theorem d_P1_PA' : dist P1 PA' = 1 := by
  unfold P1 PA'; plane_dist

private theorem d_P1_PB' : dist P1 PB' = 1 := by
  unfold P1 PB'; plane_dist

private theorem d_PA'_PB' : dist PA' PB' = 1 := by
  unfold PA' PB'; plane_dist

private theorem d_PT_PA' : dist PT PA' = 1 := by
  unfold PT PA'; plane_dist

private theorem d_PT_PB' : dist PT PB' = 1 := by
  unfold PT PB'; plane_dist

/-- **The chromatic number of the plane is at least 4.**  No colouring of the
Euclidean plane by three colours can separate all pairs of points at distance one. -/
theorem plane_not_three_colourable : ¬ ∃ c : ℂ → Fin 3, ProperUnitColouring c := by
  rintro ⟨c, hc⟩
  have e1 : c PT = c P0 :=
    fin3_forced (c PA) (c PB) (c PT) (c P0) (hc _ _ d_PA_PB)
      (hc _ _ d_PT_PA) (hc _ _ d_PT_PB)
      (hc _ _ d_P0_PA) (hc _ _ d_P0_PB)
  have e2 : c PT = c P1 :=
    fin3_forced (c PA') (c PB') (c PT) (c P1) (hc _ _ d_PA'_PB')
      (hc _ _ d_PT_PA') (hc _ _ d_PT_PB')
      (hc _ _ d_P1_PA') (hc _ _ d_P1_PB')
  exact hc _ _ d_P0_P1 (e1.symm.trans e2)

end Plane

/-!
## Three-space: `χ(ℝ³) ≥ 5`

The same "spindle" idea works one dimension up, with the rhombus replaced by the
triangular bipyramid: two apexes joined to a unit equilateral triangle.  Under a
proper `4`-colouring the triangle uses three colours, so both apexes must take the
fourth one.  The apex separation is `2√6/3`, and two points at distance `1` can both
be joined to a common third point at that distance, which yields a contradiction.
-/

section Space

private noncomputable def r2 : ℝ := Real.sqrt 2
private noncomputable def r87 : ℝ := Real.sqrt 87

private theorem r2_sq : r2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private theorem r87_sq : r87 ^ 2 = 87 := Real.sq_sqrt (by norm_num)

/-- First apex. -/
private noncomputable def X0 : EuclideanSpace ℝ (Fin 3) := !₂[-(1 / 2), 0, 0]
/-- Second apex, at distance `1` from `X0`. -/
private noncomputable def Y0 : EuclideanSpace ℝ (Fin 3) := !₂[1 / 2, 0, 0]
/-- The common third apex, at distance `2√6/3` from both `X0` and `Y0`. -/
private noncomputable def T0 : EuclideanSpace ℝ (Fin 3) := !₂[0, r87 / 6, 0]

/-- Vertex of the unit triangle of the bipyramid on `X0, T0`. -/
private noncomputable def Q1 : EuclideanSpace ℝ (Fin 3) :=
  !₂[-(1 / 4) + r2 * r87 / 24, r87 / 12 - r2 / 8, 0]
/-- Vertex of the unit triangle of the bipyramid on `X0, T0`. -/
private noncomputable def Q2 : EuclideanSpace ℝ (Fin 3) :=
  !₂[-(1 / 4) - r2 * r87 / 48, r87 / 12 + r2 / 16, 1 / 2]
/-- Vertex of the unit triangle of the bipyramid on `X0, T0`. -/
private noncomputable def Q3 : EuclideanSpace ℝ (Fin 3) :=
  !₂[-(1 / 4) - r2 * r87 / 48, r87 / 12 + r2 / 16, -(1 / 2)]

/-- Vertex of the unit triangle of the bipyramid on `Y0, T0`. -/
private noncomputable def Q1' : EuclideanSpace ℝ (Fin 3) :=
  !₂[1 / 4 - r2 * r87 / 24, r87 / 12 - r2 / 8, 0]
/-- Vertex of the unit triangle of the bipyramid on `Y0, T0`. -/
private noncomputable def Q2' : EuclideanSpace ℝ (Fin 3) :=
  !₂[1 / 4 + r2 * r87 / 48, r87 / 12 + r2 / 16, 1 / 2]
/-- Vertex of the unit triangle of the bipyramid on `Y0, T0`. -/
private noncomputable def Q3' : EuclideanSpace ℝ (Fin 3) :=
  !₂[1 / 4 + r2 * r87 / 48, r87 / 12 + r2 / 16, -(1 / 2)]

/-- Closes each of the nineteen unit-distance verifications in three-space. -/
local macro "space_dist" : tactic =>
  `(tactic| (rw [dist_space]
             apply sqrt_one_of
             ring_nf
             try simp only [r2_sq, r87_sq]
             try ring_nf
             try norm_num))

private theorem e_X0_Y0 : dist X0 Y0 = 1 := by unfold X0 Y0; space_dist
private theorem e_X0_Q1 : dist X0 Q1 = 1 := by unfold X0 Q1; space_dist
private theorem e_X0_Q2 : dist X0 Q2 = 1 := by unfold X0 Q2; space_dist
private theorem e_X0_Q3 : dist X0 Q3 = 1 := by unfold X0 Q3; space_dist
private theorem e_T0_Q1 : dist T0 Q1 = 1 := by unfold T0 Q1; space_dist
private theorem e_T0_Q2 : dist T0 Q2 = 1 := by unfold T0 Q2; space_dist
private theorem e_T0_Q3 : dist T0 Q3 = 1 := by unfold T0 Q3; space_dist
private theorem e_Q1_Q2 : dist Q1 Q2 = 1 := by unfold Q1 Q2; space_dist
private theorem e_Q1_Q3 : dist Q1 Q3 = 1 := by unfold Q1 Q3; space_dist
private theorem e_Q2_Q3 : dist Q2 Q3 = 1 := by unfold Q2 Q3; space_dist

private theorem e_Y0_Q1' : dist Y0 Q1' = 1 := by unfold Y0 Q1'; space_dist
private theorem e_Y0_Q2' : dist Y0 Q2' = 1 := by unfold Y0 Q2'; space_dist
private theorem e_Y0_Q3' : dist Y0 Q3' = 1 := by unfold Y0 Q3'; space_dist
private theorem e_T0_Q1' : dist T0 Q1' = 1 := by unfold T0 Q1'; space_dist
private theorem e_T0_Q2' : dist T0 Q2' = 1 := by unfold T0 Q2'; space_dist
private theorem e_T0_Q3' : dist T0 Q3' = 1 := by unfold T0 Q3'; space_dist
private theorem e_Q1'_Q2' : dist Q1' Q2' = 1 := by unfold Q1' Q2'; space_dist
private theorem e_Q1'_Q3' : dist Q1' Q3' = 1 := by unfold Q1' Q3'; space_dist
private theorem e_Q2'_Q3' : dist Q2' Q3' = 1 := by unfold Q2' Q3'; space_dist

/-- **The chromatic number of three-dimensional Euclidean space is at least 5.**
No colouring of `ℝ³` by four colours separates all pairs of points at distance one. -/
theorem space_not_four_colourable :
    ¬ ∃ c : EuclideanSpace ℝ (Fin 3) → Fin 4, ProperUnitColouring c := by
  rintro ⟨c, hc⟩
  have e1 : c T0 = c X0 :=
    fin4_forced (c Q1) (c Q2) (c Q3) (c T0) (c X0)
      (hc _ _ e_Q1_Q2) (hc _ _ e_Q1_Q3) (hc _ _ e_Q2_Q3)
      (hc _ _ e_T0_Q1) (hc _ _ e_T0_Q2) (hc _ _ e_T0_Q3)
      (hc _ _ e_X0_Q1) (hc _ _ e_X0_Q2) (hc _ _ e_X0_Q3)
  have e2 : c T0 = c Y0 :=
    fin4_forced (c Q1') (c Q2') (c Q3') (c T0) (c Y0)
      (hc _ _ e_Q1'_Q2') (hc _ _ e_Q1'_Q3') (hc _ _ e_Q2'_Q3')
      (hc _ _ e_T0_Q1') (hc _ _ e_T0_Q2') (hc _ _ e_T0_Q3')
      (hc _ _ e_Y0_Q1') (hc _ _ e_Y0_Q2') (hc _ _ e_Y0_Q3')
  exact hc _ _ e_X0_Y0 (e1.symm.trans e2)

end Space

/-!
## `χ(ℝ²) ≥ 5`

De Grey (2018) exhibited a finite set of points of the plane (1581 of them) whose
unit-distance graph has no proper `4`-colouring; the verification of that finite
combinatorial fact is a large computer search and is taken here as the hypothesis
`deGrey`.  Given it, the plane itself admits no proper `4`-colouring.
-/

/-- **Hadwiger–Nelson, lower bound 5.**  If some finite family `v : Fin n → ℂ` of
points of the plane has the property that every `4`-colouring of its index set
identifies two points at distance `1`, then no `4`-colouring of the whole plane is
proper for the unit-distance graph, i.e. the chromatic number of the plane is at
least `5`.

The hypothesis `deGrey` is exactly the finite combinatorial core established by
A. de Grey (2018) by computer search. -/
theorem hadwiger_nelson_5
    (deGrey : ∃ (n : ℕ) (v : Fin n → ℂ),
      ∀ c : Fin n → Fin 4, ∃ i j, dist (v i) (v j) = 1 ∧ c i = c j) :
    ¬ ∃ c : ℂ → Fin 4, ProperUnitColouring c := by
  rintro ⟨c, hc⟩
  obtain ⟨n, v, hv⟩ := deGrey
  obtain ⟨i, j, hij, hcol⟩ := hv (fun i => c (v i))
  exact hc _ _ hij hcol

/-! ## Restatements without the `ProperUnitColouring` abbreviation -/

/-- Every colouring of the plane by three colours has two points at distance `1`
of the same colour: `χ(ℝ²) ≥ 4`. -/
theorem exists_monochromatic_unit_pair_plane_three (c : ℂ → Fin 3) :
    ∃ p q : ℂ, dist p q = 1 ∧ c p = c q := by
  by_contra h
  exact plane_not_three_colourable ⟨c, fun p q hpq hcol => h ⟨p, q, hpq, hcol⟩⟩

/-- Every colouring of `ℝ³` by four colours has two points at distance `1` of the
same colour: `χ(ℝ³) ≥ 5`. -/
theorem exists_monochromatic_unit_pair_space_four
    (c : EuclideanSpace ℝ (Fin 3) → Fin 4) :
    ∃ p q : EuclideanSpace ℝ (Fin 3), dist p q = 1 ∧ c p = c q := by
  by_contra h
  exact space_not_four_colourable ⟨c, fun p q hpq hcol => h ⟨p, q, hpq, hcol⟩⟩

end Frontier

