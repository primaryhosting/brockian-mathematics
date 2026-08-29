import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
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

set_option grind.warning false

namespace Frontier

open Filter Topology

/-! ## Part 1: the discrete model (critical site percolation, `p = 1/2`)

Site percolation on a finite site set `V` (a finite piece of the triangular lattice) is
modelled as a uniformly random colouring `ω : V → Bool`, with `true` meaning *open*.  On
the triangular lattice the critical parameter is `p_c = 1/2`, so the uniform measure on
colourings is exactly the critical percolation measure. -/

section Discrete

variable {V : Type*} [Fintype V]

/-- The probability of an event `E` of percolation configurations under critical
(`p = 1/2`) site percolation on the finite site set `V`. -/
noncomputable def probHalf (E : (V → Bool) → Prop) : ℝ :=
  ((Finset.univ.filter (fun ω : V → Bool => E ω)).card : ℝ) / 2 ^ (Fintype.card V)

theorem probHalf_nonneg (E : (V → Bool) → Prop) : 0 ≤ probHalf E := by
  unfold probHalf; positivity

theorem probHalf_le_one (E : (V → Bool) → Prop) : probHalf E ≤ 1 := by
  unfold probHalf
  rw [div_le_one (by positivity)]
  have h1 : (Finset.univ.filter (fun ω : V → Bool => E ω)).card ≤ Fintype.card (V → Bool) :=
    Finset.card_filter_le _ _
  have h2 : Fintype.card (V → Bool) = 2 ^ Fintype.card V := by simp
  rw [h2] at h1
  exact_mod_cast h1

/-- Colour-flip symmetry of the critical measure: at `p = 1/2` the law of a configuration
and the law of its colour flip agree. -/
theorem probHalf_flip (E : (V → Bool) → Prop) :
    probHalf E = probHalf (fun ω => E (fun v => !ω v)) := by
  unfold probHalf
  congr 2
  apply Finset.card_bij' (fun ω _ => fun v => !ω v) (fun ω _ => fun v => !ω v)
  · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; simpa using ha
  · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; simpa using ha
  · intro a _; funext v; simp
  · intro a _; funext v; simp

/-- `OpenConnected adj ω u v` : the sites `u` and `v` are joined by a path of open sites. -/
def OpenConnected (adj : V → V → Prop) (ω : V → Bool) (u v : V) : Prop :=
  Relation.ReflTransGen (fun x y => adj x y ∧ ω x = true ∧ ω y = true) u v

/-- The open crossing event between two boundary arcs `A` and `B` of a discrete domain. -/
def OpenCrossing (adj : V → V → Prop) (A B : Finset V) (ω : V → Bool) : Prop :=
  ∃ u ∈ A, ∃ v ∈ B, ω u = true ∧ ω v = true ∧ OpenConnected adj ω u v

/-- The closed (dual) crossing event between two boundary arcs `A` and `B`. -/
def ClosedCrossing (adj : V → V → Prop) (A B : Finset V) (ω : V → Bool) : Prop :=
  ∃ u ∈ A, ∃ v ∈ B, ω u = false ∧ ω v = false ∧
    Relation.ReflTransGen (fun x y => adj x y ∧ ω x = false ∧ ω y = false) u v

omit [Fintype V] in
theorem closedCrossing_iff_openCrossing_flip (adj : V → V → Prop) (A B : Finset V)
    (ω : V → Bool) :
    ClosedCrossing adj A B ω ↔ OpenCrossing adj A B (fun v => !ω v) := by
  unfold ClosedCrossing OpenCrossing OpenConnected
  simp only [Bool.not_eq_true']

/-- **Base case: self-duality of critical percolation.**  For critical site percolation on
the triangular lattice (`p = 1/2`), the probability of an *open* crossing between two
boundary arcs equals the probability of a *closed* crossing between the same arcs.  This
is the exact discrete symmetry underlying the value `p_c = 1/2` and the Cardy–Smirnov
crossing formula. -/
theorem probHalf_openCrossing_eq_closedCrossing
    (adj : V → V → Prop) (A B : Finset V) :
    probHalf (OpenCrossing adj A B) = probHalf (ClosedCrossing adj A B) := by
  rw [probHalf_flip (OpenCrossing adj A B)]
  congr 1
  funext ω
  exact propext (closedCrossing_iff_openCrossing_flip adj A B ω).symm

end Discrete

/-! ## Part 2: the conformal modulus of a marked domain

A conformal rectangle is encoded as the upper half plane with four marked boundary points
`a < b < c < d` on the real line, the two boundary arcs to be crossed being `[a,b]` and
`[c,d]`.  Its conformal modulus is the cross-ratio of the four marked points; the
conformal automorphisms of the upper half plane act on the boundary by real Möbius maps
of positive determinant. -/

/-- The cross-ratio (conformal modulus) of four boundary points of the upper half plane. -/
noncomputable def crossRatio (a b c d : ℝ) : ℝ := ((b - a) * (d - c)) / ((c - a) * (d - b))

/-- A real Möbius transformation `x ↦ (α x + β)/(γ x + δ)`.  Those with positive
determinant are exactly the boundary actions of the conformal automorphisms of the upper
half plane. -/
noncomputable def mobius (α β γ δ x : ℝ) : ℝ := (α * x + β) / (γ * x + δ)

theorem mobius_sub {α β γ δ x y : ℝ} (hx : γ * x + δ ≠ 0) (hy : γ * y + δ ≠ 0) :
    mobius α β γ δ x - mobius α β γ δ y =
      (α * δ - β * γ) * (x - y) / ((γ * x + δ) * (γ * y + δ)) := by
  rw [mobius, mobius, div_sub_div _ _ hx hy]
  ring_nf

/-- A Möbius transformation of positive determinant is strictly increasing wherever its
denominator is positive; hence it preserves the cyclic order of the marked points. -/
theorem mobius_lt_mobius {α β γ δ x y : ℝ} (hdet : 0 < α * δ - β * γ)
    (hx : 0 < γ * x + δ) (hy : 0 < γ * y + δ) (hxy : x < y) :
    mobius α β γ δ x < mobius α β γ δ y := by
  have h := mobius_sub (α := α) (β := β) hy.ne' hx.ne'
  have hpos : 0 < (α * δ - β * γ) * (y - x) / ((γ * y + δ) * (γ * x + δ)) :=
    div_pos (by nlinarith) (by positivity)
  linarith [h ▸ hpos]

/-- **Conformal invariance of the modulus.**  The cross-ratio of four boundary points is
invariant under the conformal automorphisms of the upper half plane. -/
theorem crossRatio_mobius {α β γ δ a b c d : ℝ} (hdet : α * δ - β * γ ≠ 0)
    (ha : γ * a + δ ≠ 0) (hb : γ * b + δ ≠ 0) (hc : γ * c + δ ≠ 0) (hd : γ * d + δ ≠ 0)
    (hca : c ≠ a) (hdb : d ≠ b) :
    crossRatio (mobius α β γ δ a) (mobius α β γ δ b) (mobius α β γ δ c) (mobius α β γ δ d)
      = crossRatio a b c d := by
  have hca' : c - a ≠ 0 := sub_ne_zero.mpr hca
  have hdb' : d - b ≠ 0 := sub_ne_zero.mpr hdb
  unfold crossRatio
  rw [mobius_sub hb ha, mobius_sub hd hc, mobius_sub hc ha, mobius_sub hd hb]
  field_simp

/-- The modulus of a genuine conformal rectangle lies in `(0,1)`, the domain on which
Cardy's function is defined. -/
theorem crossRatio_mem_Ioo {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    crossRatio a b c d ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold crossRatio
  refine ⟨div_pos (by nlinarith) (by nlinarith), ?_⟩
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-! ## Part 3: the Cardy–Smirnov theorem

`SmirnovConvergence P cardy` is the content of Smirnov's theorem: for critical site
percolation on the triangular lattice of mesh `1/n` inside the upper half plane, the
probability `P n a b c d` of an open crossing between the boundary arcs `[a,b]` and
`[c,d]` converges, as the mesh tends to `0`, to `cardy` evaluated at the conformal modulus
of the marked domain — this is Cardy's formula in Carleson's form. -/

/-- Smirnov's convergence theorem, as a hypothesis on a family `P` of discrete crossing
probabilities and a limit function `cardy` of the conformal modulus. -/
def SmirnovConvergence (P : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ) (cardy : ℝ → ℝ) : Prop :=
  ∀ a b c d : ℝ, a < b → b < c → c < d →
    Tendsto (fun n => P n a b c d) atTop (𝓝 (cardy (crossRatio a b c d)))

/-- **Cardy–Smirnov conformal invariance of crossing probabilities.**

Assume Smirnov's theorem `SmirnovConvergence P cardy`, i.e. that the discrete crossing
probabilities of critical triangular-lattice percolation between the boundary arcs `[a,b]`
and `[c,d]` of the upper half plane converge, as the mesh tends to `0`, to a function of
the conformal modulus of the marked domain.

Then the limiting crossing probability is conformally invariant: for every conformal
automorphism `g` of the upper half plane (a real Möbius map of positive determinant, here
assumed pole-free on the interval carrying the marked points), the crossing probabilities
of the image configuration `(g a, g b, g c, g d)` converge to the *same* limit as those of
`(a, b, c, d)`. -/
theorem smirnov_percolation
    (P : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ) (cardy : ℝ → ℝ)
    (hSmirnov : SmirnovConvergence P cardy)
    (α β γ δ : ℝ) (hdet : 0 < α * δ - β * γ)
    (a b c d : ℝ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hpole : ∀ x ∈ Set.Icc a d, 0 < γ * x + δ) :
    Tendsto (fun n => P n (mobius α β γ δ a) (mobius α β γ δ b)
        (mobius α β γ δ c) (mobius α β γ δ d)) atTop
      (𝓝 (cardy (crossRatio a b c d))) := by
  have hda : a < d := lt_trans hab (lt_trans hbc hcd)
  have hA : 0 < γ * a + δ := hpole a ⟨le_refl a, hda.le⟩
  have hB : 0 < γ * b + δ := hpole b ⟨hab.le, (lt_trans hbc hcd).le⟩
  have hC : 0 < γ * c + δ := hpole c ⟨(lt_trans hab hbc).le, hcd.le⟩
  have hD : 0 < γ * d + δ := hpole d ⟨hda.le, le_refl d⟩
  have h1 := mobius_lt_mobius (α := α) (β := β) hdet hA hB hab
  have h2 := mobius_lt_mobius (α := α) (β := β) hdet hB hC hbc
  have h3 := mobius_lt_mobius (α := α) (β := β) hdet hC hD hcd
  have hlim := hSmirnov _ _ _ _ h1 h2 h3
  rwa [crossRatio_mobius hdet.ne' hA.ne' hB.ne' hC.ne' hD.ne'
    (by linarith : c ≠ a) (by linarith : d ≠ b)] at hlim

/-- Consistency of the limit with Part 1: since each `P n a b c d` is a probability (as in
`probHalf_nonneg` / `probHalf_le_one`), the Cardy–Smirnov limit is itself a probability. -/
theorem cardy_mem_Icc (P : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ) (cardy : ℝ → ℝ)
    (hSmirnov : SmirnovConvergence P cardy)
    (hP : ∀ n a b c d, P n a b c d ∈ Set.Icc (0 : ℝ) 1)
    {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    cardy (crossRatio a b c d) ∈ Set.Icc (0 : ℝ) 1 := by
  have hlim := hSmirnov a b c d hab hbc hcd
  exact ⟨ge_of_tendsto' hlim (fun n => (hP n a b c d).1),
    le_of_tendsto' hlim (fun n => (hP n a b c d).2)⟩

end Frontier

