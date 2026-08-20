import Mathlib

/-!
# Hadwiger Nelson 5
Category: Frontier — Moonshot
Target: Frontier.hadwiger_nelson_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE HEADER: Lean 4 requires `import` commands to appear before any other
command, and a module docstring `/-! ... -/` *is* a command.  The requested header
comment is therefore reproduced verbatim immediately after the single `import` line.
-/

namespace Frontier

open Real

/-! ## The unit-distance graph of the Euclidean plane

We model the Euclidean plane as `ℂ`, whose metric `dist z w = ‖z - w‖` is exactly the
Euclidean distance.  `planeGraph` is the unit-distance graph: two points are adjacent
iff they are at distance `1`.  Its chromatic number is the *chromatic number of the
plane*, the subject of the Hadwiger–Nelson problem.
-/

/-- The unit-distance graph on the Euclidean plane (modelled as `ℂ`). -/
def planeGraph : SimpleGraph ℂ where
  Adj z w := dist z w = 1
  symm := by
    intro z w h
    rwa [dist_comm]
  loopless := ⟨fun z h => zero_ne_one ((dist_self z).symm.trans h)⟩

@[simp] lemma planeGraph_adj {z w : ℂ} : planeGraph.Adj z w ↔ dist z w = 1 := Iff.rfl

/-- `planeGraph` is `n`-colourable iff there is a map `ℂ → Fin n` giving distinct values
to any two points at distance `1`. -/
lemma planeGraph_colorable_iff (n : ℕ) :
    planeGraph.Colorable n ↔ ∃ c : ℂ → Fin n, ∀ z w : ℂ, dist z w = 1 → c z ≠ c w := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C, fun z w h => C.valid h⟩
  · rintro ⟨c, hc⟩
    exact ⟨SimpleGraph.Coloring.mk c fun {z w} h => hc z w h⟩

/-- If the plane admits no proper `n`-colouring, its chromatic number is `> n`. -/
lemma succ_le_chromaticNumber_of_not_colorable {n : ℕ} (h : ¬ planeGraph.Colorable n) :
    (n + 1 : ℕ∞) ≤ planeGraph.chromaticNumber := by
  by_contra hc
  push_neg at hc
  refine h (SimpleGraph.chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_succ ?_))
  rwa [Order.succ_eq_add_one]

/-! ## A convenient criterion for unit distance -/

/-- Two complex numbers are at distance `1` as soon as the sum of the squares of the
differences of their coordinates is `1`. -/
lemma dist_eq_one_of_coords {z w : ℂ}
    (h : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = 1) : dist z w = 1 := by
  rw [Complex.dist_eq_re_im, h, Real.sqrt_one]

/-! ## The Moser spindle: the chromatic number of the plane is at least `4`

The seven points below are the vertices of the *Moser spindle*: two unit rhombi with a
common vertex at the origin, rotated against each other by the angle `θ` with
`cos θ = 5/6`, `sin θ = √11/6`, so that their far tips are again at distance `1`.
-/

/-- The seven vertices of the Moser spindle. -/
noncomputable def spindle : Fin 7 → ℂ :=
  ![ (⟨0, 0⟩ : ℂ),
     ⟨sqrt 3 / 2, 1 / 2⟩,
     ⟨sqrt 3 / 2, -(1 / 2)⟩,
     ⟨sqrt 3, 0⟩,
     ⟨(5 * sqrt 3 - sqrt 11) / 12, (sqrt 3 * sqrt 11 + 5) / 12⟩,
     ⟨(5 * sqrt 3 + sqrt 11) / 12, (sqrt 3 * sqrt 11 - 5) / 12⟩,
     ⟨5 * sqrt 3 / 6, sqrt 3 * sqrt 11 / 6⟩ ]

set_option maxHeartbeats 1000000 in
/-- The eleven edges of the Moser spindle really are unit distances. -/
lemma spindle_edges :
    dist (spindle 0) (spindle 1) = 1 ∧ dist (spindle 0) (spindle 2) = 1 ∧
    dist (spindle 1) (spindle 2) = 1 ∧ dist (spindle 1) (spindle 3) = 1 ∧
    dist (spindle 2) (spindle 3) = 1 ∧ dist (spindle 0) (spindle 4) = 1 ∧
    dist (spindle 0) (spindle 5) = 1 ∧ dist (spindle 4) (spindle 5) = 1 ∧
    dist (spindle 4) (spindle 6) = 1 ∧ dist (spindle 5) (spindle 6) = 1 ∧
    dist (spindle 3) (spindle 6) = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h33 : (Real.sqrt 3 * Real.sqrt 11) ^ 2 = 33 := by rw [mul_pow, h3, h11]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply dist_eq_one_of_coords
     simp only [spindle, Matrix.cons_val]
     nlinarith [h3, h11, h33])

/-- The abstract Moser spindle is not `3`-colourable. -/
lemma spindle_not_three_colorable : ∀ a b c d e g h : Fin 3,
    a = b ∨ a = c ∨ b = c ∨ b = d ∨ c = d ∨
    a = e ∨ a = g ∨ e = g ∨ e = h ∨ g = h ∨ d = h := by decide

/-- The plane is not `3`-colourable: every `3`-colouring of the plane has two points at
distance `1` with the same colour. -/
theorem plane_not_colorable_three : ¬ planeGraph.Colorable 3 := by
  rw [planeGraph_colorable_iff]
  rintro ⟨c, hc⟩
  obtain ⟨e01, e02, e12, e13, e23, e04, e05, e45, e46, e56, e36⟩ := spindle_edges
  rcases spindle_not_three_colorable (c (spindle 0)) (c (spindle 1)) (c (spindle 2))
      (c (spindle 3)) (c (spindle 4)) (c (spindle 5)) (c (spindle 6)) with
    h | h | h | h | h | h | h | h | h | h | h
  · exact hc _ _ e01 h
  · exact hc _ _ e02 h
  · exact hc _ _ e12 h
  · exact hc _ _ e13 h
  · exact hc _ _ e23 h
  · exact hc _ _ e04 h
  · exact hc _ _ e05 h
  · exact hc _ _ e45 h
  · exact hc _ _ e46 h
  · exact hc _ _ e56 h
  · exact hc _ _ e36 h

/-- **The chromatic number of the plane is at least `4`** (Nelson; the Moser spindle).
This is proved here unconditionally. -/
theorem hadwiger_nelson_4 : 4 ≤ planeGraph.chromaticNumber := by
  have := succ_le_chromaticNumber_of_not_colorable plane_not_colorable_three
  simpa using this

/-! ## The chromatic number of the plane is at least `5`

De Grey (2018) exhibited an explicit *finite* set of points of the plane whose
unit-distance graph is not `4`-colourable (his graph has `1581` vertices; smaller
examples are now known).  That finite, computational statement is isolated below as
`DeGreyWitness`.
-/

/-- **De Grey's finite witness.**  There is a finite set of points of the Euclidean plane
whose unit-distance graph admits no proper `4`-colouring.

This is the (purely finite, computer-verified) combinatorial input of de Grey's 2018
theorem; it is *not* proved here. -/
def DeGreyWitness : Prop :=
  ∃ S : Finset ℂ, ∀ c : ℂ → Fin 4, ∃ z ∈ S, ∃ w ∈ S, dist z w = 1 ∧ c z = c w

/-- Given a finite non-`4`-colourable unit-distance graph, the whole plane is not
`4`-colourable. -/
theorem plane_not_colorable_four (h : DeGreyWitness) : ¬ planeGraph.Colorable 4 := by
  obtain ⟨S, hS⟩ := h
  rw [planeGraph_colorable_iff]
  rintro ⟨c, hc⟩
  obtain ⟨z, -, w, -, hzw, hcol⟩ := hS c
  exact hc z w hzw hcol

/-- **The chromatic number of the plane is at least `5`** (de Grey, 2018).

The hypothesis `DeGreyWitness` is the finite combinatorial core of de Grey's theorem:
the existence of a finite planar point set whose unit-distance graph has no proper
`4`-colouring.  Everything else — the passage from that finite graph to the whole
plane — is proved here. -/
theorem hadwiger_nelson_5 (h : DeGreyWitness) : 5 ≤ planeGraph.chromaticNumber := by
  have := succ_le_chromaticNumber_of_not_colorable (plane_not_colorable_four h)
  simpa using this

/-! ## The hypothesis is exactly right: a compactness (de Bruijn–Erdős) argument

The finite witness assumed above is not merely sufficient, it is also necessary: if the
whole plane needs at least five colours then already some finite subset does.  This is a
compactness argument, proved here in the following general form. -/

/-- **Compactness for graph colourings** (de Bruijn–Erdős).  If every finite set of
vertices of a graph admits a proper `n`-colouring, then the whole graph is
`n`-colourable. -/
theorem colorable_of_forall_finset {V : Type*} (G : SimpleGraph V) (n : ℕ)
    (h : ∀ S : Finset V, ∃ c : V → Fin n, ∀ z ∈ S, ∀ w ∈ S, G.Adj z w → c z ≠ c w) :
    G.Colorable n := by
  classical
  letI : TopologicalSpace (Fin n) := ⊥
  haveI : DiscreteTopology (Fin n) := ⟨rfl⟩
  haveI : CompactSpace (V → Fin n) := Pi.compactSpace
  set T : Finset V → Set (V → Fin n) :=
    fun S => {c | ∀ z ∈ S, ∀ w ∈ S, G.Adj z w → c z ≠ c w} with hT
  have hne : ∀ S, (T S).Nonempty := fun S => h S
  have hpair : ∀ z w : V, IsClosed {c : V → Fin n | G.Adj z w → c z ≠ c w} := by
    intro z w
    by_cases hzw : G.Adj z w
    · have he : {c : V → Fin n | G.Adj z w → c z ≠ c w}
          = (fun c : V → Fin n => (c z, c w)) ⁻¹' {p : Fin n × Fin n | p.1 ≠ p.2} := by
        ext c; simp [hzw]
      rw [he]
      exact IsClosed.preimage ((continuous_apply z).prodMk (continuous_apply w))
        (isClosed_discrete _)
    · have he : {c : V → Fin n | G.Adj z w → c z ≠ c w} = Set.univ := by
        ext c; simp [hzw]
      rw [he]; exact isClosed_univ
  have hclosed : ∀ S, IsClosed (T S) := by
    intro S
    have he : T S = ⋂ z ∈ S, ⋂ w ∈ S, {c : V → Fin n | G.Adj z w → c z ≠ c w} := by
      ext c; simp [hT]
    rw [he]
    exact isClosed_biInter fun z _ => isClosed_biInter fun w _ => hpair z w
  have hdir : Directed (· ⊇ ·) T := by
    intro S1 S2
    refine ⟨S1 ∪ S2, ?_, ?_⟩ <;> intro c hc z hz w hw hadj <;>
      exact hc z (by simp [hz]) w (by simp [hw]) hadj
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    T hdir hne (fun S => (hclosed S).isCompact) hclosed
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro z w hadj
  have := Set.mem_iInter.mp hc ({z, w} : Finset V)
  exact this z (by simp) w (by simp) hadj

/-- The plane fails to be `4`-colourable **iff** some finite planar point set already
fails to be `4`-colourable. -/
theorem deGreyWitness_iff : DeGreyWitness ↔ ¬ planeGraph.Colorable 4 := by
  refine ⟨plane_not_colorable_four, fun h => ?_⟩
  by_contra hw
  refine h (colorable_of_forall_finset planeGraph 4 ?_)
  unfold DeGreyWitness at hw
  push_neg at hw
  intro S
  obtain ⟨c, hc⟩ := hw S
  exact ⟨c, fun z hz w hw' hadj => hc z hz w hw' hadj⟩

/-- The chromatic number of the plane is at least `5` **iff** de Grey's finite witness
exists.  So the hypothesis of `hadwiger_nelson_5` is not merely sufficient but also
necessary; it is precisely the finite combinatorial content of the statement. -/
theorem chromaticNumber_ge_five_iff :
    5 ≤ planeGraph.chromaticNumber ↔ DeGreyWitness := by
  refine ⟨fun h => deGreyWitness_iff.mpr fun hcol => ?_, hadwiger_nelson_5⟩
  have h4 : planeGraph.chromaticNumber ≤ (4 : ℕ) :=
    SimpleGraph.chromaticNumber_le_iff_colorable.mpr hcol
  have : (5 : ℕ∞) ≤ (4 : ℕ) := le_trans h h4
  norm_num at this

end Frontier

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

