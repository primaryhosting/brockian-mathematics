import Mathlib
/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
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

/-! ## Minkowski spacetime -/

/-- Four dimensional Minkowski spacetime, as coordinate tuples `(x⁰, x¹, x², x³)`. -/
abbrev Spacetime : Type := Fin 4 → ℝ

/-- The Minkowski quadratic form `x·x = (x⁰)² - (x¹)² - (x²)² - (x³)²`
(mostly-minus signature). -/
def minkowskiSq (x : Spacetime) : ℝ := (x 0) ^ 2 - (x 1) ^ 2 - (x 2) ^ 2 - (x 3) ^ 2

/-- A vector is *spacelike* when its Minkowski square is negative.  Two events
separated by a spacelike vector cannot influence each other. -/
def IsSpacelike (x : Spacetime) : Prop := minkowskiSq x < 0

lemma minkowskiSq_neg (x : Spacetime) : minkowskiSq (-x) = minkowskiSq x := by
  simp [minkowskiSq]

lemma minkowskiSq_smul (t : ℝ) (x : Spacetime) :
    minkowskiSq (t • x) = t ^ 2 * minkowskiSq x := by
  simp [minkowskiSq, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- A nonzero real multiple of a spacelike vector is spacelike. -/
lemma IsSpacelike.smul {x : Spacetime} (hx : IsSpacelike x) {t : ℝ} (ht : t ≠ 0) :
    IsSpacelike (t • x) := by
  have h2 : (0 : ℝ) < t ^ 2 := by positivity
  have := mul_neg_of_pos_of_neg h2 hx
  simpa [IsSpacelike, minkowskiSq_smul] using this

/-! ## The Wightman two-point structure of a relativistic field

The following structure packages the standard hypotheses (Wightman axioms) that
enter the Pauli–Lüders–Zumino–Burgoyne derivation of the spin–statistics
connection, specialised to the **two-point function**

`W (x - y) = ⟨Ω, φ(x) φ*(y) Ω⟩`

of a field `φ` of spin `j`, carrying `twoSpin = 2j`.

* `stat` is the statistics sign of the field: `+1` if `φ` is quantised with
  commutators (Bose), `-1` if it is quantised with anticommutators (Fermi).

* `locality` is *microcausality*: at spacelike separation the fields commute
  (`stat = 1`) or anticommute (`stat = -1`), which for the two-point function
  reads `W x = stat * W (-x)`.

* `bhw` is the consequence of Lorentz covariance and the Bargmann–Hall–Wightman
  theorem (equivalently, weak local commutativity / TCP): at a Jost point the
  two-point function of a spin-`j` field picks up the factor `(-1)^(2j)` under
  `x ↦ -x`.

* `Wc`, `analytic`, `slice` encode the analyticity of the Wightman function.
  Along a fixed spacelike direction `e`, the map `t ↦ W (t • e)` extends to a
  function `Wc` holomorphic on the punctured complex plane (the restriction to a
  complex line of the analytic continuation of `W` to the extended tube; the
  purely imaginary points of this line correspond to timelike separations).

* `nontrivial` says the field is not the zero field: its two-point function does
  not vanish identically on the complexified line.
-/
structure RelativisticQuantumField where
  /-- Twice the spin of the field, `2j`. -/
  twoSpin : ℕ
  /-- The statistics sign: `+1` for Bose (commutators), `-1` for Fermi
  (anticommutators) quantisation. -/
  stat : ℤ
  /-- The statistics sign is indeed a sign. -/
  stat_sq : stat * stat = 1
  /-- The Wightman two-point function `W (x - y) = ⟨Ω, φ(x) φ*(y) Ω⟩`. -/
  W : Spacetime → ℂ
  /-- Microcausality: (anti)commutativity of the fields at spacelike separation. -/
  locality : ∀ x : Spacetime, IsSpacelike x → W x = (stat : ℂ) * W (-x)
  /-- Bargmann–Hall–Wightman / TCP: at Jost (spacelike) points, `x ↦ -x` acts on
  the two-point function of a spin-`j` field by `(-1)^(2j)`. -/
  bhw : ∀ x : Spacetime, IsSpacelike x → W (-x) = ((-1 : ℂ)) ^ twoSpin * W x
  /-- A fixed spacelike direction. -/
  e : Spacetime
  /-- ... which is indeed spacelike. -/
  e_spacelike : IsSpacelike e
  /-- The analytic continuation of `t ↦ W (t • e)` to a complex variable. -/
  Wc : ℂ → ℂ
  /-- It is holomorphic off the origin. -/
  analytic : AnalyticOnNhd ℂ Wc ({0}ᶜ : Set ℂ)
  /-- It restricts to the two-point function on the real spacelike line. -/
  slice : ∀ t : ℝ, t ≠ 0 → Wc (t : ℂ) = W (t • e)
  /-- The field is nontrivial: its two-point function does not vanish identically. -/
  nontrivial : ∃ z : ℂ, z ≠ 0 ∧ Wc z ≠ 0

namespace RelativisticQuantumField

variable (F : RelativisticQuantumField)

/-- Wrong statistics force the two-point function to vanish at every spacelike
separation: microcausality and the Bargmann–Hall–Wightman relation combine to
`W x = stat * (-1)^(2j) * W x`, and `stat * (-1)^(2j) = -1` in the wrong case. -/
lemma W_eq_zero_of_spacelike_of_wrong_stat (h : (F.stat : ℂ) * (-1) ^ F.twoSpin = -1)
    {x : Spacetime} (hx : IsSpacelike x) : F.W x = 0 := by
  have h1 := F.locality x hx
  rw [F.bhw x hx, ← mul_assoc, h] at h1
  linear_combination h1 / 2

/-- The complexified slice vanishes on the punctured real line, in the wrong-statistics
case. -/
lemma Wc_eq_zero_of_real_of_wrong_stat (h : (F.stat : ℂ) * (-1) ^ F.twoSpin = -1)
    {t : ℝ} (ht : t ≠ 0) : F.Wc (t : ℂ) = 0 := by
  rw [F.slice t ht]
  exact F.W_eq_zero_of_spacelike_of_wrong_stat h (F.e_spacelike.smul ht)

end RelativisticQuantumField

/-! ## Auxiliary complex analysis -/

/-- The punctured complex plane is preconnected. -/
lemma isPreconnected_compl_zero : IsPreconnected ({0}ᶜ : Set ℂ) :=
  (isConnected_compl_singleton_of_one_lt_rank
    (by simp [Complex.rank_real_complex]) 0).isPreconnected

/-- A function holomorphic on the punctured plane and vanishing on all nonzero reals
vanishes identically there.  This is the one-variable identity theorem, and it is the
analytic input of the spin–statistics argument: it propagates the vanishing of the
two-point function from spacelike to timelike separations. -/
lemma eqOn_zero_of_vanishes_on_reals {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f ({0}ᶜ : Set ℂ))
    (hzero : ∀ t : ℝ, t ≠ 0 → f (t : ℂ) = 0) :
    Set.EqOn f 0 ({0}ᶜ : Set ℂ) := by
  have h1 : (1 : ℂ) ∈ ({0}ᶜ : Set ℂ) := by simp
  refine hf.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_compl_zero h1 ?_
  -- the reals near `1` are all nonzero, so `f` vanishes frequently near `1`
  have hcoe : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 1 {(1 : ℝ)}ᶜ)
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa [Complex.ofReal_eq_one] using ht
  have hfreq : ∃ᶠ t : ℝ in nhdsWithin 1 {(1 : ℝ)}ᶜ, f (t : ℂ) = 0 := by
    have hev : ∀ᶠ t : ℝ in nhdsWithin 1 {(1 : ℝ)}ᶜ, f (t : ℂ) = 0 := by
      have : ∀ᶠ t : ℝ in nhds (1 : ℝ), t ≠ 0 := by
        have : ∀ᶠ t : ℝ in nhds (1 : ℝ), (0 : ℝ) < t :=
          eventually_gt_nhds (by norm_num)
        filter_upwards [this] with t ht using ne_of_gt ht
      filter_upwards [nhdsWithin_le_nhds this] with t ht using hzero t ht
    exact hev.frequently
  exact hcoe.frequently hfreq

/-! ## The spin–statistics theorem -/

/-- **Spin–statistics connection.**

For a relativistic quantum field satisfying the Wightman hypotheses packaged in
`Frontier.RelativisticQuantumField` — microcausality at spacelike separation,
Lorentz covariance in the Bargmann–Hall–Wightman form, analyticity of the
Wightman function, and nontriviality — the statistics sign is determined by the
spin:

`stat = (-1) ^ (2j)`,

i.e. fields of integer spin obey Bose statistics and fields of half-integer spin
obey Fermi statistics.  The wrong pairing is impossible: it forces the two-point
function to vanish at all spacelike separations, hence — by analytic
continuation — identically, so that the field is trivial. -/
theorem spin_statistics (F : RelativisticQuantumField) : F.stat = (-1) ^ F.twoSpin := by
  by_contra hne
  -- `stat` and `(-1)^twoSpin` are both signs, so if they differ their product is `-1`.
  have hsign : F.stat = 1 ∨ F.stat = -1 := mul_self_eq_one_iff.mp F.stat_sq
  have hpm : ((-1 : ℤ)) ^ F.twoSpin = 1 ∨ ((-1 : ℤ)) ^ F.twoSpin = -1 := by
    rcases Nat.even_or_odd F.twoSpin with hp | hp
    · exact Or.inl hp.neg_one_pow
    · exact Or.inr hp.neg_one_pow
  have hZ : F.stat * (-1 : ℤ) ^ F.twoSpin = -1 := by
    rcases hsign with h1 | h1 <;> rcases hpm with h2 | h2 <;>
      simp [h1, h2] at hne ⊢
  have h : (F.stat : ℂ) * (-1) ^ F.twoSpin = -1 := by
    have := congrArg (fun n : ℤ => (n : ℂ)) hZ
    push_cast at this
    simpa using this
  -- Wrong statistics ⟹ the analytic slice vanishes on the punctured real line ⟹ everywhere.
  have hvan : Set.EqOn F.Wc 0 ({0}ᶜ : Set ℂ) :=
    eqOn_zero_of_vanishes_on_reals F.analytic
      (fun t ht => F.Wc_eq_zero_of_real_of_wrong_stat h ht)
  obtain ⟨z, hz, hzne⟩ := F.nontrivial
  exact hzne (hvan (by simpa using hz))

/-- Integer spin fields are bosons. -/
theorem spin_statistics_bose (F : RelativisticQuantumField) (h : Even F.twoSpin) :
    F.stat = 1 := by
  rw [spin_statistics F]; exact h.neg_one_pow

/-- Half-integer spin fields are fermions. -/
theorem spin_statistics_fermi (F : RelativisticQuantumField) (h : Odd F.twoSpin) :
    F.stat = -1 := by
  rw [spin_statistics F]; exact h.neg_one_pow

/-! ## Non-vacuity: the hypotheses are satisfiable, for both statistics -/

/-- A massless free scalar (spin `0`, Bose): `W x = 1 / (x·x)`, sliced along the
spacelike direction `e = (0,1,0,0)`. -/
noncomputable def freeScalar : RelativisticQuantumField where
  twoSpin := 0
  stat := 1
  stat_sq := by norm_num
  W := fun x => ((minkowskiSq x : ℝ) : ℂ)⁻¹
  locality := by intro x _; simp [minkowskiSq_neg]
  bhw := by intro x _; simp [minkowskiSq_neg]
  e := ![0, 1, 0, 0]
  e_spacelike := by
    norm_num [IsSpacelike, minkowskiSq, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.head_cons]
  Wc := fun z => -(z ^ 2)⁻¹
  analytic := by
    intro z hz
    have hz' : z ≠ 0 := by simpa using hz
    have h1 : AnalyticAt ℂ (fun z : ℂ => z ^ 2) z := analyticAt_id.pow 2
    exact (h1.inv (pow_ne_zero 2 hz')).neg
  slice := by
    intro t _
    have h : minkowskiSq (t • (![0, 1, 0, 0] : Spacetime)) = -t ^ 2 := by
      simp [minkowskiSq, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
        Matrix.head_cons]
    rw [h]
    push_cast
    ring
  nontrivial := ⟨1, one_ne_zero, by norm_num⟩

/-- A spin-`1/2`-type field (`2j = 1`, Fermi): a parity-odd two-point function
`W x = x⁰ / (x·x)²`, sliced along the spacelike direction `e = (1,2,0,0)`. -/
noncomputable def freeFermi : RelativisticQuantumField where
  twoSpin := 1
  stat := -1
  stat_sq := by norm_num
  W := fun x => ((x 0 : ℝ) : ℂ) * (((minkowskiSq x) ^ 2 : ℝ) : ℂ)⁻¹
  locality := by
    intro x _
    have h : minkowskiSq (-x) = minkowskiSq x := minkowskiSq_neg x
    simp [h]
  bhw := by
    intro x _
    have h : minkowskiSq (-x) = minkowskiSq x := minkowskiSq_neg x
    simp [h]
  e := ![1, 2, 0, 0]
  e_spacelike := by
    norm_num [IsSpacelike, minkowskiSq, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.head_cons]
  Wc := fun z => (9 * z ^ 3)⁻¹
  analytic := by
    intro z hz
    have hz' : z ≠ 0 := by simpa using hz
    have h1 : AnalyticAt ℂ (fun z : ℂ => 9 * z ^ 3) z := analyticAt_const.mul (analyticAt_id.pow 3)
    exact h1.inv (by simp [hz'])
  slice := by
    intro t ht
    have hx0 : (t • (![1, 2, 0, 0] : Spacetime)) 0 = t := by simp
    have hms : minkowskiSq (t • (![1, 2, 0, 0] : Spacetime)) = -3 * t ^ 2 := by
      simp [minkowskiSq, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
        Matrix.head_cons]
      ring
    rw [hx0, hms]
    have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    push_cast
    field_simp
    ring
  nontrivial := ⟨1, one_ne_zero, by norm_num⟩

end Frontier

