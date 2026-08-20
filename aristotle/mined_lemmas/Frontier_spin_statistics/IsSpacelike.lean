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
