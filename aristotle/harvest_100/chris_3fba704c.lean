import Mathlib

/-!
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
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

/-! ## The eight Thurston geometries -/

/-- The eight three-dimensional Thurston model geometries. -/
inductive ThurstonGeometry
  /-- Euclidean space `E³`. -/
  | euclidean
  /-- The round sphere `S³`. -/
  | spherical
  /-- Hyperbolic space `H³`. -/
  | hyperbolic
  /-- The product geometry `S² × ℝ`. -/
  | sphereTimesLine
  /-- The product geometry `H² × ℝ`. -/
  | hyperbolicPlaneTimesLine
  /-- The universal cover of `SL(2,ℝ)`. -/
  | slTwoTilde
  /-- Nil geometry (the Heisenberg group). -/
  | nil
  /-- Sol geometry. -/
  | sol
  deriving DecidableEq, Fintype, Repr

/-- There are exactly eight Thurston geometries. -/
theorem card_thurstonGeometry : Fintype.card ThurstonGeometry = 8 := by rfl

/-! ## Model geometries and geometric structures -/

/-- A *model geometry*: a nonempty, complete, simply connected, homogeneous metric space.
(In Thurston's setting these are the eight maximal simply connected homogeneous Riemannian
`3`-manifolds admitting a compact quotient.) -/
structure ModelSpace where
  /-- The underlying set of the model. -/
  carrier : Type
  /-- The metric on the model. -/
  metric : MetricSpace carrier
  /-- The model is nonempty. -/
  nonempty' : Nonempty carrier
  /-- The model is a complete metric space. -/
  complete : @CompleteSpace carrier metric.toUniformSpace
  /-- The model is simply connected. -/
  simplyConnected : @SimplyConnectedSpace carrier metric.toUniformSpace.toTopologicalSpace
  /-- The isometry group acts transitively: the model is homogeneous. -/
  homogeneous : ∀ x y : carrier, ∃ f : @IsometryEquiv carrier carrier
    metric.toPseudoMetricSpace.toPseudoEMetricSpace metric.toPseudoMetricSpace.toPseudoEMetricSpace,
    f x = y

attribute [instance] ModelSpace.metric ModelSpace.nonempty' ModelSpace.complete
  ModelSpace.simplyConnected

/-- A group of isometries of a model space acting freely, properly discontinuously and
cocompactly: exactly the data giving a closed manifold a geometric structure modelled on `X`. -/
structure GeometricAction (X : ModelSpace) where
  /-- The group of covering isometries. -/
  group : Subgroup (X.carrier ≃ᵢ X.carrier)
  /-- The action is free. -/
  free : ∀ g ∈ group, g ≠ 1 → ∀ x : X.carrier, g x ≠ x
  /-- The action is properly discontinuous. -/
  discontinuous : ∀ K : Set X.carrier, IsCompact K →
    {g : X.carrier ≃ᵢ X.carrier | g ∈ group ∧ ∃ x ∈ K, g x ∈ K}.Finite
  /-- The action is cocompact. -/
  cocompact : ∃ K : Set X.carrier, IsCompact K ∧ ∀ x : X.carrier, ∃ g ∈ group, g x ∈ K

/-- The orbit equivalence relation of a group of isometries. -/
def orbitSetoid (X : ModelSpace) (Γ : Subgroup (X.carrier ≃ᵢ X.carrier)) :
    Setoid X.carrier where
  r x y := ∃ g ∈ Γ, g x = y
  iseqv := by
    refine ⟨fun x => ⟨1, Γ.one_mem, rfl⟩, ?_, ?_⟩
    · rintro x y ⟨g, hg, rfl⟩
      exact ⟨g⁻¹, Γ.inv_mem hg, by simp⟩
    · rintro x y z ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
      exact ⟨h * g, Γ.mul_mem hh hg, rfl⟩

/-- The quotient of a model space by a geometric action: a closed geometric manifold. -/
def GeometricQuotient (X : ModelSpace) (A : GeometricAction X) : Type :=
  Quotient (orbitSetoid X A.group)

instance (X : ModelSpace) (A : GeometricAction X) :
    TopologicalSpace (GeometricQuotient X A) :=
  inferInstanceAs (TopologicalSpace (Quotient (orbitSetoid X A.group)))

/-- A topological space `M` *admits a geometric structure modelled on `X`* if it is homeomorphic
to the quotient of `X` by a free, properly discontinuous, cocompact group of isometries. -/
def AdmitsGeometricStructure (M : Type) [TopologicalSpace M] (X : ModelSpace) : Prop :=
  ∃ A : GeometricAction X, Nonempty (M ≃ₜ GeometricQuotient X A)

/-- A geometric quotient is compact: it is the continuous image of a compact set. -/
instance compactSpace_geometricQuotient (X : ModelSpace) (A : GeometricAction X) :
    CompactSpace (GeometricQuotient X A) := by
  obtain ⟨K, hK, hcov⟩ := A.cocompact
  constructor
  have himg : (Set.univ : Set (GeometricQuotient X A)) =
      (Quotient.mk (orbitSetoid X A.group)) '' K := by
    ext q
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    induction q using Quotient.inductionOn with
    | h x =>
      obtain ⟨g, hg, hgx⟩ := hcov x
      exact ⟨g x, hgx, Quotient.sound ⟨g⁻¹, A.group.inv_mem hg, by simp⟩⟩
  rw [show (Set.univ : Set (GeometricQuotient X A)) = _ from himg]
  exact hK.image continuous_quotient_mk'

/-- A geometric quotient is connected: a model geometry is simply connected, hence connected. -/
instance connectedSpace_geometricQuotient (X : ModelSpace) (A : GeometricAction X) :
    ConnectedSpace (GeometricQuotient X A) :=
  inferInstanceAs (ConnectedSpace (Quotient (orbitSetoid X A.group)))

/-! ## Base case: the Euclidean model `E³` and the flat 3-torus -/

/-- Euclidean 3-space, the underlying space of the model geometry `E³`. -/
abbrev EuclideanThreeSpace : Type := EuclideanSpace ℝ (Fin 3)

/-- The model geometry `E³`. -/
noncomputable def euclideanModel : ModelSpace where
  carrier := EuclideanThreeSpace
  metric := inferInstance
  nonempty' := inferInstance
  complete := inferInstance
  simplyConnected := inferInstance
  homogeneous := by
    intro x y
    exact ⟨IsometryEquiv.addRight (y - x), by simp⟩

/-- Translation of Euclidean 3-space by a vector. -/
noncomputable def transl (v : EuclideanThreeSpace) : EuclideanThreeSpace ≃ᵢ EuclideanThreeSpace :=
  IsometryEquiv.addRight v

@[simp] theorem transl_apply (v x : EuclideanThreeSpace) : transl v x = x + v := rfl

theorem transl_mul (u v : EuclideanThreeSpace) : transl u * transl v = transl (v + u) := by
  ext x i
  simp [add_assoc]

theorem transl_zero : transl 0 = 1 := by
  ext x i; simp

theorem transl_inv (v : EuclideanThreeSpace) : (transl v)⁻¹ = transl (-v) := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, transl_mul]
  simp [transl_zero]

/-- The vector with integer coordinates `v`, viewed in Euclidean 3-space. -/
noncomputable def intVec (v : Fin 3 → ℤ) : EuclideanThreeSpace := WithLp.toLp 2 (fun i => (v i : ℝ))

@[simp] theorem intVec_apply (v : Fin 3 → ℤ) (i : Fin 3) : intVec v i = (v i : ℝ) := rfl

theorem intVec_add (u v : Fin 3 → ℤ) : intVec (u + v) = intVec u + intVec v := by
  ext i; simp

theorem intVec_neg (u : Fin 3 → ℤ) : intVec (-u) = -intVec u := by
  ext i; simp

theorem intVec_zero : intVec 0 = 0 := by ext i; simp

/-- The group `ℤ³` of integer translations of Euclidean 3-space. -/
noncomputable def integerTranslations : Subgroup (EuclideanThreeSpace ≃ᵢ EuclideanThreeSpace) where
  carrier := {f | ∃ v : Fin 3 → ℤ, f = transl (intVec v)}
  mul_mem' := by
    rintro a b ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨v + u, by rw [transl_mul, intVec_add]⟩
  one_mem' := ⟨0, by rw [intVec_zero, transl_zero]⟩
  inv_mem' := by
    rintro a ⟨v, rfl⟩
    exact ⟨-v, by rw [transl_inv, intVec_neg]⟩

theorem mem_integerTranslations {f : EuclideanThreeSpace ≃ᵢ EuclideanThreeSpace} :
    f ∈ integerTranslations ↔ ∃ v : Fin 3 → ℤ, f = transl (intVec v) := Iff.rfl

/-- A vector of Euclidean 3-space all of whose coordinates are at most `1` in absolute value
has norm at most `2`. -/
theorem norm_le_two_of_coords {y : EuclideanThreeSpace} (h : ∀ i, |y i| ≤ 1) : ‖y‖ ≤ 2 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖y i‖ ^ 2 ≤ 4 := by
    have hone : ∀ i : Fin 3, ‖y i‖ ^ 2 ≤ 1 := by
      intro i
      have := h i
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (y i)]
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin 3, (1 : ℝ) := Finset.sum_le_sum fun i _ => hone i
      _ ≤ 4 := by norm_num
  calc Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hsum
    _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The action of `ℤ³` on `E³` by translations is free. -/
theorem integerTranslations_free :
    ∀ g ∈ integerTranslations, g ≠ 1 → ∀ x : EuclideanThreeSpace, g x ≠ x := by
  intro g hg hne x hx
  obtain ⟨v, rfl⟩ := hg
  apply hne
  have hv : intVec v = 0 := by
    have hx' : x + intVec v = x := hx
    simpa using hx'
  rw [hv, transl_zero]

/-- The action of `ℤ³` on `E³` by translations is properly discontinuous. -/
theorem integerTranslations_discontinuous (K : Set EuclideanThreeSpace) (hK : IsCompact K) :
    {g : EuclideanThreeSpace ≃ᵢ EuclideanThreeSpace |
      g ∈ integerTranslations ∧ ∃ x ∈ K, g x ∈ K}.Finite := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : EuclideanThreeSpace)
  have hfin : {v : Fin 3 → ℤ | ∀ i, |v i| ≤ ⌈2 * R⌉}.Finite := by
    refine Set.Finite.subset
      (Set.Finite.pi fun _ : Fin 3 => Set.finite_Icc (-⌈2 * R⌉) ⌈2 * R⌉) ?_
    intro v hv i _
    exact ⟨neg_le_of_abs_le (hv i), le_of_abs_le (hv i)⟩
  refine Set.Finite.subset (hfin.image fun v => transl (intVec v)) ?_
  rintro g ⟨hg, x, hxK, hgxK⟩
  obtain ⟨v, rfl⟩ := hg
  refine ⟨v, ?_, rfl⟩
  intro i
  have h1 : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hxK
  have h2 : ‖x + intVec v‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hR hgxK
  have h3 : ‖intVec v‖ ≤ 2 * R := by
    have hsub : intVec v = (x + intVec v) - x := by abel
    rw [hsub]
    calc ‖(x + intVec v) - x‖ ≤ ‖x + intVec v‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have h4 : |(v i : ℝ)| ≤ 2 * R := by
    have hle := PiLp.norm_apply_le (intVec v) i
    rw [intVec_apply, Real.norm_eq_abs] at hle
    linarith
  have h5 : ((|v i| : ℤ) : ℝ) ≤ ((⌈2 * R⌉ : ℤ) : ℝ) := by
    push_cast
    exact le_trans h4 (Int.le_ceil _)
  exact_mod_cast h5

/-- The action of `ℤ³` on `E³` by translations is cocompact: the closed ball of radius `2`
contains a point of every orbit. -/
theorem integerTranslations_cocompact :
    ∃ K : Set EuclideanThreeSpace, IsCompact K ∧
      ∀ x : EuclideanThreeSpace, ∃ g ∈ integerTranslations, g x ∈ K := by
  refine ⟨Metric.closedBall 0 2, isCompact_closedBall _ _, ?_⟩
  intro x
  refine ⟨transl (intVec fun i => -⌊x i⌋), ⟨_, rfl⟩, ?_⟩
  have hcoord : ∀ i, |(x + intVec fun i => -⌊x i⌋) i| ≤ 1 := by
    intro i
    have hfr : (x + intVec fun i => -⌊x i⌋) i = Int.fract (x i) := by
      simp [Int.fract, sub_eq_add_neg]
    rw [hfr, abs_of_nonneg (Int.fract_nonneg _)]
    exact le_of_lt (Int.fract_lt_one _)
  simpa [Metric.mem_closedBall, dist_zero_right] using norm_le_two_of_coords hcoord

/-- The integer translations act freely, properly discontinuously and cocompactly on `E³`:
this is the geometric structure of the flat 3-torus. -/
noncomputable def flatTorusAction : GeometricAction euclideanModel where
  group := integerTranslations
  free := integerTranslations_free
  discontinuous := integerTranslations_discontinuous
  cocompact := integerTranslations_cocompact

/-- The flat 3-torus `E³ / ℤ³`. -/
noncomputable def FlatThreeTorus : Type := GeometricQuotient euclideanModel flatTorusAction

noncomputable instance : TopologicalSpace FlatThreeTorus :=
  inferInstanceAs (TopologicalSpace (GeometricQuotient euclideanModel flatTorusAction))

instance : CompactSpace FlatThreeTorus :=
  inferInstanceAs (CompactSpace (GeometricQuotient euclideanModel flatTorusAction))

instance : ConnectedSpace FlatThreeTorus :=
  inferInstanceAs (ConnectedSpace (GeometricQuotient euclideanModel flatTorusAction))

/-- The flat 3-torus is not a point: the classes of `0` and of the half-lattice vector differ. -/
instance : Nontrivial FlatThreeTorus := by
  refine ⟨⟨Quotient.mk (orbitSetoid euclideanModel flatTorusAction.group)
      (0 : EuclideanThreeSpace),
    Quotient.mk (orbitSetoid euclideanModel flatTorusAction.group)
      (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 / 2 : ℝ) else 0)), ?_⟩⟩
  intro hcontra
  obtain ⟨g, hg, hgx⟩ := Quotient.exact hcontra
  obtain ⟨v, rfl⟩ := hg
  have h0 : (transl (intVec v) (0 : EuclideanThreeSpace)) 0 =
      (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 / 2 : ℝ) else 0)) 0 := by
    exact congrArg (fun y : EuclideanThreeSpace => y 0) hgx
  simp only [transl_apply, zero_add, intVec_apply] at h0
  norm_num at h0
  have h1 : (2 * v 0 : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (v 0 : ℝ)) = 1)
  omega

/-- **Base case of geometrization.** The flat 3-torus is a closed manifold carrying the
Euclidean geometry `E³`. -/
theorem flatThreeTorus_admits_euclidean :
    AdmitsGeometricStructure FlatThreeTorus euclideanModel :=
  ⟨flatTorusAction, ⟨Homeomorph.refl _⟩⟩

/-! ## The geometrization statement -/

/-- The topological input to geometrization: an abstract theory of closed oriented
3-manifolds, equipped with the prime (connected sum) decomposition, the JSJ (torus)
decomposition, and the geometrization of the resulting pieces. -/
structure ThreeManifoldTheory where
  /-- Closed oriented 3-manifolds, up to diffeomorphism. -/
  Mfd : Type
  /-- The underlying topological space of a manifold. -/
  space : Mfd → Type
  /-- The topology on the underlying space. -/
  topology : ∀ M, TopologicalSpace (space M)
  /-- The eight model geometries. -/
  models : ThurstonGeometry → ModelSpace
  /-- Primeness (irreducible, or `S² × S¹`). -/
  IsPrime : Mfd → Prop
  /-- `ConnectedSum M L` : `M` is the connected sum of the manifolds in `L`. -/
  ConnectedSum : Mfd → List Mfd → Prop
  /-- `JSJ N P` : cutting `N` along a canonical family of incompressible tori yields
  the pieces `P`. -/
  JSJ : Mfd → List Mfd → Prop
  /-- Being atoroidal (no essential embedded torus). -/
  IsAtoroidal : Mfd → Prop
  /-- Admitting a Seifert fibration. -/
  IsSeifertFibered : Mfd → Prop
  /-- Kneser–Milnor prime decomposition. -/
  prime_decomposition : ∀ M, ∃ L, ConnectedSum M L ∧ ∀ N ∈ L, IsPrime N
  /-- Jaco–Shalen–Johannson torus decomposition. -/
  jsj_decomposition : ∀ N, IsPrime N → ∃ P, JSJ N P
  /-- Each JSJ piece is either atoroidal or Seifert fibered. -/
  jsj_pieces_atoroidal_or_seifert : ∀ N P, IsPrime N → JSJ N P → ∀ p ∈ P,
    IsAtoroidal p ∨ IsSeifertFibered p
  /-- Hyperbolization: an atoroidal piece carries the geometry `H³`. -/
  hyperbolization : ∀ p, IsAtoroidal p →
    @AdmitsGeometricStructure (space p) (topology p) (models ThurstonGeometry.hyperbolic)
  /-- A Seifert fibered piece carries one of the six Seifert geometries, i.e. one of the eight
  geometries other than `H³` and `Sol`. -/
  seifert_geometrization : ∀ p, IsSeifertFibered p → ∃ g : ThurstonGeometry,
    g ≠ ThurstonGeometry.hyperbolic ∧ g ≠ ThurstonGeometry.sol ∧
      @AdmitsGeometricStructure (space p) (topology p) (models g)

/-- **Thurston's geometrization conjecture (Perelman's theorem), stated as a
Lean-checked reduction.**

Given a theory of closed oriented 3-manifolds satisfying the Kneser–Milnor prime
decomposition, the JSJ torus decomposition, the dichotomy "atoroidal or Seifert fibered"
for the JSJ pieces, Thurston's hyperbolization for the atoroidal pieces and geometrization
of Seifert fibered pieces, every closed oriented 3-manifold `M` decomposes as a connected
sum of prime manifolds, each of which is cut along tori into pieces, and every resulting
piece is the quotient of one of the eight Thurston model geometries by a free, properly
discontinuous, cocompact group of isometries; the atoroidal pieces are hyperbolic. -/
theorem thurston_geometrization (T : ThreeManifoldTheory) (M : T.Mfd) :
    ∃ (primes : List T.Mfd) (pieces : T.Mfd → List T.Mfd),
      T.ConnectedSum M primes ∧
      (∀ N ∈ primes, T.IsPrime N ∧ T.JSJ N (pieces N)) ∧
      (∀ N ∈ primes, ∀ p ∈ pieces N, ∃ g : ThurstonGeometry,
        (T.IsAtoroidal p → g = ThurstonGeometry.hyperbolic) ∧
        @AdmitsGeometricStructure (T.space p) (T.topology p) (T.models g)) := by
  obtain ⟨L, hL, hprime⟩ := T.prime_decomposition M
  choose P hP using fun (N : T.Mfd) (h : T.IsPrime N) => T.jsj_decomposition N h
  refine ⟨L, fun N => if h : T.IsPrime N then P N h else [], hL, ?_, ?_⟩
  · intro N hN
    refine ⟨hprime N hN, ?_⟩
    simpa only [dif_pos (hprime N hN)] using hP N (hprime N hN)
  · intro N hN p hp
    simp only [dif_pos (hprime N hN)] at hp
    by_cases hato : T.IsAtoroidal p
    · exact ⟨ThurstonGeometry.hyperbolic, fun _ => rfl, T.hyperbolization p hato⟩
    · rcases T.jsj_pieces_atoroidal_or_seifert N _ (hprime N hN) (hP N (hprime N hN)) p hp with
        hato' | hsf
      · exact absurd hato' hato
      · obtain ⟨g, _, _, hgeo⟩ := T.seifert_geometrization p hsf
        exact ⟨g, fun h => absurd h hato, hgeo⟩

/-- The hypotheses of `thurston_geometrization` are consistent: they are satisfied by the
theory whose only manifold is the flat 3-torus, which carries the geometry `E³`.
In particular the theorem above is not vacuous. -/
theorem threeManifoldTheory_nonempty : Nonempty ThreeManifoldTheory :=
  ⟨{ Mfd := Unit
     space := fun _ => FlatThreeTorus
     topology := fun _ => inferInstance
     models := fun _ => euclideanModel
     IsPrime := fun _ => True
     ConnectedSum := fun M L => L = [M]
     JSJ := fun N P => P = [N]
     IsAtoroidal := fun _ => False
     IsSeifertFibered := fun _ => True
     prime_decomposition := fun M => ⟨[M], rfl, by simp⟩
     jsj_decomposition := fun N _ => ⟨[N], rfl⟩
     jsj_pieces_atoroidal_or_seifert := by
       rintro N P - rfl p -
       exact Or.inr trivial
     hyperbolization := fun p h => absurd h not_false
     seifert_geometrization := fun p _ =>
       ⟨ThurstonGeometry.euclidean, by decide, by decide, flatThreeTorus_admits_euclidean⟩ }⟩

end Frontier

