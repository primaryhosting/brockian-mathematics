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

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well
of width `L`: `E n = n² π² ℏ² / (2 m L²)`. -/
noncomputable def boxEnergy (m hbar L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The `n`-th (unnormalised) stationary state of the infinite square well of width `L`:
`ψ n x = sin (n π x / L)`. -/
noncomputable def boxState (L : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => Real.sin ((n : ℝ) * Real.pi * x / L)

/-- `f` is a stationary state of energy `E` for a particle of mass `m` in the infinite
square well of width `L`: it is twice continuously differentiable, satisfies the
time-independent Schrödinger equation `-ℏ²/(2m) f'' = E f`, vanishes at the walls
`0` and `L`, and is not identically zero inside the well. -/
def IsBoxEigenstate (m hbar L E : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧
    (∀ x : ℝ, -(hbar ^ 2 / (2 * m)) * deriv (deriv f) x = E * f x) ∧
    f 0 = 0 ∧ f L = 0 ∧ ∃ x ∈ Set.Ioo (0 : ℝ) L, f x ≠ 0

/-- For `f'' = -c f`, the quantity `(f')² + c f²` is constant. -/
theorem harmonic_invariant (c : ℝ) (f f' : ℝ → ℝ)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hf' : ∀ x : ℝ, HasDerivAt f' (-c * f x) x)
    (x y : ℝ) :
    (f' x) ^ 2 + c * (f x) ^ 2 = (f' y) ^ 2 + c * (f y) ^ 2 := by
  set Q : ℝ → ℝ := fun t => (f' t) ^ 2 + c * (f t) ^ 2 with hQ
  have hQd : ∀ t : ℝ, HasDerivAt Q 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (f' t) ^ 2) (2 * f' t * (-c * f t)) t := by
      simpa using ((hf' t).pow 2)
    have h2 : HasDerivAt (fun t : ℝ => c * (f t) ^ 2) (c * (2 * f t * f' t)) t :=
      (((hf t).pow 2).const_mul c).congr_deriv (by ring)
    have h3 := h1.add h2
    convert h3 using 1
    ring
  exact is_const_of_deriv_eq_zero (fun t => (hQd t).differentiableAt)
    (fun t => (hQd t).deriv) x y

/-- Uniqueness: a solution of `f'' = -c f` with `c > 0` vanishing to first order at `0`
is identically zero. -/
theorem harmonic_unique_zero (c : ℝ) (hc : 0 < c) (f f' : ℝ → ℝ)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hf' : ∀ x : ℝ, HasDerivAt f' (-c * f x) x)
    (h0 : f 0 = 0) (h0' : f' 0 = 0) : ∀ x : ℝ, f x = 0 := by
  intro x
  have h := harmonic_invariant c f f' hf hf' x 0
  rw [h0, h0'] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h
  have hb : (f x) ^ 2 = 0 := by nlinarith [sq_nonneg (f' x), sq_nonneg (f x)]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hb

/-- For `c ≤ 0` there is no nontrivial solution of `f'' = -c f` vanishing at `0` and `L`. -/
theorem no_nonpositive_eigenvalue (c L : ℝ) (hL : 0 < L) (hc : c ≤ 0) (f f' : ℝ → ℝ)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hf' : ∀ x : ℝ, HasDerivAt f' (-c * f x) x)
    (h0 : f 0 = 0) (hL0 : f L = 0) : ∀ x ∈ Set.Ioo (0 : ℝ) L, f x = 0 := by
  set h : ℝ → ℝ := fun t => f t * f' t with hh
  have hhd : ∀ t : ℝ, HasDerivAt h ((f' t) ^ 2 - c * (f t) ^ 2) t := by
    intro t
    have := (hf t).mul (hf' t)
    convert this using 1
    ring
  have hmono : Monotone h := by
    apply monotone_of_deriv_nonneg (fun t => (hhd t).differentiableAt)
    intro t
    rw [(hhd t).deriv]
    nlinarith [sq_nonneg (f' t), sq_nonneg (f t)]
  have hzero : ∀ x ∈ Set.Icc (0 : ℝ) L, h x = 0 := by
    intro x hx
    have h1 : h 0 ≤ h x := hmono hx.1
    have h2 : h x ≤ h L := hmono hx.2
    simp only [hh, h0, hL0, zero_mul] at h1 h2
    linarith
  have key : ∀ x ∈ Set.Ioo (0 : ℝ) L, (f' x) ^ 2 - c * (f x) ^ 2 = 0 := by
    intro x hx
    have hev : h =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hzero y (Set.Ioo_subset_Icc_self hy)
    exact (hhd x).unique ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev)
  rcases lt_or_eq_of_le hc with hcneg | hc0
  · intro x hx
    have hkey := key x hx
    have hb : (f x) ^ 2 = 0 := by nlinarith [sq_nonneg (f' x), sq_nonneg (f x)]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hb
  · subst hc0
    have hx0 : (L / 2) ∈ Set.Ioo (0 : ℝ) L := by constructor <;> linarith
    have hk := key _ hx0
    simp only [zero_mul, sub_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true] at hk
    have hall : ∀ y : ℝ, f' y = 0 := by
      intro y
      have hy := harmonic_invariant 0 f f' hf hf' y (L / 2)
      simp only [zero_mul, add_zero, hk] at hy
      simpa using hy
    have hconst : ∀ y : ℝ, f y = f 0 := fun y =>
      is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt)
        (fun t => by rw [(hf t).deriv]; exact hall t) y 0
    intro x _
    rw [hconst x, h0]

/-- Quantisation: any nontrivial solution of `f'' = -c f` on `[0, L]` vanishing at the
endpoints forces `c = n²π²/L²` for some `n ≥ 1`. -/
theorem quantized_of_boundary (c L : ℝ) (hL : 0 < L) (f f' : ℝ → ℝ)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hf' : ∀ x : ℝ, HasDerivAt f' (-c * f x) x)
    (h0 : f 0 = 0) (hL0 : f L = 0) (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) L) (hfx₀ : f x₀ ≠ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ c = (n : ℝ) ^ 2 * Real.pi ^ 2 / L ^ 2 := by
  have hc : 0 < c := by
    by_contra hcon
    push_neg at hcon
    exact hfx₀ (no_nonpositive_eigenvalue c L hL hcon f f' hf hf' h0 hL0 x₀ hx₀)
  set k : ℝ := Real.sqrt c with hkdef
  have hk : 0 < k := Real.sqrt_pos.mpr hc
  have hk2 : k ^ 2 = c := Real.sq_sqrt hc.le
  set a : ℝ := f' 0 / k with hadef
  have hak : a * k = f' 0 := by rw [hadef, div_mul_cancel₀ _ hk.ne']
  set g : ℝ → ℝ := fun x => f x - a * Real.sin (k * x) with hg
  set g' : ℝ → ℝ := fun x => f' x - f' 0 * Real.cos (k * x) with hg'
  have hgd : ∀ x : ℝ, HasDerivAt g (g' x) x := by
    intro x
    have hs : HasDerivAt (fun x : ℝ => Real.sin (k * x)) (Real.cos (k * x) * k) x := by
      simpa using ((hasDerivAt_id x).const_mul k).sin
    have hsum := (hf x).sub (hs.const_mul a)
    convert hsum using 1
    simp only [hg']
    rw [← hak]; ring
  have hg'd : ∀ x : ℝ, HasDerivAt g' (-c * g x) x := by
    intro x
    have hcs : HasDerivAt (fun x : ℝ => Real.cos (k * x)) (-Real.sin (k * x) * k) x := by
      simpa using ((hasDerivAt_id x).const_mul k).cos
    have hsum := (hf' x).sub (hcs.const_mul (f' 0))
    convert hsum using 1
    simp only [hg]
    rw [← hak, ← hk2]; ring
  have hg0 : g 0 = 0 := by simp [hg, h0]
  have hg0' : g' 0 = 0 := by simp [hg']
  have hgz := harmonic_unique_zero c hc g g' hgd hg'd hg0 hg0'
  have hfval : ∀ x : ℝ, f x = a * Real.sin (k * x) := by
    intro x
    have hzx := hgz x
    simp only [hg, sub_eq_zero] at hzx
    exact hzx
  have ha : a ≠ 0 := by
    intro hA
    exact hfx₀ (by rw [hfval x₀, hA, zero_mul])
  have hsinL : Real.sin (k * L) = 0 := by
    have hLval := hfval L
    rw [hL0] at hLval
    rcases mul_eq_zero.mp hLval.symm with h | h
    · exact absurd h ha
    · exact h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsinL
  have hnpos : 0 < (n : ℝ) := by
    have hkl : 0 < k * L := mul_pos hk hL
    nlinarith [Real.pi_pos]
  have hnz : 0 < n := by exact_mod_cast hnpos
  refine ⟨n.toNat, by omega, ?_⟩
  have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnz.le
  rw [hcast, ← hk2]
  have hkval : k = (n : ℝ) * Real.pi / L := by field_simp; linarith [hn]
  rw [hkval, div_pow, mul_pow]

/-- `boxState L n` is a stationary state with energy `boxEnergy m hbar L n`, for `n ≥ 1`. -/
theorem isBoxEigenstate_boxState (m hbar L : ℝ) (hm : 0 < m) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n) :
    IsBoxEigenstate m hbar L (boxEnergy m hbar L n) (boxState L n) := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (n : ℝ) * Real.pi / L := ⟨_, rfl⟩
  have hLne : L ≠ 0 := ne_of_gt hL
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := by positivity
  have hpsi : boxState L n = fun x : ℝ => Real.sin (u * x) := by
    funext x
    simp only [boxState, hu]
    ring_nf
  have h1 : ∀ x : ℝ, HasDerivAt (boxState L n) (u * Real.cos (u * x)) x := by
    intro x
    rw [hpsi]
    simpa [mul_comm] using ((hasDerivAt_id x).const_mul u).sin
  have hd1 : deriv (boxState L n) = fun x : ℝ => u * Real.cos (u * x) :=
    funext fun x => (h1 x).deriv
  have h2 : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ => u * Real.cos (u * x)) (-(u ^ 2) * Real.sin (u * x)) x := by
    intro x
    have hcs := (((hasDerivAt_id x).const_mul u).cos).const_mul u
    convert hcs using 1
    simp; ring
  have hd2 : ∀ x : ℝ, deriv (deriv (boxState L n)) x = -(u ^ 2) * Real.sin (u * x) := by
    intro x; rw [hd1]; exact (h2 x).deriv
  have huL : u * L = (n : ℝ) * Real.pi := by rw [hu]; field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hpsi]
    exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  · intro x
    rw [hd2 x]
    simp only [hpsi, boxEnergy, hu]
    field_simp
  · simp [hpsi]
  · simp only [hpsi, huL]
    exact Real.sin_nat_mul_pi n
  · refine ⟨L / (2 * n), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]
      nlinarith
    · have hval : u * (L / (2 * n)) = Real.pi / 2 := by rw [hu]; field_simp
      simp only [hpsi, hval, Real.sin_pi_div_two]
      norm_num

/-- **Particle in a box.** For a particle of mass `m > 0` in an infinite square well of
width `L > 0`, a real number `E` is an energy eigenvalue (i.e. admits a nontrivial
stationary state vanishing at the walls) if and only if
`E = n² π² ℏ² / (2 m L²)` for some integer `n ≥ 1`. -/
theorem particle_in_box (m hbar L : ℝ) (hm : 0 < m) (hhbar : hbar ≠ 0) (hL : 0 < L) (E : ℝ) :
    (∃ f : ℝ → ℝ, IsBoxEigenstate m hbar L E f) ↔
      ∃ n : ℕ, 1 ≤ n ∧ E = boxEnergy m hbar L n := by
  constructor
  · rintro ⟨f, hsmooth, hode, h0, hL0, x₀, hx₀, hfx₀⟩
    obtain ⟨hdiff, -, hderiv⟩ :=
      contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f by norm_num at hsmooth ⊢; exact hsmooth)
    have hf : ∀ x : ℝ, HasDerivAt f (deriv f x) x := fun x => (hdiff x).hasDerivAt
    set c : ℝ := 2 * m * E / hbar ^ 2 with hcdef
    have hf' : ∀ x : ℝ, HasDerivAt (deriv f) (-c * f x) x := by
      intro x
      have hd : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
        ((hderiv.differentiable (by norm_num)) x).hasDerivAt
      have heq : deriv (deriv f) x = -c * f x := by
        have hx := hode x
        rw [hcdef]
        field_simp at hx ⊢
        nlinarith [hx]
      rwa [heq] at hd
    obtain ⟨n, hn1, hcn⟩ :=
      quantized_of_boundary c L hL f (deriv f) hf hf' h0 hL0 x₀ hx₀ hfx₀
    refine ⟨n, hn1, ?_⟩
    have hE : E = c * hbar ^ 2 / (2 * m) := by
      rw [hcdef]; field_simp
    rw [hE, hcn, boxEnergy]
    field_simp
  · rintro ⟨n, hn1, rfl⟩
    exact ⟨boxState L n, isBoxEigenstate_boxState m hbar L hm hL n hn1⟩

end QPhys

