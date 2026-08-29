/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a module
-- docstring before the `import` commands.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Setup

The state space of `7` qubits is modelled as the space of complex-valued functions on
`Vec := Fin 7 → ZMod 2`, the set of the `2^7` computational basis labels, with the
standard hermitian inner product `ip`.  Linear operators are `Matrix Vec Vec ℂ` acting
by `Matrix.mulVec`.
-/

/-- Computational basis labels for 7 qubits. -/
abbrev Vec := Fin 7 → ZMod 2

/-- The `𝔽₂`-bilinear form on `Vec`. -/
def dotp (a b : Vec) : ZMod 2 := ∑ i, a i * b i

/-- The additive character of `ZMod 2`. -/
def chi (t : ZMod 2) : ℂ := if t = 0 then 1 else -1

/-- Parity check matrix of the `[7,4,3]` Hamming code. -/
def Hrow : Fin 3 → Vec := ![![1,0,1,0,1,0,1], ![0,1,1,0,0,1,1], ![0,0,0,1,1,1,1]]

/-- Generator matrix of the `[7,4,3]` Hamming code `C₁ = ker Hrow`. -/
def Grow : Fin 4 → Vec := ![![1,1,1,0,0,0,0], ![1,0,0,1,1,0,0], ![0,1,0,1,0,1,0], ![1,1,0,1,0,0,1]]

/-- The dual code `C₂ = C₁^⊥`, the `[7,3,4]` simplex code. -/
def inC2 (v : Vec) : Prop := ∀ k, dotp (Grow k) v = 0

instance : DecidablePred inC2 := by unfold inC2; infer_instance

/-- Hamming weight. -/
def wt (a : Vec) : ℕ := (Finset.univ.filter (fun i => a i ≠ 0)).card

/-- The all-ones vector: a representative of the nontrivial coset of `C₂` in `C₁`. -/
def allOnes : Vec := fun _ => 1

/-- The two unnormalised logical basis states `|0_L⟩ = ψ 0` and `|1_L⟩ = ψ allOnes`:
`ψ u = ∑_{v ∈ C₂ + u} |v⟩`. -/
def psi (u : Vec) : Vec → ℂ := fun x => if inC2 (x + u) then 1 else 0

/-- The standard hermitian inner product. -/
noncomputable def ip (f g : Vec → ℂ) : ℂ := ∑ x, (starRingEnd ℂ) (f x) * g x

/-- The Pauli operator `X^a Z^b`. -/
def pauli (a b : Vec) : Matrix Vec Vec ℂ := fun x y => if x = y + a then chi (dotp b y) else 0

/-- `unit i s` is `s` at position `i` and `0` elsewhere. -/
def unit (i : Fin 7) (s : ZMod 2) : Vec := fun k => if k = i then s else 0

/-- `M` acts on qubit `i` only, i.e. `M = m ⊗ 1` for a `2 × 2` matrix `m`. -/
def OneQubitOp (i : Fin 7) (M : Matrix Vec Vec ℂ) : Prop :=
  ∃ m : ZMod 2 → ZMod 2 → ℂ, ∀ x y, M x y = if (∀ k, k ≠ i → x k = y k) then m (x i) (y i) else 0

/-- Membership in the two-dimensional code space. -/
def codeVec (f : Vec → ℂ) : Prop := ∃ α β : ℂ, f = α • psi 0 + β • psi allOnes

/-! ## Combinatorial facts about the Hamming code -/

lemma C2_min_dist : ∀ a : Vec, wt a ≤ 2 → inC2 a → a = 0 := by decide

lemma coset_min_dist : ∀ a : Vec, wt a ≤ 2 → ¬ inC2 (a + allOnes) := by decide

lemma C1_min_dist : ∀ b : Vec, wt b ≤ 2 → (∀ j, dotp (Hrow j) b = 0) → b = 0 := by decide

lemma Hrow_mem_C2 : ∀ j, inC2 (Hrow j) := by decide

lemma card_C2 : (Finset.univ.filter (fun y : Vec => inC2 y)).card = 8 := by decide

/-! ## Elementary algebra -/

lemma dotp_add_right (a b c : Vec) : dotp a (b + c) = dotp a b + dotp a c := by
  simp [dotp, mul_add, Finset.sum_add_distrib]

lemma dotp_comm (a b : Vec) : dotp a b = dotp b a := by
  simp [dotp, mul_comm]

lemma vec_add_self (x : Vec) : x + x = 0 := by
  funext k
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x k = p
  revert p
  decide

lemma inC2_add {v w : Vec} (hv : inC2 v) (hw : inC2 w) : inC2 (v + w) := by
  intro k
  rw [dotp_add_right, hv k, hw k, add_zero]

lemma chi_add (s t : ZMod 2) : chi (s + t) = chi s * chi t := by
  fin_cases s <;> fin_cases t <;> simp [chi] <;> decide

lemma chi_zero : chi 0 = 1 := rfl

lemma chi_conj (t : ZMod 2) : (starRingEnd ℂ) (chi t) = chi t := by
  fin_cases t <;> simp [chi]

lemma psi_conj (u : Vec) (x : Vec) : (starRingEnd ℂ) (psi u x) = psi u x := by
  unfold psi; split <;> simp

/-! ## The core character sum -/

lemma inC2_zero : inC2 0 := by intro k; simp [dotp]

lemma inC2_shift {c : Vec} (hc : inC2 c) (x : Vec) : inC2 (x + c) ↔ inC2 x := by
  constructor
  · intro h
    have := inC2_add h hc
    rwa [add_assoc, vec_add_self, add_zero] at this
  · intro h; exact inC2_add h hc

lemma psi_shift {c : Vec} (hc : inC2 c) (u x : Vec) : psi u (x + c) = psi u x := by
  have h : inC2 (x + c + u) ↔ inC2 (x + u) := by
    rw [add_right_comm]; exact inC2_shift hc (x + u)
  unfold psi
  by_cases hx : inC2 (x + u)
  · rw [if_pos (h.mpr hx), if_pos hx]
  · rw [if_neg (fun hh => hx (h.mp hh)), if_neg hx]

lemma sum_shift (f : Vec → ℂ) (c : Vec) : (∑ x : Vec, f x) = ∑ x : Vec, f (x + c) :=
  (Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)).symm

lemma psi_mul_self (u x : Vec) : psi u x * psi u x = psi u x := by
  unfold psi; split <;> simp

lemma sum_psi (u : Vec) : (∑ x : Vec, psi u x) = 8 := by
  rw [sum_shift (fun x => psi u x) u]
  have : ∀ x : Vec, psi u (x + u) = if inC2 x then 1 else 0 := by
    intro x
    unfold psi
    rw [add_assoc, vec_add_self, add_zero]
  simp only [this]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  rw [card_C2]
  norm_num

lemma vec_id1 (x u a w : Vec) : (x + u) + (x + (a + w)) = a + (u + w) := by
  funext k
  simp only [Pi.add_apply]
  generalize x k = p
  generalize u k = q
  generalize a k = r
  generalize w k = t
  revert p q r t
  decide

/-- A nonzero low-weight character does not sum to zero over a coset of `C₂`. -/
lemma char_sum_vanish (b u : Vec) (hb : wt b ≤ 2) (hb0 : b ≠ 0) :
    (∑ x : Vec, chi (dotp b x) * psi u x) = 0 := by
  have hex : ∃ j, dotp (Hrow j) b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hb0 (C1_min_dist b hb h)
  obtain ⟨j, hj⟩ := hex
  set c : Vec := Hrow j with hcdef
  have hc2 : inC2 c := Hrow_mem_C2 j
  have hbc : dotp b c = 1 := by
    have : dotp b c = dotp (Hrow j) b := by rw [hcdef, dotp_comm]
    rw [this]
    revert hj
    generalize dotp (Hrow j) b = z
    revert z
    decide
  have key : ∀ x : Vec, chi (dotp b (x + c)) * psi u (x + c)
      = -(chi (dotp b x) * psi u x) := by
    intro x
    rw [dotp_add_right, hbc, chi_add, psi_shift hc2,
      (by rw [chi, if_neg (by decide : ¬((1 : ZMod 2) = 0))] : chi 1 = -1)]
    ring
  have h1 : (∑ x : Vec, chi (dotp b x) * psi u x)
      = -(∑ x : Vec, chi (dotp b x) * psi u x) := by
    conv_lhs => rw [sum_shift (fun x => chi (dotp b x) * psi u x) c]
    simp only [key, Finset.sum_neg_distrib]
  have h2 : (2 : ℂ) * (∑ x : Vec, chi (dotp b x) * psi u x) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-- The fundamental character sum computation for the Steane code. -/
lemma core (a b u w : Vec) (ha : wt a ≤ 2) (hb : wt b ≤ 2)
    (hu : u = 0 ∨ u = allOnes) (hw : w = 0 ∨ w = allOnes) :
    (∑ x : Vec, chi (dotp b x) * psi u x * psi w (x + a))
      = if a = 0 ∧ b = 0 ∧ u = w then 8 else 0 := by
  by_cases hc : inC2 (a + (u + w))
  · have huw : u = w := by
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · rfl
      · exact absurd (by simpa using hc) (coset_min_dist a ha)
      · exact absurd (by simpa using hc) (coset_min_dist a ha)
      · rfl
    subst huw
    have ha0 : a = 0 := by
      refine C2_min_dist a ha ?_
      rwa [vec_add_self, add_zero] at hc
    subst ha0
    by_cases hb0 : b = 0
    · subst hb0
      simp only [dotp, Pi.zero_apply, zero_mul, Finset.sum_const_zero, chi_zero, one_mul,
        add_zero]
      simp only [psi_mul_self]
      simpa using sum_psi u
    · simp only [add_zero, mul_assoc, psi_mul_self]
      rw [char_sum_vanish b u hb hb0]
      rw [if_neg]
      rintro ⟨-, h, -⟩
      exact hb0 h
  · have hzero : ∀ x : Vec, chi (dotp b x) * psi u x * psi w (x + a) = 0 := by
      intro x
      by_cases h1 : inC2 (x + u)
      · by_cases h2 : inC2 ((x + a) + w)
        · exfalso
          apply hc
          rw [add_assoc] at h2
          have h3 : inC2 ((x + u) + (x + (a + w))) := inC2_add h1 h2
          rwa [vec_id1] at h3
        · rw [show psi w (x + a) = 0 from by unfold psi; rw [if_neg h2], mul_zero]
      · rw [show psi u x = 0 from by unfold psi; rw [if_neg h1]]
        ring
    rw [Finset.sum_congr rfl (fun x _ => hzero x), Finset.sum_const_zero]
    rw [if_neg]
    rintro ⟨rfl, rfl, rfl⟩
    exact hc (by rw [vec_add_self, add_zero]; exact inC2_zero)

/-! ## Inner products of Pauli-corrupted logical states -/

lemma dotp_zero (a : Vec) : dotp a 0 = 0 := by simp [dotp]

lemma dotp_add_left (a b c : Vec) : dotp (a + b) c = dotp a c + dotp b c := by
  rw [dotp_comm, dotp_add_right, dotp_comm a c, dotp_comm b c]

lemma vec_add_cancel (x a : Vec) : x + a + a = x := by
  rw [add_assoc, vec_add_self, add_zero]

lemma vec_add_eq_zero_iff (a b : Vec) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (· + b) h
    simpa [vec_add_cancel] using this
  · rintro rfl; exact vec_add_self a

lemma pauli_mulVec (a b : Vec) (f : Vec → ℂ) (x : Vec) :
    (pauli a b).mulVec f x = chi (dotp b (x + a)) * f (x + a) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (x + a)]
  · simp only [pauli]
    rw [if_pos (show x = x + a + a by rw [vec_add_cancel])]
  · intro y _ hy
    simp only [pauli]
    rw [if_neg (fun h => hy (by rw [h, vec_add_cancel])), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Inner products of Pauli errors applied to the two logical basis states. -/
lemma ip_pauli (a1 b1 a2 b2 u w : Vec) (hA : wt (a1 + a2) ≤ 2) (hB : wt (b1 + b2) ≤ 2)
    (hu : u = 0 ∨ u = allOnes) (hw : w = 0 ∨ w = allOnes) :
    ip ((pauli a1 b1).mulVec (psi u)) ((pauli a2 b2).mulVec (psi w))
      = if a1 = a2 ∧ b1 = b2 ∧ u = w then 8 else 0 := by
  have hpt : ∀ x : Vec,
      (starRingEnd ℂ) ((pauli a1 b1).mulVec (psi u) (x + a1))
          * ((pauli a2 b2).mulVec (psi w) (x + a1))
        = chi (dotp b2 (a1 + a2))
            * (chi (dotp (b1 + b2) x) * psi u x * psi w (x + (a1 + a2))) := by
    intro x
    rw [pauli_mulVec, pauli_mulVec, vec_add_cancel, add_assoc x a1 a2, map_mul, chi_conj,
      psi_conj, dotp_add_right b2 x (a1 + a2), chi_add, dotp_add_left, chi_add]
    ring
  unfold ip
  rw [sum_shift _ a1]
  simp only [hpt]
  rw [← Finset.mul_sum, core (a1 + a2) (b1 + b2) u w hA hB hu hw]
  simp only [vec_add_eq_zero_iff]
  by_cases h : a1 = a2 ∧ b1 = b2 ∧ u = w
  · obtain ⟨rfl, rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl, rfl⟩, vec_add_self, dotp_zero, chi_zero, one_mul]
  · rw [if_neg h, mul_zero]

/-! ## Sesquilinearity of the inner product -/

lemma ip_add_left (f1 f2 g : Vec → ℂ) : ip (f1 + f2) g = ip f1 g + ip f2 g := by
  unfold ip
  simp [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

lemma ip_add_right (f g1 g2 : Vec → ℂ) : ip f (g1 + g2) = ip f g1 + ip f g2 := by
  unfold ip
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma ip_smul_left (c : ℂ) (f g : Vec → ℂ) : ip (c • f) g = (starRingEnd ℂ) c * ip f g := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

lemma ip_smul_right (c : ℂ) (f g : Vec → ℂ) : ip f (c • g) = c * ip f g := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp [Pi.smul_apply, smul_eq_mul]
  ring

lemma ip_sum_left {ι : Type} (S : Finset ι) (F : ι → Vec → ℂ) (g : Vec → ℂ) :
    ip (∑ p ∈ S, F p) g = ∑ p ∈ S, ip (F p) g := by
  unfold ip
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_apply, map_sum, Finset.sum_mul]

lemma ip_sum_right {ι : Type} (S : Finset ι) (f : Vec → ℂ) (G : ι → Vec → ℂ) :
    ip f (∑ p ∈ S, G p) = ∑ p ∈ S, ip f (G p) := by
  unfold ip
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_apply, Finset.mul_sum]

lemma wt_unit_add (i j : Fin 7) (s t : ZMod 2) : wt (unit i s + unit j t) ≤ 2 := by
  have hsub : (Finset.univ.filter (fun k => (unit i s + unit j t) k ≠ 0))
      ⊆ ({i, j} : Finset (Fin 7)) := by
    intro k hk
    simp only [Finset.mem_filter, Pi.add_apply, unit] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hcon
    push_neg at hcon
    rw [if_neg hcon.1, if_neg hcon.2] at hk
    simp at hk
  have h2 : ({i, j} : Finset (Fin 7)).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  exact (Finset.card_le_card hsub).trans h2

/-! ## The Knill-Laflamme condition on the code space -/

lemma dotp_zero_left (a : Vec) : dotp 0 a = 0 := by rw [dotp_comm, dotp_zero]

lemma zero_ne_allOnes : (0 : Vec) ≠ allOnes := by decide

lemma ip_psi (u w : Vec) (hu : u = 0 ∨ u = allOnes) (hw : w = 0 ∨ w = allOnes) :
    ip (psi u) (psi w) = if u = w then 8 else 0 := by
  have h := core 0 0 u w (by decide) (by decide) hu hw
  simp only [dotp_zero_left, chi_zero, one_mul, add_zero, true_and] at h
  unfold ip
  simp only [psi_conj]
  exact h

lemma ip_pauli_unit (i j : Fin 7) (s1 t1 s2 t2 : ZMod 2) (u w : Vec)
    (hu : u = 0 ∨ u = allOnes) (hw : w = 0 ∨ w = allOnes) :
    ip ((pauli (unit i s1) (unit i t1)).mulVec (psi u))
       ((pauli (unit j s2) (unit j t2)).mulVec (psi w))
      = if unit i s1 = unit j s2 ∧ unit i t1 = unit j t2 ∧ u = w then 8 else 0 :=
  ip_pauli _ _ _ _ u w (wt_unit_add i j s1 s2) (wt_unit_add i j t1 t2) hu hw

/-- The Knill-Laflamme condition for a pair of single-qubit Pauli errors. -/
lemma ip_pauli_code (i j : Fin 7) (s1 t1 s2 t2 : ZMod 2) (f g : Vec → ℂ)
    (hf : codeVec f) (hg : codeVec g) :
    ip ((pauli (unit i s1) (unit i t1)).mulVec f) ((pauli (unit j s2) (unit j t2)).mulVec g)
      = (if unit i s1 = unit j s2 ∧ unit i t1 = unit j t2 then 1 else 0) * ip f g := by
  obtain ⟨α, β, rfl⟩ := hf
  obtain ⟨γ, δ, rfl⟩ := hg
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ip_add_left, ip_add_right,
    ip_smul_left, ip_smul_right]
  rw [ip_pauli_unit i j s1 t1 s2 t2 0 0 (Or.inl rfl) (Or.inl rfl),
      ip_pauli_unit i j s1 t1 s2 t2 0 allOnes (Or.inl rfl) (Or.inr rfl),
      ip_pauli_unit i j s1 t1 s2 t2 allOnes 0 (Or.inr rfl) (Or.inl rfl),
      ip_pauli_unit i j s1 t1 s2 t2 allOnes allOnes (Or.inr rfl) (Or.inr rfl),
      ip_psi 0 0 (Or.inl rfl) (Or.inl rfl), ip_psi 0 allOnes (Or.inl rfl) (Or.inr rfl),
      ip_psi allOnes 0 (Or.inr rfl) (Or.inl rfl),
      ip_psi allOnes allOnes (Or.inr rfl) (Or.inr rfl)]
  rw [if_neg zero_ne_allOnes, if_neg (Ne.symm zero_ne_allOnes), if_pos rfl, if_pos rfl]
  by_cases hP : unit i s1 = unit j s2 ∧ unit i t1 = unit j t2
  · rw [if_pos hP,
      if_pos (show unit i s1 = unit j s2 ∧ unit i t1 = unit j t2 ∧ (0 : Vec) = 0 from
        ⟨hP.1, hP.2, rfl⟩),
      if_pos (show unit i s1 = unit j s2 ∧ unit i t1 = unit j t2 ∧ allOnes = allOnes from
        ⟨hP.1, hP.2, rfl⟩),
      if_neg (fun h => (Ne.symm zero_ne_allOnes) h.2.2),
      if_neg (fun h => zero_ne_allOnes h.2.2)]
    ring
  · rw [if_neg hP, if_neg (fun h => hP ⟨h.1, h.2.1⟩), if_neg (fun h => hP ⟨h.1, h.2.1⟩),
      if_neg (fun h => hP ⟨h.1, h.2.1⟩), if_neg (fun h => hP ⟨h.1, h.2.1⟩)]
    ring

/-! ## Pauli decomposition of an arbitrary single-qubit operator -/

lemma sum_zmod2 (F : ZMod 2 → ℂ) : (∑ s : ZMod 2, F s) = F 0 + F 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

lemma zmod2_cases (p : ZMod 2) : p = 0 ∨ p = 1 := by revert p; decide

lemma dotp_unit (i : Fin 7) (t : ZMod 2) (y : Vec) : dotp (unit i t) y = t * y i := by
  unfold dotp unit
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro k _ hk; rw [if_neg hk, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma eq_add_unit_iff (i : Fin 7) (s : ZMod 2) (x y : Vec) :
    x = y + unit i s ↔ ((∀ k, k ≠ i → x k = y k) ∧ x i = y i + s) := by
  constructor
  · intro h
    subst h
    refine ⟨fun k hk => ?_, ?_⟩
    · simp [unit, hk]
    · simp [unit]
  · rintro ⟨h1, h2⟩
    funext k
    by_cases hk : k = i
    · subst hk; simpa [unit] using h2
    · simpa [unit, hk] using h1 k hk

/-- The Pauli coefficients of a `2 × 2` matrix `m`. -/
noncomputable def ccOf (m : ZMod 2 → ZMod 2 → ℂ) (s t : ZMod 2) : ℂ :=
  if s = 0 then (if t = 0 then (m 0 0 + m 1 1) / 2 else (m 0 0 - m 1 1) / 2)
  else (if t = 0 then (m 1 0 + m 0 1) / 2 else (m 1 0 - m 0 1) / 2)

lemma oneQubit_entry (i : Fin 7) (m : ZMod 2 → ZMod 2 → ℂ) (x y : Vec) :
    (if (∀ k, k ≠ i → x k = y k) then m (x i) (y i) else 0)
      = ∑ s : ZMod 2, ∑ t : ZMod 2, ccOf m s t * pauli (unit i s) (unit i t) x y := by
  have hp : ∀ s t : ZMod 2, pauli (unit i s) (unit i t) x y
      = if x = y + unit i s then chi (t * y i) else 0 := by
    intro s t
    unfold pauli
    rw [dotp_unit]
  by_cases hagree : ∀ k, k ≠ i → x k = y k
  · rw [if_pos hagree]
    have hcond : ∀ s : ZMod 2, (x = y + unit i s) ↔ (s = x i + y i) := by
      intro s
      rw [eq_add_unit_iff]
      constructor
      · rintro ⟨-, h2⟩
        rw [h2]
        generalize y i = q
        generalize s = r
        revert q r
        decide
      · rintro rfl
        refine ⟨hagree, ?_⟩
        generalize x i = p
        generalize y i = q
        revert p q
        decide
    simp only [hp, hcond]
    rw [sum_zmod2 (fun s => ∑ t : ZMod 2, ccOf m s t * (if s = x i + y i then chi (t * y i) else 0))]
    simp only [sum_zmod2]
    rcases zmod2_cases (x i) with hx | hx <;> rcases zmod2_cases (y i) with hy | hy <;>
      rw [hx, hy] <;> simp +decide [ccOf, chi] <;> try ring
  · rw [if_neg hagree]
    have : ∀ s t : ZMod 2, pauli (unit i s) (unit i t) x y = 0 := by
      intro s t
      rw [hp]
      rw [if_neg]
      intro h
      exact hagree ((eq_add_unit_iff i s x y).mp h).1
    simp [this]

lemma oneQubitOp_mulVec {i : Fin 7} {M : Matrix Vec Vec ℂ} (h : OneQubitOp i M) :
    ∃ cc : ZMod 2 → ZMod 2 → ℂ, ∀ f : Vec → ℂ,
      M.mulVec f = ∑ s : ZMod 2, ∑ t : ZMod 2, cc s t • (pauli (unit i s) (unit i t)).mulVec f := by
  obtain ⟨m, hm⟩ := h
  refine ⟨ccOf m, fun f => ?_⟩
  funext x
  have hentry : ∀ y : Vec, M x y
      = ∑ s : ZMod 2, ∑ t : ZMod 2, ccOf m s t * pauli (unit i s) (unit i t) x y := by
    intro y
    rw [hm x y]
    exact oneQubit_entry i m x y
  have hRHS : (∑ s : ZMod 2, ∑ t : ZMod 2, ccOf m s t • (pauli (unit i s) (unit i t)).mulVec f) x
      = ∑ s : ZMod 2, ∑ t : ZMod 2, ccOf m s t * ((pauli (unit i s) (unit i t)).mulVec f x) := by
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hRHS]
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ y : Vec, M x y * f y
      = ∑ y : Vec, (∑ s : ZMod 2, ∑ t : ZMod 2,
          ccOf m s t * pauli (unit i s) (unit i t) x y) * f y :=
        Finset.sum_congr rfl (fun y _ => by rw [hentry y])
    _ = ∑ y : Vec, ∑ s : ZMod 2, ∑ t : ZMod 2,
          ccOf m s t * pauli (unit i s) (unit i t) x y * f y := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun s _ => by rw [Finset.sum_mul])
    _ = ∑ s : ZMod 2, ∑ t : ZMod 2, ∑ y : Vec,
          ccOf m s t * pauli (unit i s) (unit i t) x y * f y := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun s _ => by rw [Finset.sum_comm])
    _ = ∑ s : ZMod 2, ∑ t : ZMod 2, ccOf m s t
          * ∑ y : Vec, pauli (unit i s) (unit i t) x y * f y := by
        refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun y _ => by ring)

/-! ## Main theorem -/

/-- Single-qubit Pauli operators are indeed single-qubit operators. -/
lemma pauli_unit_oneQubitOp (i : Fin 7) (s t : ZMod 2) :
    OneQubitOp i (pauli (unit i s) (unit i t)) := by
  refine ⟨fun p q => if p = q + s then chi (t * q) else 0, fun x y => ?_⟩
  unfold pauli
  rw [dotp_unit]
  by_cases hagree : ∀ k, k ≠ i → x k = y k
  · rw [if_pos hagree]
    show (if x = y + unit i s then chi (t * y i) else 0)
      = (if x i = y i + s then chi (t * y i) else 0)
    by_cases hi : x i = y i + s
    · rw [if_pos hi, if_pos ((eq_add_unit_iff i s x y).mpr ⟨hagree, hi⟩)]
    · rw [if_neg hi, if_neg (fun h => hi ((eq_add_unit_iff i s x y).mp h).2)]
  · rw [if_neg hagree, if_neg (fun h => hagree ((eq_add_unit_iff i s x y).mp h).1)]

/--
**The 7-qubit Steane code corrects an arbitrary single-qubit error.**

The `7`-qubit state space is `Vec → ℂ` with `Vec = Fin 7 → ZMod 2` the computational
basis labels, equipped with the hermitian inner product `ip`.  The code space is the
span of the two logical states `psi 0` and `psi allOnes`, i.e. the CSS code built from
the `[7,4,3]` Hamming code and its dual.

The first conjunct says that the two logical states are orthogonal and of equal
(nonzero) norm, so the code space is genuinely two-dimensional: it encodes one qubit.

The second conjunct is the Knill-Laflamme error-correction condition: for any two
operators `E`, `F` acting nontrivially on at most one qubit each (qubit `i` and qubit
`j` respectively), there is a *single* scalar `c`, independent of the code states, with
`⟪E f, F g⟫ = c ⟪f, g⟫` for all code vectors `f`, `g`.  By the Knill-Laflamme theorem
this is exactly the statement that the error set consisting of all single-qubit
operators is correctable, i.e. the Steane code corrects any single-qubit error.
-/
theorem steane_code :
    (ip (psi 0) (psi 0) = 8 ∧ ip (psi allOnes) (psi allOnes) = 8 ∧
      ip (psi 0) (psi allOnes) = 0) ∧
    ∀ (i j : Fin 7) (E F : Matrix Vec Vec ℂ), OneQubitOp i E → OneQubitOp j F →
      ∃ c : ℂ, ∀ f g : Vec → ℂ, codeVec f → codeVec g →
        ip (E.mulVec f) (F.mulVec g) = c * ip f g := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [ip_psi 0 0 (Or.inl rfl) (Or.inl rfl), if_pos rfl]
  · rw [ip_psi allOnes allOnes (Or.inr rfl) (Or.inr rfl), if_pos rfl]
  · rw [ip_psi 0 allOnes (Or.inl rfl) (Or.inr rfl), if_neg zero_ne_allOnes]
  · intro i j E F hE hF
    obtain ⟨cc, hEc⟩ := oneQubitOp_mulVec hE
    obtain ⟨dd, hFd⟩ := oneQubitOp_mulVec hF
    refine ⟨∑ s : ZMod 2, ∑ t : ZMod 2, ∑ s' : ZMod 2, ∑ t' : ZMod 2,
      (starRingEnd ℂ) (cc s' t') * dd s t *
        (if unit i s' = unit j s ∧ unit i t' = unit j t then 1 else 0), ?_⟩
    intro f g hf hg
    rw [hEc f, hFd g]
    simp only [ip_sum_left, ip_sum_right, ip_smul_left, ip_smul_right]
    simp only [ip_pauli_code i j _ _ _ _ f g hf hg]
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ =>
      Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun t' _ => by ring

/-! ## Consequences: unitarity and orthogonality of distinct error images -/

lemma chi_mul_self (t : ZMod 2) : chi t * chi t = 1 := by
  fin_cases t <;> norm_num [chi]

/-- Pauli operators are unitary: they preserve the inner product. -/
theorem ip_pauli_unitary (a b : Vec) (f g : Vec → ℂ) :
    ip ((pauli a b).mulVec f) ((pauli a b).mulVec g) = ip f g := by
  unfold ip
  rw [sum_shift (fun x => (starRingEnd ℂ) ((pauli a b).mulVec f x)
    * ((pauli a b).mulVec g x)) a]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [pauli_mulVec, pauli_mulVec, vec_add_cancel, map_mul, chi_conj]
  calc chi (dotp b x) * (starRingEnd ℂ) (f x) * (chi (dotp b x) * g x)
      = (chi (dotp b x) * chi (dotp b x)) * ((starRingEnd ℂ) (f x) * g x) := by ring
    _ = (starRingEnd ℂ) (f x) * g x := by rw [chi_mul_self, one_mul]

/-- Distinct single-qubit Pauli errors send the code space to orthogonal subspaces:
this is what makes syndrome measurement followed by the inverse Pauli a valid recovery. -/
theorem steane_distinct_errors_orthogonal (i j : Fin 7) (s1 t1 s2 t2 : ZMod 2)
    (h : ¬(unit i s1 = unit j s2 ∧ unit i t1 = unit j t2))
    (f g : Vec → ℂ) (hf : codeVec f) (hg : codeVec g) :
    ip ((pauli (unit i s1) (unit i t1)).mulVec f)
       ((pauli (unit j s2) (unit j t2)).mulVec g) = 0 := by
  rw [ip_pauli_code i j s1 t1 s2 t2 f g hf hg, if_neg h, zero_mul]

/-! ## An explicit recovery operation -/

/-- Index set for the correctable errors: the `21` nontrivial single-qubit Paulis
together with a single copy of the identity. -/
def ErrIdx : Finset (Fin 7 × ZMod 2 × ZMod 2) :=
  Finset.univ.filter (fun e => e.2.1 ≠ 0 ∨ e.2.2 ≠ 0 ∨ e.1 = 0)

/-- The Pauli operator attached to an error index. -/
def PauliOf (e : Fin 7 × ZMod 2 × ZMod 2) : Matrix Vec Vec ℂ :=
  pauli (unit e.1 e.2.1) (unit e.1 e.2.2)

/-- There are exactly `22` correctable Pauli errors: the identity and `3 * 7` nontrivial
single-qubit Paulis. -/
lemma ErrIdx_card : ErrIdx.card = 22 := by decide

lemma ErrIdx_inj : ∀ e ∈ ErrIdx, ∀ e' ∈ ErrIdx, e ≠ e' →
    ¬(unit e.1 e.2.1 = unit e'.1 e'.2.1 ∧ unit e.1 e.2.2 = unit e'.1 e'.2.2) := by
  decide

/-- The recovery operation: measure the error syndrome and undo the corresponding Pauli. -/
noncomputable def recover (h : Vec → ℂ) : Vec → ℂ :=
  ∑ e ∈ ErrIdx, (8 : ℂ)⁻¹ •
    ((ip ((PauliOf e).mulVec (psi 0)) h) • psi 0
      + (ip ((PauliOf e).mulVec (psi allOnes)) h) • psi allOnes)

lemma recover_term_self (e : Fin 7 × ZMod 2 × ZMod 2) (f : Vec → ℂ) (hf : codeVec f) :
    (8 : ℂ)⁻¹ • ((ip ((PauliOf e).mulVec (psi 0)) ((PauliOf e).mulVec f)) • psi 0
      + (ip ((PauliOf e).mulVec (psi allOnes)) ((PauliOf e).mulVec f)) • psi allOnes) = f := by
  unfold PauliOf
  rw [ip_pauli_unitary, ip_pauli_unitary]
  obtain ⟨α, β, rfl⟩ := hf
  rw [ip_add_right, ip_add_right, ip_smul_right, ip_smul_right, ip_smul_right, ip_smul_right,
    ip_psi 0 0 (Or.inl rfl) (Or.inl rfl), ip_psi 0 allOnes (Or.inl rfl) (Or.inr rfl),
    ip_psi allOnes 0 (Or.inr rfl) (Or.inl rfl),
    ip_psi allOnes allOnes (Or.inr rfl) (Or.inr rfl),
    if_pos rfl, if_pos rfl, if_neg zero_ne_allOnes, if_neg (Ne.symm zero_ne_allOnes)]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma recover_term_other (e e' : Fin 7 × ZMod 2 × ZMod 2) (he : e ∈ ErrIdx) (he' : e' ∈ ErrIdx)
    (hne : e' ≠ e) (f : Vec → ℂ) (hf : codeVec f) :
    (8 : ℂ)⁻¹ • ((ip ((PauliOf e').mulVec (psi 0)) ((PauliOf e).mulVec f)) • psi 0
      + (ip ((PauliOf e').mulVec (psi allOnes)) ((PauliOf e).mulVec f)) • psi allOnes) = 0 := by
  have hne' := ErrIdx_inj e' he' e he hne
  unfold PauliOf
  rw [steane_distinct_errors_orthogonal e'.1 e.1 e'.2.1 e'.2.2 e.2.1 e.2.2 hne' _ f
        ⟨1, 0, by funext x; simp [psi]⟩ hf,
      steane_distinct_errors_orthogonal e'.1 e.1 e'.2.1 e'.2.2 e.2.1 e.2.2 hne' _ f
        ⟨0, 1, by funext x; simp [psi]⟩ hf]
  simp

/-- **Explicit recovery.**  For every single-qubit Pauli error `PauliOf e` and every state
`f` of the code space, applying the recovery operation to the corrupted state returns `f`. -/
theorem steane_recovery (e : Fin 7 × ZMod 2 × ZMod 2) (he : e ∈ ErrIdx)
    (f : Vec → ℂ) (hf : codeVec f) : recover ((PauliOf e).mulVec f) = f := by
  unfold recover
  rw [Finset.sum_eq_single e]
  · exact recover_term_self e f hf
  · intro e' he' hne
    exact recover_term_other e e' he he' hne f hf
  · intro h; exact absurd he h

end QI

