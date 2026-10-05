import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Statement: Every hydra game terminates for any strategy (Kirby–Paris).

A hydra is a finite rooted tree.  Hercules repeatedly cuts off a head (a leaf).
If the head is at depth `1` (a child of the root) it simply disappears.  Otherwise
the head is removed from its parent `p` and then an arbitrary finite number `n` of
extra copies of the (already shortened) subtree `p` are attached to the grandparent
of the head.  The Kirby–Paris theorem says that whatever the strategy is — that is,
whichever head is chosen at each turn and however many copies grow back — the hydra
is eventually reduced to the single node `dead = node []`.

The proof below is the usual ordinal assignment: a hydra is mapped to an ordinal
below `ε₀` by `val (node [t₁, …, t_k]) = ω ^ val t₁ ♯ … ♯ ω ^ val t_k`, where `♯`
is the natural (Hessenberg) sum, and each move is shown to strictly decrease this
ordinal.

The key ordinal fact needed — that `ω ^ c` is closed under natural sums — is not in
Mathlib, so it is proved here (`Frontier.nadd_lt_opow_omega0`).
-/

open Ordinal
open scoped NaturalOps

namespace Frontier

/-! ### Natural sums are bounded by powers of `ω` -/

/-- Every `x` below `e * n + c` (with `c ≤ e`) is of the form `e * j + x₀` with `x₀ < e`
and `j ≤ n`. -/
private theorem nat_decomp (e : Ordinal.{0}) (hene : e ≠ 0) (n : ℕ) (x c : Ordinal.{0})
    (hc : c ≤ e) (hx : x < e * (n : Ordinal) + c) :
    ∃ (j : ℕ) (x₀ : Ordinal.{0}), x = e * (j : Ordinal) + x₀ ∧ x₀ < e ∧ j < n + 1 := by
  have hx₀ : x % e < e := Ordinal.mod_lt x hene
  have hxeq : e * (x / e) + x % e = x := Ordinal.div_add_mod x e
  have hklt : x / e < ((n : Ordinal) + 1) := by
    rw [Ordinal.div_lt hene, mul_add, mul_one]
    exact hx.trans_le (add_le_add_right hc _)
  have h1 : ((n + 1 : ℕ) : Ordinal) = (n : Ordinal) + 1 := by push_cast; ring_nf
  obtain ⟨j, hj⟩ := Ordinal.lt_omega0.1 (hklt.trans (h1 ▸ Ordinal.nat_lt_omega0 (n + 1)))
  refine ⟨j, x % e, ?_, hx₀, ?_⟩
  · rw [← hj]; exact hxeq.symm
  · have : (j : Ordinal) < ((n + 1 : ℕ) : Ordinal) := by rw [h1, ← hj]; exact hklt
    exact_mod_cast this

/-- If `e` is closed under natural sums, then natural sums add the "digits" of the
multiples of `e`: `(e * n + a) ♯ (e * m + b) ≤ e * (n + m) + (a ♯ b)`. -/
private theorem nadd_mul_nat_add_le (e : Ordinal.{0}) (he0 : 0 < e)
    (he : ∀ x y : Ordinal.{0}, x < e → y < e → x ♯ y < e) (N : ℕ) :
    ∀ n m : ℕ, n + m = N → ∀ a : Ordinal.{0}, a < e → ∀ b : Ordinal.{0}, b < e →
      (e * (n : Ordinal) + a) ♯ (e * (m : Ordinal) + b) ≤ e * (N : Ordinal) + (a ♯ b) := by
  have hene : e ≠ 0 := ne_of_gt he0
  have hmul_le : ∀ k K : ℕ, k ≤ K → e * (k : Ordinal) ≤ e * (K : Ordinal) := by
    intro k K hk
    exact mul_le_mul_right (by exact_mod_cast hk) e
  have hstep : ∀ k : ℕ, e * ((k : ℕ) : Ordinal) + e = e * ((k + 1 : ℕ) : Ordinal) := by
    intro k
    have h : ((k + 1 : ℕ) : Ordinal) = ((k : ℕ) : Ordinal) + 1 := by push_cast; ring_nf
    rw [h, mul_add, mul_one]
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    intro n m hnm a
    induction a using Ordinal.induction with
    | h a iha =>
      intro ha b
      induction b using Ordinal.induction with
      | h b ihb =>
        intro hb
        rw [Ordinal.nadd_le_iff]
        constructor
        · intro x hx
          obtain ⟨j, x₀, rfl, hx₀, hjn⟩ := nat_decomp e hene n x a ha.le hx
          rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hjn) with rfl | hjn'
          · have hx₀a : x₀ < a := lt_of_add_lt_add_left hx
            calc (e * (j : Ordinal) + x₀) ♯ (e * (m : Ordinal) + b)
                ≤ e * (N : Ordinal) + (x₀ ♯ b) := iha x₀ hx₀a hx₀ b hb
              _ < e * (N : Ordinal) + (a ♯ b) :=
                  add_lt_add_right (Ordinal.nadd_lt_nadd_right hx₀a b) _
          · have hsum : j + m < N := by omega
            calc (e * (j : Ordinal) + x₀) ♯ (e * (m : Ordinal) + b)
                ≤ e * ((j + m : ℕ) : Ordinal) + (x₀ ♯ b) := ihN (j + m) hsum j m rfl x₀ hx₀ b hb
              _ < e * ((j + m : ℕ) : Ordinal) + e := add_lt_add_right (he _ _ hx₀ hb) _
              _ = e * ((j + m + 1 : ℕ) : Ordinal) := hstep (j + m)
              _ ≤ e * (N : Ordinal) := hmul_le _ _ (by omega)
              _ ≤ e * (N : Ordinal) + (a ♯ b) := le_self_add
        · intro y hy
          obtain ⟨j, y₀, rfl, hy₀, hjm⟩ := nat_decomp e hene m y b hb.le hy
          rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hjm) with rfl | hjm'
          · have hy₀b : y₀ < b := lt_of_add_lt_add_left hy
            calc (e * (n : Ordinal) + a) ♯ (e * (j : Ordinal) + y₀)
                ≤ e * (N : Ordinal) + (a ♯ y₀) := ihb y₀ hy₀b hy₀
              _ < e * (N : Ordinal) + (a ♯ b) :=
                  add_lt_add_right (Ordinal.nadd_lt_nadd_left hy₀b a) _
          · have hsum : n + j < N := by omega
            calc (e * (n : Ordinal) + a) ♯ (e * (j : Ordinal) + y₀)
                ≤ e * ((n + j : ℕ) : Ordinal) + (a ♯ y₀) := ihN (n + j) hsum n j rfl a ha y₀ hy₀
              _ < e * ((n + j : ℕ) : Ordinal) + e := add_lt_add_right (he _ _ ha hy₀) _
              _ = e * ((n + j + 1 : ℕ) : Ordinal) := hstep (n + j)
              _ ≤ e * (N : Ordinal) := hmul_le _ _ (by omega)
              _ ≤ e * (N : Ordinal) + (a ♯ b) := le_self_add

/-- Powers of `ω` are closed under the natural (Hessenberg) sum. -/
theorem nadd_lt_opow_omega0 (c : Ordinal.{0}) :
    ∀ a b : Ordinal.{0}, a < ω ^ c → b < ω ^ c → a ♯ b < ω ^ c := by
  induction c using Ordinal.induction with
  | h c ih =>
    rcases Ordinal.zero_or_succ_or_isSuccLimit c with rfl | ⟨c', rfl⟩ | hlim
    · intro a b ha hb
      rw [Ordinal.opow_zero, Ordinal.lt_one_iff_zero] at ha hb
      subst ha; subst hb
      simp
    · intro a b ha hb
      have he0 : (0 : Ordinal) < ω ^ c' := Ordinal.opow_pos _ Ordinal.omega0_pos
      have hene : (ω : Ordinal) ^ c' ≠ 0 := ne_of_gt he0
      have he : ∀ x y : Ordinal.{0}, x < ω ^ c' → y < ω ^ c' → x ♯ y < ω ^ c' :=
        ih c' (Order.lt_succ c')
      rw [Ordinal.opow_succ] at ha hb ⊢
      set e : Ordinal.{0} := ω ^ c' with hedef
      have hdn : a / e < ω := by rw [Ordinal.div_lt hene]; exact ha
      have hdm : b / e < ω := by rw [Ordinal.div_lt hene]; exact hb
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 hdn
      obtain ⟨m, hm⟩ := Ordinal.lt_omega0.1 hdm
      have hA : e * (n : Ordinal) + a % e = a := by rw [← hn]; exact Ordinal.div_add_mod a e
      have hB : e * (m : Ordinal) + b % e = b := by rw [← hm]; exact Ordinal.div_add_mod b e
      have ha₀ : a % e < e := Ordinal.mod_lt a hene
      have hb₀ : b % e < e := Ordinal.mod_lt b hene
      have key := nadd_mul_nat_add_le e he0 he (n + m) n m rfl (a % e) ha₀ (b % e) hb₀
      rw [hA, hB] at key
      have h3 : ((n + m : ℕ) : Ordinal) + 1 < ω := by
        have h4 : ((n + m + 1 : ℕ) : Ordinal) < ω := Ordinal.nat_lt_omega0 _
        push_cast at h4 ⊢
        exact h4
      calc a ♯ b ≤ e * ((n + m : ℕ) : Ordinal) + (a % e ♯ (b % e)) := key
        _ < e * ((n + m : ℕ) : Ordinal) + e := add_lt_add_right (he _ _ ha₀ hb₀) _
        _ = e * (((n + m : ℕ) : Ordinal) + 1) := by rw [mul_add, mul_one]
        _ < e * ω := (mul_lt_mul_iff_right₀ he0).2 h3
    · intro a b ha hb
      obtain ⟨c₁, hc₁, ha₁⟩ := (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hlim).1 ha
      obtain ⟨c₂, hc₂, hb₂⟩ := (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hlim).1 hb
      have hmax : max c₁ c₂ < c := max_lt hc₁ hc₂
      have h1 : a < ω ^ max c₁ c₂ :=
        ha₁.trans_le (Ordinal.opow_le_opow_right Ordinal.omega0_pos (le_max_left _ _))
      have h2 : b < ω ^ max c₁ c₂ :=
        hb₂.trans_le (Ordinal.opow_le_opow_right Ordinal.omega0_pos (le_max_right _ _))
      exact (ih _ hmax a b h1 h2).trans_le
        (Ordinal.opow_le_opow_right Ordinal.omega0_pos hmax.le)

/-! ### Hydras -/

/-- A hydra is a finite rooted tree: a node together with the (ordered) list of the
hydras hanging from it. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- The dead hydra: a single node with no heads left. -/
def dead : Hydra := .node []

/-- One legal move of the Kirby–Paris hydra game.

* `chop` : a head at depth `1` (a leaf child of the root) is cut off and disappears.
* `dup n` : a head at depth `2` is cut off from its parent `p`; the shortened parent
  `p'` replaces `p` and `n` further copies of `p'` are attached to the root.
* `deeper` : a move performed inside one of the subtrees hanging from the root.

Composing `deeper` with `chop`/`dup` produces exactly the moves that cut a head at an
arbitrary depth; `deeper` applied to `chop` also allows a deep head to be removed with
no regrowth, a move which is not available to Hercules, so the termination theorem
proved below is (slightly) stronger than needed. -/
inductive Step : Hydra → Hydra → Prop
  | chop (l₁ l₂ : List Hydra) :
      Step (.node (l₁ ++ .node [] :: l₂)) (.node (l₁ ++ l₂))
  | dup (n : ℕ) (m₁ m₂ l₁ l₂ : List Hydra) :
      Step (.node (l₁ ++ .node (m₁ ++ .node [] :: m₂) :: l₂))
        (.node (l₁ ++ List.replicate (n + 1) (.node (m₁ ++ m₂)) ++ l₂))
  | deeper {t t' : Hydra} (l₁ l₂ : List Hydra) :
      Step t t' → Step (.node (l₁ ++ t :: l₂)) (.node (l₁ ++ t' :: l₂))

mutual

/-- The ordinal `ω ^ val t₁ ♯ ⋯ ♯ ω ^ val t_k` attached to a hydra. -/
noncomputable def val : Hydra → Ordinal.{0}
  | .node l => vals l

/-- The natural sum of `ω ^ val t` over a list of hydras. -/
noncomputable def vals : List Hydra → Ordinal.{0}
  | [] => 0
  | t :: l => (ω ^ val t) ♯ vals l

end

@[simp] theorem val_node (l : List Hydra) : val (.node l) = vals l := by rw [val]

@[simp] theorem vals_nil : vals [] = 0 := by rw [vals]

@[simp] theorem vals_cons (t : Hydra) (l : List Hydra) :
    vals (t :: l) = (ω ^ val t) ♯ vals l := by rw [vals]

theorem vals_append (l₁ l₂ : List Hydra) : vals (l₁ ++ l₂) = vals l₁ ♯ vals l₂ := by
  induction l₁ with
  | nil => simp
  | cons t l ih => simp [ih, Ordinal.nadd_assoc]

/-- Replacing an element of a list of hydras by a smaller one decreases the value. -/
theorem vals_lt_of_val_lt {t t' : Hydra} (l₁ l₂ : List Hydra) (h : val t' < val t) :
    vals (l₁ ++ t' :: l₂) < vals (l₁ ++ t :: l₂) := by
  have hpow : (ω : Ordinal) ^ val t' < ω ^ val t :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 h
  simp only [vals_append, vals_cons]
  exact Ordinal.nadd_lt_nadd_left (Ordinal.nadd_lt_nadd_right hpow _) _

/-- Replacing an element of a list of hydras by a list of hydras of small total value
decreases the value. -/
theorem vals_lt_of_vals_lt {t : Hydra} (l₁ l₂ r : List Hydra) (h : vals r < ω ^ val t) :
    vals (l₁ ++ r ++ l₂) < vals (l₁ ++ t :: l₂) := by
  simp only [vals_append, vals_cons, Ordinal.nadd_assoc]
  exact Ordinal.nadd_lt_nadd_left (Ordinal.nadd_lt_nadd_right h _) _

/-- Cutting a head off a hydra strictly decreases its value. -/
theorem val_chop_lt (m₁ m₂ : List Hydra) :
    val (.node (m₁ ++ m₂)) < val (.node (m₁ ++ .node [] :: m₂)) := by
  simp only [val_node, vals_append, vals_cons, val_node, vals_nil, Ordinal.opow_zero]
  refine Ordinal.nadd_lt_nadd_left ?_ _
  rw [Ordinal.one_nadd]
  exact Order.lt_succ _

/-- A finite number of copies of a hydra of value `< val t` has total value `< ω ^ val t`. -/
theorem vals_replicate_lt {t t' : Hydra} (h : val t' < val t) (k : ℕ) :
    vals (List.replicate k t') < ω ^ val t := by
  induction k with
  | zero => simpa using Ordinal.opow_pos (val t) Ordinal.omega0_pos
  | succ k ih =>
    rw [List.replicate_succ, vals_cons]
    exact nadd_lt_opow_omega0 (val t) _ _
      ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 h) ih

/-- Every legal move strictly decreases the ordinal value of the hydra. -/
theorem val_lt_of_step {h h' : Hydra} (hs : Step h h') : val h' < val h := by
  induction hs with
  | chop l₁ l₂ => exact val_chop_lt l₁ l₂
  | dup n m₁ m₂ l₁ l₂ =>
    simpa using vals_lt_of_vals_lt l₁ l₂ _ (vals_replicate_lt (val_chop_lt m₁ m₂) (n + 1))
  | deeper l₁ l₂ _ ih =>
    simpa using vals_lt_of_val_lt l₁ l₂ ih

/-- The move relation of the hydra game is well-founded: there is no infinite play. -/
theorem step_wellFounded : WellFounded (fun h' h => Step h h') := by
  have : WellFounded (InvImage (· < ·) val) := InvImage.wf val Ordinal.lt_wf
  exact Subrelation.wf (fun {h h'} hs => val_lt_of_step hs) this

end Hydra

/-- **Kirby–Paris hydra theorem.**  Every hydra game terminates, for any strategy:
if `f 0, f 1, f 2, …` is any play in which a legal move is made at each turn at which
the hydra is still alive, then the hydra is dead after finitely many turns. -/
theorem Hydra_Kirby_Paris (f : ℕ → Hydra)
    (hf : ∀ n, f n ≠ Hydra.dead → Hydra.Step (f n) (f (n + 1))) :
    ∃ n, f n = Hydra.dead := by
  by_contra hcon
  push_neg at hcon
  have hdec : ∀ n, Hydra.val (f (n + 1)) < Hydra.val (f n) := fun n =>
    Hydra.val_lt_of_step (hf n (hcon n))
  exact (RelEmbedding.natGT (fun n => Hydra.val (f n)) hdec).not_wellFounded Ordinal.lt_wf

end Frontier

