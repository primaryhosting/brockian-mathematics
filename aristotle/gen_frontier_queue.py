#!/usr/bin/env python3
"""gen_frontier_queue.py — 100 FRONTIER targets with (as far as known) NO Mathlib /
physics-Lean equivalent: set theory & infinity, primes & NT frontier, Millennium
moonshots, Fields-Medal & Abel results (last ~60y), physics-Nobel / math-physics,
and formal phenomenology / logic-of-mind.

Tiers (be honest about what "solve" means here):
  STATEMENT  formalize the precise statement (+ defs) in Lean 4 — always valuable, tractable
  SPECIAL    prove a concrete special/finite/base case — often tractable
  MOONSHOT   the full theorem — research-level; realistic win is a partial or a reduction

Emits frontier_queue.json. A separate novelty_gate.py checks each against local Mathlib.
"""
import json
import pathlib

OUT = pathlib.Path(__file__).resolve().parent / "frontier_queue.json"


def t(name, cluster, tier, statement):
    goal = {"STATEMENT": "Formalize the precise statement (with all definitions) in Lean 4.",
            "SPECIAL": "Prove the stated special/base case in Lean 4, axiom-clean.",
            "MOONSHOT": "Formalize the statement; prove the base case or a Lean-checked reduction."}[tier]
    # tractable-first: SPECIAL/STATEMENT jump ahead of the corpus tail; MOONSHOT trails
    rank = {"SPECIAL": 2, "STATEMENT": 2, "MOONSHOT": 6}[tier]
    return {"target": name, "tier": f"FRONTIER-{cluster}", "rank": rank,
            "difficulty": tier, "goal": goal, "statement": statement}


F = [
# ---- Set theory, logic & infinity ----
t("Frontier.Goodstein_terminates", "set", "MOONSHOT", "Every Goodstein sequence reaches 0 (uses ε₀ well-foundedness; independent of PA)."),
t("Frontier.Hydra_Kirby_Paris", "set", "MOONSHOT", "Every hydra game terminates for any strategy (Kirby–Paris; PA-independent)."),
t("Frontier.Borel_determinacy", "set", "MOONSHOT", "Every Borel game is determined (Martin's theorem)."),
t("Frontier.Gale_Stewart_open", "set", "SPECIAL", "Every open game is determined (Gale–Stewart)."),
t("Frontier.Banach_Tarski", "set", "MOONSHOT", "The unit ball in ℝ³ admits a paradoxical decomposition (Banach–Tarski)."),
t("Frontier.Paris_Harrington", "set", "MOONSHOT", "The strengthened finite Ramsey theorem is true but unprovable in PA."),
t("Frontier.Goedel_second_incompleteness", "set", "MOONSHOT", "No consistent recursively-axiomatized theory extending PA proves its own consistency."),
t("Frontier.Tarski_undefinability", "set", "STATEMENT", "Arithmetical truth is not arithmetically definable (Tarski)."),
t("Frontier.Aronszajn_tree_exists", "set", "SPECIAL", "There exists an Aronszajn tree (a tree of height ω₁ with no uncountable branch/level)."),
t("Frontier.CH_independent_statement", "set", "MOONSHOT", "The Continuum Hypothesis is independent of ZFC (Gödel + Cohen forcing)."),
t("Frontier.inaccessible_implies_ConZFC", "set", "MOONSHOT", "An inaccessible cardinal yields a model of ZFC, so Con(ZFC+inaccessible)→Con(ZFC)."),
t("Frontier.infinite_ramsey", "set", "SPECIAL", "Every 2-colouring of [ℕ]² has an infinite monochromatic set (infinite Ramsey)."),
t("Frontier.Suslin_line", "set", "MOONSHOT", "A Suslin line exists iff ◊-type hypotheses fail; state Suslin's problem precisely."),
t("Frontier.Loeb_theorem", "set", "STATEMENT", "Löb's theorem: if PA ⊢ (□φ → φ) then PA ⊢ φ."),

# ---- Primes & number-theory frontier ----
t("Frontier.Green_Tao", "primes", "MOONSHOT", "The primes contain arbitrarily long arithmetic progressions."),
t("Frontier.bounded_prime_gaps", "primes", "MOONSHOT", "liminf (p_{n+1}−p_n) is finite (Zhang/Maynard)."),
t("Frontier.Chen_theorem", "primes", "MOONSHOT", "Every sufficiently large even number is p + q with q having ≤ 2 prime factors."),
t("Frontier.Vinogradov_three_primes", "primes", "MOONSHOT", "Every sufficiently large odd number is a sum of three primes."),
t("Frontier.Brun_twin_reciprocal", "primes", "SPECIAL", "The sum of reciprocals of twin primes converges (Brun's constant)."),
t("Frontier.Mordell_finite_generation", "primes", "MOONSHOT", "The group of rational points of an elliptic curve over ℚ is finitely generated (Mordell)."),
t("Frontier.Catalan_Mihailescu", "primes", "MOONSHOT", "8 and 9 are the only consecutive perfect powers (x^p − y^q = 1 ⇒ 3²−2³)."),
t("Frontier.abc_statement", "primes", "MOONSHOT", "State the abc conjecture: for ε>0, finitely many coprime a+b=c with c > rad(abc)^{1+ε}."),
t("Frontier.FLT_statement", "primes", "MOONSHOT", "Fermat's Last Theorem: xⁿ+yⁿ=zⁿ has no positive-integer solution for n>2."),
t("Frontier.sum_three_cubes_42", "primes", "SPECIAL", "42 = (−80538738812075974)³ + 80435758145817515³ + 12602123297335631³."),
t("Frontier.erdos_discrepancy", "primes", "MOONSHOT", "Every ±1 sequence has unbounded discrepancy on homogeneous APs (Tao)."),
t("Frontier.artin_primitive_root", "primes", "MOONSHOT", "State Artin's conjecture on primitive roots."),

# ---- Millennium & moonshots ----
t("Frontier.RH_statement", "moonshot", "MOONSHOT", "All nontrivial zeros of ζ(s) have real part 1/2."),
t("Frontier.RH_Li_criterion", "moonshot", "SPECIAL", "RH ⇔ Li's coefficients λ_n ≥ 0 for all n≥1 (state and prove the equivalence)."),
t("Frontier.P_vs_NP_statement", "moonshot", "STATEMENT", "State P ≠ NP via time-bounded Turing machines and polynomial reducibility."),
t("Frontier.cook_levin", "moonshot", "SPECIAL", "SAT is NP-complete (Cook–Levin)."),
t("Frontier.navier_stokes_regularity", "moonshot", "MOONSHOT", "State global smoothness/existence for 3D incompressible Navier–Stokes."),
t("Frontier.yang_mills_mass_gap", "moonshot", "MOONSHOT", "State existence of quantum Yang–Mills on ℝ⁴ with a positive mass gap."),
t("Frontier.hodge_statement", "moonshot", "MOONSHOT", "State the Hodge conjecture on algebraicity of Hodge classes."),
t("Frontier.BSD_statement", "moonshot", "MOONSHOT", "State Birch–Swinnerton-Dyer: ord_{s=1}L(E,s) = rank E(ℚ)."),
t("Frontier.poincare_3sphere", "moonshot", "MOONSHOT", "Every simply-connected closed 3-manifold is homeomorphic to S³ (Perelman)."),
t("Frontier.hadwiger_nelson_5", "moonshot", "SPECIAL", "The chromatic number of the plane is ≥ 5 (de Grey's unit-distance graph)."),

# ---- Fields Medal results (1966–2022) ----
t("Frontier.atiyah_singer_index", "fields", "MOONSHOT", "The analytic index of an elliptic operator equals its topological index."),
t("Frontier.deligne_weil_RH", "fields", "MOONSHOT", "The Riemann hypothesis for varieties over finite fields (Weil conjectures; Deligne)."),
t("Frontier.faltings_mordell", "fields", "MOONSHOT", "A curve of genus ≥ 2 over ℚ has finitely many rational points (Faltings)."),
t("Frontier.thurston_geometrization", "fields", "MOONSHOT", "State the geometrization of closed 3-manifolds into eight geometries."),
t("Frontier.exotic_R4", "fields", "MOONSHOT", "There exists a smooth manifold homeomorphic but not diffeomorphic to ℝ⁴ (Donaldson/Freedman)."),
t("Frontier.jones_polynomial_invariant", "fields", "SPECIAL", "The Jones polynomial is a link invariant (well-defined under Reidemeister moves)."),
t("Frontier.zelmanov_restricted_burnside", "fields", "MOONSHOT", "The restricted Burnside problem has a positive solution (Zelmanov)."),
t("Frontier.ngo_fundamental_lemma", "fields", "MOONSHOT", "State the Langlands–Shelstad fundamental lemma (Ngô)."),
t("Frontier.smirnov_percolation", "fields", "MOONSHOT", "Crossing probabilities of critical triangular-lattice percolation are conformally invariant (Cardy–Smirnov)."),
t("Frontier.bhargava_cube_law", "fields", "SPECIAL", "Bhargava's cube gives a composition law on pairs of binary quadratic forms recovering Gauss composition."),
t("Frontier.hairer_KPZ", "fields", "MOONSHOT", "The KPZ equation is well-posed via regularity structures (Hairer)."),
t("Frontier.mirzakhani_WP_volume", "fields", "MOONSHOT", "Weil–Petersson volumes of moduli of bordered surfaces satisfy Mirzakhani's recursion."),
t("Frontier.avila_ten_martini", "fields", "MOONSHOT", "The almost Mathieu operator has Cantor spectrum for all irrational flux (Ten Martini)."),
t("Frontier.scholze_perfectoid_tilt", "fields", "MOONSHOT", "State the tilting equivalence of perfectoid fields (Scholze)."),
t("Frontier.figalli_OT_regularity", "fields", "MOONSHOT", "Regularity of optimal transport maps under the MTW condition (Figalli)."),
t("Frontier.duminil_ising_sharp", "fields", "MOONSHOT", "Sharpness of the phase transition for the Ising model (Duminil-Copin)."),
t("Frontier.huh_matroid_log_concave", "fields", "SPECIAL", "The coefficients of the characteristic polynomial of a matroid are log-concave (Adiprasito–Huh–Katz)."),
t("Frontier.voevodsky_milnor", "fields", "MOONSHOT", "The Milnor conjecture: mod-2 Galois cohomology ≅ Milnor K-theory / 2 (Voevodsky)."),
t("Frontier.lindenstrauss_QUE", "fields", "MOONSHOT", "Arithmetic quantum unique ergodicity on congruence surfaces (Lindenstrauss)."),
t("Frontier.mcmullen_renormalization", "fields", "MOONSHOT", "State the renormalization/rigidity results for quadratic-like maps (McMullen)."),

# ---- Abel Prize results ----
t("Frontier.feit_thompson_odd_order", "abel", "MOONSHOT", "Every finite group of odd order is solvable (Feit–Thompson; Thompson/Tits Abel)."),
t("Frontier.milnor_exotic_7sphere", "abel", "MOONSHOT", "There exist smooth manifolds homeomorphic but not diffeomorphic to S⁷ (Milnor)."),
t("Frontier.furstenberg_szemeredi", "abel", "MOONSHOT", "Positive-density subsets of ℕ contain arbitrarily long APs, via multiple recurrence (Furstenberg)."),
t("Frontier.margulis_superrigidity", "abel", "MOONSHOT", "State Margulis superrigidity for higher-rank lattices."),
t("Frontier.lovasz_kneser", "abel", "SPECIAL", "The chromatic number of the Kneser graph KG_{n,k} is n − 2k + 2 (Lovász, via Borsuk–Ulam)."),
t("Frontier.uhlenbeck_bubbling", "abel", "MOONSHOT", "Uhlenbeck compactness / removable singularities for Yang–Mills connections."),
t("Frontier.langlands_reciprocity", "abel", "MOONSHOT", "State the Langlands reciprocity conjecture linking Galois and automorphic representations."),
t("Frontier.nirenberg_gagliardo", "abel", "SPECIAL", "The Gagliardo–Nirenberg interpolation inequality."),
t("Frontier.szemeredi_regularity", "abel", "SPECIAL", "State and prove Szemerédi's regularity lemma for graphs."),
t("Frontier.wigderson_expander_mixing", "abel", "SPECIAL", "The expander mixing lemma bounds edge discrepancy by the second eigenvalue."),

# ---- Physics Nobel / mathematical physics ----
t("Frontier.bell_theorem", "physics", "SPECIAL", "No local hidden-variable model reproduces all quantum correlations (Bell); CHSH ≤ 2 classically."),
t("Frontier.kochen_specker", "physics", "SPECIAL", "No noncontextual hidden-variable assignment exists for QM in dimension ≥ 3 (Kochen–Specker)."),
t("Frontier.gleason_theorem", "physics", "MOONSHOT", "Every quantum measure on a Hilbert space of dim ≥ 3 comes from a density operator (Gleason)."),
t("Frontier.no_communication", "physics", "SPECIAL", "Local operations on one half of an entangled pair cannot transmit information."),
t("Frontier.tknn_chern_hall", "physics", "SPECIAL", "The integer-quantum-Hall conductance equals a Chern number times e²/h (TKNN)."),
t("Frontier.ssh_winding_invariant", "physics", "SPECIAL", "The SSH model's topological phase is classified by a ℤ winding number."),
t("Frontier.berry_phase_quantized", "physics", "SPECIAL", "The Berry phase around a closed loop is the integral of the Berry curvature."),
t("Frontier.landau_levels", "physics", "SPECIAL", "A charged particle in a uniform magnetic field has spectrum ℏω_c(n+½)."),
t("Frontier.bcs_gap_binding", "physics", "SPECIAL", "The BCS gap equation has a nonzero solution for any attractive coupling (Cooper pairing)."),
t("Frontier.higgs_mass_toy", "physics", "SPECIAL", "In an abelian Higgs toy model, spontaneous symmetry breaking gives the gauge boson a mass."),
t("Frontier.asymptotic_freedom_sign", "physics", "SPECIAL", "The one-loop SU(N) beta function is negative (asymptotic freedom)."),
t("Frontier.penrose_singularity", "physics", "MOONSHOT", "A spacetime with a trapped surface and the null energy condition is geodesically incomplete (Penrose)."),
t("Frontier.onsager_2d_ising", "physics", "MOONSHOT", "The exact free energy of the 2D square-lattice Ising model (Onsager)."),
t("Frontier.kam_theorem", "physics", "MOONSHOT", "Invariant tori persist under small perturbation of an integrable system (KAM)."),
t("Frontier.lieb_robinson", "physics", "SPECIAL", "Lieb–Robinson bound: an effective light cone for local spin dynamics."),
t("Frontier.noether_conservation", "physics", "SPECIAL", "Each smooth symmetry of an action yields a conserved current (Noether, 1D case)."),
t("Frontier.spin_statistics", "physics", "MOONSHOT", "State the spin–statistics connection for relativistic quantum fields."),
t("Frontier.lieb_thirring_stability", "physics", "MOONSHOT", "The Lieb–Thirring inequality and stability of matter."),

# ---- Formal phenomenology / logic of mind ----
t("Frontier.aumann_agreement", "mind", "SPECIAL", "Agents with common priors and common knowledge of posteriors cannot agree to disagree (Aumann)."),
t("Frontier.good_regulator", "mind", "SPECIAL", "Every good regulator of a system is (contains) a model of that system (Conant–Ashby)."),
t("Frontier.self_nonprediction", "mind", "SPECIAL", "No machine can always correctly predict its own next output before producing it (diagonal self-reference)."),
t("Frontier.iit_phi_partition", "mind", "STATEMENT", "Formalize integrated information Φ as minimized effective-information over bipartitions; prove Φ=0 for a disconnected system."),
t("Frontier.global_workspace_fixpoint", "mind", "STATEMENT", "A monotone broadcast (global-workspace) operator on a finite state lattice reaches a least fixed point (Knaster–Tarski)."),
t("Frontier.loeb_no_self_trust", "mind", "STATEMENT", "A consistent theory cannot prove its own reflection schema for an unprovable sentence (Löb-based)."),

# ---- +10: recent prizes & tractable classics ----
t("Frontier.arrow_impossibility", "mind", "SPECIAL", "No ranked voting rule for ≥3 alternatives satisfies unanimity, IIA, and non-dictatorship (Arrow; Nobel)."),
t("Frontier.nash_equilibrium_exists", "mind", "MOONSHOT", "Every finite game has a mixed-strategy Nash equilibrium (Nash; via Brouwer/Kakutani)."),
t("Frontier.friendship_theorem", "fields", "SPECIAL", "If every two people have exactly one common friend, someone is everyone's friend (Erdős–Ko–Rényi)."),
t("Frontier.five_color_theorem", "fields", "SPECIAL", "Every planar graph is 5-colourable."),
t("Frontier.four_color_statement", "moonshot", "MOONSHOT", "Every planar graph is 4-colourable (Appel–Haken)."),
t("Frontier.huang_sensitivity", "fields", "SPECIAL", "Boolean sensitivity and degree are polynomially related (Huang's sensitivity theorem, 2019)."),
t("Frontier.kadison_singer", "fields", "MOONSHOT", "The Kadison–Singer problem holds (Marcus–Spielman–Srivastava; interlacing families)."),
t("Frontier.ham_sandwich", "physics", "SPECIAL", "Any n finite measures in ℝⁿ can be simultaneously bisected by one hyperplane (Ham–Sandwich)."),
t("Frontier.gaussian_correlation", "fields", "MOONSHOT", "The Gaussian correlation inequality for symmetric convex sets (Royen)."),
t("Frontier.willmore_conjecture", "fields", "MOONSHOT", "The Clifford torus minimizes Willmore energy among genus-1 surfaces (Marques–Neves)."),
]


def main():
    # dedupe defensively
    seen, out = set(), []
    for it in F:
        if it["target"] in seen:
            continue
        seen.add(it["target"]); out.append(it)
    OUT.write_text(json.dumps({"count": len(out), "queue": out}, indent=1))
    import collections
    c = collections.Counter(x["tier"].split("-")[1] for x in out)
    d = collections.Counter(x["difficulty"] for x in out)
    print(f"wrote {OUT} with {len(out)} frontier targets")
    print("by cluster:", dict(c))
    print("by difficulty:", dict(d))


if __name__ == "__main__":
    main()
