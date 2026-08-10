#!/usr/bin/env python3
"""gen_frontier2.py — frontier WAVE 2: deeper quantum, physics, CS, and math targets
(mostly no Mathlib equivalent). Same tiering as frontier_queue. Emits frontier2.json;
novelty_gate vets it, night_submit sends it. Statements kept crisp + formalizable."""
import json
import pathlib

OUT = pathlib.Path(__file__).resolve().parent / "frontier2.json"


def t(name, cluster, tier, statement):
    rank = {"SPECIAL": 2, "STATEMENT": 2, "MOONSHOT": 6}[tier]
    return {"target": name, "tier": f"FRONTIER-{cluster}", "rank": rank,
            "difficulty": tier, "goal": "Prove in Lean 4 (Mathlib), axiom-clean.",
            "statement": statement}


F = [
# ===== Quantum computing & information =====
t("QI.no_deleting", "qi", "SPECIAL", "There is no unitary that deletes an unknown quantum state (no-deleting theorem)."),
t("QI.holevo_bound", "qi", "SPECIAL", "Accessible information about a quantum ensemble is at most its Holevo χ quantity."),
t("QI.schmidt_decomposition", "qi", "SPECIAL", "Every bipartite pure state has a Schmidt decomposition with unique Schmidt coefficients."),
t("QI.strong_subadditivity", "qi", "MOONSHOT", "Von Neumann entropy is strongly subadditive: S(ABC)+S(B) ≤ S(AB)+S(BC) (Lieb–Ruskai)."),
t("QI.data_processing", "qi", "SPECIAL", "Quantum relative entropy is monotone under CPTP maps (data-processing inequality)."),
t("QI.monogamy_ckw", "qi", "MOONSHOT", "Entanglement is monogamous: the CKW inequality for three qubits."),
t("QI.choi_jamiolkowski", "qi", "SPECIAL", "CP maps correspond to positive Choi matrices (Choi–Jamiołkowski isomorphism)."),
t("QI.stinespring", "qi", "MOONSHOT", "Every CPTP map dilates to a unitary on a larger space (Stinespring)."),
t("QI.uhlmann_fidelity", "qi", "SPECIAL", "Fidelity equals the maximal overlap over purifications (Uhlmann's theorem)."),
t("QI.purification_exists", "qi", "SPECIAL", "Every mixed state has a purification, unique up to isometry on the ancilla."),
t("QI.grover_optimal", "qi", "MOONSHOT", "Unstructured search needs Ω(√N) queries; Grover is optimal (BBBV bound)."),
t("QI.shor_period", "qi", "MOONSHOT", "Shor's algorithm recovers the period of a modular-exponentiation function w.h.p."),
t("QI.simon_algorithm", "qi", "SPECIAL", "Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically."),
t("QI.deutsch_jozsa", "qi", "SPECIAL", "Deutsch–Jozsa decides constant-vs-balanced with one query."),
t("QI.pbr_theorem", "qi", "MOONSHOT", "The quantum state is ontic under preparation independence (Pusey–Barrett–Rudolph)."),
t("QI.hardy_paradox", "qi", "SPECIAL", "Hardy's nonlocality argument: a fraction of runs violate local realism without inequalities."),
t("QI.knill_laflamme", "qi", "SPECIAL", "A code corrects an error set iff it satisfies the Knill–Laflamme conditions."),
t("QI.shor_code_corrects", "qi", "SPECIAL", "The 9-qubit Shor code corrects an arbitrary single-qubit error."),
t("QI.steane_code", "qi", "SPECIAL", "The 7-qubit Steane (CSS) code corrects any single-qubit error."),
t("QI.quantum_singleton", "qi", "SPECIAL", "Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1)."),
t("QI.threshold_theorem", "qi", "MOONSHOT", "Below a constant error threshold, fault-tolerant quantum computation is possible (statement)."),
t("QI.gottesman_knill", "qi", "MOONSHOT", "Stabilizer circuits are efficiently classically simulable (Gottesman–Knill)."),

# ===== Physics / mathematical physics =====
t("Phys.adiabatic_theorem", "phys", "MOONSHOT", "A slowly varying Hamiltonian keeps a nondegenerate eigenstate in its instantaneous eigenspace."),
t("Phys.hellmann_feynman", "phys", "SPECIAL", "dE_n/dλ = ⟨ψ_n|∂H/∂λ|ψ_n⟩ (Hellmann–Feynman)."),
t("Phys.virial_theorem", "phys", "SPECIAL", "For a bound stationary state, 2⟨T⟩ = ⟨r·∇V⟩ (quantum virial theorem)."),
t("Phys.kramers_degeneracy", "phys", "SPECIAL", "A time-reversal-invariant half-integer-spin system has doubly degenerate levels (Kramers)."),
t("Phys.bloch_theorem", "phys", "SPECIAL", "Eigenstates of a periodic Hamiltonian are Bloch waves e^{ikx}u_k(x)."),
t("Phys.mermin_wagner", "phys", "MOONSHOT", "No spontaneous breaking of a continuous symmetry in dimensions ≤ 2 at T>0 (Mermin–Wagner)."),
t("Phys.goldstone", "phys", "MOONSHOT", "Spontaneous breaking of a continuous global symmetry yields a massless mode (Goldstone)."),
t("Phys.cpt_theorem", "phys", "MOONSHOT", "Any Lorentz-invariant local QFT is CPT-invariant (statement)."),
t("Phys.area_law_1d", "phys", "MOONSHOT", "Gapped 1D ground states obey an entanglement-entropy area law (Hastings)."),
t("Phys.lieb_schultz_mattis", "phys", "MOONSHOT", "A half-integer-spin translation-invariant chain is gapless or degenerate (LSM)."),
t("Phys.jarzynski_equality", "phys", "SPECIAL", "⟨e^{−βW}⟩ = e^{−βΔF} for nonequilibrium work (Jarzynski)."),
t("Phys.crooks_theorem", "phys", "SPECIAL", "Crooks fluctuation theorem: P_F(W)/P_R(−W) = e^{β(W−ΔF)}."),
t("Phys.landauer_principle", "phys", "SPECIAL", "Erasing one bit dissipates at least kT ln 2 of heat (Landauer)."),
t("Phys.fluctuation_dissipation", "phys", "SPECIAL", "The FDT relates linear response to equilibrium correlations."),
t("Phys.bekenstein_bound", "phys", "STATEMENT", "State the Bekenstein bound S ≤ 2πkRE/ℏc."),
t("Phys.hawking_temperature", "phys", "STATEMENT", "State the Hawking temperature T = ℏc³/(8πGMk) of a Schwarzschild black hole."),
t("Phys.unruh_effect", "phys", "STATEMENT", "State the Unruh temperature T = ℏa/(2πck) seen by a uniformly accelerated observer."),
t("Phys.bkt_transition", "phys", "MOONSHOT", "State the Berezinskii–Kosterlitz–Thouless topological phase transition of the 2D XY model."),
t("Phys.wigner_eckart", "phys", "SPECIAL", "Matrix elements of tensor operators factor into a Clebsch–Gordan × reduced element (Wigner–Eckart)."),
t("Phys.kochen_specker_18", "phys", "SPECIAL", "An explicit 18-vector Kochen–Specker set in ℝ⁴ has no {0,1} coloring."),

# ===== Computer science / complexity =====
t("CS.time_hierarchy", "cs", "SPECIAL", "The time hierarchy theorem: more time gives strictly more languages (diagonalization)."),
t("CS.savitch", "cs", "SPECIAL", "NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch)."),
t("CS.immerman_szelepcsenyi", "cs", "MOONSHOT", "NL = coNL (nondeterministic space is closed under complement)."),
t("CS.ladner", "cs", "MOONSHOT", "If P ≠ NP then NP-intermediate problems exist (Ladner)."),
t("CS.baker_gill_solovay", "cs", "SPECIAL", "There are oracles A,B with P^A=NP^A and P^B≠NP^B (relativization barrier)."),
t("CS.pcp_theorem", "cs", "MOONSHOT", "NP = PCP(log n, 1): the PCP theorem (statement)."),
t("CS.toda_theorem", "cs", "MOONSHOT", "PH ⊆ P^{#P} (Toda's theorem)."),
t("CS.parity_not_ac0", "cs", "MOONSHOT", "PARITY ∉ AC⁰ (Håstad switching lemma)."),
t("CS.barrington", "cs", "MOONSHOT", "NC¹ equals width-5 permutation branching programs (Barrington)."),
t("CS.valiant_permanent", "cs", "MOONSHOT", "The 0/1 permanent is #P-complete (Valiant)."),
t("CS.impagliazzo_wigderson", "cs", "MOONSHOT", "Strong circuit lower bounds imply P = BPP (Impagliazzo–Wigderson)."),
t("CS.nisan_wigderson_prg", "cs", "MOONSHOT", "The Nisan–Wigderson generator derandomizes from a hard function."),
t("CS.reingold_sl_l", "cs", "MOONSHOT", "Undirected s-t connectivity is in L (SL = L; Reingold)."),
t("CS.aks_primes_in_p", "cs", "MOONSHOT", "PRIMES ∈ P (Agrawal–Kayal–Saxena)."),
t("CS.recursion_theorem", "cs", "SPECIAL", "Kleene's recursion theorem: every computable transformation of programs has a fixed point."),
t("CS.rice_extended", "cs", "SPECIAL", "The set of indices of a nontrivial semantic property is not recursive (Rice)."),
t("CS.blum_speedup", "cs", "MOONSHOT", "There exist problems with no fastest algorithm (Blum speedup)."),
t("CS.disjointness_lb", "cs", "SPECIAL", "Set-disjointness has Ω(n) randomized communication complexity."),
t("CS.yao_principle", "cs", "SPECIAL", "Yao's minimax principle relates randomized and distributional complexity."),
t("CS.razborov_smolensky", "cs", "MOONSHOT", "MOD_p ∉ AC⁰[q] for distinct primes p,q (Razborov–Smolensky)."),
t("CS.hilbert10_undecidable", "cs", "MOONSHOT", "Hilbert's tenth problem is undecidable: Diophantine solvability (MRDP)."),
t("CS.pcp_dinur", "cs", "MOONSHOT", "Dinur's gap-amplification proof of the PCP theorem (statement)."),

# ===== Math frontier (number theory / analysis / geometry / combinatorics) =====
t("Math2.modularity", "math", "MOONSHOT", "Every elliptic curve over ℚ is modular (Taniyama–Shimura–Wiles; statement)."),
t("Math2.sato_tate", "math", "MOONSHOT", "State the Sato–Tate distribution of Frobenius angles for a non-CM elliptic curve."),
t("Math2.chebotarev", "math", "MOONSHOT", "Chebotarev density theorem for Frobenius conjugacy classes."),
t("Math2.class_number_formula", "math", "MOONSHOT", "The analytic class number formula for a number field's Dedekind zeta residue."),
t("Math2.carleson", "math", "MOONSHOT", "Fourier series of an L² function converge almost everywhere (Carleson)."),
t("Math2.nash_embedding", "math", "MOONSHOT", "Every Riemannian manifold embeds isometrically in some ℝ^N (Nash)."),
t("Math2.robertson_seymour", "math", "MOONSHOT", "Graphs are well-quasi-ordered by the minor relation (Robertson–Seymour)."),
t("Math2.van_der_waerden", "math", "SPECIAL", "Any finite coloring of ℕ has arbitrarily long monochromatic APs (van der Waerden)."),
t("Math2.hales_jewett", "math", "MOONSHOT", "The Hales–Jewett theorem on combinatorial lines."),
t("Math2.erdos_ko_rado", "math", "SPECIAL", "A k-uniform intersecting family on [n] (n≥2k) has size ≤ C(n−1,k−1) (Erdős–Ko–Rado)."),
t("Math2.cap_set", "math", "MOONSHOT", "The cap-set bound: subsets of 𝔽₃ⁿ with no 3-term AP have size o(3ⁿ) (Croot–Lev–Pach / Ellenberg–Gijswijt)."),
t("Math2.kahn_kalai", "math", "MOONSHOT", "Expectation and threshold are within a log factor (Park–Pham proof of Kahn–Kalai)."),
t("Math2.sunflower_bound", "math", "MOONSHOT", "The improved sunflower lemma bound (Alweiss–Lovett–Wu–Zhang)."),
t("Math2.kruskal_katona", "math", "SPECIAL", "The Kruskal–Katona theorem on shadows of set systems."),
t("Math2.chern_gauss_bonnet", "math", "MOONSHOT", "The Chern–Gauss–Bonnet theorem for even-dimensional closed manifolds."),
t("Math2.hironaka_resolution", "math", "MOONSHOT", "Resolution of singularities in characteristic 0 (Hironaka; statement)."),
t("Math2.riemann_roch_curve", "math", "MOONSHOT", "Riemann–Roch for a smooth projective curve: ℓ(D)−ℓ(K−D)=deg D+1−g."),
t("Math2.belyi_theorem", "math", "MOONSHOT", "A curve is defined over ℚ̄ iff it has a Belyi map to ℙ¹ ramified over {0,1,∞}."),
t("Math2.ratner", "math", "MOONSHOT", "Ratner's orbit-closure/measure-classification theorems for unipotent flows (statement)."),
t("Math2.donsker_invariance", "math", "MOONSHOT", "Donsker's invariance principle: rescaled random walk converges to Brownian motion."),
t("Math2.gromov_nonsqueezing", "math", "MOONSHOT", "Gromov's nonsqueezing theorem in symplectic geometry."),
t("Math2.kervaire_invariant", "math", "MOONSHOT", "The Kervaire invariant is nonzero only in dimensions 2,6,14,30,62,126 (Hill–Hopkins–Ravenel; statement)."),
]


def main():
    seen, out = set(), []
    for it in F:
        if it["target"] in seen:
            continue
        seen.add(it["target"]); out.append(it)
    OUT.write_text(json.dumps({"count": len(out), "queue": out}, indent=1))
    import collections
    print(f"wrote {OUT} with {len(out)} wave-2 frontier targets")
    print("cluster:", dict(collections.Counter(x["tier"].split("-")[1] for x in out)))
    print("difficulty:", dict(collections.Counter(x["difficulty"] for x in out)))


if __name__ == "__main__":
    main()
