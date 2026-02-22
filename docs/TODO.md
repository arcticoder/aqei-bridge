# TODO: aqei-bridge — Lean 4 Formal Verification Track

**Status Update (2026-02-22):** Repository split complete. Numerical validation pipeline moved to [`aqei-numerical-validation`](https://github.com/arcticoder/aqei-numerical-validation). This repo is now focused exclusively on the Lean 4 formalization and the formal verification manuscript.

**Active objective:** Prove the bridge conjecture — causal futures J⁺(p) are topologically stable (H₁ invariant) under AQEI-admissible perturbations.

---

## CRITICAL: Manuscript Citations (Lean Formalization Paper)

Add bibliography entries to `papers/aqei-lean-formalization.tex` for the three real-world applications documented in §7:

```latex
\bibitem{abbott2016ligo}
B.~P. Abbott et al. (LIGO/Virgo), \textit{Observation of Gravitational Waves from a Binary Black Hole Merger}, Phys. Rev. Lett. \textbf{116}, 061102 (2016).

\bibitem{alcubierre2008numerical}
M.~Alcubierre, \textit{Introduction to 3+1 Numerical Relativity}, Oxford University Press (2008).

\bibitem{gisin2002quantum}
N.~Gisin et al., \textit{Quantum cryptography}, Rev. Mod. Phys. \textbf{74}, 145 (2002).

\bibitem{ashby2003relativity}
N.~Ashby, \textit{Relativity in the Global Positioning System}, Living Rev. Relativ. \textbf{6}, 1 (2003).

\bibitem{fewster2012lectures}
C.~J. Fewster, \textit{Lectures on quantum energy inequalities}, arXiv:1208.5399 (2012).

\bibitem{penrose1965gravitational}
R.~Penrose, \textit{Gravitational Collapse and Space-Time Singularities}, Phys. Rev. Lett. \textbf{14}, 57 (1965).
```

Also update `\cite{}` commands in §7.1–§7.3.

---

## HIGH: Prove `homology_functorial` in PosetHomologyProxy.lean

**File:** `lean/src/AqeiBridge/PosetHomologyProxy.lean`

**Current state:** `sorry` — structure in place, need to prove `(g ∘ f)* = g* ∘ f*`

**Proof strategy:**
- Show chain maps compose: `chainMap (g ∘ f) = chainMap g ∘ chainMap f`
- Lift to homology via the H₁ functor definition
- Use `DiscreteHomologyProxy.lean` `boundary_boundary_zero` as the key lemma

**Why this unblocks:** `homology_functorial` unlocks `h1_preserves_zero` (the bridge conjecture in small-epsilon regime).

---

## HIGH: Prove `h1_stable_small_pert` (Core Bridge Theorem)

**File:** `lean/src/AqeiBridge/PosetHomologyProxy.lean` or new `H1Stability.lean`

**Statement:**
```lean
lemma h1_stable_small_pert (P : DiscreteCausalPoset) (ε : ℝ) (hε : ε ≤ 0.1)
    (h0 : dimH1 P = 0) : ∀ P' ∈ pertBall P ε, dimH1 P' = 0
```

**Proof strategy:**
- Use empirical evidence: 100% invariance observed for ε ≤ 0.3 in `aqei-numerical-validation`
- Key lemma: if |E'| - |V'| + c(P') = |E| - |V| + c(P) when |edge_delta| < ε·|E|
- Sub-lemma: small edge perturbation doesn't change connected component count

**Empirical support:** See `aqei-numerical-validation/runs/h1_stability_sweep/` — 100% invariance over 100 trials, ε ∈ [0.05, 0.3].

---

## MEDIUM: Prove `admissible_region_pathConnected`

**File:** `lean/src/AqeiBridge/CausalStability.lean`

**Current state:** `axiom` — stated but not proven

**Statement:**
```lean
axiom admissible_region_pathConnected (F : List (AQEIFunctional n)) :
  IsPathConnected {T : StressEnergy n | T ∈ AQEI_cone F ∧ Small (n := n) T}
```

**Proof strategy:**
- AQEI_cone is convex (already proven: `AQEI_cone_convex`)
- Any convex set intersected with an open ball is path-connected if non-empty
- Use `Convex.pathConnected` from Mathlib: `Convex.isPathConnected`
- Need: non-emptiness (find one T in the cone); then `convex_iff_isPathConnected`

**Key Mathlib lemma:** `Convex.isPathConnected` (check if exists; may need `IsConnected` first).

---

## MEDIUM: Prove `aqei_bridge_conjecture_discrete`

**File:** `lean/src/AqeiBridge/CausalStability.lean`

**Current state:** `axiom` — the core conjecture

**Prerequisites:** Must complete `homology_functorial` + `h1_stable_small_pert` first.

**Proof strategy:**
1. Given: T ∈ AQEI_cone F, Small T, dimH1(P_g) = 0
2. Show: dimH1(P_{g+δg(T)}) = 0
3. Key argument: The perturbation δg(T) is bounded by ‖T‖ · (linearized GR operator)
4. Use `h1_stable_small_pert` with ε = C·‖T‖ ≤ 0.1

---

## LOW: Add `energy-tensor-cone` Theorems as Foundation

The PRD submission in `energy-tensor-cone` proves that the AQEI cone has:
1. Non-trivial extreme rays (`Candidate_Is_Extreme_Point`)
2. Exact rational coordinates for the vertex

**Action:** Add a Lean `import` or a comment in `AQEI_Cone.lean` referencing these results, noting that the geometric foundation is established in the companion work.

---

## LOW: Complete GlobalConjectures.lean

**File:** `lean/src/AqeiBridge/GlobalConjectures.lean`

**Current state:** Placeholder statements

**Refinements needed:**
- State `global_h1_invariance` more precisely: for all T in AQEI_cone, all base posets P
- Add `chronology_topological_invariant` (chronology as poset topological invariant)
- These are the long-term goals; leave as axioms for now but sharpen types

---

## Mathematical Reference

### Bridge Conjecture (Formal Target)

For a discrete causal poset $P$ with causal adjacency relation $\leq_G$:

$$\dim H_1(P) = 0 \implies \dim H_1(P_\epsilon) = 0 \quad \text{for all } \epsilon \text{-perturbations in AQEI cone}$$

where $\dim H_1(P) = |E| - |V| + c(G)$ (Z₁ dimension proxy).

### Key Mathlib tactics available

- `have h := AQEI_cone_convex F` — convexity of the cone (proven)
- `have h := boundary_boundary_zero` — chain complex axiom (proven)
- `exact Convex.isPathConnected` — if convex set non-empty, it's path-connected
- `nlinarith`, `linarith`, `ring` — for arithmetic steps
- `simp [AQEI_cone, AQEIFunctional]` — unfold definitions
