# Conjecture (bridge statement): causal stability under AQEI-admissible perturbations

## Scope and intent

This document states the conjecture in a way that is:

- precise enough to formalize *interfaces* in Lean now, and
- explicit about which parts are **heuristic** vs **formalizable**.

The goal is a bridge paper submission (SciPost Physics) independent of the
CQG-review manuscript, while citing the unpublished manuscript for any
nontrivial analytic/QFT content.

## Background objects (informal mathematics)

Let $(M,g)$ be a Lorentzian spacetime. Let $T_{ab}$ be a (renormalized) stress–energy
expectation value in some QFT state.

### AQEI admissibility (informal)

AQEI constraints are (schematically) lower bounds on averaged null energy
functionals, e.g.

$$
\int_{\gamma} T_{ab} k^a k^b \, w(\lambda)\, d\lambda \ge -B_{\gamma,w}
$$

for families of null/timelike curves $\gamma$ and sampling weights $w$.

**Formalizable now (toy):** represent these as finitely many linear inequalities
$L_i(T) \ge -B_i$ on a finite coefficient vector.

**Not formalized yet:** deriving the correct $L_i, B_i$ from QFT on curved
spacetimes.

### Metric perturbation sourced by $T$

In a weak-field / linearized regime (harmonic gauge as an example), one has a
linear relation between source and perturbation:

$$
\Box h_{ab} = 16\pi S_{ab}(T)
$$

with a Green operator producing $h[T]$.

**Heuristic in current code:** we use a scalar FFT Green multiplier in 1+1 as a toy.

### Causal future family

For a point $p\in M$, the causal future is $J_g^+(p)$. Under perturbed metrics
$g' = g + h[T]$, we get a family

$$
\mathcal{J}_p := \{ J^+_{g+h[T]}(p) : T \in \mathcal{C}_{\mathrm{AQEI}} \cap \mathcal{U} \}
$$

where $\mathcal{U}$ is a small neighborhood (e.g. norm ball) of admissible stress–energy
configurations.

## Conjecture (informal)

> **Causal stability conjecture (bridge form).** In sufficiently small neighborhoods
> of AQEI-admissible stress–energy, the family $\mathcal{J}_p$ is path-connected (and
> does not change the global causal homotopy class).

### What is “formalizable now”

In Lean, we can state a parametric version:

- a type of points `M.Pt`
- an abstract metric `g : Pt → Pt → ℝ` (placeholder)
- an abstract `linearized_solution : StressEnergy n → MetricPerturbation`
- a predicate `CausalFuture g p q`

and then define the *interface statement*.

### What remains heuristic/analytic

- identifying the correct topology on the space of causal futures
- proving continuity of $J^+$ under metric perturbations
- validating the PDE → observable reduction used in computation

## Lean interface sketch (current repo)

The current Lean repo already contains typed placeholders in:

- `lean/src/AqeiBridge/CausalStability.lean`

As the bridge paper matures, replace `axiom causal_stability : True` with a
concrete statement for a discrete spacetime model, then generalize.
