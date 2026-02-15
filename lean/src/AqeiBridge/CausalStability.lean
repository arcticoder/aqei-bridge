import Mathlib.Data.Set.Basic
import Mathlib.Topology.Connected.PathConnected

import AqeiBridge.Spacetime
import AqeiBridge.StressEnergy
import AqeiBridge.AQEI_Cone

/-!
# Causal stability (formal statements; proof skeletons)

This file contains *statements* that we want to connect to the numerical search.

**Formalizable now:** these are well-typed theorem statements with explicit
parameters and hypotheses.

**Not formalized yet:** the analytic content of solving (linearized) Einstein
and the relationship between toy observables and true causal futures.
-/

namespace AqeiBridge

variable {n : ℕ}

/-- A placeholder "linearized solution" operator mapping stress-energy to a metric perturbation.

In the current toy phase this is left abstract to keep later models pluggable.
-/
noncomputable def linearized_solution {M : Spacetime} (_T : StressEnergy n) : MetricPerturbation M :=
  ⟨fun _ _ => 0⟩

/-- A toy notion of causal gain: `q` becomes causally reachable from `p` after
adding the perturbation sourced by `T`, but was not reachable in the background.

**Speculative:** interpreting this predicate as genuine superluminal "cone advance"
requires a concrete causal model.
-/
def causal_gain {M : Spacetime} (g : Metric M) (p q : M.Pt) (T : StressEnergy n) : Prop :=
  CausalFuture M (metricAdd g (linearized_solution (M := M) T)) p q ∧
  ¬ CausalFuture M g p q

/-- A small cone: a convenient subtype used for later local statements.

This is purely a bookkeeping device in the toy model.
-/
structure AQEI_cone_small (F : List (AQEIFunctional n)) where
  T : StressEnergy n
  mem : T ∈ AQEI_cone F

/-- Conjecture B (formal skeleton): the reachable futures vary "stably" as we
move inside a constrained AQEI cone.

For now, we state a very weak topological form; later versions should be
replaced with a concrete local/causal statement for discrete spacetimes.
-/
axiom causal_stability
  {M : Spacetime} (g : Metric M) (p : M.Pt) (F : List (AQEIFunctional n)) :
  True

/-!
## Parameter-space stability (path-connectedness)

This is the concrete shape we can aim to prove first in the finite-dimensional
toy model: the admissible region (intersected with a small neighborhood) is
path-connected.

The stronger statement about invariance of *global causal homotopy class* is
tracked as backlog work.
-/

/-- A placeholder predicate for “smallness” of a coefficient vector.

In later phases this can be instantiated by a norm bound or membership in a
metric ball.
-/
abbrev Small (_T : StressEnergy n) : Prop := True

/-- A path-connectedness skeleton for the admissible coefficient region.

This is intentionally abstract, but is already a meaningful topological goal in
the `StressEnergy n = Fin n → ℝ` model.
-/
axiom admissible_region_pathConnected (F : List (AQEIFunctional n)) :
  IsPathConnected {T : StressEnergy n | T ∈ AQEI_cone F ∧ Small (n := n) T}

/-!
## Toward “no change in global causal homotopy class” (interface placeholders)

The bridge conjecture talks about a family of causal futures and the claim that
their “global causal homotopy class” does not change inside small neighborhoods.

We do not yet commit to a concrete topology on the space of futures, nor to a
specific homology/cohomology invariant. Instead we introduce typed placeholders
so later work can refine the statement without reworking the whole repo.
-/

/-- A family of perturbed futures for a fixed base metric `g` and basepoint `p`.

This is an interface placeholder: later instantiations should choose a concrete
causal model and a topology on the codomain.
-/
noncomputable def PerturbedFutures {M : Spacetime} (g : Metric M) (p : M.Pt)
    (F : List (AQEIFunctional n)) : Set (Set M.Pt) :=
  {J | ∃ T : StressEnergy n, T ∈ AQEI_cone F ∧ Small (n := n) T ∧ J = Jplus M g p}

/-- Placeholder for an invariant “global causal homotopy class” predicate.

In later phases this should be replaced by a concrete invariant (e.g. an order
invariant for a causal poset, or a homology/cohomology class for an associated
space).
-/
abbrev InvariantHomotopyClass {M : Spacetime} (_g : Metric M) (_p : M.Pt)
    (_F : List (AQEIFunctional n)) : Prop := True

/-- Conjecture-shaped interface statement (placeholder).

This is deliberately weak/axiomatic right now; the near-term goal is to prove a
nontrivial analogue in the discrete toy model, then strengthen this statement.
-/
axiom causal_stability_pathConnected
  {M : Spacetime} (g : Metric M) (p : M.Pt) (F : List (AQEIFunctional n)) :
  IsPathConnected {T : StressEnergy n | T ∈ AQEI_cone F ∧ Small (n := n) T} ∧
    InvariantHomotopyClass (M := M) g p F

end AqeiBridge
