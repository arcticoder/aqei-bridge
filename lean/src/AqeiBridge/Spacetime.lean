import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic

/-!
# Spacetime (toy models)

This file defines *placeholders* for spacetime / metric data sufficient for
stating the AQEI-bridge conjectures.

**Formalizable now:** basic types, predicates, and parametric theorem statements.

**Speculative / heuristic:** any claim that these placeholders faithfully model
Lorentzian geometry or causal futures of PDE solutions.
-/

namespace AqeiBridge

/-- A minimal spacetime model: a type of points. -/
structure Spacetime where
  Pt : Type

/-- A toy "metric" as a real-valued function of two points.

In real differential geometry this would be a bilinear form on tangent vectors.
Here it is only a placeholder to keep statements parametric.
-/
abbrev Metric (M : Spacetime) : Type := M.Pt → M.Pt → ℝ

/-- A toy causal future predicate for a metric `g`.

**NOTE:** This is deliberately abstract. In later stages it can be refined to a
concrete reachability relation on a discrete spacetime model.
-/
abbrev CausalFuture (M : Spacetime) (_g : Metric M) (_p _q : M.Pt) : Prop := True

/-!
## Causal-structure interface (abstract)

These are intentionally abstract so that we can:
- keep Lean statements well-typed,
- later replace them with either a discrete reachability model or a genuine
  Lorentzian-manifold development.
-/

/-- A placeholder predicate for existence of a causal curve from `p` to `q`.

In later stages, `CausalCurve` should depend on tangent data and the sign
condition $g(\dot\gamma,\dot\gamma) \le 0$.
-/
abbrev CausalCurve (M : Spacetime) (g : Metric M) (p q : M.Pt) : Prop :=
  CausalFuture M g p q

/-- The causal future set $J^+(p)$ in the current abstract interface. -/
def Jplus (M : Spacetime) (g : Metric M) (p : M.Pt) : Set M.Pt := {q | CausalCurve M g p q}

/-- A placeholder for selecting a “small neighborhood” around a point.

In a real manifold development, this can be instantiated with chart-topology
balls; for now it is an abstract predicate.
-/
abbrev SmallNeighborhood (M : Spacetime) : Type := M.Pt → Set M.Pt

/-- A metric perturbation placeholder. -/
structure MetricPerturbation (M : Spacetime) where
  h : Metric M

/-- Add a perturbation to a background metric. -/
def metricAdd {M : Spacetime} (g : Metric M) (h : MetricPerturbation M) : Metric M :=
  fun p q => g p q + h.h p q

end AqeiBridge
