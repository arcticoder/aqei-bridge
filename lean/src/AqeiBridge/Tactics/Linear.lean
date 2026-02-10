import Mathlib.Tactic

/-!
# Tactics: linear / convex helpers

This is intentionally tiny: we add helpers as recurring proof patterns emerge.
-/

namespace AqeiBridge.Tactics

/-- A small convenience tactic for goals that are (after simp) linear arithmetic. -/
macro "aqei_linarith" : tactic => `(tactic| (simp; linarith))

end AqeiBridge.Tactics
