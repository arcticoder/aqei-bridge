/-- Auto-generated from mathematica/search.wl. -/
import Std
import Mathlib.Data.Rat.Basic

namespace AqeiBridge

structure Candidate where
  rayIndex : Nat
  rayName : String
  score : Float
  aRat : Array Rat
  activeConstraints : Array Nat
deriving Repr

def nBasis : Nat := 3
def mConstraints : Nat := 12

def topCandidates : List Candidate := [
  {
    rayIndex := 2,
    rayName := "t=-x",
    score := 3971.398346580124,
    aRat := #[((( -72801 : Int) : Rat) / 924475), ((( -252565 : Int) : Rat) / 796579), ((( -62989 : Int) : Rat) / 478119)],
    activeConstraints := #[1, 9, 11]
  },
  {
    rayIndex := 4,
    rayName := "t=-0.5x",
    score := 942.9935090131671,
    aRat := #[((( -247573 : Int) : Rat) / 734629), ((( -110050 : Int) : Rat) / 379999), ((( -154307 : Int) : Rat) / 484728)],
    activeConstraints := #[7, 9, 11]
  },
  {
    rayIndex := 1,
    rayName := "t=x",
    score := 934.1721395151882,
    aRat := #[((( -247573 : Int) : Rat) / 734629), ((( -110050 : Int) : Rat) / 379999), ((( -154307 : Int) : Rat) / 484728)],
    activeConstraints := #[7, 9, 11]
  },
  {
    rayIndex := 3,
    rayName := "t=0.5x",
    score := 818.5791733731907,
    aRat := #[((( -247573 : Int) : Rat) / 734629), ((( -110050 : Int) : Rat) / 379999), ((( -154307 : Int) : Rat) / 484728)],
    activeConstraints := #[7, 9, 11]
  },
]

/--
Heuristic certificate skeleton.

This lemma is intentionally weak: it only packages the exported data.
Replace `True` with real inequalities once the AQEI functionals are formalized.
-/
theorem topCandidates_exported : True := by
  trivial

end AqeiBridge
