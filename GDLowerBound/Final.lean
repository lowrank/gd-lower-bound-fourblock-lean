import GDLowerBound.Geometry.FunctionalAttainment
import GDLowerBound.RankAnalysis.Normalized

namespace GDLowerBound

/-- Formal version of `thm:main` from the manuscript. -/
theorem mainTheorem : mainStatement :=
  RankAnalysis.mainStatement_of_normalizedFloor
    functionalAttainment RankAnalysis.normalizedFloorTheorem

end GDLowerBound
