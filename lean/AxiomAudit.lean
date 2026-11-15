-- SPDX-License-Identifier: Apache-2.0
module

import HubbardMoments.Main

/-!
# Axiom audit

Every headline theorem may depend only on `propext`, `Classical.choice` and `Quot.sound`,
the standard axioms of Mathlib. Run from `lean/` with `lake env lean AxiomAudit.lean`.
-/

#print axioms HubbardMoments.sectorDimensions
#print axioms HubbardMoments.sectorDimensionsQuoted
#print axioms HubbardMoments.hopAverage
#print axioms HubbardMoments.hopAverageRegular
#print axioms HubbardMoments.hopAverageTorus
#print axioms HubbardMoments.hopAverageTorusValues
#print axioms HubbardMoments.projectedHoppingDiagonalZero
#print axioms HubbardMoments.projectedHoppingSquareDiagonal
#print axioms HubbardMoments.secondMomentTheorem
#print axioms HubbardMoments.secondMomentRegular
#print axioms HubbardMoments.secondMomentTorus
#print axioms HubbardMoments.projectedHoppingExists
#print axioms HubbardMoments.pairHoppingHermitian
#print axioms HubbardMoments.doublonFirstOrderZero
#print axioms HubbardMoments.doubledPeierlsPhase
#print axioms HubbardMoments.doublonHoppingRange
#print axioms HubbardMoments.doublonOnSiteShift
#print axioms HubbardMoments.doublonOnSiteShiftTorus
#print axioms HubbardMoments.torusTriangleFree
#print axioms HubbardMoments.schriefferWolffCrossTerm
#print axioms HubbardMoments.schriefferWolffSecondMoment
#print axioms HubbardMoments.schriefferWolffSecondMomentTorus
#print axioms HubbardMoments.crossTermNeedsTriangleFree
#print axioms HubbardMoments.sampleMean
#print axioms HubbardMoments.finitePopulationVariance
#print axioms HubbardMoments.finitePopulationFourthMoment
#print axioms HubbardMoments.independentSumSecondMoment
#print axioms HubbardMoments.independentSumFourthMoment
#print axioms HubbardMoments.torusBandMoments
#print axioms HubbardMoments.freeFermionSecondMomentTorus
#print axioms HubbardMoments.freeAndProjectedSecondMomentsAgree
#print axioms HubbardMoments.finitePopulationTable
#print axioms HubbardMoments.closedWalkFewMoved
#print axioms HubbardMoments.fourHopPermutations
#print axioms HubbardMoments.fourHopExchangesOccur
#print axioms HubbardMoments.threeCycleCountAffine
#print axioms HubbardMoments.canonicalAnticommutation
#print axioms HubbardMoments.sortedTupleSignRule
#print axioms HubbardMoments.hubbardHoppingHermitian
#print axioms HubbardMoments.hubbardHoppingIsHoppingOperator
#print axioms HubbardMoments.projectedHubbardIsProjectedHopping
#print axioms HubbardMoments.secondMomentHubbard
#print axioms HubbardMoments.secondMomentHubbardTorus
#print axioms HubbardMoments.schriefferWolffHubbard
#print axioms HubbardMoments.secondMomentWeightedTheorem
#print axioms HubbardMoments.secondMomentHubbardWeighted
