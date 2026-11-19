-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.Spec

/-!
# Challenge: the reference statements

Each theorem below states one proposition of `HubbardMoments.Spec`, under the same name
as its proof in `HubbardMoments.Main`, and is left as `sorry`. `lake comparator` (see
`comparator.json`) checks that every theorem of `Main` proves exactly this statement,
uses only `propext`, `Classical.choice` and `Quot.sound`, and is accepted by the kernel.

The trusted part is this file's import closure: Mathlib, `HubbardMoments.Defs` and
`HubbardMoments.Spec`. Nothing here is proved; the `sorry`s are the point. This library is
not a default target, so `lake build` and `lake check` never see them.

Generated from `HubbardMoments/Main.lean` (one line per theorem, same order) by
`checks/make_challenge.py`; regenerate rather than edit by hand.
-/

public section

namespace HubbardMoments

theorem sectorDimensions : Spec.SectorDimensions := sorry

theorem sectorDimensionsQuoted : Spec.SectorDimensionsQuoted := sorry

theorem hopAverage : Spec.HopAverage := sorry

theorem hopAverageRegular : Spec.HopAverageRegular := sorry

theorem hopAverageTorus : Spec.HopAverageTorus := sorry

theorem hopAverageTorusValues : Spec.HopAverageTorusValues := sorry

theorem projectedHoppingDiagonalZero : Spec.ProjectedHoppingDiagonalZero := sorry

theorem projectedHoppingSquareDiagonal : Spec.ProjectedHoppingSquareDiagonal := sorry

theorem secondMomentTheorem : Spec.SecondMomentTheorem := sorry

theorem secondMomentRegular : Spec.SecondMomentRegular := sorry

theorem secondMomentTorus : Spec.SecondMomentTorus := sorry

theorem projectedHoppingExists : Spec.ProjectedHoppingExists := sorry

theorem pairHoppingHermitian : Spec.PairHoppingHermitian := sorry

theorem doublonFirstOrderZero : Spec.DoublonFirstOrderZero := sorry

theorem doubledPeierlsPhase : Spec.DoubledPeierlsPhase := sorry

theorem doublonHoppingRange : Spec.DoublonHoppingRange := sorry

theorem doublonOnSiteShift : Spec.DoublonOnSiteShift := sorry

theorem doublonOnSiteShiftTorus : Spec.DoublonOnSiteShiftTorus := sorry

theorem torusTriangleFree : Spec.TorusTriangleFree := sorry

theorem schriefferWolffCrossTerm : Spec.SchriefferWolffCrossTerm := sorry

theorem schriefferWolffSecondMoment : Spec.SchriefferWolffSecondMoment := sorry

theorem schriefferWolffSecondMomentTorus : Spec.SchriefferWolffSecondMomentTorus := sorry

theorem crossTermNeedsTriangleFree : Spec.CrossTermNeedsTriangleFree := sorry

theorem sampleMean : Spec.SampleMean := sorry

theorem finitePopulationVariance : Spec.FinitePopulationVariance := sorry

theorem finitePopulationFourthMoment : Spec.FinitePopulationFourthMoment := sorry

theorem independentSumSecondMoment : Spec.IndependentSumSecondMoment := sorry

theorem independentSumFourthMoment : Spec.IndependentSumFourthMoment := sorry

theorem torusBandMoments : Spec.TorusBandMoments := sorry

theorem freeFermionSecondMomentTorus : Spec.FreeFermionSecondMomentTorus := sorry

theorem freeAndProjectedSecondMomentsAgree : Spec.FreeAndProjectedSecondMomentsAgree := sorry

theorem finitePopulationTable : Spec.FinitePopulationTable := sorry

theorem closedWalkFewMoved : Spec.ClosedWalkFewMoved := sorry

theorem fourHopPermutations : Spec.FourHopPermutations := sorry

theorem fourHopExchangesOccur : Spec.FourHopExchangesOccur := sorry

theorem threeCycleCountAffine : Spec.ThreeCycleCountAffine := sorry

theorem canonicalAnticommutation : Spec.CanonicalAnticommutation := sorry

theorem sortedTupleSignRule : Spec.SortedTupleSignRule := sorry

theorem hubbardHoppingHermitian : Spec.HubbardHoppingHermitian := sorry

theorem hubbardHoppingIsHoppingOperator : Spec.HubbardHoppingIsHoppingOperator := sorry

theorem projectedHubbardIsProjectedHopping : Spec.ProjectedHubbardIsProjectedHopping := sorry

theorem secondMomentHubbard : Spec.SecondMomentHubbard := sorry

theorem secondMomentHubbardTorus : Spec.SecondMomentHubbardTorus := sorry

theorem schriefferWolffHubbard : Spec.SchriefferWolffHubbard := sorry

theorem secondMomentWeightedTheorem : Spec.SecondMomentWeightedTheorem := sorry

theorem secondMomentHubbardWeighted : Spec.SecondMomentHubbardWeighted := sorry

theorem torusGraphCounts : Spec.TorusGraphCounts := sorry

theorem hardCoreBosonFourthMoment : Spec.HardCoreBosonFourthMoment := sorry

theorem fourthMomentHubbard : Spec.FourthMomentHubbard := sorry

theorem fourthMomentHubbardTorus : Spec.FourthMomentHubbardTorus := sorry

theorem fourthMomentTableL4 : Spec.FourthMomentTableL4 := sorry

end HubbardMoments
