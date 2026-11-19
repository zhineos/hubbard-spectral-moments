-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.Defs
public import HubbardMoments.Spec
public import HubbardMoments.Combinatorics.Subsets
public import HubbardMoments.Torus
public import HubbardMoments.Sectors
public import HubbardMoments.SecondMoment
public import HubbardMoments.ProjectedHopping
public import HubbardMoments.Doublon
public import HubbardMoments.SchriefferWolff
public import HubbardMoments.FinitePopulation
public import HubbardMoments.TorusBand
public import HubbardMoments.ClosedWalks
public import HubbardMoments.Fermions
public import HubbardMoments.Hubbard
public import HubbardMoments.Weighted
public import HubbardMoments.FourthMoment.GraphCounts
public import HubbardMoments.FourthMoment.HardCoreBosons
public import HubbardMoments.FourthMoment.FermionSigns
public import HubbardMoments.FourthMoment.FermionPaths
public import HubbardMoments.FourthMoment.FermionValues
public import HubbardMoments.FourthMoment.FermionDelta
public import HubbardMoments.FourthMoment.SpinCounts
public import HubbardMoments.FourthMoment.FermionMoment
public import HubbardMoments.FourthMoment.TorusMoment
public import HubbardMoments.Main

/-!
# HubbardMoments

The library root, and the default build target: it imports every module, so `lake build`
and `lake check` cover the whole formalization. It proves nothing itself. The claims are
stated in `HubbardMoments.Spec` and proved in `HubbardMoments.Main`; `README.md` maps them
to the paper.
-/
