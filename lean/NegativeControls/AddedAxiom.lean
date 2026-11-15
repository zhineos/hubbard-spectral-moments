-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.Spec

/-!
# Negative control: an added axiom

States the headline theorem exactly, but proves it from a new axiom. The statement matches;
the axiom is not permitted, so `lake comparator` must reject it (exit code 1).
-/

public section

namespace HubbardMoments

axiom secondMomentCheat : Spec.SecondMomentTheorem

theorem secondMomentTheorem : Spec.SecondMomentTheorem := secondMomentCheat

end HubbardMoments
