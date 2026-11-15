-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.Spec

/-!
# Negative control: an unfinished proof

States the headline theorem exactly and leaves it as `sorry`, which depends on `sorryAx`.
That axiom is not permitted, so `lake comparator` must reject it (exit code 1).
-/

public section

namespace HubbardMoments

theorem secondMomentTheorem : Spec.SecondMomentTheorem := sorry

end HubbardMoments
