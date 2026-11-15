-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.Spec

/-!
# Negative control: a weakened statement

Proves `SecondMomentTheorem ∨ True` under the name of the headline theorem. The statement is
weaker than the challenge's, so `lake comparator` must reject it (exit code 1).
-/

public section

namespace HubbardMoments

theorem secondMomentTheorem : Spec.SecondMomentTheorem ∨ True := Or.inr trivial

end HubbardMoments
