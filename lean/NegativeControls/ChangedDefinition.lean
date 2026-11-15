-- SPDX-License-Identifier: Apache-2.0
module

/-!
# Negative control: a changed definition

Does not import `HubbardMoments.Spec`. Instead it defines a constant with the same name,
`HubbardMoments.Spec.SecondMomentTheorem`, as `True`, and proves the headline theorem
against it. The theorem's statement is the same expression as the challenge's, but the
definition it unfolds to is not, so `lake comparator` must reject it (exit code 1).
-/

public section

namespace HubbardMoments

def Spec.SecondMomentTheorem : Prop := True

theorem secondMomentTheorem : Spec.SecondMomentTheorem := trivial

end HubbardMoments
