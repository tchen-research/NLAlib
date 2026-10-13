import NLAlib
import Batteries.Tactic.Lint.Frontend
import Batteries.Tactic.Lint.Misc
import Batteries.Tactic.Lint.TypeClass

/-! Standard environment linters for the default public library. These check declaration
types and instance validity; naming and documentation checks are maintained separately. -/

#lint only checkType impossibleInstance nonClassInstance in NLAlib
