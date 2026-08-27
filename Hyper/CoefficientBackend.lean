import Hyper.HyperFieldOfFractions

/-!
Single selection point for the standard coefficient field.

`Active` deliberately remains `Rational` while `HyperList` is being migrated
from `(coefficient × coefficient)` to `(coefficient × ℚ)`.  Once the remaining
coefficient assumptions are isolated, switching the active backend is exactly
the one-line change documented below.
-/

namespace CoefficientBackend

abbrev Rational := ℚ
abbrev PiE := RFrac

/- Change this to `PiE` to select the computable `ℚ(π,e)` representation. -/
abbrev Active := Rational

end CoefficientBackend
