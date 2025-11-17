import Rudin.Partition
import Rudin.Prelude

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} {P P' : Partition I} (f α : ℝ → ℝ)

section T1
--- Rudin, Theorem 6.4, Page 123
variable {P P' : Partition I} (h : P ≤ P')

/-- If P' is a refinement of P, then the lower sum obtained from P' will be
greater or equal to that of P. -/
axiom L_mono
  (hP : P ≤ P')
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))
  : P ≤ P' → L P f α ≤ L P' f α

/-- If P' is a refinement of P, then the upper sum obtained from P' will be
lesser or equal to that of P. -/
axiom U_anti
  (hP : P ≤ P')
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))
  : U P' f α ≤ U P f α

end T1

end Rudin
