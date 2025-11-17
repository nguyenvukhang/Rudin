import Rudin.Partition.Union
import Rudin.Defs

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b}

section T1
--- Rudin, Theorem 6.4, Page 123
variable {f α : ℝ → ℝ}

/-- If P' is a refinement of P, then the lower sum obtained from P' will be
greater or equal to that of P. -/
axiom L_mono
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))
  : Monotone fun P : Partition I ↦ L P f α

/-- If P' is a refinement of P, then the upper sum obtained from P' will be
lesser or equal to that of P. -/
axiom U_anti
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))
  : Antitone fun P : Partition I ↦ U P f α

end T1

end Rudin
