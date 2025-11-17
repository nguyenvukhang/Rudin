import Rudin.Partition.Core.Length

namespace Rudin

variable {a b : ℝ} {I : a < b} (P : Partition I)

namespace Partition

theorem get_strictMono : StrictMono P.l.get
  := by --
  exact P.sorted'.get_strictMono -- ∎

@[deprecated get_strictMono (since := "when")]
theorem idx_strictMono : StrictMono fun i : Fin P.n ↦ P[i]
  := by --
  exact P.sorted'.get_strictMono -- ∎

theorem get_mono : Monotone P.l.get
  := by --
  exact P.get_strictMono.monotone -- ∎

@[deprecated get_mono (since := "when")]
theorem idx_mono : Monotone fun i : Fin P.n ↦ P[i]
  := by --
  exact P.get_strictMono.monotone -- ∎

end Partition
end Rudin
