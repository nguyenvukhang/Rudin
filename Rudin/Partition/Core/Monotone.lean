import Rudin.Defs.Partition

namespace Rudin

variable {a b : ℝ} {I : a < b} (P : Partition I)

namespace Partition

@[deprecated sorted' (since := "when")]
theorem strictMonoᵢ : StrictMono fun i : Fin P.n ↦ P[i]
  := by --
  exact P.sorted' -- ∎

theorem get_mono : Monotone P.l.get
  := by --
  exact P.sorted'.monotone -- ∎

@[deprecated get_mono (since := "when")]
theorem monoᵢ : Monotone fun i : Fin P.n ↦ P[i]
  := by --
  exact P.sorted'.monotone -- ∎

end Partition
end Rudin
