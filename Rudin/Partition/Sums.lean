import Rudin.Prelude
import Rudin.Partition.Interval

namespace Rudin

variable {a b : ℝ} {I : a < b} (P : Partition I)

section Globals

variable (f α : ℝ → ℝ)

noncomputable def M (i : ℕ) : ℝ := sSup (f '' P.interval i)
noncomputable def m (i : ℕ) : ℝ := sInf (f '' P.interval i)

lemma ℓ {i : Fin P.n} : i.val - 1 < P.n := Nat.sub_lt_of_lt i.is_lt

noncomputable def U : ℝ := ∑ i : Fin P.n, M P f i * (α (P[i]) - α (P[i.val - 1]'(ℓ P)))
noncomputable def L : ℝ := ∑ i : Fin P.n, m P f i * (α (P[i]) - α (P[i.val - 1]'(ℓ P)))

/-- Upper integral. -/
noncomputable def Uι : ℝ := sSup ((L · f α) '' (@Set.univ (Partition I)))

/-- Lower integral. -/
noncomputable def Lι : ℝ := sInf ((U · f α) '' (@Set.univ (Partition I)))

end Globals

theorem m_le_M (hf : BddOn f (Set.Icc a b)) (i : ℕ) : m P f i ≤ M P f i := by
  replace hf : BddOn f (P.interval i) := hf.mono (P.interval_subset i)
  refine Real.sInf_le_sSup (f '' (P.interval i)) ?_ ?_
  · exact hf.below'
  · exact hf.above'

end Rudin
