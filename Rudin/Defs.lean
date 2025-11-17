import Rudin.Prelude
import Rudin.Partition.Interval
import Rudin.Partition.OrderBot

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} (P : Partition I)

section Globals

variable (f α : ℝ → ℝ)

noncomputable def M (i : ℕ) : ℝ := sSup (f '' P.interval i)
noncomputable def m (i : ℕ) : ℝ := sInf (f '' P.interval i)

lemma ℓ {i : Fin P.n} : i.val - 1 < P.n := Nat.sub_lt_of_lt i.is_lt

noncomputable def U : ℝ := ∑ i : Fin P.n, M P f i * (α (P[i]) - α (P[i.val - 1]'(ℓ P)))
noncomputable def L : ℝ := ∑ i : Fin P.n, m P f i * (α (P[i]) - α (P[i.val - 1]'(ℓ P)))

section Integrals

variable (I : a < b) (f α : ℝ → ℝ)

/-- Upper integral. -/
noncomputable def Uι : ℝ := sInf { U P f α | P : Partition I }

/-- Lower integral. -/
noncomputable def Lι : ℝ := sSup { L P f α | P : Partition I }

theorem U_nonempty : { U P f α | P : Partition I }.Nonempty
  := by --
  let P₀ : Partition I := ⊥
  let M' := sSup (f '' Icc a b)
  use M' * (α b - α a), P₀
  have : P₀.n = 2 := rfl
  change ∑ i : Fin 2, M P₀ f ↑i * (α P₀[i] - α P₀[↑i - 1]) = M' * (α b - α a)
  rw [Fin.sum_univ_two]
  simp only [Fin.getElem_fin, Fin.coe_ofNat_eq_mod]
  rw [sub_self, mul_zero, zero_add]
  exact rfl -- ∎

theorem L_nonempty : { L P f α | P : Partition I }.Nonempty
  := by --
  let P₀ : Partition I := ⊥
  let m' := sInf (f '' Icc a b)
  use m' * (α b - α a), P₀
  have : P₀.n = 2 := rfl
  change ∑ i : Fin 2, m P₀ f ↑i * (α P₀[i] - α P₀[↑i - 1]) = m' * (α b - α a)
  rw [Fin.sum_univ_two]
  simp only [Fin.getElem_fin, Fin.coe_ofNat_eq_mod]
  rw [sub_self, mul_zero, zero_add]
  exact rfl -- ∎

def RiemannStieltjesIntegrable : Prop := Uι I f α = Lι I f α

end Integrals

end Globals

theorem m_le_M (hf : BddOn f (Set.Icc a b)) (i : ℕ) : m P f i ≤ M P f i := by
  replace hf : BddOn f (P.interval i) := hf.mono (P.interval_subset i)
  refine Real.sInf_le_sSup (f '' (P.interval i)) ?_ ?_
  · exact hf.below'
  · exact hf.above'

end Rudin
