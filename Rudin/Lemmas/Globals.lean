import Mathlib.Algebra.BigOperators.Fin

import Rudin.Defs.Globals
import Rudin.Partition.Interval
import Rudin.Partition.OrderBot

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} (P : Partition I) {f : ℝ → ℝ}

theorem m_le_M (hf : BddOn f (Icc a b)) (i : ℕ) : m P f i ≤ M P f i
  := by --
  refine BddOn.sInf_le_sSup ?_
  exact hf.anti (P.interval_subset i) -- ∎

section Globals

variable (f α : ℝ → ℝ)

lemma U_eq : U P f α = ∑ i ∈ Finset.range P.n, M P f i * (α (P i) - α (P (i - 1))) := rfl
lemma L_eq : L P f α = ∑ i ∈ Finset.range P.n, m P f i * (α (P i) - α (P (i - 1))) := rfl

private lemma ℓ {i : Fin P.n} : i.val - 1 < P.n := Nat.sub_lt_of_lt i.is_lt

-- Reassurances of legitness of definition.
example : U P f α = ∑ i : Fin P.n, M P f i * (α (P[i]) - α (P[i.val - 1]'(ℓ P)))
  := by --
  let n := P.n
  have h₁ (i : Fin n) : P i = P[i] := Partition.ieq.idx_fin P
  have h₂ (i : Fin n) : P (i - 1) = P[↑i - 1] := Partition.ieq.idx_cond P _
  dsimp only [U, Partition.Δ]
  rw [Finset.sum_range]
  simp only [h₁, h₂]
  exact rfl -- ∎
example : L P f α = ∑ i : Fin P.n, m P f i * (α (P[i]) - α (P[i.val - 1]'(ℓ P)))
  := by --
  let n := P.n
  have h₁ (i : Fin n) : P i = P[i] := Partition.ieq.idx_fin P
  have h₂ (i : Fin n) : P (i - 1) = P[↑i - 1] := Partition.ieq.idx_cond P _
  dsimp only [L, Partition.Δ]
  rw [Finset.sum_range]
  simp only [h₁, h₂]
  exact rfl -- ∎

theorem UL_eq : U P f α - L P f α =
  ∑ i ∈ Finset.range P.n, (M P f i - m P f i) * P.Δ α i
  := by --
  dsimp only [U, L]
  rw [<-Finset.sum_sub_distrib]
  simp only [<-sub_mul] -- ∎

section Integrals

variable (I : a < b) (f α : ℝ → ℝ)

lemma IsTag.n_le {t : ℕ → ℝ} (ht : IsTag P t) {i : ℕ} (h : P.n ≤ i) : t i = b
  := by --
  replace ht : t i ∈ Icc (P (i - 1)) (P i) := ht i
  have h' := P.fn_eq₂ i
  rw [dif_neg h.not_gt] at h'
  rw [h'.1, h'.2] at ht
  exact le_antisymm ht.2 ht.1 -- ∎

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

end Integrals
end Globals
end Rudin
