import Rudin.Results.Basic

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} {P P' P₁ P₂ : Partition I} {f α : ℝ → ℝ}
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))

set_option linter.dupNamespace false in
include hf hα in
@[deprecated RiemannStieltjesIntegrable.iff (since := "when")]
theorem Theorem._6._6 : RiemannStieltjesIntegrable I f α ↔
  ∀ ε > 0, ∃ P : Partition I, U P f α - L P f α < ε
  := by --
  exact RiemannStieltjesIntegrable.iff hf hα -- ∎

include hf hα in
theorem Theorem._6._7._a (ε : ℝ) :
  U P f α - L P f α < ε → ∀ P' ≥ P, U P' f α - L P' f α < ε
  := by --
  intro h P' (hP : P ≤ P')
  have hU : U P' f α ≤ U P f α := U_anti hf hα hP
  have hL : L P f α ≤ L P' f α := L_mono hf hα hP
  exact (tsub_le_tsub hU hL).trans_lt h -- ∎

include hf hα in
theorem Theorem._6._7._b (ε : ℝ) :
  U P f α - L P f α < ε → ∀ s t, IsTag P s → IsTag P t →
  ∑ i ∈ Finset.range P.n, |f (s i) - f (t i)| * (α (P i) - α (P (i - 1))) < ε
  := by --
  intro h s t hs ht
  rw [UL_eq] at h

  have (i : ℕ) : |f (s i) - f (t i)| ≤ M P f i - m P f i := by
    dsimp only [m, M]
    rcases Nat.lt_or_ge i P.n with hlt | hge
    · specialize hs i
      specialize ht i
      have hs' : f (s i) ∈ f '' P.interval i := ⟨s i, hs, rfl⟩
      have ht' : f (t i) ∈ f '' P.interval i := ⟨t i, ht, rfl⟩
      have hbd : BddOn f (P.interval i) := bdd_f_bdd_on_interval hf i
      refine abs_sub_le_of_le_of_le ?_ ?_ ?_ ?_
      · refine hbd.csInf_le hs
      · exact hbd.le_csSup hs
      · exact hbd.csInf_le ht
      · exact hbd.le_csSup ht
    · rw [ht.n_le P hge, hs.n_le P hge, sub_self, abs_zero]
      exact sub_nonneg_of_le (m_le_M P hf i)

  have (i : ℕ) : |f (s i) - f (t i)| * (α (P i) - α (P (i - 1)))
    ≤ (M P f i - m P f i) * (α (P i) - α (P (i - 1))) := by
    refine mul_le_mul_of_nonneg_right ?_ (α_nonneg₂ hα P i)
    exact this i

  have : ∑ i ∈ Finset.range P.n, |f (s i) - f (t i)| * (α (P i) - α (P (i - 1))) ≤
  ∑ i ∈ Finset.range P.n, (M P f i - m P f i) * (α (P i) - α (P (i - 1))) := by
    exact Finset.sum_le_sum fun i _ ↦ this i
  exact this.trans_lt h -- ∎

end Rudin
