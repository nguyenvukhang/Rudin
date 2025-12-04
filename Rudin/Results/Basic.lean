import Rudin.Partition.Globals
import Rudin.Partition.Union

open Set

namespace Rudin

variable {a b : ℝ} {I : a < b} {P P' P₁ P₂ : Partition I} {f α : ℝ → ℝ}
  (hf : BddOn f (Icc a b))
  (hα : MonotoneOn α (Icc a b))

include hf hα in
theorem L_le_U_same_P : L P f α ≤ U P f α
  := by --
  have (i : ℕ) : m P f i * P.Δ α i ≤ M P f i * P.Δ α i := by
    refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα i)
    exact m_le_M P hf i
  exact Finset.sum_le_sum fun i _ ↦ this i -- ∎

include hf hα in
theorem L_le_U : L P₁ f α ≤ U P₂ f α
  := by --
  have h₁ : P₁ ≤ P₁ ⊔ P₂ := le_sup_left
  have h₂ : P₂ ≤ P₁ ⊔ P₂ := le_sup_right
  have hL := L_mono hf hα h₁
  have hU := U_anti hf hα h₂
  exact hL.trans ((L_le_U_same_P hf hα).trans hU) -- ∎

include hf hα in
theorem Lι_le_Uι : Lι I f α ≤ Uι I f α
  := by --
  let P₀ : Partition I := ⊥
  have (P₂ : Partition I) : sSup { L P f α | P : Partition I } ≤ U P₂ f α := by
    refine csSup_le (L_nonempty I f α) ?_
    intro v ⟨P, heq⟩
    subst heq
    exact L_le_U hf hα
  have :  sSup { L P f α | P : Partition I } ≤ sInf { U P f α | P : Partition I } := by
    refine le_csInf (U_nonempty I f α) ?_
    intro v ⟨P, heq⟩
    subst heq
    exact this P
  exact this -- ∎

include hf in
@[deprecated m_le_M (since := "when")]
theorem interval_sInf_le_sSup (i : ℕ) : sInf (f '' P.interval i) ≤ sSup (f '' P.interval i)
  := by --
  refine BddOn.sInf_le_sSup ?_
  exact hf.anti (P.interval_subset i) -- ∎

theorem sInf_ab_le_sInf_interval (i : ℕ) : sInf (Icc a b) ≤ sInf (P.interval i)
  := by --
  refine csInf_le_csInf ?_ ?_ (P.interval_subset i)
  · exact bddBelow_Icc
  · exact P.interval_nonempty i -- ∎

include hf in
theorem sInf_ab_le_sInf_interval_f (i : ℕ) :
  sInf (f '' Icc a b) ≤ sInf (f '' P.interval i)
  := by --
  refine csInf_le_csInf ?_ ?_ (image_mono <| P.interval_subset i)
  · exact hf.below'
  · exact (P.interval_nonempty i).image f -- ∎

theorem sSup_interval_le_sSup_ab (i : ℕ) : sSup (P.interval i) ≤ sSup (Icc a b)
  := by --
  refine csSup_le_csSup ?_ ?_ (P.interval_subset i)
  · exact bddAbove_Icc
  · exact P.interval_nonempty i -- ∎

include hf in
theorem sSup_interval_le_sSup_ab_f (i : ℕ) : sSup (f '' P.interval i) ≤ sSup (f '' Icc a b)
  := by --
  refine csSup_le_csSup ?_ ?_ (image_mono <| P.interval_subset i)
  · exact hf.above'
  · exact (P.interval_nonempty i).image f -- ∎

include hf hα in
theorem L_bdd_below : BddBelow { L P f α | P : Partition I }
  := by --
  obtain ⟨y, hy⟩ := hf.below'
  use y * (α b - α a)
  intro val ⟨P, heq⟩
  subst heq
  have : y ≤ sInf (f '' Icc a b) := by
    refine le_csInf ?_ ?_
    · exact (nonempty_Icc.mpr I.le).image f
    · intro z ⟨x, hx, heq⟩
      subst heq
      exact hy ⟨x, hx, rfl⟩
  have : ∑ i ∈ Finset.range P.n, y * P.Δ α i ≤
    ∑ i ∈ Finset.range P.n, sInf (f '' P.interval ↑i) * P.Δ α i := by
    refine Finset.sum_le_sum ?_
    intro i _
    refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα i)
    exact this.trans (sInf_ab_le_sInf_interval_f hf i)
  refine le_trans ?_ this
  rw [<-Finset.mul_sum]
  refine le_of_eq ?_
  rw [mul_eq_mul_left_iff]
  exact Or.inl α_telescope.symm -- ∎

include hf hα in
theorem U_bdd_above : BddAbove { U P f α | P : Partition I }
  := by --
  obtain ⟨y, hy⟩ := hf.above'
  use y * (α b - α a)
  intro val ⟨P, heq⟩
  subst heq
  have : sSup (f '' Icc a b) ≤ y := by
    refine csSup_le ?_ ?_
    · exact (nonempty_Icc.mpr I.le).image f
    · intro z ⟨x, hx, heq⟩
      subst heq
      exact hy ⟨x, hx, rfl⟩
  have : ∑ i ∈ Finset.range P.n, sSup (f '' P.interval ↑i) * P.Δ α i
    ≤ ∑ i ∈ Finset.range P.n, y * P.Δ α i := by
    refine Finset.sum_le_sum ?_
    intro i _
    refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα i)
    refine (sSup_interval_le_sSup_ab_f hf i).trans this
  refine this.trans ?_
  rw [<-Finset.mul_sum]
  refine le_of_eq ?_
  rw [mul_eq_mul_left_iff]
  exact Or.inl α_telescope -- ∎

include hf hα in
theorem L_bdd_above : BddAbove { L P f α | P : Partition I }
  := by --
  obtain ⟨y, hy⟩ := U_bdd_above (I := I) hf hα
  use y
  intro val ⟨P, heq⟩
  subst heq
  exact (L_le_U_same_P hf hα).trans (hy ⟨P, rfl⟩) -- ∎

include hf hα in
theorem U_bdd_below : BddBelow { U P f α | P : Partition I }
  := by --
  obtain ⟨y, hy⟩ := L_bdd_below (I := I) hf hα
  use y
  intro val ⟨P, heq⟩
  subst heq
  exact (hy ⟨P, rfl⟩).trans (L_le_U_same_P hf hα) -- ∎

include hf hα in
theorem Uι_bot (P : Partition I) : Uι I f α ≤ U P f α
  := by --
  exact csInf_le (U_bdd_below hf hα) ⟨P, rfl⟩ -- ∎

include hf hα in
theorem Lι_top (P : Partition I) : L P f α ≤ Lι I f α
  := by --
  exact le_csSup (L_bdd_above hf hα) ⟨P, rfl⟩ -- ∎

include hf hα in
theorem RiemannStieltjesIntegrable.iff : RiemannStieltjesIntegrable I f α ↔
  ∀ ε > 0, ∃ P : Partition I, U P f α - L P f α < ε
  := by --
  constructor
  · intro h ε hε
    have hε₂ : 0 < ε / 2 := half_pos hε
    obtain ⟨P₁, hP₁⟩ : ∃ P₁ : Partition I, Lι I f α - L P₁ f α < ε / 2 := by
      have := sSup.exist_sub_lt_ε (L_nonempty I f α) (L_bdd_above hf hα) (ε / 2) hε₂
      obtain ⟨val, ⟨P, heq⟩, h⟩ := this
      subst heq
      exact ⟨P, h⟩
    obtain ⟨P₂, hP₂⟩ : ∃ P₂ : Partition I, U P₂ f α - Uι I f α < ε / 2 := by
      have := sInf.exist_sub_lt_ε (U_nonempty I f α) (U_bdd_below hf hα) (ε / 2) hε₂
      obtain ⟨val, ⟨P, heq⟩, h⟩ := this
      subst heq
      exact ⟨P, h⟩
    let P := P₁ ⊔ P₂
    refine ⟨P, sub_right_lt_of_lt_add ?_⟩
    have : U P f α ≤ U P₂ f α := U_anti hf hα le_sup_right
    refine this.trans_lt ?_
    have : U P₂ f α < ε / 2 + Uι I f α := lt_add_of_tsub_lt_right hP₂
    refine this.trans ?_
    rw [h]
    have : L P₁ f α ≤ L P f α := L_mono hf hα le_sup_left
    have : ε + L P₁ f α ≤ ε + L P f α := (add_le_add_iff_left ε).mpr this
    refine this.trans_lt' ?_
    conv => rhs; rw [<-add_halves ε]
    rw [add_assoc]
    have : Lι I f α < ε / 2 + L P₁ f α := lt_add_of_tsub_lt_right hP₁
    exact add_lt_add_right this (ε / 2)
  · intro h
    have hU (P : Partition I) : Uι I f α ≤ U P f α := Uι_bot hf hα P
    have hL (P : Partition I) : L P f α ≤ Lι I f α := Lι_top hf hα P
    have h₁ : 0 ≤ Uι I f α - Lι I f α := sub_nonneg_of_le (Lι_le_Uι hf hα)
    have h₂ : ∀ ε > 0, Uι I f α - Lι I f α ≤ ε := by
      intro ε hε
      specialize h ε hε
      obtain ⟨P, hP⟩ := h
      specialize hU P
      specialize hL P
      exact (tsub_le_tsub hU hL).trans hP.le
    have := eq_zero_of_nonneg_le_pos h₁ h₂
    rw [sub_eq_zero] at this
    exact this -- ∎

section MultipleFunctions
variable {f₁ f₂ : ℝ → ℝ} (hf₁ : BddOn f₁ (Icc a b)) (hf₂ : BddOn f₂ (Icc a b))

include hf₂ hα in
theorem U_f_mono (hle : ∀ x ∈ Icc a b, f₁ x ≤ f₂ x) :
  U P f₁ α ≤ U P f₂ α
  := by --
  dsimp only [U]
  refine Finset.sum_le_sum ?_
  intro i _
  refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα i)
  dsimp only [M]
  have hle : ∀ x ∈ f₁ '' P.interval i, ∃ y ∈ f₂ '' P.interval i, x ≤ y := by
    intro x ⟨t, ht, htx⟩
    subst htx
    refine ⟨f₂ t, ?_, ?_⟩
    · exact mem_image_of_mem f₂ ht
    · refine hle t (P.interval_subset i ht)
  let I₁ := f₁ '' P.interval i
  let I₂ := f₂ '' P.interval i
  refine ConditionallyCompleteLattice.csSup_le I₁ (sSup I₂) ?_ ?_
  · exact (P.interval_nonempty i).image f₁
  · intro x hx
    specialize hle x hx
    obtain ⟨y, hy, hle⟩ := hle
    refine hle.trans ?_
    refine le_csSup ?_ hy
    exact P.interval_bdd_above hf₂ i -- ∎

include hf₁ hα in
theorem L_f_mono (hle : ∀ x ∈ Icc a b, f₁ x ≤ f₂ x) :
  L P f₁ α ≤ L P f₂ α
  := by --
  dsimp only [L]
  refine Finset.sum_le_sum ?_
  intro i _
  refine mul_le_mul_of_nonneg_right ?_ (α_nonneg hα i)
  dsimp only [m]
  have hle : ∀ y ∈ f₂ '' P.interval i, ∃ x ∈ f₁ '' P.interval i, x ≤ y := by
    intro y ⟨t, ht, hty⟩
    subst hty
    refine ⟨f₁ t, ?_, ?_⟩
    · exact mem_image_of_mem f₁ ht
    · refine hle t (P.interval_subset i ht)
  let I₁ := f₁ '' P.interval i
  let I₂ := f₂ '' P.interval i
  refine ConditionallyCompleteLattice.le_csInf I₂ (sInf I₁) ?_ ?_
  · exact (P.interval_nonempty i).image f₂
  · intro y hy
    specialize hle y hy
    obtain ⟨x, hx, hle⟩ := hle
    refine hle.trans' ?_
    refine csInf_le ?_ hx
    exact P.interval_bdd_below hf₁ i -- ∎

include hf₁ hf₂ hα in
theorem Uι_f_mono (hle : ∀ x ∈ Icc a b, f₁ x ≤ f₂ x) :
  Uι I f₁ α ≤ Uι I f₂ α
  := by --
  dsimp only [Uι]
  let S₁ := { U P f₁ α | P : Partition I }
  let S₂ := { U P f₂ α | P : Partition I }
  change sInf S₁ ≤ sInf S₂
  have hle : ∀ y ∈ S₂, ∃ x ∈ S₁, x ≤ y := by
    intro y ⟨P, heq⟩
    subst heq
    exact ⟨U P f₁ α, ⟨P, rfl⟩, U_f_mono hα hf₂ hle⟩
  refine ConditionallyCompleteLattice.le_csInf S₂ (sInf S₁) ?_ ?_
  · exact U_nonempty I f₂ α
  · intro y hy
    specialize hle y hy
    obtain ⟨x, hx, hle⟩ := hle
    refine hle.trans' ?_
    refine csInf_le ?_ hx
    exact U_bdd_below hf₁ hα -- ∎

include hf₁ hf₂ hα in
theorem Lι_f_mono (hle : ∀ x ∈ Icc a b, f₁ x ≤ f₂ x) :
  Lι I f₁ α ≤ Lι I f₂ α
  := by --
  dsimp only [Lι]
  let S₁ := { L P f₁ α | P : Partition I }
  let S₂ := { L P f₂ α | P : Partition I }
  change sSup S₁ ≤ sSup S₂
  have hle : ∀ x ∈ S₁, ∃ y ∈ S₂, x ≤ y := by
    intro y ⟨P, heq⟩
    subst heq
    exact ⟨L P f₂ α, ⟨P, rfl⟩, L_f_mono hα hf₁ hle⟩
  refine ConditionallyCompleteLattice.csSup_le S₁ (sSup S₂) ?_ ?_
  · exact L_nonempty I f₁ α
  · intro y hy
    specialize hle y hy
    obtain ⟨x, hx, hle⟩ := hle
    refine hle.trans ?_
    refine le_csSup ?_ hx
    exact L_bdd_above hf₂ hα -- ∎

end MultipleFunctions

end Rudin
