import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Archimedean

import Rudin.Defs.Partition

namespace Rudin

variable {a b : ℝ} {I : a < b} (P : Partition I)

section SingleLetterVariables
variable (f α : ℝ → ℝ)

noncomputable def M (i : ℕ) : ℝ := sSup (f '' P.interval i)
noncomputable def m (i : ℕ) : ℝ := sInf (f '' P.interval i)

/-- Upper sum. -/
noncomputable def U : ℝ := ∑ i ∈ Finset.range P.n, M P f i * P.Δ α i
/-- Lower sum. -/
noncomputable def L : ℝ := ∑ i ∈ Finset.range P.n, m P f i * P.Δ α i

end SingleLetterVariables

section Integrals
variable (I : a < b) (f α : ℝ → ℝ)

/-- Upper integral. Infimum of upper sums. -/
noncomputable def Uι : ℝ := sInf { U P f α | P : Partition I }

/-- Lower integral. Supremum of lower sums. -/
noncomputable def Lι : ℝ := sSup { L P f α | P : Partition I }

/-- Is a tag for a partition. -/
def IsTag (t : ℕ → ℝ) : Prop := ∀ i, t i ∈ P.interval i

/-- A function is said to be Riemann-Stieltjes Integrable if its upper integral
is equal to its lower integral. -/
def RiemannStieltjesIntegrable : Prop := Uι I f α = Lι I f α

open Classical in
noncomputable def RiemannStieltjesIntegral : ℝ
  := if RiemannStieltjesIntegrable I f α then Uι I f α else 0

scoped notation "∫" I "," f "d" α:70 => RiemannStieltjesIntegral I f α

open Classical in
lemma RiemannStieltjesIntegral.def_eq :
  ∫ I, f d α = if RiemannStieltjesIntegrable I f α then Uι I f α else 0 := rfl

section RSI
variable (h : RiemannStieltjesIntegrable I f α)

set_option linter.unusedSectionVars false in
include h in
lemma RiemannStieltjesIntegrable.eq_U : ∫ I, f d α = Uι I f α
  := by --
  rw [RiemannStieltjesIntegral.def_eq]
  exact if_pos h -- ∎

include h in
lemma RiemannStieltjesIntegrable.eq_L : ∫ I, f d α = Lι I f α
  := by --
  rw [RiemannStieltjesIntegral.def_eq]
  rw [if_pos h]
  exact h -- ∎

end RSI
end Integrals
end Rudin
