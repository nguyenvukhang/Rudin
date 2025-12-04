/-
This file introduces BddOn, which is BddAbove ∧ BddBelow
-/
import Mathlib.Data.Real.Archimedean

universe u v

variable
  {β : Type u}
  {R : Type v}
  {A B : Set β}
  {f g : β → R}

/-- Declares that `f` is bounded on `A`. -/
class BddOn [LE R] (f : β → R) (A : Set β) : Prop where
  below' : BddBelow (f '' A)
  above' : BddAbove (f '' A)

example : f '' A = { f x | x ∈ A } := rfl -- quick reminder.

--------------------------------------------------------------------------------
section Preorder
variable [Preorder R]

theorem BddOn.anti : Antitone fun A ↦ BddOn f A
  := by --
  intro B A h
  have h : f '' B ⊆ f '' A := Set.image_mono h
  intro s
  exact { below' := s.below'.mono h, above' := s.above'.mono h } -- ∎
theorem BddOn.subset (s : BddOn f A) {B : Set β} (h : B ⊆ A) : BddOn f B
  := by --
  exact BddOn.anti h s -- ∎
theorem BddOn.inter_left (hA : BddOn f A) : BddOn f (A ∩ B)
  := by --
  exact BddOn.anti Set.inter_subset_left hA -- ∎
theorem BddOn.inter_right (hB : BddOn f B) : BddOn f (A ∩ B)
  := by --
  exact BddOn.anti Set.inter_subset_right hB -- ∎

end Preorder
--------------------------------------------------------------------------------
section LinearOrder
variable [LinearOrder R]

theorem BddOn.union (hA : BddOn f A) (hB : BddOn f B) : BddOn f (A ∪ B)
  := by --
  exact {
    above' := by
      obtain ⟨m₁, hm₁⟩ := hA.above'
      obtain ⟨m₂, hm₂⟩ := hB.above'
      use m₁ ⊔ m₂
      intro y ⟨x, hx, heq⟩
      subst heq
      rcases hx with hA | hB
      · have : f x ∈ f '' A := Set.mem_image_of_mem f hA
        exact (hm₁ this).trans (le_max_left m₁ m₂)
      · have : f x ∈ f '' B := Set.mem_image_of_mem f hB
        exact (hm₂ this).trans (le_max_right m₁ m₂)
    below' := by
      obtain ⟨m₁, hm₁⟩ := hA.below'
      obtain ⟨m₂, hm₂⟩ := hB.below'
      use m₁ ⊓ m₂
      intro y ⟨x, hx, heq⟩
      subst heq
      rcases hx with hA | hB
      · have : f x ∈ f '' A := Set.mem_image_of_mem f hA
        exact (min_le_left m₁ m₂).trans (hm₁ this)
      · have : f x ∈ f '' B := Set.mem_image_of_mem f hB
        exact (min_le_right m₁ m₂).trans (hm₂ this)
  } -- ∎


end LinearOrder
--------------------------------------------------------------------------------
section AddGroup

variable [AddGroup R]

theorem BddOn.neg [LE R] [AddRightMono R] [AddLeftMono R] (s : BddOn f A) : BddOn (-f) A
  := by --
  obtain ⟨b₀, h₀⟩ := s.below'; obtain ⟨b₁, h₁⟩ := s.above'
  refine { below' := ⟨-b₁, ?_⟩, above' := ⟨-b₀, ?_⟩ }
  · intro y ⟨x, hx, hxy⟩
    subst hxy
    rw [Pi.neg_apply, neg_le_neg_iff]
    exact h₁ (Set.mem_image_of_mem f hx)
  · intro y ⟨x, hx, hxy⟩
    subst hxy
    rw [Pi.neg_apply, neg_le_neg_iff]
    exact h₀ (Set.mem_image_of_mem f hx) -- ∎

theorem BddOn.add [Preorder R] [AddRightMono R] [AddLeftMono R]
  : BddOn f A → BddOn g A → BddOn (f + g) A
  := by --
  intro hf hg
  obtain ⟨bf₀, hf₀⟩ := hf.below'; obtain ⟨bf₁, hf₁⟩ := hf.above'
  obtain ⟨bg₀, hg₀⟩ := hg.below'; obtain ⟨bg₁, hg₁⟩ := hg.above'
  refine { below' := ⟨bf₀ + bg₀, ?_⟩, above' := ⟨bf₁ + bg₁, ?_⟩ }
  · intro y ⟨x, hx, hxy⟩
    subst hxy
    rw [Pi.add_apply]
    have hfx : f x ∈ f '' A := Set.mem_image_of_mem f hx
    have hgx : g x ∈ g '' A := Set.mem_image_of_mem g hx
    exact add_le_add (hf₀ hfx) (hg₀ hgx)
  · intro y ⟨x, hx, hxy⟩
    subst hxy
    rw [Pi.add_apply]
    have hfx : f x ∈ f '' A := Set.mem_image_of_mem f hx
    have hgx : g x ∈ g '' A := Set.mem_image_of_mem g hx
    exact add_le_add (hf₁ hfx) (hg₁ hgx) -- ∎

theorem BddOn.sub [Preorder R] [AddRightMono R] [AddLeftMono R]
  : BddOn f A → BddOn g A → BddOn (f - g) A
  := by --
  rw [sub_eq_add_neg]
  exact (·.add ·.neg) -- ∎

theorem BddOn.abs [Lattice R] [AddLeftMono R] [AddRightMono R] (s : BddOn f A) : BddOn |f| A
  := by --
  obtain ⟨b₀, h₀⟩ := s.below'; obtain ⟨b₁, h₁⟩ := s.above'
  refine { below' := ⟨0, ?_⟩, above' := ⟨max |b₀| |b₁|, ?_⟩ }
  · intro y ⟨x, hx, hxy⟩
    subst hxy
    exact abs_nonneg (f x)
  · intro y ⟨x, hx, hxy⟩
    subst hxy
    have hfx : f x ∈ f '' A := Set.mem_image_of_mem f hx
    specialize h₀ hfx
    specialize h₁ hfx
    rw [<-neg_le_neg_iff] at h₀
    have h₀ : -f x ≤ |b₀| := h₀.trans (neg_le_abs b₀)
    have h₁ : f x ≤ |b₁| := h₁.trans (le_abs_self b₁)
    exact abs_le'.mpr ⟨le_sup_of_le_right h₁, le_sup_of_le_left h₀⟩ -- ∎

theorem BddOn.abs' [Lattice R] [AddLeftMono R] [AddRightMono R]
  {f : β → R} (s : BddOn f A) : ∃ M, ∀ n ∈ A, |f n| ≤ M
  := by --
  let ⟨b, h⟩ := (s.abs).above'
  exact ⟨b, fun _ ↦ (h <| Set.mem_image_of_mem |f| ·)⟩ -- ∎

theorem BddOn.abs_iff [Lattice R] [AddLeftMono R] [AddRightMono R] : BddOn f A ↔ BddOn |f| A
  := by --
  refine ⟨BddOn.abs, ?_⟩
  intro s
  let ⟨b, h⟩ := s.above'
  refine { below' := ⟨-b, ?_⟩, above' := ⟨b, ?_⟩ }
  · intro y ⟨x, hx, hxy⟩
    subst hxy
    have hfx : |f x| ∈ |f| '' A := Set.mem_image_of_mem |f| hx
    specialize h hfx
    rw [<-neg_le_neg_iff] at h
    refine h.trans ?_
    rw [neg_le]
    exact neg_le_abs (f x)
  · intro y ⟨x, hx, hxy⟩
    subst hxy
    have hfx : |f x| ∈ |f| '' A := Set.mem_image_of_mem |f| hx
    exact (h hfx).trans' <| le_abs_self (f x) -- ∎

end AddGroup
--------------------------------------------------------------------------------
section RealValuedFunctions
-- Theorems in here are new and so they probably spawn midway through going
-- through lecture notes or doing homework. Not the best time to generalize.
-- Some are just chilling. And that's okay.

variable {f g : β → ℝ}

theorem BddOn.mul : BddOn f A → BddOn g A → BddOn (f * g) A
  := by --
  intro hf hg
  have h := BddOn.abs_iff (A := A) (β := β) (R := ℝ) (f := f * g)
  rw [BddOn.abs_iff]
  obtain ⟨bf₀, hf₀⟩ := hf.below'; obtain ⟨bf₁, hf₁⟩ := hf.above'
  obtain ⟨bg₀, hg₀⟩ := hg.below'; obtain ⟨bg₁, hg₁⟩ := hg.above'
  refine { below' := ⟨0, ?_⟩, above' := ?_ }
  · intro y ⟨x, hx, hxy⟩
    subst hxy
    exact abs_nonneg ((f * g) x)
  · use max |bf₀| |bf₁| * max |bg₀| |bg₁|
    intro y ⟨x, hx, hxy⟩
    subst hxy
    rw [Pi.abs_apply, Pi.mul_apply]
    have hfx : f x ∈ f '' A := Set.mem_image_of_mem f hx
    have hgx : g x ∈ g '' A := Set.mem_image_of_mem g hx
    specialize hf₀ hfx; specialize hf₁ hfx; specialize hg₀ hgx; specialize hg₁ hgx
    rw [abs_mul (f x) (g x)]
    refine mul_le_mul ?_ ?_ ?_ ?_
    · exact abs_le_max_abs_abs hf₀ hf₁
    · exact abs_le_max_abs_abs hg₀ hg₁
    · exact abs_nonneg (g x)
    · exact le_sup_of_le_left (abs_nonneg bf₀) -- ∎

theorem BddOn.real_iff : BddOn f A ↔ ∃ M, ∀ n ∈ A, |f n| ≤ M
  := by --
  refine ⟨?_, ?_⟩
  · intro s
    obtain ⟨b₀, h₀⟩ := s.below'; obtain ⟨b₁, h₁⟩ := s.above'
    use max |b₀| |b₁|
    intro x hx
    have hfx : f x ∈ f '' A := Set.mem_image_of_mem f hx
    exact abs_le_max_abs_abs (h₀ hfx) (h₁ hfx)
  · intro ⟨M, hM⟩
    refine abs_iff.mpr ?_
    refine { below' := ⟨0, ?_⟩, above' := ?_ }
    · intro y ⟨x, hx, hxy⟩; subst hxy; exact abs_nonneg (f x)
    · refine ⟨M, fun y ⟨x, hx, hxy⟩ ↦ ?_⟩
      subst hxy
      exact hM x hx -- ∎

theorem BddOn.sInf_le_sSup (s : BddOn f A) : sInf (f '' A) ≤ sSup (f '' A)
  := by --
  exact Real.sInf_le_sSup (f '' A) s.below' s.above' -- ∎

end RealValuedFunctions
--------------------------------------------------------------------------------
section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice R] {x : β}

theorem BddOn.le_csSup (s : BddOn f A)
  : x ∈ A → f x ≤ sSup (f '' A)
  := by --
  intro hx
  have hx := Set.mem_image_of_mem f hx
  exact ConditionallyCompleteLattice.le_csSup (f '' A) (f x) s.above' hx -- ∎

theorem BddOn.csInf_le (s : BddOn f A)
  : x ∈ A → sInf (f '' A) ≤ f x
  := by --
  intro hx
  exact ConditionallyCompleteLattice.csInf_le (f '' A) (f x)
    s.below' (Set.mem_image_of_mem f hx) -- ∎

theorem BddOn.csSup_le {ε : R} (s : BddOn f A) (h : sSup (f '' A) ≤ ε)
  : x ∈ A → f x ≤ ε
  := by --
  exact fun hx => (s.le_csSup hx).trans h -- ∎

theorem BddOn.csSup_lt {ε : R} (s : BddOn f A) (h : sSup (f '' A) < ε)
  : x ∈ A → f x < ε
  := by --
  exact fun hx => (s.le_csSup hx).trans_lt h -- ∎

theorem BddOn.csInf_le_csSup (s : BddOn f A) (hA : A.Nonempty) : sInf (f '' A) ≤ sSup (f '' A)
  := by --
  exact _root_.csInf_le_csSup s.below' s.above' (hA.image f) -- ∎

end ConditionallyCompleteLattice
--------------------------------------------------------------------------------
class Bdd [LE R] (f : β → R) : Prop where
  univ' : BddOn f Set.univ

theorem Bdd.exist [AddGroup R] [Lattice R] [AddLeftMono R] [AddRightMono R]
  (s : Bdd f) : ∃ M, ∀ n, |f n| ≤ M
  := by --
  obtain ⟨M, hM⟩ := BddOn.abs' s.univ'
  exact ⟨M, (hM · trivial)⟩ -- ∎
