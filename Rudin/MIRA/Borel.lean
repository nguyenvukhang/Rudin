import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

def Z : MeasurableSpace ℝ := borel ℝ

example : ∀ (b : Set ℝ), @MeasurableSet _ (borel ℝ) b → IsOpen b := by
  intro b hb
  sorry
