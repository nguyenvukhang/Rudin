import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Stieltjes

import Rudin.Alpha
import Rudin.Partition
import Rudin.Prelude
import Rudin.Lemmas

open Filter Topology
open MeasureTheory

namespace Rudin

-- variable {a b : ℝ} {I : a < b} {f : ℝ → ℝ} {α : StieltjesFunction}
--
-- example :
--   |∫ x in a..b, f x ∂(α.measure)| ≤ ∫ x in a..b, |f x| ∂(α.measure)
--   := intervalIntegral.abs_integral_le_integral_abs I.le
--
-- example : IntervalIntegrable f α.measure a b ↔ RiemannStieltjesIntegrable I f α
--   := by
--   constructor
--   · intro h
--     sorry
--   · intro h
--     sorry
--
-- example (hf : IntervalIntegrable f α.measure a b) :
--   ∫ x in a..b, f x ∂(α.measure) = Uι I f α
--   := by
--   sorry

end Rudin
