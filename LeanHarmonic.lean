import Mathlib.Tactic

import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Set.Basic

--import Mathlib.MeasureTheory.PiSystem

-- structure StandardSimplex (n : ℕ) where
--   V : Fin n → ℝ
--   NonNeg : ∀ i : Fin n, 0 ≤ V i
--   sum_eq_one : (∑ i, V i) = 1

-- structure RyansStruct (r : ℝ) (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E] where
--   S : 
--   on_sphere : ∀ x ∈ S, ‖x‖ = r 
section 
variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure SphericalAngle (F : Type)  [NormedAddCommGroup F] (r : ℝ) where
  A : Set F
  on_sphere : ∀ x ∈ A, ‖x‖ = r

instance : Coe (SA : SphericalAngle E r) (Set E) where
  coe a := a.A

attribute [coe] SphericalAngle.A

open Set

theorem sphericalAngle_on_sphere {r : ℝ} (SA : SphericalAngle E r) : 
    SA.A ⊆ Metric.sphere 0 r := by
  rw [Metric.sphere,subset_def]
  intros x hx
  dsimp
  rw [dist_eq_norm_sub,sub_zero]
  exact SA.on_sphere x hx



