import Mathlib.Tactic

import Mathlib.Analysis.NormedSpace.Basic

-- definition of EuclideanSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

-- theorem on linear map on R^n
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Topology.MetricSpace.Basic

-- interesting things on scaling balls
import Mathlib.Topology.MetricSpace.Dilation


import Mathlib.Data.Set.Basic

-- check out piiUnionInter: generate a pi system from a collection of sets
import Mathlib.MeasureTheory.PiSystem

noncomputable section 

variable {E : Type _} [NormedAddCommGroup E] 
variable {r : ℝ}


@[ext]
structure PolarSector (F : Type) (r : ℝ) [NormedAddCommGroup F] where
  polar_set : Set F
  on_sphere {x} : x ∈ polar_set → ‖x‖ = r

instance [NormedAddCommGroup F] {r: ℝ}: SetLike (PolarSector F r) F where
  coe := PolarSector.polar_set
  coe_injective' := PolarSector.ext

attribute [coe] PolarSector.polar_set


open Set

theorem PolarSector_on_sphere (PC : PolarSector E r) : ∀ x∈ PC, x∈ Metric.sphere 0 r := by
  intro x hx
  rw [Metric.sphere]
  dsimp
  rw [dist_eq_norm_sub,sub_zero]
  exact PC.on_sphere hx

--theorem PolarSector_on_sphere' (PC : PolarSector E r) : PC ⊆ Metric.sphere (0:E) r := by sorry

theorem PolarSector_on_sphere' (PC : PolarSector E r) : PC.polar_set ⊆ Metric.sphere (0:E) r := by 
  rw [subset_def]
  intro x hx
  exact PolarSector_on_sphere PC x hx



-- variable (n:ℕ )
-- #check EuclideanSpace ℝ (Fin n)
-- #check R 10

-- #check EuclideanSpace ℝ (Fin n)

-- noncomputable example (x : EuclideanSpace ℝ (Fin n)): ℝ := by
--   exact ‖x‖  

-- --example [EuclideanSpace ℝ (Fin n)] : NormedAddCommGroup ((Fin n) → ℝ)
-- #check NormedAddCommGroup ((Fin n)→ℝ )


def S (n:ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 
def R (n:ℕ) := EuclideanSpace ℝ (Fin n)

example {n:ℕ}: NormedSpace ℝ (EuclideanSpace ℝ (Fin n)) := by infer_instance

variable {n:ℕ}

def Φ (n:ℕ): (@Ioi ℝ _ 0) × (S n) → (R n) := fun ⟨ r, x ⟩ =>
  by
  have r' : ℝ := r
  have x' : EuclideanSpace ℝ (Fin n) := x
  exact r'•x'


def PolarCone (PC : PolarSector E r) [NormedAddCommGroup E] [NormedSpace ℝ E] := { x | ∃ (s : ℝ) (y : E), y∈ PC ∧ x = s•y }



end
