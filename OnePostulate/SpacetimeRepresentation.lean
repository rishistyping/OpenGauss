/-
Spacetime representation skeleton for phase 1.

This module stays matrix-first. It records the explicit spacetime metric, the
`κ = 0` invariant time line, and the positive-`κ` Lorentzian normal form via an
explicit diagonal congruence.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic
import OnePostulate.SpacetimeMatrices
import OnePostulate.VelocitySpace

namespace OnePostulate

/-- The concrete spacetime metric preserved by the current boost normalization. -/
def spacetime_metric (κ : ℝ) : RealSquareMatrix SpacetimeDim :=
  !![κ, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

def representationMetricMatrix (κ : ℝ) : RealSquareMatrix SpacetimeDim :=
  spacetime_metric κ

def absoluteTimeCovector : SpacetimeIndex → ℝ :=
  ![1, 0, 0, 0]

def timeLineSubmodule : Submodule ℝ (SpacetimeIndex → ℝ) where
  carrier := {v | v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    rcases hv with ⟨hv1, hv2, hv3⟩
    rcases hw with ⟨hw1, hw2, hw3⟩
    exact ⟨by simp [hv1, hw1], by simp [hv2, hw2], by simp [hv3, hw3]⟩
  smul_mem' := by
    intro a v hv
    rcases hv with ⟨hv1, hv2, hv3⟩
    exact ⟨by simp [hv1], by simp [hv2], by simp [hv3]⟩

noncomputable def lorentzCongruenceMatrix (κ : ℝ) : RealSquareMatrix SpacetimeDim :=
  Matrix.diagonal ![1 / Real.sqrt κ, 1, 1, 1]

theorem spacetime_metric_eq_diagonal (κ : ℝ) :
    spacetime_metric κ = Matrix.diagonal ![κ, -1, -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spacetime_metric]

set_option maxHeartbeats 0 in
theorem spacetime_metric_invariant (κ : ℝ) :
    (∀ i : SpatialIndex,
        Matrix.transpose (rotMatrix i) * spacetime_metric κ + spacetime_metric κ * rotMatrix i = 0) ∧
    (∀ i : SpatialIndex,
        Matrix.transpose (boostMatrix κ i) * spacetime_metric κ + spacetime_metric κ * boostMatrix κ i = 0) := by
  constructor
  · intro i
    fin_cases i
    all_goals
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [spacetime_metric, rotMatrix, Matrix.transpose, Matrix.add_apply,
          Matrix.mul_apply, Fin.sum_univ_four]
  · intro i
    fin_cases i
    all_goals
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [spacetime_metric, boostMatrix, Matrix.transpose, Matrix.add_apply,
          Matrix.mul_apply, Fin.sum_univ_four]

theorem reducible_of_kappa_zero :
    timeLineSubmodule ≠ ⊥ ∧ timeLineSubmodule ≠ ⊤ ∧
      (∀ i : SpatialIndex, ∀ v : SpacetimeIndex → ℝ, v ∈ timeLineSubmodule →
        Matrix.mulVec (rotMatrix i) v ∈ timeLineSubmodule ∧
        Matrix.mulVec (boostMatrix 0 i) v ∈ timeLineSubmodule) := by
  constructor
  · intro hbot
    have hmem : absoluteTimeCovector ∈ timeLineSubmodule := by
      simp [absoluteTimeCovector, timeLineSubmodule]
    have hzero : absoluteTimeCovector = 0 := by
      simpa using
        (show absoluteTimeCovector ∈ (⊥ : Submodule ℝ (SpacetimeIndex → ℝ)) from hbot ▸ hmem)
    have hentry := congrArg (fun v => v 0) hzero
    simp [absoluteTimeCovector] at hentry
  constructor
  · intro htop
    have hmem : (![0, 1, 0, 0] : SpacetimeIndex → ℝ) ∈ timeLineSubmodule := by
      exact htop ▸ Submodule.mem_top
    simp [timeLineSubmodule] at hmem
  · intro i v hv
    rcases hv with ⟨hv1, hv2, hv3⟩
    constructor
    · refine ⟨?_, ?_, ?_⟩ <;>
        fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, rotMatrix, hv1, hv2, hv3, Fin.sum_univ_four]
    · refine ⟨?_, ?_, ?_⟩ <;>
        fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, boostMatrix, hv1, hv2, hv3, Fin.sum_univ_four]

theorem spacetime_metric_degenerate_of_kappa_zero :
    ¬ Matrix.Nondegenerate (spacetime_metric 0) := by
  rw [Matrix.nondegenerate_iff_det_ne_zero]
  rw [spacetime_metric_eq_diagonal]
  simp [Matrix.det_diagonal, Fin.prod_univ_four]

set_option maxHeartbeats 0 in
theorem spacetime_metric_congruent_stdLorentz_of_kappa_pos (κ : ℝ) (hκ : 0 < κ) :
    Matrix.transpose (lorentzCongruenceMatrix κ) * spacetime_metric κ * lorentzCongruenceMatrix κ =
      Matrix.diagonal ![1, -1, -1, -1] := by
  have hs : Real.sqrt κ ≠ 0 := Real.sqrt_ne_zero'.mpr hκ
  have hsq : κ = Real.sqrt κ * Real.sqrt κ := by
    symm
    simpa [pow_two] using (Real.sq_sqrt hκ.le)
  have hs1 : (Real.sqrt κ)⁻¹ * Real.sqrt κ = 1 := by
    field_simp [hs]
  have hs2 : Real.sqrt κ * (Real.sqrt κ)⁻¹ = 1 := by
    field_simp [hs]
  have htime : (Real.sqrt κ)⁻¹ * κ * (Real.sqrt κ)⁻¹ = 1 := by
    have hrewrite :
        (Real.sqrt κ)⁻¹ * κ * (Real.sqrt κ)⁻¹ =
          (Real.sqrt κ)⁻¹ * (Real.sqrt κ * Real.sqrt κ) * (Real.sqrt κ)⁻¹ := by
      exact congrArg (fun t => (Real.sqrt κ)⁻¹ * t * (Real.sqrt κ)⁻¹) hsq
    calc
      (Real.sqrt κ)⁻¹ * κ * (Real.sqrt κ)⁻¹
          = (Real.sqrt κ)⁻¹ * (Real.sqrt κ * Real.sqrt κ) * (Real.sqrt κ)⁻¹ := hrewrite
      _ = ((Real.sqrt κ)⁻¹ * Real.sqrt κ) * (Real.sqrt κ * (Real.sqrt κ)⁻¹) := by ring
      _ = 1 := by simp [hs1, hs2]
  rw [lorentzCongruenceMatrix, spacetime_metric_eq_diagonal, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [htime]
  · simp [Matrix.diagonal_apply_ne, hij]

theorem galilean_representation_metric :
    representationMetricMatrix 0 = Matrix.diagonal ![0, -1, -1, -1] := by
  rw [representationMetricMatrix, spacetime_metric_eq_diagonal]

theorem positive_kappa_suggests_lorentzian_behavior (κ : ℝ) (hκ : 0 < κ) :
    True := by
  have _ := spacetime_metric_congruent_stdLorentz_of_kappa_pos κ hκ
  trivial

end OnePostulate
