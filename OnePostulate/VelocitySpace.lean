/-
Velocity-space skeleton for phase 1.

This module works only on the boost subspace. The key step is a direct matrix
calculation: a symmetric `3 x 3` form commuting with the rotation action is
forced to be scalar, so the Killing restriction recovers the metric as
`4 * κ * δ`.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import OnePostulate.KillingForm

namespace OnePostulate

abbrev BoostSpan := SpatialIndex → ℝ

def boostRotationAction : SpatialIndex → RealSquareMatrix SpatialDim
  | 0 => !![0, 0, 0;
            0, 0, -1;
            0, 1, 0]
  | 1 => !![0, 0, 1;
            0, 0, 0;
            -1, 0, 0]
  | _ => !![0, -1, 0;
            1, 0, 0;
            0, 0, 0]

def velocityMetricMatrix (κ : ℝ) : RealSquareMatrix SpatialDim :=
  boostKillingBlock κ

def velocityMetricScale (κ : ℝ) : ℝ :=
  4 * κ

set_option maxHeartbeats 0 in
theorem boost_invariant_form_scalar (G : RealSquareMatrix SpatialDim)
    (hSymm : Matrix.IsSymm G)
    (hComm : ∀ i : SpatialIndex, boostRotationAction i * G = G * boostRotationAction i) :
    ∃ c : ℝ, G = Matrix.diagonal ![c, c, c] := by
  have hs10 : G 1 0 = G 0 1 := by
    simpa using (Matrix.IsSymm.apply hSymm 0 1)
  have hs20 : G 2 0 = G 0 2 := by
    simpa using (Matrix.IsSymm.apply hSymm 0 2)
  have hs21 : G 2 1 = G 1 2 := by
    simpa using (Matrix.IsSymm.apply hSymm 1 2)
  have h01 : G 0 1 = 0 := by
    have h := congrArg (fun M => M 0 2) (hComm 0)
    simp [boostRotationAction, Matrix.mul_apply, Fin.sum_univ_three] at h
    linarith
  have h02 : G 0 2 = 0 := by
    have h := congrArg (fun M => M 0 1) (hComm 0)
    simp [boostRotationAction, Matrix.mul_apply, Fin.sum_univ_three] at h
    linarith
  have h10 : G 1 0 = 0 := by
    rw [hs10, h01]
  have h20 : G 2 0 = 0 := by
    rw [hs20, h02]
  have h12 : G 1 2 = 0 := by
    have h := congrArg (fun M => M 1 1) (hComm 0)
    simp [boostRotationAction, Matrix.mul_apply, Fin.sum_univ_three, hs21] at h
    linarith
  have h21 : G 2 1 = 0 := by
    rw [hs21, h12]
  have h22_eq_h11 : G 2 2 = G 1 1 := by
    have h := congrArg (fun M => M 1 2) (hComm 0)
    simp [boostRotationAction, Matrix.mul_apply, Fin.sum_univ_three] at h
    linarith
  have h22_eq_h00 : G 2 2 = G 0 0 := by
    have h := congrArg (fun M => M 0 2) (hComm 1)
    simp [boostRotationAction, Matrix.mul_apply, Fin.sum_univ_three] at h
    linarith
  have h11_eq_h00 : G 1 1 = G 0 0 := by
    linarith
  refine ⟨G 0 0, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.diagonal]
  all_goals
    first
      | exact h01
      | exact h02
      | exact h10
      | exact h11_eq_h00
      | exact h12
      | exact h20
      | exact h21
      | exact h22_eq_h00

theorem killing_restricts_to_metric (κ : ℝ) :
    velocityMetricMatrix κ = Matrix.diagonal ![4 * κ, 4 * κ, 4 * κ] := by
  simpa [velocityMetricMatrix] using boost_killing_form_eq κ

theorem boost_metric_fixed_by_killing_if_kappa_ne_zero
    (κ : ℝ) (_hκ : κ ≠ 0) {G : RealSquareMatrix SpatialDim}
    (hSymm : Matrix.IsSymm G)
    (hComm : ∀ i : SpatialIndex, boostRotationAction i * G = G * boostRotationAction i)
    (hNorm : G 0 0 = 4 * κ) :
    G = velocityMetricMatrix κ := by
  obtain ⟨c, hc⟩ := boost_invariant_form_scalar G hSymm hComm
  have hc_entry : G 0 0 = c := by
    simpa using congrArg (fun M => M 0 0) hc
  have hc_eq : c = 4 * κ := by
    exact hc_entry.symm.trans hNorm
  rw [hc, killing_restricts_to_metric]
  simp [hc_eq]

theorem velocityMetricMatrix_at_zero :
    velocityMetricMatrix 0 = 0 := by
  rw [killing_restricts_to_metric]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem invariantSpeedSquared_formula (κ : ℝ) :
    invariantSpeedSquared κ = κ⁻¹ := by
  rfl

end OnePostulate
