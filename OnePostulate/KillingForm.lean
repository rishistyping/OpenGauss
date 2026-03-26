/-
Phase-1 Killing form skeleton.

This file takes the explicit computational route first. We write down the six
adjoint matrices in the ordered basis `(Jx, Jy, Jz, Kx, Ky, Kz)`, define the
Killing entries using `Matrix.trace`, and only then package the resulting
diagonal form. This keeps a later comparison to Mathlib's abstract
`killingForm` straightforward.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import OnePostulate.KinematicAlgebra

namespace OnePostulate

def adjointBasisTag : AdjointIndex → BasisTag
  | 0 => BasisTag.rotation 0
  | 1 => BasisTag.rotation 1
  | 2 => BasisTag.rotation 2
  | 3 => BasisTag.boost 0
  | 4 => BasisTag.boost 1
  | _ => BasisTag.boost 2

/-- Explicit adjoint matrices for the ordered basis `(Jx, Jy, Jz, Kx, Ky, Kz)`. -/
def adjointMatrix (κ : ℝ) : BasisTag → RealSquareMatrix AdjointDim
  | BasisTag.rotation 0 =>
      !![0, 0, 0, 0, 0, 0;
         0, 0, -1, 0, 0, 0;
         0, 1, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, -1;
         0, 0, 0, 0, 1, 0]
  | BasisTag.rotation 1 =>
      !![0, 0, 1, 0, 0, 0;
         0, 0, 0, 0, 0, 0;
         -1, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 1;
         0, 0, 0, 0, 0, 0;
         0, 0, 0, -1, 0, 0]
  | BasisTag.rotation _ =>
      !![0, -1, 0, 0, 0, 0;
         1, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, -1, 0;
         0, 0, 0, 1, 0, 0;
         0, 0, 0, 0, 0, 0]
  | BasisTag.boost 0 =>
      !![0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, κ;
         0, 0, 0, 0, -κ, 0;
         0, 0, 0, 0, 0, 0;
         0, 0, -1, 0, 0, 0;
         0, 1, 0, 0, 0, 0]
  | BasisTag.boost 1 =>
      !![0, 0, 0, 0, 0, -κ;
         0, 0, 0, 0, 0, 0;
         0, 0, 0, κ, 0, 0;
         0, 0, 1, 0, 0, 0;
         0, 0, 0, 0, 0, 0;
         -1, 0, 0, 0, 0, 0]
  | BasisTag.boost _ =>
      !![0, 0, 0, 0, κ, 0;
         0, 0, 0, -κ, 0, 0;
         0, 0, 0, 0, 0, 0;
         0, -1, 0, 0, 0, 0;
         1, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0]

def killingFormEntry (κ : ℝ) (x y : BasisTag) : ℝ :=
  Matrix.trace (adjointMatrix κ x * adjointMatrix κ y)

def rotationKillingBlock : RealSquareMatrix SpatialDim :=
  fun i j => killingFormEntry 0 (BasisTag.rotation i) (BasisTag.rotation j)

def boostKillingBlock (κ : ℝ) : RealSquareMatrix SpatialDim :=
  fun i j => killingFormEntry κ (BasisTag.boost i) (BasisTag.boost j)

def killingFormMatrix (κ : ℝ) : RealSquareMatrix AdjointDim :=
  fun i j => killingFormEntry κ (adjointBasisTag i) (adjointBasisTag j)

set_option maxHeartbeats 0 in
theorem killing_form_diag (κ : ℝ) :
    killingFormMatrix κ = Matrix.diagonal ![-4, -4, -4, 4 * κ, 4 * κ, 4 * κ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [killingFormMatrix, killingFormEntry, adjointBasisTag, adjointMatrix,
      Matrix.trace, Fin.sum_univ_six] <;>
    ring

set_option maxHeartbeats 0 in
theorem boost_killing_form_eq (κ : ℝ) :
    boostKillingBlock κ = Matrix.diagonal ![4 * κ, 4 * κ, 4 * κ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostKillingBlock, killingFormEntry, adjointMatrix, Matrix.trace, Fin.sum_univ_six] <;>
    ring

theorem boost_killing_nondegenerate_iff_kappa_ne_zero (κ : ℝ) :
    Matrix.Nondegenerate (boostKillingBlock κ) ↔ κ ≠ 0 := by
  rw [Matrix.nondegenerate_iff_det_ne_zero, boost_killing_form_eq, Matrix.det_diagonal,
    Fin.prod_univ_three]
  constructor
  · intro hdet hκ
    apply hdet
    simp [hκ]
  · intro hκ
    have hk : (4 * κ : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hκ
    exact mul_ne_zero (mul_ne_zero hk hk) hk

theorem boostKillingBlock_entry (κ : ℝ) :
    boostKillingBlock κ 0 0 = 4 * κ := by
  exact congrArg (fun M => M 0 0) (boost_killing_form_eq κ)

theorem killingFormMatrix_has_expected_diagonal_shape (κ : ℝ) :
    killingFormMatrix κ = Matrix.diagonal ![-4, -4, -4, 4 * κ, 4 * κ, 4 * κ] := by
  exact killing_form_diag κ

theorem killingFormMatrix_matches_adjoint_trace_model (κ : ℝ) :
    killingFormMatrix κ = adjointTraceModel κ := by
  simpa [adjointTraceModel] using killing_form_diag κ

end OnePostulate
