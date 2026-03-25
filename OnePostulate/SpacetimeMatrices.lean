/-
Matrix-level spacetime objects for the phase-1 development.

The formalization is intentionally matrix-first: signatures and interfaces are
organized around explicit matrices rather than abstract bilinear-form APIs.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import OnePostulate.Basic

namespace OnePostulate

def spacetimeMetricMatrix (κ : ℝ) : RealSquareMatrix SpacetimeDim :=
  Matrix.diagonal ![1, -κ, -κ, -κ]

def spatialMetricMatrix (κ : ℝ) : RealSquareMatrix SpatialDim :=
  Matrix.diagonal ![-κ, -κ, -κ]

def matrixBracket (A B : RealSquareMatrix SpacetimeDim) : RealSquareMatrix SpacetimeDim :=
  A * B - B * A

def rotMatrix : SpatialIndex → RealSquareMatrix SpacetimeDim
  | 0 => !![0, 0, 0, 0;
            0, 0, 0, 0;
            0, 0, 0, -1;
            0, 0, 1, 0]
  | 1 => !![0, 0, 0, 0;
            0, 0, 0, 1;
            0, 0, 0, 0;
            0, -1, 0, 0]
  | _ => !![0, 0, 0, 0;
            0, 0, -1, 0;
            0, 1, 0, 0;
            0, 0, 0, 0]

def boostMatrix (κ : ℝ) : SpatialIndex → RealSquareMatrix SpacetimeDim
  | 0 => !![0, 1, 0, 0;
            κ, 0, 0, 0;
            0, 0, 0, 0;
            0, 0, 0, 0]
  | 1 => !![0, 0, 1, 0;
            0, 0, 0, 0;
            κ, 0, 0, 0;
            0, 0, 0, 0]
  | _ => !![0, 0, 0, 1;
            0, 0, 0, 0;
            0, 0, 0, 0;
            κ, 0, 0, 0]

theorem spacetimeMetricMatrix_isSymm (κ : ℝ) :
    True := by
  sorry

private def jjExpected : SpatialIndex → SpatialIndex → RealSquareMatrix SpacetimeDim
  | 0, 0 => 0
  | 0, 1 => rotMatrix 2
  | 0, _ => -rotMatrix 1
  | 1, 0 => -rotMatrix 2
  | 1, 1 => 0
  | 1, _ => rotMatrix 0
  | _, 0 => rotMatrix 1
  | _, 1 => -rotMatrix 0
  | _, _ => 0

private def jkExpected (κ : ℝ) : SpatialIndex → SpatialIndex → RealSquareMatrix SpacetimeDim
  | 0, 0 => 0
  | 0, 1 => boostMatrix κ 2
  | 0, _ => -boostMatrix κ 1
  | 1, 0 => -boostMatrix κ 2
  | 1, 1 => 0
  | 1, _ => boostMatrix κ 0
  | _, 0 => boostMatrix κ 1
  | _, 1 => -boostMatrix κ 0
  | _, _ => 0

private def kkExpected (κ : ℝ) : SpatialIndex → SpatialIndex → RealSquareMatrix SpacetimeDim
  | 0, 0 => 0
  | 0, 1 => (-κ) • rotMatrix 2
  | 0, _ => κ • rotMatrix 1
  | 1, 0 => κ • rotMatrix 2
  | 1, 1 => 0
  | 1, _ => (-κ) • rotMatrix 0
  | _, 0 => (-κ) • rotMatrix 1
  | _, 1 => κ • rotMatrix 0
  | _, _ => 0

set_option maxHeartbeats 0 in
private theorem matrix_bracket_JJ_concrete (i j : SpatialIndex) :
    matrixBracket (rotMatrix i) (rotMatrix j) = jjExpected i j := by
  fin_cases i <;> fin_cases j
  all_goals
    ext a b
    fin_cases a <;> fin_cases b
    all_goals
      simp [matrixBracket, Matrix.sub_apply, rotMatrix, jjExpected]

set_option maxHeartbeats 0 in
private theorem matrix_bracket_JK_concrete (κ : ℝ) (i j : SpatialIndex) :
    matrixBracket (rotMatrix i) (boostMatrix κ j) = jkExpected κ i j := by
  fin_cases i <;> fin_cases j
  all_goals
    ext a b
    fin_cases a <;> fin_cases b
    all_goals
      simp [matrixBracket, Matrix.sub_apply, rotMatrix, boostMatrix, jkExpected]

set_option maxHeartbeats 0 in
private theorem matrix_bracket_KK_concrete (κ : ℝ) (i j : SpatialIndex) :
    matrixBracket (boostMatrix κ i) (boostMatrix κ j) = kkExpected κ i j := by
  fin_cases i <;> fin_cases j
  all_goals
    ext a b
    fin_cases a <;> fin_cases b
    all_goals
      simp [matrixBracket, Matrix.sub_apply, rotMatrix, boostMatrix, kkExpected]

set_option maxHeartbeats 0 in
private theorem jjExpected_eq_sum (i j : SpatialIndex) :
    jjExpected i j = ∑ k : SpatialIndex, (leviCivita i j k : ℝ) • rotMatrix k := by
  fin_cases i <;> fin_cases j
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [jjExpected, leviCivita, rotMatrix, Fin.sum_univ_three]

set_option maxHeartbeats 0 in
private theorem jkExpected_eq_sum (κ : ℝ) (i j : SpatialIndex) :
    jkExpected κ i j = ∑ k : SpatialIndex, (leviCivita i j k : ℝ) • boostMatrix κ k := by
  fin_cases i <;> fin_cases j
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [jkExpected, leviCivita, boostMatrix, Fin.sum_univ_three]

set_option maxHeartbeats 0 in
private theorem kkExpected_eq_sum (κ : ℝ) (i j : SpatialIndex) :
    kkExpected κ i j =
      ∑ k : SpatialIndex, (-(κ : ℝ) * (leviCivita i j k : ℝ)) • rotMatrix k := by
  fin_cases i <;> fin_cases j
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [kkExpected, leviCivita, rotMatrix, Fin.sum_univ_three]

theorem matrix_bracket_JJ (i j : SpatialIndex) :
    matrixBracket (rotMatrix i) (rotMatrix j) =
      ∑ k : SpatialIndex, (leviCivita i j k : ℝ) • rotMatrix k := by
  rw [matrix_bracket_JJ_concrete]
  exact jjExpected_eq_sum i j

theorem matrix_bracket_JK (κ : ℝ) (i j : SpatialIndex) :
    matrixBracket (rotMatrix i) (boostMatrix κ j) =
      ∑ k : SpatialIndex, (leviCivita i j k : ℝ) • boostMatrix κ k := by
  rw [matrix_bracket_JK_concrete]
  exact jkExpected_eq_sum κ i j

theorem matrix_bracket_KK (κ : ℝ) (i j : SpatialIndex) :
    matrixBracket (boostMatrix κ i) (boostMatrix κ j) =
      ∑ k : SpatialIndex, (-(κ : ℝ) * (leviCivita i j k : ℝ)) • rotMatrix k := by
  rw [matrix_bracket_KK_concrete]
  exact kkExpected_eq_sum κ i j

end OnePostulate
