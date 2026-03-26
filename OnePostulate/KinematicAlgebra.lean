/-
Phase-1 kinematic algebra scaffolding.

This module packages the chosen spacetime generators as a `κ`-indexed family.
For phase 1, the simplest compileable choice is to use the ambient `4 x 4`
matrix Lie algebra and record the six distinguished generators inside it.
-/
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Data.Fin.VecNotation
import OnePostulate.SpacetimeMatrices

namespace OnePostulate

/-- Phase-1 scaffold: the `κ`-indexed kinematic algebra is represented by the
ambient spacetime matrix Lie algebra. -/
abbrev KinematicAlgebra (_κ : ℝ) := RealSquareMatrix SpacetimeDim

def rotationGenerator (κ : ℝ) (i : SpatialIndex) : KinematicAlgebra κ :=
  rotMatrix i

def boostGenerator (κ : ℝ) (i : SpatialIndex) : KinematicAlgebra κ :=
  boostMatrix κ i

def basisGenerator (κ : ℝ) : BasisTag → KinematicAlgebra κ
  | BasisTag.rotation i => rotationGenerator κ i
  | BasisTag.boost i => boostGenerator κ i

theorem kinematic_bracket_table (κ : ℝ) :
    (∀ i j : SpatialIndex,
        ⁅rotationGenerator κ i, rotationGenerator κ j⁆ =
          ∑ k : SpatialIndex, (leviCivita i j k : ℝ) • rotationGenerator κ k) ∧
    (∀ i j : SpatialIndex,
        ⁅rotationGenerator κ i, boostGenerator κ j⁆ =
          ∑ k : SpatialIndex, (leviCivita i j k : ℝ) • boostGenerator κ k) ∧
    (∀ i j : SpatialIndex,
        ⁅boostGenerator κ i, boostGenerator κ j⁆ =
          ∑ k : SpatialIndex, (-(κ : ℝ) * (leviCivita i j k : ℝ)) • rotationGenerator κ k) := by
  constructor
  · intro i j
    simpa [rotationGenerator, matrixBracket, LieRing.of_associative_ring_bracket] using
      matrix_bracket_JJ i j
  constructor
  · intro i j
    simpa [rotationGenerator, boostGenerator, matrixBracket,
      LieRing.of_associative_ring_bracket] using
      matrix_bracket_JK κ i j
  · intro i j
    simpa [rotationGenerator, boostGenerator, matrixBracket,
      LieRing.of_associative_ring_bracket] using
      matrix_bracket_KK κ i j

theorem kinematic_bracket_jacobi (κ : ℝ) (x y z : KinematicAlgebra κ) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  exact leibniz_lie x y z

def boostCommutatorMatrix (κ : ℝ) : RealSquareMatrix SpatialDim :=
  Matrix.diagonal ![-κ, -κ, -κ]

def adjointTraceModel (κ : ℝ) : RealSquareMatrix AdjointDim :=
  Matrix.diagonal ![-4, -4, -4, 4 * κ, 4 * κ, 4 * κ]

theorem boostCommutator_scales_with_kappa (κ : ℝ) :
    boostCommutatorMatrix κ 0 0 = -κ := by
  simp [boostCommutatorMatrix]

theorem adjointTraceModel_matches_paper_shape (κ : ℝ) :
    adjointTraceModel κ 3 3 = 4 * κ := by
  simp [adjointTraceModel]

end OnePostulate
