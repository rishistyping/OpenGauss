/-
First classification bridge for the phase-1 matrix development.

This module stays out of the phase-1 import graph. It records the first real
derivation statements connecting the explicit matrix calculations already proved
elsewhere to the Bacry-Levy-Leblond / Ignatowski sign split.
-/

import OnePostulate.Selection

namespace OnePostulate

/- Inputs from the matrix-first phase-1 development. -/

def classificationInputReady (κ : ℝ) : Prop :=
  velocityMetricMatrix κ = Matrix.diagonal ![4 * κ, 4 * κ, 4 * κ] ∧
    spacetime_metric κ = Matrix.diagonal ![κ, -1, -1, -1]

theorem classification_input_ready (κ : ℝ) :
    classificationInputReady κ := by
  exact ⟨killing_restricts_to_metric κ, spacetime_metric_eq_diagonal κ⟩

/- Branch extraction stage. -/

def classificationNegativeBranch (κ : ℝ) : Prop :=
  preferredBranch κ = Branch.euclidean ∧
    ∀ v : SpacetimeIndex → ℝ,
      v ≠ 0 → dotProduct v (Matrix.mulVec (spacetime_metric κ) v) ≠ 0

def classificationZeroBranch : Prop :=
  preferredBranch 0 = Branch.galilean ∧
    ¬ Matrix.Nondegenerate (velocityMetricMatrix 0) ∧
    ¬ Matrix.Nondegenerate (spacetime_metric 0) ∧
    absoluteTimeCovector ∈ timeLineSubmodule ∧
    (∀ i : SpatialIndex,
      Matrix.mulVec (rotMatrix i) absoluteTimeCovector = 0 ∧
        Matrix.mulVec (boostMatrix 0 i) absoluteTimeCovector = 0) ∧
    timeLineSubmodule ≠ ⊥ ∧
    timeLineSubmodule ≠ ⊤

def classificationPositiveBranch (κ : ℝ) : Prop :=
  preferredBranch κ = Branch.lorentz ∧
    Matrix.Nondegenerate (velocityMetricMatrix κ) ∧
    Matrix.transpose (lorentzCongruenceMatrix κ) * spacetime_metric κ *
        lorentzCongruenceMatrix κ = Matrix.diagonal ![1, -1, -1, -1] ∧
    0 < invariantSpeedSquared κ ∧
    ∃ c : ℝ, 0 < c ∧ c^2 = invariantSpeedSquared κ

theorem classification_negative_branch (κ : ℝ) (hκ : κ < 0) :
    classificationNegativeBranch κ := by
  exact (phase1_selection_summary κ).1 hκ

theorem classification_zero_branch :
    classificationZeroBranch := by
  exact (phase1_selection_summary 0).2.1 rfl

theorem classification_positive_branch (κ : ℝ) (hκ : 0 < κ) :
    classificationPositiveBranch κ := by
  exact (phase1_selection_summary κ).2.2 hκ

/- Reduction stage: explicit invariant forms and representation data. -/

def classificationReducesToInvariantForms (κ : ℝ) : Prop :=
  classificationInputReady κ ∧
    (κ < 0 → classificationNegativeBranch κ) ∧
    (κ = 0 → classificationZeroBranch) ∧
    (0 < κ → classificationPositiveBranch κ)

theorem classification_reduces_to_invariant_forms (κ : ℝ) :
    classificationReducesToInvariantForms κ := by
  refine ⟨classification_input_ready κ, ?_, ?_, ?_⟩
  · intro hκ
    exact classification_negative_branch κ hκ
  · intro hκ
    subst hκ
    exact classification_zero_branch
  · intro hκ
    exact classification_positive_branch κ hκ

/- Final phase-1 classification output. -/

def classificationDerivationComplete (κ : ℝ) : Prop :=
  (κ < 0 ∧ classificationNegativeBranch κ) ∨
    (κ = 0 ∧ classificationZeroBranch) ∨
    (0 < κ ∧ classificationPositiveBranch κ)

theorem classification_derivation_complete (κ : ℝ) :
    classificationDerivationComplete κ := by
  rcases lt_trichotomy κ 0 with hneg | hzero | hpos
  · exact Or.inl ⟨hneg, classification_negative_branch κ hneg⟩
  · exact Or.inr <| Or.inl <| by
      subst hzero
      exact ⟨rfl, classification_zero_branch⟩
  · exact Or.inr <| Or.inr ⟨hpos, classification_positive_branch κ hpos⟩

/- Full topological derivation remains deferred. This file only records the
first algebraic bridge from the explicit matrix development to the classical
classification split. -/

end OnePostulate
