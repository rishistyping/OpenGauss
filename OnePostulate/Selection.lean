/-
Selection layer for phase 1.

This is the thin interface that states the branch-selection conclusions used by
the rest of the development while heavier proofs remain deferred.
-/
import OnePostulate.SpacetimeRepresentation

namespace OnePostulate

noncomputable def preferredBranch (κ : ℝ) : Branch :=
  classifyKappa κ

theorem positive_kappa_selects_lorentz (κ : ℝ) (hκ : 0 < κ) :
    preferredBranch κ = Branch.lorentz := by
  simp [preferredBranch, classifyKappa, hκ]

theorem zero_kappa_selects_galilean :
    preferredBranch 0 = Branch.galilean := by
  simp [preferredBranch, classifyKappa]

theorem negative_kappa_selects_euclidean (κ : ℝ) (hκ : κ < 0) :
    preferredBranch κ = Branch.euclidean := by
  have hnot : ¬ 0 < κ := not_lt.mpr hκ.le
  simp [preferredBranch, classifyKappa, hnot, hκ.ne]

theorem negative_kappa_no_nonzero_null_vectors (κ : ℝ) (hκ : κ < 0) :
    ∀ v : SpacetimeIndex → ℝ,
      v ≠ 0 → dotProduct v (Matrix.mulVec (spacetime_metric κ) v) ≠ 0 := by
  intro v hv
  have hcoords : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 := by
    by_cases h0 : v 0 = 0
    · by_cases h1 : v 1 = 0
      · by_cases h2 : v 2 = 0
        · by_cases h3 : v 3 = 0
          · exfalso
            have hvzero : v = 0 := by
              ext i
              fin_cases i
              · exact h0
              · exact h1
              · exact h2
              · exact h3
            exact hv hvzero
          · exact Or.inr <| Or.inr <| Or.inr h3
        · exact Or.inr <| Or.inr <| Or.inl h2
      · exact Or.inr <| Or.inl h1
    · exact Or.inl h0
  have hform :
      dotProduct v (Matrix.mulVec (spacetime_metric κ) v) =
        κ * (v 0)^2 - (v 1)^2 - (v 2)^2 - (v 3)^2 := by
    simp [spacetime_metric, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  rcases hcoords with h0 | h1 | h2 | h3
  · have hs : 0 < (v 0)^2 := sq_pos_of_ne_zero h0
    have hneg :
        κ * (v 0)^2 - (v 1)^2 - (v 2)^2 - (v 3)^2 < 0 := by
      nlinarith [hκ, hs, sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
    simpa [hform] using ne_of_lt hneg
  · have hs : 0 < (v 1)^2 := sq_pos_of_ne_zero h1
    have hneg :
        κ * (v 0)^2 - (v 1)^2 - (v 2)^2 - (v 3)^2 < 0 := by
      nlinarith [hκ, sq_nonneg (v 0), hs, sq_nonneg (v 2), sq_nonneg (v 3)]
    simpa [hform] using ne_of_lt hneg
  · have hs : 0 < (v 2)^2 := sq_pos_of_ne_zero h2
    have hneg :
        κ * (v 0)^2 - (v 1)^2 - (v 2)^2 - (v 3)^2 < 0 := by
      nlinarith [hκ, sq_nonneg (v 0), sq_nonneg (v 1), hs, sq_nonneg (v 3)]
    simpa [hform] using ne_of_lt hneg
  · have hs : 0 < (v 3)^2 := sq_pos_of_ne_zero h3
    have hneg :
        κ * (v 0)^2 - (v 1)^2 - (v 2)^2 - (v 3)^2 < 0 := by
      nlinarith [hκ, sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2), hs]
    simpa [hform] using ne_of_lt hneg

theorem positive_kappa_gives_finite_real_invariant_speed (κ : ℝ) (hκ : 0 < κ) :
    0 < invariantSpeedSquared κ ∧
      ∃ c : ℝ, 0 < c ∧ c^2 = invariantSpeedSquared κ := by
  have hs : 0 < invariantSpeedSquared κ := by
    rw [invariantSpeedSquared_formula]
    exact inv_pos.mpr hκ
  refine ⟨hs, ?_⟩
  refine ⟨Real.sqrt (invariantSpeedSquared κ), Real.sqrt_pos.mpr hs, ?_⟩
  simpa [pow_two] using (Real.sq_sqrt hs.le)

theorem selection_of_positive_kappa (κ : ℝ) (hκ : 0 < κ) :
    preferredBranch κ = Branch.lorentz ∧
      Matrix.Nondegenerate (velocityMetricMatrix κ) ∧
      Matrix.transpose (lorentzCongruenceMatrix κ) * spacetime_metric κ *
          lorentzCongruenceMatrix κ = Matrix.diagonal ![1, -1, -1, -1] ∧
      0 < invariantSpeedSquared κ ∧
      ∃ c : ℝ, 0 < c ∧ c^2 = invariantSpeedSquared κ := by
  refine ⟨positive_kappa_selects_lorentz κ hκ, ?_, ?_, ?_⟩
  · have hdet : (velocityMetricMatrix κ).det ≠ 0 := by
      rw [killing_restricts_to_metric, Matrix.det_diagonal, Fin.prod_univ_three]
      have hk : (4 * κ : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hκ)
      exact mul_ne_zero (mul_ne_zero hk hk) hk
    exact Matrix.nondegenerate_of_det_ne_zero hdet
  · exact spacetime_metric_congruent_stdLorentz_of_kappa_pos κ hκ
  · exact positive_kappa_gives_finite_real_invariant_speed κ hκ

theorem phase1_selection_summary (κ : ℝ) :
    (κ < 0 →
      preferredBranch κ = Branch.euclidean ∧
        ∀ v : SpacetimeIndex → ℝ,
          v ≠ 0 → dotProduct v (Matrix.mulVec (spacetime_metric κ) v) ≠ 0) ∧
    (κ = 0 →
      preferredBranch κ = Branch.galilean ∧
        ¬ Matrix.Nondegenerate (velocityMetricMatrix 0) ∧
        ¬ Matrix.Nondegenerate (spacetime_metric 0) ∧
        timeLineSubmodule ≠ ⊥ ∧
        timeLineSubmodule ≠ ⊤ ∧
        (∀ i : SpatialIndex, ∀ v : SpacetimeIndex → ℝ, v ∈ timeLineSubmodule →
          Matrix.mulVec (rotMatrix i) v ∈ timeLineSubmodule ∧
            Matrix.mulVec (boostMatrix 0 i) v ∈ timeLineSubmodule)) ∧
    (0 < κ →
      preferredBranch κ = Branch.lorentz ∧
        Matrix.Nondegenerate (velocityMetricMatrix κ) ∧
        Matrix.transpose (lorentzCongruenceMatrix κ) * spacetime_metric κ *
            lorentzCongruenceMatrix κ = Matrix.diagonal ![1, -1, -1, -1] ∧
        0 < invariantSpeedSquared κ ∧
        ∃ c : ℝ, 0 < c ∧ c^2 = invariantSpeedSquared κ) := by
  constructor
  · intro hneg
    exact ⟨negative_kappa_selects_euclidean κ hneg,
      negative_kappa_no_nonzero_null_vectors κ hneg⟩
  constructor
  · intro hzero
    subst hzero
    obtain ⟨hneqBot, hneqTop, hInvariant⟩ := reducible_of_kappa_zero
    have hboostDegenerate : ¬ Matrix.Nondegenerate (velocityMetricMatrix 0) := by
      intro hnondeg
      have hone : (![1, 0, 0] : SpatialIndex → ℝ) ≠ 0 := by
        intro hzero
        have hentry := congrArg (fun v => v 0) hzero
        simp at hentry
      rw [velocityMetricMatrix_at_zero] at hnondeg
      obtain ⟨w, hw⟩ := hnondeg.exists_not_ortho_of_ne_zero hone
      have horth : dotProduct (![1, 0, 0] : SpatialIndex → ℝ)
          (Matrix.mulVec (0 : RealSquareMatrix SpatialDim) w) = 0 := by
        simp [Matrix.mulVec, dotProduct]
      exact hw horth
    exact ⟨zero_kappa_selects_galilean, hboostDegenerate,
      spacetime_metric_degenerate_of_kappa_zero, hneqBot, hneqTop, hInvariant⟩
  · intro hpos
    exact selection_of_positive_kappa κ hpos

theorem positive_branch_is_phase1_target (κ : ℝ) (hκ : 0 < κ) :
    preferredBranch κ = Branch.lorentz := by
  exact positive_kappa_selects_lorentz κ hκ

end OnePostulate
