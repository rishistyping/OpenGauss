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
  sorry

theorem positive_branch_is_phase1_target (κ : ℝ) (hκ : 0 < κ) :
    preferredBranch κ = Branch.lorentz := by
  exact positive_kappa_selects_lorentz κ hκ

end OnePostulate
