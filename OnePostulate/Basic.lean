/-
Shared foundational material for the One Postulate development.

This file is intentionally boring: finite-index helpers, basis tags, the
Levi-Civita symbol on `Fin 3`, a couple of tiny permutation utilities, and
shared scalar utilities used by later modules.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

namespace OnePostulate

abbrev SpatialDim : Nat := 3
abbrev SpacetimeDim : Nat := 4
abbrev AdjointDim : Nat := 6

abbrev SpatialIndex := Fin SpatialDim
abbrev SpacetimeIndex := Fin SpacetimeDim
abbrev AdjointIndex := Fin AdjointDim

abbrev RealSquareMatrix (n : Nat) := Matrix (Fin n) (Fin n) ℝ

abbrev ix : SpatialIndex := 0
abbrev iy : SpatialIndex := 1
abbrev iz : SpatialIndex := 2

@[simp] theorem ix_ne_iy : (ix : SpatialIndex) ≠ iy := by
  decide

@[simp] theorem ix_ne_iz : (ix : SpatialIndex) ≠ iz := by
  decide

@[simp] theorem iy_ne_iz : (iy : SpatialIndex) ≠ iz := by
  decide

def cycle : SpatialIndex → SpatialIndex
  | 0 => 1
  | 1 => 2
  | _ => 0

def swap01 : SpatialIndex → SpatialIndex
  | 0 => 1
  | 1 => 0
  | _ => 2

@[simp] theorem cycle_ix : cycle ix = iy := rfl
@[simp] theorem cycle_iy : cycle iy = iz := rfl
@[simp] theorem cycle_iz : cycle iz = ix := rfl

@[simp] theorem swap01_ix : swap01 ix = iy := rfl
@[simp] theorem swap01_iy : swap01 iy = ix := rfl
@[simp] theorem swap01_iz : swap01 iz = iz := rfl

def leviCivita : SpatialIndex → SpatialIndex → SpatialIndex → ℤ
  | 0, 1, 2 => 1
  | 1, 2, 0 => 1
  | 2, 0, 1 => 1
  | 0, 2, 1 => -1
  | 2, 1, 0 => -1
  | 1, 0, 2 => -1
  | _, _, _ => 0

@[simp] theorem leviCivita_ix_iy_iz :
    leviCivita ix iy iz = 1 := rfl

@[simp] theorem leviCivita_ix_iz_iy :
    leviCivita ix iz iy = -1 := rfl

inductive BasisTag where
  | rotation : SpatialIndex → BasisTag
  | boost : SpatialIndex → BasisTag
  deriving DecidableEq, Repr

notation "J[" i "]" => BasisTag.rotation i
notation "K[" i "]" => BasisTag.boost i

inductive Branch where
  | lorentz
  | galilean
  | euclidean
  deriving DecidableEq, Repr

variable (κ : ℝ)

noncomputable def classifyKappa : Branch :=
  if 0 < κ then
    .lorentz
  else if κ = 0 then
    .galilean
  else
    .euclidean

noncomputable def invariantSpeedSquared : ℝ :=
  κ⁻¹

end OnePostulate
