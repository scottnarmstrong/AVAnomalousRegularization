-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergyPlane.Fourier.LaplacianProjection
public import AVRegularity.CoupledEnergyPlane.Variational.SourcePrimitiveInitial
import AVRegularity.CoupledEnergyPlane.Variational.FiniteFamilyPrimitive

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Projected diffusion equals the divergence of the full genuine Sobolev gradient. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem bandGradient_planeHk_value (N K : ℕ) (q : PlaneHk Set.univ (K + 1) E) :
    bandGradientOperator (E := E) N (planeHkValueOperator (E := E) (K + 1) q) =
      hilbertProjection (E := PiLp 2 (fun _ : Fin 2 => E)) N
        (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K (planeGradientTensor q)) := by
  have he := congrArg (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K)
    (planeHkCutoff_gradient N K q)
  change planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K
      (planeGradientTensor (hilbertBandHk N (K + 1) (planeHkValueOperator (E := E) (K + 1) q))) =
    planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K
      (hilbertBandHk N K (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K (planeGradientTensor q))) at he
  rw [planeGradientTensor_band_value (E := E) N K] at he
  simpa only [planeHkValueOperator_apply, hilbertBandHk_value,
    AVRegularity.Analysis.Convolution.univToPlane_planeToUniv] using he

theorem bandLaplacian_planeHk_eq_divergence (N K : ℕ) (q : PlaneHk Set.univ (K + 1) E) :
    bandLaplacianOperator (E := E) N (planeHkValueOperator (E := E) (K + 1) q) =
      bandDivergenceOperator (E := E) N
        (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K (planeGradientTensor q)) := by
  rw [bandLaplacian_eq_divergence_gradient, bandGradient_planeHk_value,
    bandDivergence_projection]
end

/-! Actual two-cutoff source pairings reduce to value and gradient carrier tails. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance bandSourcePairingNormed (K : ℕ) : NormedAddCommGroup (PlaneHk Set.univ K E) :=
  inferInstance
local instance bandSourcePairingTensorNormed (K : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance
local instance bandSourcePairingHilbert (K : ℕ) : InnerProductSpace ℝ (PlaneHk Set.univ K E) :=
  inferInstance
local instance bandSourcePairingTensorHilbert (K : ℕ) :
    InnerProductSpace ℝ (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance

local instance bandSourcePairingAdd (K : ℕ) : AddCommGroup (PlaneHk Set.univ K E) := inferInstance
local instance bandSourcePairingTopAdd (K : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ K E) :=
  inferInstance
local instance bandSourcePairingTensorAdd (K : ℕ) :
    AddCommGroup (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance
local instance bandSourcePairingTensorTopAdd (K : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance
local instance bandSourcePairingModule (K : ℕ) : Module ℝ (PlaneHk Set.univ K E) := inferInstance
local instance bandSourcePairingTensorModule (K : ℕ) :
    Module ℝ (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance

theorem planeHkCutoff_truncate (N K L : ℕ) (hKL : K ≤ L)
    (q : PlaneHk Set.univ L E) :
    truncatePlaneHk hKL (planeHkCutoff N L q) =
      planeHkCutoff N K (truncatePlaneHk hKL q) := by
  change truncatePlaneHk hKL (hilbertBandHk N L (planeHkValueOperator L q)) = _
  rw [hilbertBandHk_truncate]
  rfl

theorem planeGradientTensor_cutoff_sub (N M K : ℕ) (w : PlaneHk Set.univ (K + 1) E) :
    planeGradientTensor (planeHkCutoff N (K + 1) w - planeHkCutoff M (K + 1) w) =
      planeHkCutoff N K (planeGradientTensor w) -
        planeHkCutoff M K (planeGradientTensor w) := by
  have hs := (planeGradientTensorOperator (E := E) K).map_sub
    (planeHkCutoff N (K + 1) w) (planeHkCutoff M (K + 1) w)
  simp only [planeGradientTensorOperator_apply] at hs
  rw [planeHkCutoff_gradient, planeHkCutoff_gradient] at hs
  exact hs

theorem planeBandSobolevSource_pairing_to_gradient (N M K : ℕ)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (H : PlaneHk Set.univ K E) (q : PlaneHk Set.univ (K + 1) E) :
    inner ℝ
      ((planeBandDivergenceCLM N K S + planeHkCutoff N K H) -
        (planeBandDivergenceCLM M K S + planeHkCutoff M K H))
      (truncatePlaneHk (Nat.le_succ K) q) =
      inner ℝ (planeHkCutoff N K H - planeHkCutoff M K H)
        (truncatePlaneHk (Nat.le_succ K) q) -
        inner ℝ (planeHkCutoff N K S - planeHkCutoff M K S) (planeGradientTensor q) := by
  have hN := bandDivergence_planeHk_pairing N K S q
  have hM := bandDivergence_planeHk_pairing M K S q
  change inner ℝ (planeBandDivergenceCLM N K S).val
    (truncatePlaneHk (Nat.le_succ K) q).val =
    -inner ℝ (planeHkCutoff N K S).val (planeGradientTensor q).val at hN
  change inner ℝ (planeBandDivergenceCLM M K S).val
    (truncatePlaneHk (Nat.le_succ K) q).val =
    -inner ℝ (planeHkCutoff M K S).val (planeGradientTensor q).val at hM
  change inner ℝ
    (((planeBandDivergenceCLM N K S).val + (planeHkCutoff N K H).val) -
      ((planeBandDivergenceCLM M K S).val + (planeHkCutoff M K H).val))
    (truncatePlaneHk (Nat.le_succ K) q).val =
    inner ℝ ((planeHkCutoff N K H).val - (planeHkCutoff M K H).val)
      (truncatePlaneHk (Nat.le_succ K) q).val -
      inner ℝ ((planeHkCutoff N K S).val - (planeHkCutoff M K S).val)
        (planeGradientTensor q).val
  exact inner_band_source_of_adjoint _ _ _ _ _ _ _ _ hN hM


theorem planeBandSobolevSource_pairing (N M K : ℕ)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (H : PlaneHk Set.univ K E) (w : PlaneHk Set.univ (K + 1) E) :
    inner ℝ
      ((planeBandDivergenceCLM (E := E) N K S + planeHkCutoff (E := E) N K H) -
        (planeBandDivergenceCLM (E := E) M K S + planeHkCutoff (E := E) M K H))
      (planeHkCutoff (E := E) N K (truncatePlaneHk (E := E) (Nat.le_succ K) w) -
        planeHkCutoff (E := E) M K (truncatePlaneHk (E := E) (Nat.le_succ K) w)) =
      inner ℝ (planeHkCutoff (E := E) N K H - planeHkCutoff (E := E) M K H)
        (planeHkCutoff (E := E) N K (truncatePlaneHk (E := E) (Nat.le_succ K) w) -
          planeHkCutoff (E := E) M K (truncatePlaneHk (E := E) (Nat.le_succ K) w)) -
        inner ℝ (planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) N K S - planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) M K S)
          (planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) N K (planeGradientTensor (E := E) w) -
            planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) M K (planeGradientTensor (E := E) w)) := by
  let q : PlaneHk Set.univ (K + 1) E :=
    planeHkCutoff (E := E) N (K + 1) w - planeHkCutoff (E := E) M (K + 1) w
  have hc : truncatePlaneHk (E := E) (Nat.le_succ K) q =
      planeHkCutoff (E := E) N K (truncatePlaneHk (E := E) (Nat.le_succ K) w) -
        planeHkCutoff (E := E) M K (truncatePlaneHk (E := E) (Nat.le_succ K) w) := by
    dsimp only [q]
    rw [map_sub, planeHkCutoff_truncate, planeHkCutoff_truncate]
  have hg : planeGradientTensor (E := E) q =
      planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) N K (planeGradientTensor (E := E) w) -
        planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) M K (planeGradientTensor (E := E) w) := by
    exact planeGradientTensor_cutoff_sub N M K w
  let d : PlaneHk Set.univ K E := (planeBandDivergenceCLM (E := E) N K S + planeHkCutoff (E := E) N K H) -
    (planeBandDivergenceCLM (E := E) M K S + planeHkCutoff (E := E) M K H)
  let h : PlaneHk Set.univ K E := planeHkCutoff (E := E) N K H - planeHkCutoff (E := E) M K H
  let v : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)) := planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) N K S - planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) M K S
  have hp : inner ℝ d (truncatePlaneHk (E := E) (Nat.le_succ K) q) =
      inner ℝ h (truncatePlaneHk (E := E) (Nat.le_succ K) q) - inner ℝ v (planeGradientTensor (E := E) q) :=
    planeBandSobolevSource_pairing_to_gradient N M K S H q
  exact ((congrArg (fun c => inner ℝ d c) hc).symm.trans hp).trans
    (congrArg₂ (fun x y : ℝ => x - y)
      (congrArg (fun c => inner ℝ h c) hc)
      (congrArg (fun g => inner ℝ v g) hg))
end

end AVRegularity.CoupledEnergyPlane.Fourier
end
