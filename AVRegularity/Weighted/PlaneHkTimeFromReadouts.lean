-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Analysis.Convolution.Kernel.PairedSmoothing
import AVRegularity.Weighted.PlaneH1Readouts

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! Every stored weak jet is a bounded readout and inherits actual time integrability. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeJetReadoutOperator (K : ℕ) (α : JetIndex2 K) :
    PlaneHk Set.univ K E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  univToPlane.toContinuousLinearMap.comp
    ((PiLp.proj (𝕜 := ℝ) 2
      (fun _ : JetIndex2 K => ComponentL2 (volume.restrict Set.univ) E) α).comp
      (planeHkGraph (E := E) Set.univ K).toSubmodule.subtypeL)

@[simp] theorem planeJetReadoutOperator_apply (K : ℕ) (α : JetIndex2 K)
    (U : PlaneHk Set.univ K E) :
    planeJetReadoutOperator K α U = univToPlane (U.val α) := rfl

theorem planeJetReadout_intervalIntegrable {K : ℕ} {a b s t : ℝ}
    (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 (volume.restrict (Set.Icc a b)))
    (α : JetIndex2 K) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    IntervalIntegrable (fun r => univToPlane ((U r).val α)) volume s t := by
  have hm := (planeJetReadoutOperator (E := E) K α).comp_memLp' hU
  apply intervalIntegrable_iff.mpr
  rw [Set.uIoc_of_le hst]
  exact (hm.integrable (by norm_num)).mono_measure
    (Measure.restrict_mono
      (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hs.1 ht.2)) le_rfl)

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! Literal plane L2 readouts characterize time integrability in the weak Sobolev graph. -/

variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [MeasurableSpace T]

theorem planeHk_time_memLp_of_readouts {K : ℕ}
    (μ : Measure T) (u : T → PlaneHk Set.univ K E)
    (hj : ∀ α, MemLp (fun t => planeJetReadoutOperator K α (u t)) 2 μ) : MemLp u 2 μ := by
  apply planeHk_time_memLp_of_jets μ u
  intro α
  have hh := planeToUniv.toContinuousLinearMap.comp_memLp' (hj α)
  change MemLp (fun t => planeToUniv (univToPlane ((u t).val α))) 2 μ at hh
  simpa only [planeToUniv_univToPlane] using hh

end AVRegularity.Weighted
end
