-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleWords.OcCellMetric
public import AVRegularity.Statements.Intermediate.CycleEvolution.OcCellDrift
import AVRegularity.CycleJoint.PlaneScalarDiffusionDeviationReadout
public import AVRegularity.Statements.Intermediate.CoupledEnergy.DriftCoefficient
import AVRegularity.CycleReference.MeanEnhancementScale
import AVRegularity.CycleWords.NativeScalarErrorChain
public import AVRegularity.Statements.Construction.IsFastProfile

section
public section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Recentring a native cell translates the spatial argument. This keeps the
actual globally spatial cover bounds available at every localized patch. -/

theorem cellCoordinate_recenter (e : ℝ) (he : e ≠ 0) (yc yd z : Vec 2) :
    yc + e • (z + e⁻¹ • (yd - yc)) = yd + e • z := by
  rw [smul_add, smul_smul, mul_inv_cancel₀ he, one_smul]
  abel

theorem ocCellMetric_recenter {α q : ℝ} {Λ m : ℕ}
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (l : ℤ)
    (ν : ℝ) (he : ocEpsilon q Λ m ≠ 0) (yc yd : Vec 2) (t : ℝ) (z : Vec 2) :
    ocCellMetric α q Λ m φ hφ l ν yd t z =
      ocCellMetric α q Λ m φ hφ l ν yc t
        (z + (ocEpsilon q Λ m)⁻¹ • (yd - yc)) := by
  unfold ocCellMetric
  rw [cellCoordinate_recenter _ he]

theorem ocCellDrift_recenter {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (ν : ℝ) (he : ocEpsilon q Λ m ≠ 0) (yc yd : Vec 2) (t : ℝ) (z : Vec 2) :
    ocCellDrift α q Λ ζ m ν yd t z =
      ocCellDrift α q Λ ζ m ν yc t
        (z + (ocEpsilon q Λ m)⁻¹ • (yd - yc)) := by
  unfold ocCellDrift
  rw [cellCoordinate_recenter _ he]

theorem ocCellMetric_iteratedFDeriv_recenter {α q : ℝ} {Λ m : ℕ}
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (l : ℤ)
    (ν : ℝ) (he : ocEpsilon q Λ m ≠ 0) (yc yd : Vec 2) (t : ℝ)
    (n : ℕ) (z : Vec 2) (r c : Fin 2) :
    iteratedFDeriv ℝ n (fun x => ocCellMetric α q Λ m φ hφ l ν yd t x r c) z =
      iteratedFDeriv ℝ n (fun x => ocCellMetric α q Λ m φ hφ l ν yc t x r c)
        (z + (ocEpsilon q Λ m)⁻¹ • (yd - yc)) := by
  simp_rw [ocCellMetric_recenter hφ l ν he yc yd]
  exact iteratedFDeriv_comp_add_right (𝕜 := ℝ)
    (f := fun x : Vec 2 => ocCellMetric α q Λ m φ hφ l ν yc t x r c)
    n ((ocEpsilon q Λ m)⁻¹ • (yd - yc)) z

theorem ocCellDrift_coefficientDerivativeArray_recenter {α q : ℝ} {Λ m : ℕ}
    {ζ : ℝ → ℝ} (ν : ℝ) (he : ocEpsilon q Λ m ≠ 0)
    (yc yd : Vec 2) (t : ℝ) (n : ℕ) (z : Vec 2) :
    coefficientDerivativeArray (driftCoefficient (ocCellDrift α q Λ ζ m ν yd t)) n z =
      coefficientDerivativeArray (driftCoefficient (ocCellDrift α q Λ ζ m ν yc t)) n
        (z + (ocEpsilon q Λ m)⁻¹ • (yd - yc)) := by
  have hh : driftCoefficient (ocCellDrift α q Λ ζ m ν yd t) =
      fun x => driftCoefficient (ocCellDrift α q Λ ζ m ν yc t)
        (x + (ocEpsilon q Λ m)⁻¹ • (yd - yc)) := by
    funext x
    unfold driftCoefficient
    rw [ocCellDrift_recenter ν he yc yd t x]
  rw [hh, coefficientDerivativeArray_comp_translation]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance Set AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Continuous periodic scalar row coefficients have genuine finite spatial multiplier budgets. -/

theorem periodicScalarRow_exists_budget {J : Type*}
    (c : J → Vec 2 → ℝ) (hc : ∀ j, Continuous (c j))
    (hp : ∀ j, IsZ2Periodic (c j)) :
    ∃ M : J → ℝ, (∀ j, 0 ≤ M j) ∧ ∀ j x, |c j x| ≤ M j := by
  have hb (j : J) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |c j x| ≤ M := by
    obtain ⟨M, hM, hbound⟩ := spatial_periodic_bound_on_compact_time
      (fun z : ℝ × Vec 2 => c j z.2) ((hc j).comp continuous_snd)
      (fun _ x n => hp j n x) ({0} : Set ℝ) isCompact_singleton
    exact ⟨M, hM, fun x => by simpa only [Real.norm_eq_abs] using hbound 0 (mem_singleton 0) x⟩
  choose M hM hbound using hb
  exact ⟨M, hM, hbound⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVenhance AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The cell drift remains measurable on a time subtype with every composition argument typed. -/

theorem cellDrift_window_measurable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (yc : Vec 2) (a b : ℝ) :
    Measurable (fun p : Set.Icc a b × Vec 2 => ocCellDrift α q Λ ζ m ν yc p.1 p.2) := by
  have hmap : Measurable (fun p : Set.Icc a b × Vec 2 => ((p.1 : ℝ), p.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hv : Measurable (fun p : ℝ × Vec 2 => ocCellDrift α q Λ ζ m ν yc p.1 p.2) :=
    (cellDrift_joint_contDiff (α := α) (q := q) (m := m) hΛ hζ ν yc).continuous.measurable
  change Measurable ((fun p : ℝ × Vec 2 => ocCellDrift α q Λ ζ m ν yc p.1 p.2) ∘
    (fun p : Set.Icc a b × Vec 2 => ((p.1 : ℝ), p.2)))
  exact hv.comp hmap

end AVRegularity.CycleJointProofs
end
end
