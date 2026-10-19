-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.SourcePairProjectionLimit
public import AVRegularity.Weighted.PlaneIntervalCoefficients
import AVRegularity.KernelEnergy.TorusMultiplierCLM

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane
open AVRegularity.Analysis.Convolution
open scoped Topology
namespace AVRegularity.Weighted

/-! Actual Bochner Sobolev sources differentiate the original weak time equation at every order. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem plane_ordered_source_increment {K : ℕ} {a b s t : ℝ}
    (U H : ℝ → PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hH : MemLp H 2 (volume.restrict (Set.Icc a b)))
    (hS : MemLp S 2 (volume.restrict (Set.Icc a b)))
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (heq : ∀ Z : PlaneHk Set.univ 1 E,
      inner ℝ (planeHkValueOperator K (U t)) (planeHkValueOperator 1 Z) -
        inner ℝ (planeHkValueOperator K (U s)) (planeHkValueOperator 1 Z) =
      ∫ r in s..t, inner ℝ (planeHkValueOperator K (H r)) (planeHkValueOperator 1 Z) -
        inner ℝ (planeFluxValueOperator K (S r)) (planeH1GradientOperator Z))
    (α : JetIndex2 K) (Z : PlaneHk Set.univ 1 E) :
    inner ℝ (univToPlane ((U t).val α)) (planeHkValueOperator 1 Z) -
      inner ℝ (univToPlane ((U s).val α)) (planeHkValueOperator 1 Z) =
      ∫ r in s..t, planeJetSourcePair α (H r) (S r) Z := by
  have hiH := planeJetReadout_intervalIntegrable H hH α hs ht hst
  have hiS (k : Fin 2) : IntervalIntegrable (fun r => univToPlane
      ((mapPlaneHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S r)).val α)) volume s t := by
    have hm : MemLp (fun r => mapPlaneHk
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S r)) 2
        (volume.restrict (Set.Icc a b)) := by
      have hm := (mapPlaneHkOperator K
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k)).comp_memLp' hS
      have he : (mapPlaneHkOperator K
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k)) ∘ S =
          (fun r => mapPlaneHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S r)) :=
        funext (fun r => mapPlaneHkOperator_apply _ (S r))
      rw [he] at hm
      exact hm
    exact planeJetReadout_intervalIntegrable _ hm α hs ht hst
  have hl := ((tendsto_hilbertProjection (univToPlane ((U t).val α))).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := planeHkValueOperator 1 Z))).sub
      ((tendsto_hilbertProjection (univToPlane ((U s).val α))).inner (𝕜 := ℝ)
        (tendsto_const_nhds (x := planeHkValueOperator 1 Z)))
  have hr := tendsto_planeProjectedJetSourcePair_integral H S α Z hst hiH hiS
  exact tendsto_nhds_unique hl
    (hr.congr (fun N => (plane_ordered_projected_source_increment N U H S s t heq α Z).symm))

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.KernelEnergy
namespace AVRegularity.Weighted

/-! The actual plane `H¹` coefficient multiplier as a continuous linear operator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Multiplication by one fixed coefficient respects addition in the actual Sobolev carrier. -/
theorem planeH1_mulCoefficient_add
    (C : Vec 2 → E →L[ℝ] E) (hC : ContDiff ℝ 1 C)
    (A : Fin 2 → ℝ) (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)
    (u v : PlaneHk Set.univ 1 E) :
    (u + v).mulCoefficient C hC hb = u.mulCoefficient C hC hb + v.mulCoefficient C hC hb := by
  apply PlaneHk.ext_value isOpen_univ
  apply Lp.ext
  filter_upwards [planeMulCoefficient_toFunction_value_ae (u + v) C hC hb,
    planeMulCoefficient_toFunction_value_ae u C hC hb,
    planeMulCoefficient_toFunction_value_ae v C hC hb,
    Lp.coeFn_add (u.val (valueIndex2 1)) (v.val (valueIndex2 1)),
    Lp.coeFn_add ((u.mulCoefficient C hC hb).val (valueIndex2 1))
      ((v.mulCoefficient C hC hb).val (valueIndex2 1))] with x hsum hu hv hi ho
  change ((u + v).mulCoefficient C hC hb).toFunction.jet (valueIndex2 1) x =
    ((u.mulCoefficient C hC hb).val (valueIndex2 1) +
      (v.mulCoefficient C hC hb).val (valueIndex2 1)) x
  rw [hsum, ho]
  change C x ((u.val (valueIndex2 1) + v.val (valueIndex2 1)) x) = _
  rw [hi]
  change C x (u.val (valueIndex2 1) x + v.val (valueIndex2 1) x) =
    (u.mulCoefficient C hC hb).val (valueIndex2 1) x +
      (v.mulCoefficient C hC hb).val (valueIndex2 1) x
  rw [map_add]
  exact congrArg₂ (· + ·) hu.symm hv.symm

/-- Multiplication respects scalar multiplication in the actual Sobolev carrier. -/
theorem planeH1_mulCoefficient_smul
    (C : Vec 2 → E →L[ℝ] E) (hC : ContDiff ℝ 1 C)
    (A : Fin 2 → ℝ) (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)
    (c : ℝ) (u : PlaneHk Set.univ 1 E) :
    (c • u).mulCoefficient C hC hb = c • u.mulCoefficient C hC hb := by
  apply PlaneHk.ext_value isOpen_univ
  apply Lp.ext
  filter_upwards [planeMulCoefficient_toFunction_value_ae (c • u) C hC hb,
    planeMulCoefficient_toFunction_value_ae u C hC hb,
    Lp.coeFn_smul c (u.val (valueIndex2 1)),
    Lp.coeFn_smul c ((u.mulCoefficient C hC hb).val (valueIndex2 1))] with x hsm hu hi ho
  change ((c • u).mulCoefficient C hC hb).toFunction.jet (valueIndex2 1) x =
    (c • (u.mulCoefficient C hC hb).val (valueIndex2 1)) x
  rw [hsm, ho]
  change C x ((c • u.val (valueIndex2 1)) x) = _
  rw [hi]
  change C x (c • u.val (valueIndex2 1) x) =
    c • (u.mulCoefficient C hC hb).val (valueIndex2 1) x
  rw [map_smul]
  exact congrArg (fun e => c • e) hu.symm

/-- The proven coefficient multiplier, with its proven Sobolev norm bound. -/
def planeH1CoefficientOperator
    (C : Vec 2 → E →L[ℝ] E) (hC : ContDiff ℝ 1 C)
    (A : Fin 2 → ℝ) (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) :
    PlaneHk Set.univ 1 E →L[ℝ] PlaneHk Set.univ 1 E :=
  ({ toFun := fun u => u.mulCoefficient C hC hb
     map_add' := planeH1_mulCoefficient_add C hC A hb
     map_smul' := planeH1_mulCoefficient_smul C hC A hb } :
      PlaneHk Set.univ 1 E →ₗ[ℝ] PlaneHk Set.univ 1 E).mkContinuous (A 0 + A 1)
        (planeH1_mulCoefficient_norm_le C hC A hb)

@[simp] theorem planeH1CoefficientOperator_apply
    (C : Vec 2 → E →L[ℝ] E) (hC : ContDiff ℝ 1 C)
    (A : Fin 2 → ℝ) (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)
    (u : PlaneHk Set.univ 1 E) :
    planeH1CoefficientOperator C hC A hb u = u.mulCoefficient C hC hb := rfl

end AVRegularity.Weighted
end
