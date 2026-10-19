-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
public import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Actual native coefficient families glue with one fixed component matrix and no pulse-count loss. -/

open CycleComparison.Lift FastJets
section GeneralRadiusAction
variable {ι : Type*} [Fintype ι] {hv : ι → Type*}
  [∀ v, NormedAddCommGroup (hv v)] [∀ v, NormedSpace ℝ (hv v)]

/-- Active pulses glue at arbitrary radii without a pulse-count loss. -/
theorem glued_word_bound_of_data
    {par : ℤ → Fin 2} {tlo thi : ℤ → ℝ} {lam : ℝ}
    {P₀ Q N H : ℕ}
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι hv) (M : ℕ → ι → ι → ℝ)
    (hM : ∀ hh ≤ H, ∀ v u, 0 ≤ M hh v u)
    (kset : Finset ℤ)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ Q)
    (ϖ : ℤ → ℝ → ℝ)
    (c εc τ : ℝ) (hc : c ≠ 0) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (a : ℝ → Vec 2 → ∀ v : ι, hv v)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    {C ρ : ℝ} (hC : 1 ≤ C)
    (hchart : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart j τ))
    (hJ : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (chart j τ) (P₀ + N) C ρ)
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (hlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ (r : ℕ∞) (label j τ))
    (hJlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (label j τ) r C ρ)
    (hw : ∀ j ∈ kset, 0 ≤ ϖ j τ) (hs : ∑ j ∈ kset, ϖ j τ ≤ 1)
    (β : DerivativeWord2 r) (x : Vec 2)
    (hinv : ∀ j ∈ kset, ϖ j τ ≠ 0 → chart j τ (label j τ x) = x)
    (ht : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      c⁻¹ * τ ∈ Set.Icc (tlo j) (thi j))
    (hwindow : ∀ j ∈ kset, ϖ j τ ≠ 0 → tlo j ≤ thi j)
    (data : ∀ (j : ℤ) (hj : j ∈ kset) (hwj : ϖ j τ ≠ 0), ∀ hh ≤ H, ∀ n ≤ N,
      AmbientLiftCoefficientData (par j) (tlo j) (thi j) (hwindow j hj hwj)
        lam n P₀ Q (Cc j hh n) (M hh))
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (v : ι) :
    rs ^ r * ‖orderedDerivative β (fun Y =>
      gluedLift kset ϖ c ρ e εc N H Cc
        chart label a τ Y v) x‖ ≤
      (∑ n ∈ Finset.range (N + 1), nativeChartTransportConstant C (P₀ + N) n r) *
        ∑ u, (∑ hh ∈ Finset.range (H + 1),
          M hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), ρ ^ j *
            ‖iteratedFDeriv ℝ j (fun X => a τ X u) x‖ := by
  classical
  have hclock : c * (c⁻¹ * τ) = τ := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hreg : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ (r : ℕ∞)
      (fun Y => pulsePhysicalLift c ρ e εc N H (Cc j) (chart j) (label j) a τ Y v) := by
    intro j hj hwj
    rw [pulsePhysicalLift_freeze_time, hclock]
    apply pulsePhysicalLift_static_contDiff_of_boxes c ρ e εc N H r (Cc j)
      (chart j τ) (label j τ) (a τ) τ
      (ha.of_le (by exact_mod_cast Nat.add_le_add_right hrP N))
      ((hchart j hj hwj).of_le (by exact_mod_cast Nat.add_le_add_right hrP N)) (hlabel j hj hwj)
    intro hh hhh n hn m hm α v u
    exact ((data j hj hwj hh hhh n hn).mono hrP hrQ).box m hm α v u _ (ht j hj hwj)
  have hB : 0 ≤
      (∑ n ∈ Finset.range (N + 1), nativeChartTransportConstant C (P₀ + N) n r) *
        ∑ u, (∑ hh ∈ Finset.range (H + 1), M hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), ρ ^ j *
            ‖iteratedFDeriv ℝ j (fun X => a τ X u) x‖ := by
    apply mul_nonneg (Finset.sum_nonneg (fun n _ => nativeChartTransportConstant_nonneg hC _ _ _))
    apply Finset.sum_nonneg
    intro u _
    exact mul_nonneg
      (Finset.sum_nonneg (fun hh hhh => hM hh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)) v u))
      (Finset.sum_nonneg (fun j _ => mul_nonneg
        (pow_nonneg (hrs.trans_le (hrse.trans heρ)).le _) (norm_nonneg _)))
  apply gluedLift_spatial_word_norm_le kset ϖ c ρ e εc N H Cc chart label a τ v
    hw hs hreg hrs.le hB β x
  intro j hj hwj
  exact time_pulse_fixed_matrix_word_bound_of_data (Cc j) M hM (data j hj hwj) hlam hlam1
    r hrP hrQ c εc τ hc a ha (chart j) (hchart j hj hwj) hC
    (hJ j hj hwj) hrs hrse heρ (label j) (hlabel j hj hwj) (hJlabel j hj hwj)
    β x (hinv j hj hwj) hεc hεc1 (ht j hj hwj) v

end GeneralRadiusAction

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeStageLiftFamily_glued_word_bound
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ)
    (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (kset : Finset ℤ) (hodd : ∀ j ∈ kset, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c εc τ : ℝ) (hc : c ≠ 0) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    {C : ℝ} (hC : 1 ≤ C)
    (hchart : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart j τ))
    (hJ : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (chart j τ) (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    (hlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ (r : ℕ∞) (label j τ))
    (hJlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (label j τ) r C (liftLength D G.level))
    (hw : ∀ j ∈ kset, 0 ≤ ϖ j τ) (hs : ∑ j ∈ kset, ϖ j τ ≤ 1)
    (β : DerivativeWord2 r) (x : Vec 2)
    (hinv : ∀ j ∈ kset, ϖ j τ ≠ 0 → chart j τ (label j τ x) = x)
    (ht : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    rs ^ r * ‖orderedDerivative β (fun Y =>
      gluedLift kset ϖ c (liftLength D G.level) e εc N H (nativeStageLiftFamily slotLifts)
        chart label a τ Y v) x‖ ≤
      (∑ n ∈ Finset.range (N + 1), nativeChartTransportConstant C (P₀ + N) n r) *
        ∑ u, (∑ hh ∈ Finset.range (H + 1),
          nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), (liftLength D G.level) ^ j *
            ‖iteratedFDeriv ℝ j (fun X => a τ X u) x‖ := by
  classical
  apply glued_word_bound_of_data (par := fun j => EntryWeakProofs.pulseParallel j)
    (nativeStageLiftFamily slotLifts)
    (fun hh v u => nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u)
    (fun hh hhh v u => (nativeSlotLift_uniform_coefficient_data
      (slotLifts ⟨1, by decide⟩) P₀ (hreserve _) hh hhh 0 (Nat.zero_le N)).nonneg v u)
    kset r hrP hrQ ϖ c εc τ hc hεc hεc1 a ha chart label hC hchart hJ
    hrs hrse heρ hlabel hJlabel hw hs β x hinv ht
    (fun j hj _ => (slotLifts ⟨j, hodd j hj⟩).setting.window) _
    (div_nonneg (slotLifts ⟨1, by decide⟩).setting.ρ_pos.le
      (slotLifts ⟨1, by decide⟩).setting.E_pos.le) (slotLifts ⟨1, by decide⟩).setting.lam_le v
  intro j hj hwj hh hhh n hn
  simp only [nativeStageLiftFamily, dite_eq_left (hodd j hj)]
  exact (nativeSlotLift_uniform_coefficient_data
    (slotLifts ⟨j, hodd j hj⟩) P₀ (hreserve _) hh hhh n hn).mono
    (show P₀ ≤ ambientDegreeSlowReserve P₀ (N + (slotLifts ⟨j, hodd j hj⟩).cap) n by
      unfold ambientDegreeSlowReserve; omega)
    (show max k (L + 2) ≤ ambientDegreeFastReserve (max k (L + 2))
        (slotLifts ⟨j, hodd j hj⟩).cap H (N + (slotLifts ⟨j, hodd j hj⟩).cap) hh n by
      unfold ambientDegreeFastReserve; omega)

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

/-! Separate component spatial energies of the actual glued native lift. -/

open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeStageLiftFamily_glued_word_spatial_energy_le
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hS : 0 ≤ S) (P₀ : ℕ)
    (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (kset : Finset ℤ) (hodd : ∀ j ∈ kset, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c εc τ : ℝ) (hc : c ≠ 0) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    {C : ℝ} (hC : 1 ≤ C)
    (hchart : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart j τ))
    (hJ : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (chart j τ) (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    (hlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ (r : ℕ∞) (label j τ))
    (hJlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (label j τ) r C (liftLength D G.level))
    (hw : ∀ j ∈ kset, 0 ≤ ϖ j τ) (hs : ∑ j ∈ kset, ϖ j τ ≤ 1)
    (β : DerivativeWord2 r)
    (hinv : ∀ j ∈ kset, ϖ j τ ≠ 0 → ∀ x, chart j τ (label j τ x) = x)
    (ht : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    (∫⁻ x in AVenhance.unitCube, ENNReal.ofReal ((π v)⁻¹ *
      (rs ^ r * ‖orderedDerivative β (fun Y =>
        gluedLift kset ϖ c (liftLength D G.level) e εc N H (nativeStageLiftFamily slotLifts)
          chart label a τ Y v) x‖) ^ 2)) ≤
      ENNReal.ofReal ((∑ n ∈ Finset.range (N + 1),
        nativeChartTransportConstant C (P₀ + N) n r) ^ 2 *
        (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
          ∑ hh ∈ Finset.range (H + 1), S ^ hh)) *
      ∑ u, ENNReal.ofReal (massConjugatedMatrix π (fun v u =>
        ∑ hh ∈ Finset.range (H + 1),
          nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) v u * (π u)⁻¹) *
        (ENNReal.ofReal (((P₀ + N + 1 : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (P₀ + N + 1), 2 ^ j * (j.factorial : ℝ) ^ 2) *
          classicalFactorialSq (liftLength D G.level) (P₀ + N) (fun X => a τ X u)) := by
  let slotLift := slotLifts ⟨1, by decide⟩
  have hmass := slotLift.setting.mass_pos
  have hmatrix := nativeSlotLift_height_matrix_schur_budget slotLift hS P₀
  have hcomponent (u : CompIn G.comps) :
      ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (fun X => a τ X u) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun v : CompIn G.comps => hr v.1.root) u).contDiff.comp ha
  have hdensity (u : CompIn G.comps) := physical_jet_density_aemeasurable
    (volume.restrict AVenhance.unitCube) (P₀ + N) (liftLength D G.level)
    (fun X => a τ X u) (hcomponent u)
  have hb (x : Vec 2) := nativeStageLiftFamily_glued_word_bound slotLifts P₀ hreserve r hrP hrQ
    kset hodd ϖ c εc τ hc hεc hεc1 a ha chart label hC hchart hJ hrs hrse heρ hlabel hJlabel
    hw hs β x (fun j hj hwj => hinv j hj hwj x) ht v
  have hi := weighted_matrix_row_lintegral_le (volume.restrict AVenhance.unitCube) π hmass _ _ _
    (Finset.sum_nonneg (fun n _ => nativeChartTransportConstant_nonneg hC (P₀ + N) n r))
    hmatrix _ (fun u => (hdensity u).pow_const 2 |>.ennreal_ofReal) v _
    (fun _ => mul_nonneg (pow_nonneg hrs.le r) (norm_nonneg _)) hb
  apply hi.trans
  apply mul_le_mul' le_rfl
  apply Finset.sum_le_sum
  intro u _
  exact mul_le_mul' le_rfl (physical_jet_density_energy_le (P₀ + N)
    slotLift.setting.ρ_pos (fun X => a τ X u) (hcomponent u))

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Separate component spatial energies of the actual glued native lift. -/

open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeStageLiftFamily_glued_factorial_spatial_energy_le
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hS : 0 ≤ S) (P₀ : ℕ)
    (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (kset : Finset ℤ) (hodd : ∀ j ∈ kset, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c εc τ : ℝ) (hc : c ≠ 0) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    {C : ℝ} (hC : 1 ≤ C)
    (hchart : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart j τ))
    (hJ : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (chart j τ) (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    (hlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ (r : ℕ∞) (label j τ))
    (hJlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (label j τ) r C (liftLength D G.level))
    (hw : ∀ j ∈ kset, 0 ≤ ϖ j τ) (hs : ∑ j ∈ kset, ϖ j τ ≤ 1)
    (hinv : ∀ j ∈ kset, ϖ j τ ≠ 0 → ∀ x, chart j τ (label j τ x) = x)
    (ht : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    let Mout := fun v u => ∑ hh ∈ Finset.range (H + 1),
      nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u
    let Cinput := ((P₀ + N + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (P₀ + N + 1), 2 ^ j * (j.factorial : ℝ) ^ 2
    let Cbudget := fun j => ENNReal.ofReal
      ((∑ n ∈ Finset.range (N + 1), nativeChartTransportConstant C (P₀ + N) n j) ^ 2 *
        (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
          ∑ hh ∈ Finset.range (H + 1), S ^ hh))
    let Z := ∑ u, ENNReal.ofReal (massConjugatedMatrix π Mout v u * (π u)⁻¹) *
      (ENNReal.ofReal Cinput * classicalFactorialSq (liftLength D G.level) (P₀ + N) (fun X => a τ X u))
    ENNReal.ofReal (π v)⁻¹ * classicalFactorialSq rs r (fun Y =>
      gluedLift kset ϖ c (liftLength D G.level) e εc N H (nativeStageLiftFamily slotLifts)
        chart label a τ Y v) ≤
      (∑ j ∈ Finset.range (r + 1),
        (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ * (2 : ℝ≥0∞) ^ j * Cbudget j) * Z := by
  intro Mout Cinput Cbudget Z
  rw [weighted_classical_factorial_energy_eq ((slotLifts ⟨1, by decide⟩).setting.mass_pos v)]
  apply factorial_word_energy_sum_le r _ Cbudget Z
  intro j hj w
  exact nativeStageLiftFamily_glued_word_spatial_energy_le slotLifts hS P₀ hreserve j
    (hj.trans hrP) (hj.trans hrQ) kset hodd ϖ c εc τ hc hεc hεc1 a ha chart label hC hchart hJ
    hrs hrse heρ (fun l hl hw => (hlabel l hl hw).of_le (by exact_mod_cast hj))
    (fun l hl hw p hp hpj => hJlabel l hl hw p hp (hpj.trans hj)) hw hs w hinv ht v

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Actual native coefficient families glue with one fixed component matrix and no pulse-count loss. -/

open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeStageLiftFamily_glued_dissipation_word_bound
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ)
    (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hr0 : 1 ≤ r) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (kset : Finset ℤ) (hodd : ∀ j ∈ kset, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c εc τ : ℝ) (hc : c ≠ 0) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    {C : ℝ} (hC : 1 ≤ C)
    (hchart : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart j τ))
    (hJ : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (chart j τ) (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) (hνB : ν ≤ B)
    (hprice : εc = (e / Real.sqrt ν * Real.sqrt B) / liftLength D G.level)
    (hlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ (r : ℕ∞) (label j τ))
    (hJlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (label j τ) r C (liftLength D G.level))
    (hw : ∀ j ∈ kset, 0 ≤ ϖ j τ) (hs : ∑ j ∈ kset, ϖ j τ ≤ 1)
    (β : DerivativeWord2 r) (x : Vec 2)
    (hinv : ∀ j ∈ kset, ϖ j τ ≠ 0 → ∀ Y, chart j τ (label j τ Y) = Y)
    (ht : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    Real.sqrt ν * (rs ^ (r - 1) * ‖orderedDerivative β (fun Y =>
      gluedLift kset ϖ c (liftLength D G.level) e εc N H (nativeStageLiftFamily slotLifts)
        chart label a τ Y v) x‖) ≤
      Real.sqrt B * ((∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
        (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => a τ X v) x‖) + (∑ n ∈ Finset.range N,
        nativeChartTransportConstant C (P₀ + N) (n + 1) r) *
          (∑ u, (∑ hh ∈ Finset.range (H + 1),
            nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
              finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
            ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
              (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => a τ X u) x‖)) := by
  classical
  have hclock : c * (c⁻¹ * τ) = τ := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hreg : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ (r : ℕ∞)
      (fun Y => pulsePhysicalLift c (liftLength D G.level) e εc N H
        (nativeStageLiftFamily slotLifts j) (chart j) (label j) a τ Y v) := by
    intro j hj hwj
    simp only [nativeStageLiftFamily, dite_eq_left (hodd j hj)]
    exact nativeSlotLift_time_pulse_contDiff (slotLifts ⟨j, hodd j hj⟩) P₀
      (hreserve _) r hrP hrQ a (chart j) (label j) c e εc τ
      (by simpa only [hclock] using ha)
      (by simpa only [hclock] using hchart j hj hwj) (hlabel j hj hwj) (ht j hj hwj) v
  have hd (hh : ℕ) (hhh : hh ≤ H) := nativeSlotLift_uniform_coefficient_data
    (slotLifts ⟨1, by decide⟩) P₀ (hreserve _) hh hhh 0 (Nat.zero_le N)
  have hdensity (u : CompIn G.comps) : 0 ≤
      ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
        (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => a τ X u) x‖ :=
    Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (pow_nonneg (slotLifts ⟨1, by decide⟩).setting.ρ_pos.le _) (norm_nonneg _)
  have hout : 0 ≤ Real.sqrt B * ((∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
        (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => a τ X v) x‖) +
      (∑ n ∈ Finset.range N, nativeChartTransportConstant C (P₀ + N) (n + 1) r) *
        (∑ u, (∑ hh ∈ Finset.range (H + 1),
          nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
            (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => a τ X u) x‖)) := by
    apply mul_nonneg (Real.sqrt_nonneg B)
    apply add_nonneg (hdensity v)
    apply mul_nonneg (Finset.sum_nonneg fun n _ => nativeChartTransportConstant_nonneg hC _ _ _)
    exact Finset.sum_nonneg fun u _ => mul_nonneg
      (Finset.sum_nonneg fun hh hhh => (hd hh
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh))).nonneg v u) (hdensity u)
  conv_lhs => rw [← mul_assoc]
  apply gluedLift_weighted_spatial_word_norm_le kset ϖ c (liftLength D G.level) e εc N H
    (nativeStageLiftFamily slotLifts) chart label a τ v hw hs hreg
    (mul_nonneg (Real.sqrt_nonneg ν) (pow_nonneg hrs.le _)) hout β x
  intro j hj hwj
  simp only [nativeStageLiftFamily, dite_eq_left (hodd j hj)]
  have hb := nativeSlotLift_time_pulse_dissipation_word_bound (slotLifts ⟨j, hodd j hj⟩)
    P₀ (hreserve _) r hr0 hrP hrQ c εc τ hc a ha (chart j) (hchart j hj hwj) hC
    (hJ j hj hwj) hrs hrse heρ (label j) (hlabel j hj hwj) (hJlabel j hj hwj)
    β x (hinv j hj hwj) hεc hεc1 hν hB hνB hprice (ht j hj hwj) v
  simpa only [mul_assoc] using hb

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

/-! Every lifted field uses the constructed coefficients on each active native pulse. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G Gr : GenStage D hr Dm bw j₀} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem native_liftedField_value_eq_constructed
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (p Naux sX sZ : ℕ) (η tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    {r : ℕ} (û : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
    (hfield : IsLiftedField G Gr G.level p Naux N H sX sZ η tp tf Y CcT PZ aRep û) :
    ∀ v, ∀ t ∈ Set.Icc tp tf,
      (û v t).toFunction.jet (valueIndex2 r) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => gluedLift (ocObsPulses D.α D.q D.Λ G.level t t)
          (fun j => ocCutoff D.α D.q D.Λ G.level j)
          (D.cellScaleSq G.level) (liftLength D G.level) (D.eps G.level)
          (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) / liftLength D G.level)
          N H (nativeStageLiftFamily slotLifts)
          (fun j s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level j))
          (fun j s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y s') aRep t x v := by
  classical
  intro v t ht
  have hc : 0 < D.cellScaleSq G.level :=
    EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hband G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  apply (hfield.2.2 v t ht).trans
  apply Filter.Eventually.of_forall
  intro x
  refine congrArg (fun f : ∀ w : CompIn G.comps, hr w.1.root => f v) ?_
  apply gluedLift_coeff_congr
  intro j hj hcut hh hhh n _hn m α X z v' u
  have hjodd : Odd j := (Finset.mem_filter.mp hj).2.1
  have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
  have htcell : (D.cellScaleSq G.level)⁻¹ * t ∈
      Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) := by
    rw [inv_mul_eq_div]
    exact ⟨div_le_div_of_nonneg_right htw.1 hc.le,
      div_le_div_of_nonneg_right htw.2 hc.le⟩
  exact nativeStageLiftFamily_coefficients_unique slotLifts sX sZ CcT hfield.1
    j hjodd hh hhh n m α _ htcell X z v' u
end

/-! Actual native coefficient families glue with one fixed component matrix and no pulse-count loss. -/

section
open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeStageLiftFamily_glued_dissipation_spatial_energy_le
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hS : 0 ≤ S) (P₀ : ℕ)
    (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hr0 : 1 ≤ r) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (kset : Finset ℤ) (hodd : ∀ j ∈ kset, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c εc τ : ℝ) (hc : c ≠ 0) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    {C : ℝ} (hC : 1 ≤ C)
    (hchart : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart j τ))
    (hJ : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (chart j τ) (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) (hνB : ν ≤ B)
    (hprice : εc = (e / Real.sqrt ν * Real.sqrt B) / liftLength D G.level)
    (hlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ (r : ℕ∞) (label j τ))
    (hJlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (label j τ) r C (liftLength D G.level))
    (hw : ∀ j ∈ kset, 0 ≤ ϖ j τ) (hs : ∑ j ∈ kset, ϖ j τ ≤ 1)
    (β : DerivativeWord2 r)
    (hinv : ∀ j ∈ kset, ϖ j τ ≠ 0 → ∀ Y, chart j τ (label j τ Y) = Y)
    (ht : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    let Kprice := ∑ n ∈ Finset.range N, nativeChartTransportConstant C (P₀ + N) (n + 1) r
    let Mout := fun v u => ∑ hh ∈ Finset.range (H + 1),
      nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u
    let Aout := fun v u => (if v = u then 1 else 0) + Kprice * Mout v u
    (∫⁻ x in AVenhance.unitCube, ENNReal.ofReal ((π v)⁻¹ *
      (Real.sqrt ν * (rs ^ (r - 1) * ‖orderedDerivative β (fun Y =>
        gluedLift kset ϖ c (liftLength D G.level) e εc N H (nativeStageLiftFamily slotLifts)
          chart label a τ Y v) x‖)) ^ 2)) ≤
      ENNReal.ofReal (B * (1 + Kprice *
        (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
          ∑ hh ∈ Finset.range (H + 1), S ^ hh))) *
      ∑ u, ENNReal.ofReal (massConjugatedMatrix π Aout v u * (π u)⁻¹) *
        (ENNReal.ofReal (((P₀ + N + 1 : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
            2 ^ j * ((j - 1).factorial : ℝ) ^ 2) *
          classicalGradFactorialSq (liftLength D G.level) (P₀ + N - 1) (fun X => a τ X u)) := by
  classical
  intro Kprice Mout Aout
  let slotLift := slotLifts ⟨1, by decide⟩
  have hmass := slotLift.setting.mass_pos
  have hK : 0 ≤ Kprice := Finset.sum_nonneg fun n _ => nativeChartTransportConstant_nonneg hC _ _ _
  have hmatrix := mass_conjugated_identity_add_schur_budget π hmass Mout
    (nativeSlotLift_height_matrix_schur_budget slotLift hS P₀) hK
  have hcomponent (u : CompIn G.comps) :
      ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (fun X => a τ X u) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun v : CompIn G.comps => hr v.1.root) u).contDiff.comp ha
  have hdensity (u : CompIn G.comps) := physical_gradient_density_aemeasurable
    (volume.restrict AVenhance.unitCube) (P₀ + N) (liftLength D G.level)
    (fun X => a τ X u) (hcomponent u)
  have hb (x : Vec 2) := nativeStageLiftFamily_glued_dissipation_word_bound slotLifts P₀ hreserve r hr0 hrP hrQ
    kset hodd ϖ c εc τ hc hεc hεc1 a ha chart label hC hchart hJ hrs hrse heρ
    hν hB hνB hprice hlabel hJlabel hw hs β x hinv ht v
  have hb' (x : Vec 2) : Real.sqrt ν * (rs ^ (r - 1) * ‖orderedDerivative β (fun Y =>
      gluedLift kset ϖ c (liftLength D G.level) e εc N H (nativeStageLiftFamily slotLifts)
        chart label a τ Y v) x‖) ≤
      Real.sqrt B * ∑ u, Aout v u *
        (∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
          (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => a τ X u) x‖) := by
    rw [← identity_add_matrix_action Mout Kprice]
    exact hb x
  have hi := weighted_matrix_row_lintegral_le (volume.restrict AVenhance.unitCube) π hmass Aout _
    (Real.sqrt B) (Real.sqrt_nonneg B) hmatrix _
    (fun u => (hdensity u).pow_const 2 |>.ennreal_ofReal) v _
    (fun _ => mul_nonneg (Real.sqrt_nonneg ν)
      (mul_nonneg (pow_nonneg hrs.le _) (norm_nonneg _))) hb'
  rw [Real.sq_sqrt hB.le] at hi
  apply hi.trans
  apply mul_le_mul' le_rfl
  refine Finset.sum_le_sum fun u _ => ?_
  exact mul_le_mul' le_rfl (physical_gradient_density_energy_le (P₀ + N)
    (hr0.trans (hrP.trans (Nat.le_add_right P₀ N))) slotLift.setting.ρ_pos
    (fun X => a τ X u) (hcomponent u))
end

/-! Actual native coefficient families glue with one fixed component matrix and no pulse-count loss. -/

section
open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeStageLiftFamily_glued_dissipation_spatial_energy_le_of_price_le
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hS : 0 ≤ S) (P₀ : ℕ)
    (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hr0 : 1 ≤ r) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (kset : Finset ℤ) (hodd : ∀ j ∈ kset, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c εc τ : ℝ) (hc : c ≠ 0) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    {C : ℝ} (hC : 1 ≤ C)
    (hchart : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart j τ))
    (hJ : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (chart j τ) (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) (hνB : ν ≤ B)
    (hprice : εc = (e / Real.sqrt ν * Real.sqrt B) / liftLength D G.level)
    (hlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ (r : ℕ∞) (label j τ))
    (hJlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (label j τ) r C (liftLength D G.level))
    (hw : ∀ j ∈ kset, 0 ≤ ϖ j τ) (hs : ∑ j ∈ kset, ϖ j τ ≤ 1)
    (β : DerivativeWord2 r)
    (hinv : ∀ j ∈ kset, ϖ j τ ≠ 0 → ∀ Y, chart j τ (label j τ Y) = Y)
    (ht : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) (Kmax : ℝ)
    (hKprice : (∑ n ∈ Finset.range N, nativeChartTransportConstant C (P₀ + N) (n + 1) r) ≤ Kmax) :
    let Kprice := Kmax
    let Mout := fun v u => ∑ hh ∈ Finset.range (H + 1),
      nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u
    let Aout := fun v u => (if v = u then 1 else 0) + Kprice * Mout v u
    (∫⁻ x in AVenhance.unitCube, ENNReal.ofReal ((π v)⁻¹ *
      (Real.sqrt ν * (rs ^ (r - 1) * ‖orderedDerivative β (fun Y =>
        gluedLift kset ϖ c (liftLength D G.level) e εc N H (nativeStageLiftFamily slotLifts)
          chart label a τ Y v) x‖)) ^ 2)) ≤
      ENNReal.ofReal (B * (1 + Kprice *
        (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
          ∑ hh ∈ Finset.range (H + 1), S ^ hh))) *
      ∑ u, ENNReal.ofReal (massConjugatedMatrix π Aout v u * (π u)⁻¹) *
        (ENNReal.ofReal (((P₀ + N + 1 : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
            2 ^ j * ((j - 1).factorial : ℝ) ^ 2) *
          classicalGradFactorialSq (liftLength D G.level) (P₀ + N - 1) (fun X => a τ X u)) := by
  classical
  intro Kprice Mout Aout
  let slotLift := slotLifts ⟨1, by decide⟩
  have hd (hh : ℕ) (hhh : hh ≤ H) := nativeSlotLift_uniform_coefficient_data
    slotLift P₀ (hreserve _) hh hhh 0 (Nat.zero_le N)
  have hM (v u : CompIn G.comps) : 0 ≤ Mout v u := Finset.sum_nonneg fun hh hhh =>
    (hd hh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh))).nonneg v u
  have hCmat : 0 ≤ nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
      ∑ hh ∈ Finset.range (H + 1), S ^ hh :=
    mul_nonneg (zero_le_one.trans (nativeLiftScalarBudget_ge_one _ _ _ _ _ _ _ _))
      (Finset.sum_nonneg fun _ _ => pow_nonneg hS _)
  have hb := nativeStageLiftFamily_glued_dissipation_spatial_energy_le slotLifts hS P₀ hreserve
    r hr0 hrP hrQ kset hodd ϖ c εc τ hc hεc hεc1 a ha chart label hC hchart hJ hrs hrse heρ
    hν hB hνB hprice hlabel hJlabel hw hs β hinv ht v
  exact hb.trans (identity_plus_matrix_energy_mono π slotLift.setting.mass_pos Mout hM hB.le hCmat hKprice
    (fun u => ENNReal.ofReal (((P₀ + N + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else 2 ^ j * ((j - 1).factorial : ℝ) ^ 2) *
      classicalGradFactorialSq (liftLength D G.level) (P₀ + N - 1) (fun X => a τ X u)) v)
end

end AVRegularity.Construction.Preservation.FullLift
end
