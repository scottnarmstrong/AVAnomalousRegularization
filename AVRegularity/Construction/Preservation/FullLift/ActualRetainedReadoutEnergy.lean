-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.FullLift.CovarianceTimeMeasurable
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
public import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
public import AVRegularity.CycleComparison.Coarse.Fact.GradFluxIdent
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
public import AVRegularity.EntryWeak.WeakTransferPartitionBudget
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.CycleReference.TorusStreamFluxEquation
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
public import AVRegularity.Definitions.Construction.ResidualOps
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees
import AVRegularity.CycleComparison.Lift.SecondCrossMean
import Mathlib.Algebra.Order.Star.Real

section
section
/-! The incoming invariant supplies both actual record Schur prices, ordinary and marked. -/
@[expose] public section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {law : BirthLaw} {P : ProvParams} {seedK freshK : ℕ → KernelSpec}
  {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {M : ℕ} {k : InvConsts}
  {tA tB S θK : ℝ} {G : GenStage D hr Dm bw j₀}

theorem stage_record_schur_bounds
    (hG : IsStageInvariant law P seedK freshK φ₀ hφ₀ M k tA tB S θK G) :
    (∀ v u, 0 ≤ recordMajorant (G.mass law) G.fam v u) ∧
    (∀ v, ∑ u, recordMajorant (G.mass law) G.fam v u ≤ S) ∧
    (∀ u, ∑ v, recordMajorant (G.mass law) G.fam v u ≤ S) ∧
    (∀ v, ∑ u, G.marker law v / G.marker law u *
      recordMajorant (G.mass law) G.fam v u ≤ S) ∧
    (∀ u, ∑ v, G.marker law v / G.marker law u *
      recordMajorant (G.mass law) G.fam v u ≤ S) := by
  obtain ⟨_, _, _, _, _, _, henv, _⟩ := hG
  have he := henv (fun _ => 0) (fun _ => Nat.zero_le _)
  exact ⟨he.1.nonneg, he.1.row_sum, he.1.col_sum, he.2.row_sum, he.2.col_sum⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Actual enhanced-radius analytic drift smallness at one threshold for every band chain. -/
@[expose] public section
open Homogenization AVenhance Filter Topology
namespace AVRegularity.Construction.Preservation.FullLift

theorem enhanced_scalar_drift_budget {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ cr : ℝ, 0 < cr →
      ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ M : ℕ, ∀ κ : ℕ → ℝ,
        IsOCBandChain α q Λ ζ M κ → ∀ m : ℕ, m₀ ≤ m → m ≤ M →
        let ρ := cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m)
        0 < κ (m - 1) ∧ 0 < ρ ∧
        1024 * ρ / ocEpsilon q Λ (m - 1) ≤ 1 / 2 ∧
        (Buffer.actualDriftJetConstant * ocA α q Λ (m - 1)) * 1024 * ρ ^ 2 ≤
          κ (m - 1) / 8 := by
  obtain ⟨Lr, hLr, hr⟩ := band_enhanced_radius_parent_price hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Lp, _hLp, hp⟩ := Buffer.band_preparation_positivity hα0 hα1 hs0 hs1 hq hζ
  refine ⟨max Lr Lp, hLr.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ cr hcr
  have hΛr := (le_max_left Lr Lp).trans hΛ
  have hΛp := (le_max_right Lr Lp).trans hΛ
  have h128 := hLr.trans hΛr
  obtain ⟨C, _hC, hratio⟩ := hr Λ hΛr cr hcr
  have hc : 0 < ocC α q := by
    simpa only [ocC, Scales.ocC] using
      (Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.2.2.2.2
  have hpow := Buffer.preparation_parent_power_tendsto_zero hq.1 h128 hc
  have hlim : Tendsto (fun m : ℕ => (1024 * C) *
      ocEpsilon q Λ (m - 1) ^ ocC α q) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hpow
  obtain ⟨nr, hnr⟩ := eventually_atTop.1
    (hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  obtain ⟨ns, hns, hstrain⟩ := parent_drift_time_eventually_small hα0 hα1 hs0 hs1 hq h128
    (Buffer.actualDriftJetConstant * 1024 * cr ^ 2)
    (mul_nonneg (mul_nonneg Buffer.actualDriftJetConstant_nonneg (by norm_num)) (sq_nonneg cr))
    (1 / 8) (by norm_num)
  refine ⟨max nr ns, hns.trans (le_max_right _ _), ?_⟩
  intro M κ hκ m hm hmM
  have hm2 := hns.trans ((le_max_right nr ns).trans hm)
  have hpos := hp Λ hΛp M κ hκ m hm2 hmM cr hcr
  refine ⟨hpos.2.1, hpos.2.2, ?_, ?_⟩
  · calc
      _ = 1024 * ((cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m)) /
          ocEpsilon q Λ (m - 1)) := by ring
      _ ≤ 1024 * (C * ocEpsilon q Λ (m - 1) ^ ocC α q) :=
        mul_le_mul_of_nonneg_left (hratio M κ hκ m hm2 hmM) (by norm_num)
      _ ≤ 1 / 2 := by
        simpa only [mul_assoc] using hnr m ((le_max_left nr ns).trans hm)
  · exact enhanced_drift_strain_le_of_price hpos.2.1.le
      (Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) (by omega : 1 ≤ Λ)).le
      (hstrain m ((le_max_right nr ns).trans hm))

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! All-order analytic drift inputs at the actual enhanced radius with a uniform threshold. -/
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

theorem actual_enhanced_drift_budget {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ cr : ℝ, 0 < cr →
      ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ Φ : ℕ → ℝ → Vec 2 → ℝ,
        IsOCStreamSeq α q Λ ζ Φ → ∀ M : ℕ, ∀ κ : ℕ → ℝ,
        IsOCBandChain α q Λ ζ M κ → ∀ m : ℕ, m₀ ≤ m → m ≤ M →
        let ρ := cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m)
        0 < κ (m - 1) ∧ 0 < ρ ∧
        1024 * ρ / ocEpsilon q Λ (m - 1) ≤ 1 / 2 ∧
        (Buffer.actualDriftJetConstant * ocA α q Λ (m - 1)) * 1024 * ρ ^ 2 ≤
          κ (m - 1) / 8 ∧
        ∀ t : ℝ, ∀ j : ℕ, 1 ≤ j → ∀ x : Vec 2,
          ‖coefficientDerivativeArray (driftCoefficient (streamVel (Φ (m - 1)) t)) j x‖ ≤
            (Buffer.actualDriftJetConstant * ocA α q Λ (m - 1)) *
              1024 ^ j * (j.factorial : ℝ) *
                (ocEpsilon q Λ (m - 1)) ^ ((1 : ℤ) - j) := by
  obtain ⟨Λ₀, hΛ₀, hbudget⟩ := enhanced_scalar_drift_budget hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ cr hcr
  obtain ⟨m₀, hm₀, hscalar⟩ := hbudget Λ hΛ cr hcr
  refine ⟨m₀, hm₀, ?_⟩
  intro Φ hΦ M κ hκ m hm hmM
  have hs := hscalar M κ hκ m hm hmM
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, ?_⟩
  intro t j hj x
  exact Buffer.actual_stream_drift_arrays α s hα0 hα1 hs0 hs1 q hq ζ hζ Λ (hΛ₀.trans hΛ)
    Φ hΦ (m - 1) (by omega) t j hj x

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Classical periodic representatives are fixed by their stored value, including their higher jets. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem classicalRep_unique {K r s : ℕ} (W : TorusHk K E) (a b : Vec 2 → E)
    (ha : IsClassicalRep W a r) (hb : IsClassicalRep W b s) : a = b := by
  exact CycleComparison.Lift.periodicContinuous_eq_of_cell_ae a b ha.2.1.continuous
    hb.2.1.continuous ha.2.2.1 hb.2.2.1
    ((classicalRep_value_ae W a ha).symm.trans (classicalRep_value_ae W b hb))

variable [FiniteDimensional ℝ E]

theorem classicalRep_of_value_ae {K r : ℕ} (W V : TorusHk K E) (a : Vec 2 → E)
    (hV : IsClassicalRep V a r)
    (hW : W.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube] a) :
    IsClassicalRep W a r := by
  have he : W = V := KernelEnergy.torusCarrier_eq_of_value_ae W V
    (hW.trans (classicalRep_value_ae V a hV).symm)
  exact he.symm ▸ hV

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Uniform physical flow jets supply the actual inverse-Piola matrix budget. -/
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.FullLift
open EntryWeakProofs CycleJointProofs ChartTransport

theorem uniform_native_piola_matrix_jets (α s q : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ m, M + 1 ≤ m → 0 < D.eps (m - 1) → ∀ slot : ℤ, Odd slot →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ m slot, ∀ a b j, j ≤ N → ∀ x,
        D.eps (m - 1) ^ j * ‖iteratedFDeriv ℝ j
          (fun y => naturalPreparationJacobian (D.hΦ (m - 1)) (D.slotAnchor m slot) t y a b) x‖ ≤ C := by
  let Cflow := weakChartJetBudget (N + 1) 0
  have hCflow : 1 ≤ Cflow := weakChartJetBudget_ge_one _ _
  have hprod : 0 ≤ compConst Cflow N * Cflow :=
    mul_nonneg (compConst_nonneg hCflow N) (zero_le_one.trans hCflow)
  obtain ⟨M, hM, hflow⟩ := uniform_native_physical_flow_jets α s q hα0 hα1 hs0 hs1
    hq Λ hΛ ζ hζ (N + 1)
  refine ⟨1 + compConst Cflow N * Cflow, le_add_of_nonneg_right hprod, M, hM, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq m hm hE slot hslot t ht a b j hj x
  obtain ⟨hback, hfwd⟩ := hflow D hDα hDq hDΛ hDζ hseq m hm slot hslot
    (D.eps (m - 1)) hE (le_refl _) t ht
  have hb : ContDiff ℝ ((N + 1 : ℕ) : ℕ∞)
      (fun y => D.flowOf (m - 1) t y (D.slotAnchor m slot)) :=
    (CycleReference.streamFlow_spatial_smooth (D.hΦ (m - 1)) t
      (D.slotAnchor m slot)).of_le (by simp)
  have hf : ContDiff ℝ (N : ℕ∞)
      (fun y => D.flowOf (m - 1) (D.slotAnchor m slot) y t) :=
    (CycleReference.streamFlow_spatial_smooth (D.hΦ (m - 1))
      (D.slotAnchor m slot) t).of_le (by simp)
  have hh := jacComp_bound hb hf hCflow hE (le_refl _) hback
    (fun p hp hpN => hfwd p hp (hpN.trans (Nat.le_succ N))) a b x j hj
  have hlast : compConst Cflow N * Cflow ≤ 1 + compConst Cflow N * Cflow :=
    le_add_of_nonneg_left zero_le_one
  apply le_trans _ hlast
  simpa only [naturalPreparationJacobian, chartJacobian, jacMatrix, OCData.flowOf] using hh

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Componentwise readout bounds in the exact extended-valued inverse-mass convention. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem readout_component_inverse_mass_le {S S' : Finset Comp} {K : ℕ}
    (m : ℕ) (E η ρ C : ℝ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (π : CompIn S → ℝ) (σ : CompIn S' → ℝ)
    (hπ : ∀ v, 0 < π v) (hσ : ∀ c, 0 < σ c) (v : CompIn S)
    (hentry : ∀ c : CompIn S', compParent m c.1 = v.1 →
      (Real.sqrt (π v))⁻¹ / (Real.sqrt (σ c))⁻¹ *
        E ^ (η * (compWord m c.1).length) ≤ 1)
    (hfiber : ((Finset.univ : Finset (CompIn S')).filter fun c => compParent m c.1 = v.1).card ≤ C)
    (X : ∀ c : CompIn S', TorusHk K (hr c.1.root)) :
    (ENNReal.ofReal (π v))⁻¹ * ENNReal.ofReal (factorialNormSq ρ (succReadout m E η K X v).val) ≤
      ENNReal.ofReal C * ∑ c : CompIn S', if compParent m c.1 = v.1 then
        (ENNReal.ofReal (σ c))⁻¹ * ENNReal.ofReal (factorialNormSq ρ (X c).val) else 0 := by
  have hs := readout_component_factorial_square_le m E η ρ C (Real.sqrt (π v))⁻¹ hE
    (inv_nonneg.mpr (Real.sqrt_nonneg _)) (fun c => (Real.sqrt (σ c))⁻¹)
    (fun c => inv_pos.mpr (Real.sqrt_pos.mpr (hσ c))) v hentry hfiber X
  have hσsqrt : ∀ c, (Real.sqrt (σ c)) ^ 2 = σ c := fun c => Real.sq_sqrt (hσ c).le
  simp only [inv_pow] at hs
  rw [Real.sq_sqrt (hπ v).le] at hs
  simp_rw [hσsqrt] at hs
  exact inverse_mass_parent_bound (fun c : CompIn S' => compParent m c.1) v.1 C (π v)
    (factorialNormSq ρ (succReadout m E η K X v).val) σ
    (fun c => factorialNormSq ρ (X c).val) hC (hπ v) hσ
    (fun c => factorialNormSq_nonneg ρ (X c).val) hs

variable [∀ r, FiniteDimensional ℝ (hr r)]

theorem readout_component_inverse_mass_gradient_le {S S' : Finset Comp} {K : ℕ}
    (m : ℕ) (E η ρ C : ℝ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (π : CompIn S → ℝ) (σ : CompIn S' → ℝ)
    (hπ : ∀ v, 0 < π v) (hσ : ∀ c, 0 < σ c) (v : CompIn S)
    (hentry : ∀ c : CompIn S', compParent m c.1 = v.1 →
      (Real.sqrt (π v))⁻¹ / (Real.sqrt (σ c))⁻¹ *
        E ^ (η * (compWord m c.1).length) ≤ 1)
    (hfiber : ((Finset.univ : Finset (CompIn S')).filter fun c => compParent m c.1 = v.1).card ≤ C)
    (X : ∀ c : CompIn S', TorusHk (K + 1) (hr c.1.root)) :
    (ENNReal.ofReal (π v))⁻¹ * ENNReal.ofReal (gradFactorialNormSq ρ (succReadout m E η (K + 1) X v).val) ≤
      ENNReal.ofReal C * ∑ c : CompIn S', if compParent m c.1 = v.1 then
        (ENNReal.ofReal (σ c))⁻¹ * ENNReal.ofReal (gradFactorialNormSq ρ (X c).val) else 0 := by
  have hs := readout_component_inverse_mass_le (hr := fun r => PiLp 2 (fun _ : Fin 2 => hr r))
    m E η ρ C hE hC π σ hπ hσ v hentry hfiber (fun c => torusGradientTensor (X c))
  rw [← readout_gradient_tensor, torusGradientTensor_factorialNormSq] at hs
  simpa only [torusGradientTensor_factorialNormSq] using hs

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Kernel properties pass through actual source provenance without changing inherited geometry. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem succSource_kernel_property (G : GenStage D hr Dm bw j₀) (P : ProvParams)
    (Q : KernelKey → Prop)
    (hold : ∀ v u (γ : G.fam.Γ v u), Q ((G.prov v u γ).tags P).kernel)
    (hfresh : Q (.fresh (G.level - 1))) (s : SuccSource G) :
    Q ((s.prov G.level).tags P).kernel := by
  have hpath {h : ℕ} (π : StagePath G h) (tw : ProvTags)
      (htw : tw ∈ Prov.pathTags P π.provList) : Q tw.kernel := by
    rw [Providers.CascadeInvariants.pathTags_eq_map] at htw
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp htw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hold _ _ _
  cases s with
  | copyDir _ v u γ => simpa only [SuccSource.prov, Prov.tags] using hold v u γ
  | copyQuad _ _ π =>
    cases hw : widestTags (Prov.pathTags P π.provList) with
    | none => simpa only [SuccSource.prov, Prov.tags, hw] using hfresh
    | some tw =>
      simpa only [SuccSource.prov, Prov.tags, hw] using hpath π tw (widestTags_mem hw)
  | letterDiag _ _ => simpa only [SuccSource.prov, Prov.tags] using hfresh
  | letterMean _ _ _ _ => simpa only [SuccSource.prov, Prov.tags] using hfresh
  | letterCov _ _ _ _ _ _ => simpa only [SuccSource.prov, Prov.tags] using hfresh

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Original kernel properties persist through actual production and the retained cascade. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem actual_successor_kernel_key_property (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm bw j₀) (hactual : IsActualSuccessor D P Mn G G')
    (Q : KernelKey → Prop)
    (hold : ∀ v u (γ : G.fam.Γ v u), Q ((G.prov v u γ).tags P).kernel)
    (hfresh : Q (.fresh (G.level - 1))) :
    ∀ v u (γ : G'.fam.Γ v u), Q ((G'.prov v u γ).tags P).kernel := by
  obtain ⟨_, _, _, _, _, _, e, _Cc, _Cc0, _, _, hall⟩ := hactual
  intro v u γ
  rw [(hall v u γ).1]
  exact succSource_kernel_property G P Q hold hfresh (e v u γ).1

theorem cascade_kernel_key_property (P : ProvParams) (Mn : SuccMenu)
    (seed G : GenStage D hr Dm bw j₀) (hc : IsCascadeStage D P Mn seed G)
    (Q : KernelKey → Prop)
    (hseed : ∀ v u (γ : seed.fam.Γ v u), Q ((seed.prov v u γ).tags P).kernel)
    (m₀ : ℕ) (hfresh : ∀ b, m₀ ≤ b → b < seed.level → Q (.fresh b))
    (hlevel : m₀ ≤ G.level) :
    ∀ v u (γ : G.fam.Γ v u), Q ((G.prov v u γ).tags P).kernel := by
  induction hc with
  | seed => exact hseed
  | @step G G' hc hactual ih =>
    have hlevel' : m₀ ≤ G'.level := hlevel
    have hGlevel : G'.level = G.level - 1 := hactual.2.1
    have hOld := ih (by omega : m₀ ≤ G.level)
    have hFresh : Q (.fresh (G.level - 1)) := hfresh _ (by omega) (by
      have hseedlevel := Providers.CascadeInvariants.level_le_of_cascade hc
      have hpos := hactual.1
      omega)
    have hnext := actual_successor_kernel_key_property P Mn G G' hactual Q hOld hFresh
    intro v u γ
    exact hnext ⟨v.1, Finset.mem_of_mem_filter _ v.2⟩ ⟨u.1, Finset.mem_of_mem_filter _ u.2⟩ γ

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The successor birth law has exactly the positive exponents and bounded birth prefactor
needed by the ordinary and marked readout estimates. -/
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

theorem successor_eta0_pos {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3)
    (hs0 : 0 < s) (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) :
    0 < succEta0 α q s := by
  have hf := Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  have hmu : 0 < ocMuS α q s := hf.2.2.1
  exact lt_min (div_pos hf.2.1 (by norm_num)) (div_pos hmu (by norm_num))

theorem successor_readout_law_facts {α q s : ℝ} {Tw : ℕ} {law : BirthLaw}
    (hη : 0 < succEta0 α q s) (hlaw : IsSuccessorLaw α q s Tw law) :
    law.cH ≤ 1 ∧ 0 ≤ law.etaB ∧ 0 ≤ law.eta0 ∧ 0 ≤ law.iota := by
  obtain ⟨h0, hB, hi, hc, _hcount⟩ := hlaw
  have hpow : 0 ≤ (128 : ℝ) ^ (-(succEta0 α q s / 2)) := Real.rpow_nonneg (by norm_num) _
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · rw [hB]
    exact (div_pos hη (by norm_num)).le
  · rw [h0]
    exact hη.le
  · rw [hi]
    exact (div_pos hη (by norm_num)).le

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! A classical covariance representative is independent of both carrier and representative choices. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem classical_covImage_rep_unique {K L r s : ℕ}
    (P : (Vec 2 → E) → Vec 2 → E) (Z : TorusHk K E) (W V : TorusHk L E)
    (hW : IsCovImage P Z W) (hV : IsCovImage P Z V)
    (a b : Vec 2 → E) (ha : IsClassicalRep W a r) (hb : IsClassicalRep V b s) : a = b := by
  have he : W = V := covImage_unique P Z W V hW hV
  exact classicalRep_unique W a b ha (he.symm ▸ hb)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The quantitative schedule pays the higher intermediate solution used for classical traces. -/
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

variable {α q s Q σ₀ a σ σf lamC : ℝ}
  {D₀ H J N p nk Lc Lf Lpr Acl Naux Nout : ℕ}

theorem successor_schedule_p_ge_five
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hQ : 0 < Q)
    (hsched : IsSuccessorSchedule α q s Q σ₀ a σ σf lamC
      D₀ H J N p nk Lc Lf Lpr Acl Naux Nout) : 5 ≤ p := by
  have hf := Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  have hd := hf.2.1
  have hg := hf.1
  have hdu := ocDelta_lt_one hα0.le hq.1
  have hprice : Q + q * ocGamma α q + 4 < ocDelta α q * (p : ℝ) := hsched.2.2.2.1
  by_contra hp
  have hpR : (p : ℝ) ≤ 4 := by exact_mod_cast (by omega : p ≤ 4)
  have hupper := mul_le_mul_of_nonneg_left hpR hd.le
  have hqg : 0 ≤ q * ocGamma α q := mul_nonneg (lt_trans zero_lt_one hq.1).le hg.le
  linarith only [hQ, hqg, hdu, hprice, hupper]

theorem successor_higher_preparation_classical_reserve
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hQ : 0 < Q)
    (hsched : IsSuccessorSchedule α q s Q σ₀ a σ σf lamC
      D₀ H J N p nk Lc Lf Lpr Acl Naux Nout) : Naux + 2 + 2 * p + 4 ≤ Nout := by
  have hp := successor_schedule_p_ge_five hα0 hα1 hs0 hs1 hq hQ hsched
  have halloc : Naux + 4 * p ≤ Nout := hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  omega

theorem successor_lift_gradient_trace_reserve
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hQ : 0 < Q)
    (hsched : IsSuccessorSchedule α q s Q σ₀ a σ σf lamC
      D₀ H J N p nk Lc Lf Lpr Acl Naux Nout) : Naux + 3 + 2 * p + 2 ≤ Nout := by
  have h := successor_higher_preparation_classical_reserve hα0 hα1 hs0 hs1 hq hQ hsched
  omega

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Reuse the compiled covariance adjoint bound for every actual duality-defined covariance image. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open CycleComparison.Coarse
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem covImage_covPolyP_factorial_le {K p : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Z : TorusHk (K + 2 * p) E) (W : TorusHk K E)
    (hW : IsCovImage (covPolyP Hc p) Z W) :
    factorialNormSq ρ W.val ≤
      covPolyConst (fbCovConst ρ Hc (K + 2 * p)) p ^ 2 * factorialNormSq ρ Z.val := by
  let A := TorusAdj.covPolyP (E := E) Hc le_rfl p 0 (K + 2 * p)
  have hA : IsCovImage (covPolyP Hc p) Z (A.adj K le_rfl Z) := by
    intro ψ hψ hp
    exact A.ident K le_rfl Z ψ (hψ.of_le (by exact_mod_cast le_top)) hp
  have he : W = A.adj K le_rfl Z := covImage_unique (covPolyP Hc p) Z W _ hW hA
  have hb := (TorusAdj.FBound.covPolyP (E := E) hρ Hc le_rfl p 0 (K + 2 * p)) K le_rfl Z
  rw [← he] at hb
  calc
    _ = (Real.sqrt (factorialNormSq ρ W.val)) ^ 2 :=
      (Real.sq_sqrt (factorialNormSq_nonneg _ _)).symm
    _ ≤ (covPolyConst (fbCovConst ρ Hc (K + 2 * p)) p *
        Real.sqrt (factorialNormSq ρ Z.val)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt (factorialNormSq_nonneg _ _)]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The existing quiet margin covariance estimate is quadratic in the literal native lift length. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift
open CycleComparison.Coarse

theorem native_covariance_entry_radius_bound (D : OCData) (m : ℕ) (t C : ℝ)
    (hΛ : 1 ≤ D.Λ) (hC : 0 ≤ C) (hB : 0 ≤ D.κ (m - 1))
    (hentry : ∀ i j, |covPrimitive D m t i j| ≤
      C * D.κ (m - 1) * ocTauP D.α D.q D.Λ m) :
    ∀ i j, |covPrimitive D m t i j| ≤ C * liftLength D m ^ 2 := by
  have hP : 0 ≤ ocTauP D.α D.q D.Λ m :=
    (Construction.Stream.ocTau_pos hΛ).le.trans
      (CycleReference.pulse_time_scale_relations hΛ).1
  have htime : ocTauP D.α D.q D.Λ m ≤ ocTauPP D.α D.q D.Λ m := by
    have ht := (CycleReference.pulse_time_scale_relations (α := D.α) (q := D.q) (m := m) hΛ).2
    linarith only [ht, hP]
  have hPP : 0 ≤ D.κ (m - 1) * ocTauPP D.α D.q D.Λ m :=
    mul_nonneg hB (hP.trans htime)
  intro i j
  calc
    _ ≤ C * D.κ (m - 1) * ocTauP D.α D.q D.Λ m := hentry i j
    _ ≤ C * D.κ (m - 1) * ocTauPP D.α D.q D.Λ m :=
      mul_le_mul_of_nonneg_left htime (mul_nonneg hC hB)
    _ = C * liftLength D m ^ 2 := by
      rw [liftLength, Real.sq_sqrt hPP, mul_assoc]

theorem native_covariance_polynomial_price (D : OCData) (m K p : ℕ) (t C : ℝ)
    (hΛ : 1 ≤ D.Λ) (hC : 0 ≤ C) (hB : 0 ≤ D.κ (m - 1))
    (hρ : 0 < liftLength D m)
    (hentry : ∀ i j, |covPrimitive D m t i j| ≤
      C * D.κ (m - 1) * ocTauP D.α D.q D.Λ m) :
    covPolyConst (fbCovConst (liftLength D m) (covPrimitive D m t) K) p ≤
      covPolyConst (4 * C * (K : ℝ) ^ 2) p :=
  covPolyConst_le_of_radius_entries hρ _ C K p
    (native_covariance_entry_radius_bound D m t C hΛ hC hB hentry)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The effective window setting supplies inverse uniqueness for the original-cap recurrence.

Copy-adapt of CycleComparison.Lift.LiftSequenceUniquenessStep and LiftSequenceUniqueness:
only the metric and drift of the setting enter inverse uniqueness, and restriction leaves them unchanged. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D Ksrc H N K k L qs qf : ℕ} {hKD : Ksrc ≤ D} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting
    (EntryWeakProofs.restrictLiftData Ksrc hKD {Q with edge := windowEdges a b Q.edge})
    π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem effective_liftSequence_positive_coefficients_unique_of_predecessors
    (sX sZ sX' sZ' : ℕ) (Cc Dc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hd : IsLiftSequence Q sX' sZ' a b N H Dc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m (α : DerivativeWord2 m) t, t ∈ Set.Icc a b → ∀ X z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u)
    (m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (X z : Vec 2) (v u : ι) : Cc hh n m α t X z v u = Dc hh n m α t X z v u := by
  classical
  by_cases hmn : n < m
  · rw [hc.2.2.2.1 hh hhh n m hmn, hd.2.2.2.1 hh hhh n m hmn]
  · apply symmetric_lift_coefficient_eq_of_operator_eq n m (by omega)
      (Cc hh n) (Dc hh n) (hc.2.2.2.2.1 hh hhh n m) (hd.2.2.2.2.1 hh hhh n m)
      t X z v u
    intro a₀ ha₀
    have hC := hc.2.2.2.2.2.2 hh hhh n hn hnN a₀ ha₀ X
    have hD := hd.2.2.2.2.2.2 hh hhh n hn hnN a₀ ha₀ X
    have hhEq := setting_cellFieldInverse_unique P X sZ sZ' (fun _ => 0)
      (fun r y => liftCellSource Q Cc (fun _ => a₀) hh n r X y)
      (fun r y => liftCellSource Q Dc (fun _ => a₀) hh n r X y)
      (fun r y => liftApply n (Cc hh n) (fun _ => a₀) r X y)
      (fun r y => liftApply n (Dc hh n) (fun _ => a₀) r X y) hC hD (by
        intro r hr
        have hs := liftCellSource_congr_predecessors Q Cc Dc (fun _ => a₀) hh n hn r
          (fun p q hpq m β Y y w j => he p q hpq m β r hr Y y w j)
        exact congrFun hs X)
    exact congrFun (congrFun (hhEq t ht) z) v


include P in
theorem effective_liftSequence_coefficients_unique (sX sZ sX' sZ' : ℕ)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hd : IsLiftSequence Q sX' sZ' a b N H Dc) :
    ∀ hh, hh ≤ H → ∀ n m (α : DerivativeWord2 m) t, t ∈ Set.Icc a b → ∀ X z v u,
      Cc hh n m α t X z v u = Dc hh n m α t X z v u := by
  intro hh
  induction hh using Nat.strong_induction_on with
  | h hh ih =>
    intro hhh n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      by_cases hnN : N < n
      · intro m α t _ X z v u
        rw [hc.2.2.1 hh hhh n hnN, hd.2.2.1 hh hhh n hnN]
      · by_cases hn0 : n = 0
        · subst n
          exact liftSequence_zero_degree_coefficients_unique Q sX sZ sX' sZ' a b N H
            Cc Dc hc hd hh hhh
        · apply effective_liftSequence_positive_coefficients_unique_of_predecessors P sX sZ sX' sZ'
            Cc Dc hc hd hh n hhh (by omega) (by omega)
          intro p q hpq
          rcases hpq with hp | ⟨hp, hq⟩
          · exact ih p hp (by omega) q
          · subst p
            exact ihn q hq

end AVRegularity.Construction.Preservation.FullLift
end
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! The native enhanced preparation radius satisfies both dimensionless lift scale bounds. -/

theorem band_enhanced_lift_scale_bounds {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ cr : ℝ, 0 < cr →
      ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ M : ℕ, ∀ κ : ℕ → ℝ,
        IsOCBandChain α q Λ ζ M κ → ∀ m : ℕ, m₀ ≤ m → m ≤ M →
        let ρ := cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m)
        0 < κ (m - 1) ∧ 0 < ρ ∧
        ocDStar q Λ m (κ m) (κ (m - 1)) / ρ ≤ 1 ∧
        ρ / ocEpsilon q Λ (m - 1) ≤ 1 := by
  obtain ⟨Lc, hLc, hc⟩ := band_enhanced_cell_ratio_eventually_small hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Lr, _hLr, hr⟩ := enhanced_scalar_drift_budget hα0 hα1 hs0 hs1 hq hζ
  refine ⟨max Lc Lr, hLc.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ cr hcr
  obtain ⟨mc, hmc, hcell⟩ := hc Λ ((le_max_left Lc Lr).trans hΛ) cr hcr
  obtain ⟨mr, _hmr, hrad⟩ := hr Λ ((le_max_right Lc Lr).trans hΛ) cr hcr
  refine ⟨max mc mr, hmc.trans (le_max_left _ _), ?_⟩
  intro M κ hκ m hm hmM
  have hb := hrad M κ hκ m ((le_max_right mc mr).trans hm) hmM
  refine ⟨hb.1, hb.2.1, hcell M κ hκ m ((le_max_left mc mr).trans hm) hmM, ?_⟩
  have hl := hb.2.2.1
  rw [mul_div_assoc] at hl
  linarith

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! The actual parent readout preserves the literal component-sup strong energy under its
entrywise diagonal and finite word-menu bounds. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]

theorem readout_strongEnergy_of_diagonal_entries {S S' : Finset Comp} {K : ℕ}
    (m : ℕ) (E η ρ ν a b C : ℝ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (π : CompIn S → ℝ) (σ : CompIn S' → ℝ)
    (hπ : ∀ v, 0 < π v) (hσ : ∀ c, 0 < σ c)
    (hparent : ∀ c : CompIn S', compParent m c.1 ∈ S)
    (hentry : ∀ v : CompIn S, ∀ c : CompIn S', compParent m c.1 = v.1 →
      (Real.sqrt (π v))⁻¹ / (Real.sqrt (σ c))⁻¹ *
        E ^ (η * (compWord m c.1).length) ≤ 1)
    (hfiber : ∀ v : CompIn S,
      ((Finset.univ : Finset (CompIn S')).filter fun c => compParent m c.1 = v.1).card ≤ C)
    (u : ∀ c : CompIn S', ℝ → TorusHk K (hr c.1.root))
    (w : ∀ c : CompIn S', ℝ → TorusHk (K + 1) (hr c.1.root))
    (hw : ∀ c, MemLp (w c) 2 (volume.restrict (Set.Icc a b))) :
    strongEnergy ρ ν π a b
      (fun v t => succReadout m E η K (fun c => u c t) v)
      (fun v t => succReadout m E η (K + 1) (fun c => w c t) v) ≤
        ENNReal.ofReal (Real.sqrt C) * strongEnergy ρ ν σ a b u w := by
  let p : CompIn S' → CompIn S := fun c => ⟨compParent m c.1, hparent c⟩
  let F : CompIn S → ℝ → ℝ≥0∞ := fun v t =>
    (ENNReal.ofReal (π v))⁻¹ * ENNReal.ofReal (factorialNormSq ρ (succReadout m E η K (fun c => u c t) v).val)
  let W : CompIn S → ℝ → ℝ≥0∞ := fun v t =>
    (ENNReal.ofReal (π v))⁻¹ * ENNReal.ofReal (gradFactorialNormSq ρ (succReadout m E η (K + 1) (fun c => w c t) v).val)
  let G : CompIn S' → ℝ → ℝ≥0∞ := fun c t =>
    (ENNReal.ofReal (σ c))⁻¹ * ENNReal.ofReal (factorialNormSq ρ (u c t).val)
  let V : CompIn S' → ℝ → ℝ≥0∞ := fun c t =>
    (ENNReal.ofReal (σ c))⁻¹ * ENNReal.ofReal (gradFactorialNormSq ρ (w c t).val)
  have hV (c : CompIn S') : AEMeasurable (V c) (volume.restrict (Set.Icc a b)) := by
    exact aemeasurable_const.mul
      (CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hw c)).aemeasurable.ennreal_ofReal
  have hvalue : ∀ v, ∀ t ∈ Set.Icc a b,
      F v t ≤ ENNReal.ofReal C * ∑ c, if p c = v then G c t else 0 := by
    intro v t _ht
    have hs := readout_component_inverse_mass_le m E η ρ C hE hC π σ hπ hσ v
      (hentry v) (hfiber v) (fun c => u c t)
    simpa only [F, G, p, Subtype.ext_iff] using hs
  have hgrad : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      W v t ≤ ENNReal.ofReal C * ∑ c, if p c = v then V c t else 0 := by
    intro v
    apply Filter.Eventually.of_forall
    intro t
    have hs := readout_component_inverse_mass_gradient_le m E η ρ C hE hC π σ hπ hσ v
      (hentry v) (hfiber v) (fun c => w c t)
    simpa only [W, V, p, Subtype.ext_iff] using hs
  have hs := parent_component_strong_energy_le (volume.restrict (Set.Icc a b)) p (Set.Icc a b)
    (ENNReal.ofReal C) (ENNReal.ofReal ν) F W G V hV hvalue hgrad
  have hroot : (ENNReal.ofReal C) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt C) := by
    rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hC (by norm_num)]
  rw [strongEnergy_weighted_components ρ ν a b π hπ,
    strongEnergy_weighted_components ρ ν a b σ hσ]
  simpa only [hroot, F, W, G, V] using hs

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift

/-! The native covariance price is chosen before the band chain and every stage time. -/

open CycleComparison.Coarse

theorem uniform_native_covariance_price {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ m, 2 ≤ m → m ≤ D.term → ∀ K p t,
        covPolyConst (fbCovConst (liftLength D m) (covPrimitive D m t) K) p ≤
          covPolyConst (4 * C * (K : ℝ) ^ 2) p := by
  obtain ⟨C, hC, Λ₀, hΛ₀, hc⟩ :=
    CycleReference.bandChain_covariance_bound hα0 hα1 hs0 hs1 hq hζ
  refine ⟨C, hC, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ D hDα hDq hDΛ hDζ hband m hm hmterm K p t
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hB : 0 < D.κ (m - 1) := CycleReference.bandChain_pos hΛ1 hζD hband
    ((Nat.sub_le m 1).trans hmterm)
  have hρ : 0 < liftLength D m := Real.sqrt_pos.mpr
    (mul_pos hB (Construction.Stream.ocTauPP_pos hΛ1))
  have hband' : IsOCBandChain α q Λ ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ] using hband
  have he := hc Λ hΛ D.term (by omega) D.κ hband' m hm hmterm 0 t
  apply native_covariance_polynomial_price D m K p t C hΛ1
    (zero_le_one.trans hC) hB.le hρ
  intro i j
  simpa only [covPrimitive, hDα, hDq, hDΛ, hDζ] using he i j

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! A higher input carrier upgrades every classical covariance representative, independently of its chosen carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem covPolyP_classicalRep_higher_regularity {K L R n s : ℕ}
    (hKR : K ≤ R) (p : ℕ) (hreserve : max L s + 2 * p + 2 ≤ R)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, Hc i j = Hc j i)
    (Z : TorusHk K E) (Zhi : TorusHk R E) (W : TorusHk L E)
    (hZ : truncateTorusHk hKR Zhi = Z)
    (hcov : IsCovImage (covPolyP Hc p) Z W)
    (a : Vec 2 → E) (ha : IsClassicalRep W a n) : ContDiff ℝ (s : ℕ∞) a := by
  obtain ⟨u, hu⟩ := hilbert_classicalRep_exists R (max L s + 2 * p) hreserve Zhi
  obtain ⟨V, hV, hv⟩ := covPolyP_carrier_exists Hc hH p (max L s) Zhi u hu
  have hVl := covImage_truncate (Nat.le_max_left L s) (covPolyP Hc p) Zhi V hV
  have hVlow := covImage_truncate_input hKR (covPolyP Hc p) Zhi
    (truncateTorusHk (Nat.le_max_left L s) V) hVl
  rw [hZ] at hVlow
  have hvlow := classicalRep_truncate (Nat.le_max_left L s) (Nat.le_refl L) V
    (covPolyP Hc p u) (classicalRep_order_mono V _ hv (Nat.le_max_left L s))
  have he := classical_covImage_rep_unique (covPolyP Hc p) Z W
    (truncateTorusHk (Nat.le_max_left L s) V) hcov hVlow a (covPolyP Hc p u) ha hvlow
  rw [he]
  exact hv.2.1.of_le (by exact_mod_cast Nat.le_max_right L s)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! The band-scale estimate at cr=1 supplies the literal radius prescribed by native lifts. -/

/-- The defining dimensional length identity, valid on the passage levels as well as the tail. -/
theorem native_dstar_eq (D : OCData) (m : ℕ) (hB : 0 ≤ D.kap (m - 1)) :
    ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) =
      (D.eps m / Real.sqrt (D.kap m)) * Real.sqrt (D.kap (m - 1)) := by
  unfold ocDStar
  rw [Real.sqrt_div hB]
  change D.eps m * (Real.sqrt (D.kap (m - 1)) / Real.sqrt (D.kap m)) = _
  ring

/-- The contrast and cell-ratio conditions put the fast cell below the native lift radius. -/
theorem cell_scale_le_lift_radius {e ν B ρ : ℝ} (he : 0 ≤ e) (hν : 0 < ν)
    (hνB : ν ≤ B) (hρ : 0 < ρ) (hcell : e * Real.sqrt (B / ν) / ρ ≤ 1) :
    e ≤ ρ := by
  have hratio : 1 ≤ B / ν := (one_le_div hν).mpr hνB
  have hsqrt : 1 ≤ Real.sqrt (B / ν) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hratio
  exact (le_mul_of_one_le_right he hsqrt).trans ((div_le_one hρ).mp hcell)

theorem native_lift_scale_bounds {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ D : OCData,
        D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
        IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
        ∀ m, m₀ ≤ m → m ≤ D.term →
          0 < liftLength D m ∧
          ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / liftLength D m ≤ 1 ∧
          liftLength D m / D.eps (m - 1) ≤ 1 := by
  obtain ⟨Λ₀, hΛ₀, hb⟩ := band_enhanced_lift_scale_bounds hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨m₀, hm₀, hscale⟩ := hb Λ hΛ 1 zero_lt_one
  refine ⟨m₀, hm₀, ?_⟩
  intro D hDα hDq hDΛ hDζ hband m hm hmterm
  have hband' : IsOCBandChain α q Λ ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ] using hband
  have hbound := hscale D.term D.κ hband' m hm hmterm
  have hprev : m - 1 ≤ D.term := (Nat.sub_le m 1).trans hmterm
  simpa only [liftLength, OCData.kap, Nat.min_eq_left hmterm,
    Nat.min_eq_left hprev, OCData.eps, hDα, hDq, hDΛ, hDζ, one_mul] using hbound.2

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! A smooth periodic value fixes the full jets of any carrier, including compatible gradient carriers. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem classicalRep_of_smooth_periodic_value_ae {K : ℕ} (W : TorusHk K E)
    (a : Vec 2 → E) (ha : ContDiff ℝ (K : ℕ∞) a) (hp : AVenhance.IsZ2Periodic a)
    (hW : W.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube] a) :
    IsClassicalRep W a K :=
  classicalRep_of_value_ae W (classicalHilbertHk K a ha hp) a
    (classicalHilbertHk_rep K a ha hp) hW

theorem classicalRep_of_compatible_smooth_value {K : ℕ}
    (U : TorusHk K E) (W : TorusHk (K + 1) E) (a : Vec 2 → E)
    (ha : ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) a) (hp : AVenhance.IsZ2Periodic a)
    (hU : U.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube] a)
    (hcompat : truncateTorusHk (Nat.le_succ K) W = U) :
    IsClassicalRep W a (K + 1) := by
  let V := classicalHilbertHk (K + 1) a ha hp
  have hV : IsClassicalRep V a (K + 1) := classicalHilbertHk_rep (K + 1) a ha hp
  have htr : IsClassicalRep (truncateTorusHk (Nat.le_succ K) V) a K :=
    classicalRep_truncate (Nat.le_succ K) le_rfl V a
      (classicalRep_order_mono V a hV (Nat.le_succ K))
  have he : truncateTorusHk (Nat.le_succ K) V = U :=
    KernelEnergy.torusCarrier_eq_of_value_ae _ U ((classicalRep_value_ae _ a htr).trans hU.symm)
  have hWV : W = V := torus_truncation_injective (Nat.le_succ K) (hcompat.trans he.symm)
  exact hWV.symm ▸ hV
end

/-! The ordinary parent readout strong energy has a fixed word-menu constant. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]

theorem birth_readout_strongEnergy {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hm : 1 ≤ m) (law : BirthLaw) (hcH : law.cH ≤ 1) (hηB : 0 ≤ law.etaB)
    (hη0 : 0 ≤ law.eta0) {A : Finset WordLetter} {J : ℕ} {S S' : Finset Comp}
    (hold : ∀ v ∈ S, ∀ e ∈ v.births, m ≤ e.scale) (hsub : S' ⊆ succExtComps m A J S)
    {K : ℕ} (ρ ν a b : ℝ)
    (u : ∀ c : CompIn S', ℝ → TorusHk K (hr c.1.root))
    (w : ∀ c : CompIn S', ℝ → TorusHk (K + 1) (hr c.1.root))
    (hw : ∀ c, MemLp (w c) 2 (volume.restrict (Set.Icc a b))) :
    strongEnergy ρ ν (fun v : CompIn S => compMass q Λ law v.1) a b
      (fun v t => succReadout m (ocEpsilon q Λ (m - 1)) law.eta0 K (fun c => u c t) v)
      (fun v t => succReadout m (ocEpsilon q Λ (m - 1)) law.eta0 (K + 1) (fun c => w c t) v) ≤
        ENNReal.ofReal (Real.sqrt ((wordsUpTo A (J + 1)).card + 1)) *
          strongEnergy ρ ν (fun c : CompIn S' => compMass q Λ law c.1) a b u w := by
  apply readout_strongEnergy_of_diagonal_entries m (ocEpsilon q Λ (m - 1)) law.eta0 ρ ν a b
    ((wordsUpTo A (J + 1)).card + 1) (Scales.epsilon_basic hq hΛ).1.le
    (by positivity) _ _ (fun v => Buffer.birth_compMass_pos hq hΛ law v.1)
    (fun c => Buffer.birth_compMass_pos hq hΛ law c.1)
    (fun c => readout_parent_mem hm hold (hsub c.2)) _ _ u w hw
  · intro v c hpar
    rw [← hpar]
    exact readout_ordinary_entry_le_one hq hΛ law hcH hηB hη0 m c.1
  · intro v
    exact_mod_cast readout_indexed_fiber_card_le hm hold hsub v.1
end

/-! Qualitative extra smoothness supplies a compatible covariance gradient carrier without extra energy reserve. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem smooth_classical_gradient_carrier_exists {K : ℕ}
    (W : TorusHk K E) (a : Vec 2 → E) (hW : IsClassicalRep W a K)
    (ha : ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) a) :
    ∃ Ww : TorusHk (K + 1) E,
      IsClassicalRep Ww a (K + 1) ∧ truncateTorusHk (Nat.le_succ K) Ww = W := by
  let Ww := classicalHilbertHk (K + 1) a ha hW.2.2.1
  have hWw : IsClassicalRep Ww a (K + 1) :=
    classicalHilbertHk_rep (K + 1) a ha hW.2.2.1
  have htr : IsClassicalRep (truncateTorusHk (Nat.le_succ K) Ww) a K :=
    classicalRep_truncate (Nat.le_succ K) le_rfl Ww a
      (classicalRep_order_mono Ww a hWw (Nat.le_succ K))
  exact ⟨Ww, hWw, KernelEnergy.torusCarrier_eq_of_value_ae _ W
    ((classicalRep_value_ae _ a htr).trans (classicalRep_value_ae W a hW).symm)⟩
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Higher retained values provide qualitative smoothness for every lifted input, with no higher energy estimate. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem liftedField_classical_input_higher_regularity
    (G Gr : GenStage D hr Dm bw j₀) (m p Naux N H sX sZ s R : ℕ)
    (hNR : Naux ≤ R) (hreserve : max (Naux - 2 * p) s + 2 * p + 2 ≤ R)
    (η tp tf : ℝ) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (Yhi : ∀ v : CompIn Gr.comps, ℝ → TorusHk R (hr v.1.root))
    (heq : ∀ v, ∀ t ∈ Set.Icc tp tf, Y v t = truncateTorusHk hNR (Yhi v t))
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    {k : ℕ} (u : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (hfield : IsLiftedField G Gr m p Naux N H sX sZ η tp tf Y CcT PZ a u) :
    ∀ t ∈ Set.Icc tp tf, ContDiff ℝ (s : ℕ∞) (a t) := by
  intro t ht
  apply contDiff_pi.mpr
  intro v
  apply covPolyP_classicalRep_higher_regularity hNR p hreserve
    (covPrimitive D m t) (native_covPrimitive_entry_symm D hΛ hζ m t)
    (succReadout m (D.eps (m - 1)) η Naux (fun c => Y c t) v)
    (succReadout m (D.eps (m - 1)) η R (fun c => Yhi c t) v)
    (PZ v t) _ (hfield.2.1 v t ht).1 (fun x => a t x v) (hfield.2.1 v t ht).2
  rw [truncate_succReadout]
  congr 1
  funext c
  exact (heq c t ht).symm

/-- Three qualitative Sobolev derivatives beyond the retained order suffice for the lifted gradient. -/
theorem liftedField_higher_regularity_reserve {k N p Naux : ℕ}
    (hk : k + N + 2 * p ≤ Naux) :
    max (Naux - 2 * p) (k + N + 1) + 2 * p + 2 ≤ Naux + 3 := by
  omega

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! The same word-menu bound for the marker-conjugated parent readout. -/

section
theorem inverse_sqrt_effective_mass {π d : ℝ} (hπ : 0 ≤ π) (hd : 0 ≤ d) :
    (Real.sqrt (π / d ^ 2))⁻¹ = d * (Real.sqrt π)⁻¹ := by
  rw [Real.sqrt_div hπ, Real.sqrt_sq hd, inv_div]
  rfl

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]

theorem birth_marked_readout_strongEnergy {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hm : 1 ≤ m) (law : BirthLaw) (hcH : law.cH ≤ 1) (hηB : 0 ≤ law.etaB)
    (hη0 : 0 ≤ law.eta0) (hiota : 0 ≤ law.iota)
    {A : Finset WordLetter} {J : ℕ} {S S' : Finset Comp}
    (hold : ∀ v ∈ S, ∀ e ∈ v.births, m ≤ e.scale) (hsub : S' ⊆ succExtComps m A J S)
    {K : ℕ} (ρ ν a b : ℝ)
    (u : ∀ c : CompIn S', ℝ → TorusHk K (hr c.1.root))
    (w : ∀ c : CompIn S', ℝ → TorusHk (K + 1) (hr c.1.root))
    (hw : ∀ c, MemLp (w c) 2 (volume.restrict (Set.Icc a b))) :
    strongEnergy ρ ν (fun v : CompIn S => compMass q Λ law v.1 / compMarker q Λ law v.1 ^ 2) a b
      (fun v t => succReadout m (ocEpsilon q Λ (m - 1)) law.eta0 K (fun c => u c t) v)
      (fun v t => succReadout m (ocEpsilon q Λ (m - 1)) law.eta0 (K + 1) (fun c => w c t) v) ≤
        ENNReal.ofReal (Real.sqrt ((wordsUpTo A (J + 1)).card + 1)) *
          strongEnergy ρ ν (fun c : CompIn S' => compMass q Λ law c.1 / compMarker q Λ law c.1 ^ 2)
            a b u w := by
  have hmass (c : Comp) := Buffer.birth_compMass_pos hq hΛ law c
  have hmarker (c : Comp) := Buffer.birth_compMarker_pos hq hΛ law c
  apply readout_strongEnergy_of_diagonal_entries m (ocEpsilon q Λ (m - 1)) law.eta0 ρ ν a b
    ((wordsUpTo A (J + 1)).card + 1) (Scales.epsilon_basic hq hΛ).1.le (by positivity)
    _ _ (fun v => div_pos (hmass v.1) (pow_pos (hmarker v.1) 2))
    (fun c => div_pos (hmass c.1) (pow_pos (hmarker c.1) 2))
    (fun c => readout_parent_mem hm hold (hsub c.2)) _ _ u w hw
  · intro v c hpar
    rw [inverse_sqrt_effective_mass (hmass v.1).le (hmarker v.1).le,
      inverse_sqrt_effective_mass (hmass c.1).le (hmarker c.1).le, ← hpar]
    exact readout_marked_entry_le_one hq hΛ hm law hcH hηB hiota hη0 hold (hsub c.2)
  · intro v
    exact_mod_cast readout_indexed_fiber_card_le hm hold hsub v.1
end

/-! The seed invariant's kernel bounds persist through every retained cascade stage.
The kernel-key induction is reused; transfers its certificates between source roots. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  [∀ r, Nontrivial (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Kernel regularization survives the cascade, including kernels copied from another root. -/
theorem cascade_kernel_regularizers_of_seed_invariant
    (P : ProvParams) (Mn : SuccMenu) (seed G : GenStage D hr Dm bw j₀)
    (hc : IsCascadeStage D P Mn seed G)
    (law : BirthLaw) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (M : ℕ) (kS : InvConsts)
    (tS tf Sbound θK : ℝ)
    (hseed : IsStageInvariant law P seedK freshK φ₀ hφ₀ M kS tS tf Sbound θK seed)
    (a b : ℝ) (hwindow : Set.Icc a b ⊆ Set.Icc tS tf)
    (C : ℕ → ℝ) (hC : ∀ j, j + 2 ≤ Dm → kS.cker j ≤ C j)
    (m₀ : ℕ) (hlevel : m₀ ≤ G.level)
    (hfresh : ∀ l, m₀ ≤ l → l < seed.level → ∀ ρ : ℝ, 0 < ρ → ∀ k, k ≤ kS.Ks →
      IsSpatialRegularizerTorus (G := ℝ) ρ k Dm a b C (freshK l).width
        ((freshK l).op φ₀ hφ₀)) :
    ∀ v u (γ : G.fam.Γ v u), ∀ ρ : ℝ, 0 < ρ → ∀ k, k ≤ kS.Ks →
      IsSpatialRegularizerTorus ρ k Dm a b C (G.kernelOf P seedK freshK v u γ).width
        (G.sysS P seedK freshK φ₀ hφ₀ v u γ) := by
  let lookup : KernelKey → KernelSpec := fun key => match key with
    | .seed i => seedK i
    | .fresh i => freshK i
  let Q : KernelKey → Prop := fun key => ∀ r : ℕ, ∀ ρ : ℝ, 0 < ρ → ∀ k, k ≤ kS.Ks →
    IsSpatialRegularizerTorus (G := hr r) ρ k Dm a b C (lookup key).width
      ((lookup key).op φ₀ hφ₀)
  have hseedQ : ∀ v u (γ : seed.fam.Γ v u), Q ((seed.prov v u γ).tags P).kernel := by
    obtain ⟨_, _, _, _, _, _, _, _, hker, _⟩ := hseed
    intro v u γ r ρ hρ k hk
    have hsrc := (hker v u γ).2.2.2.2 ρ hρ k hk
    have hpos : 0 ≤ (seed.kernelOf P seedK freshK v u γ).width := by
      rw [(hker v u γ).2.1]
      exact (seed.fam.identity v u γ).record.width_pos.le
    have hreg := spatial_regularizer_constants_mono
      (Buffer.spatialRegularizerTorus_time_restrict hsrc hwindow) hpos hC
    exact kernel_regularizer_transfer (F := hr r) φ₀ hφ₀
      (seed.kernelOf P seedK freshK v u γ) hreg
  have hfreshQ : ∀ l, m₀ ≤ l → l < seed.level → Q (.fresh l) := by
    intro l hl hs r ρ hρ k hk
    exact kernel_regularizer_of_scalar φ₀ hφ₀ (freshK l) (hfresh l hl hs ρ hρ k hk)
  have hkeys := cascade_kernel_key_property P Mn seed G hc Q hseedQ m₀ hfreshQ hlevel
  intro v u γ ρ hρ k hk
  exact hkeys v u γ u.1.root ρ hρ k hk
end

/-! Strong ordinary and marked readout bounds for the actual retained successor. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem actual_retained_readout_strongEnergy {P : ProvParams} {Mn : SuccMenu}
    {G G' : GenStage D hr Dm b j₀} (hactual : IsActualSuccessor D P Mn G G')
    {m : ℕ} (hlevel : G.level = m) (hm : 1 ≤ m)
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, m ≤ e.scale)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (law : BirthLaw)
    (hcH : law.cH ≤ 1) (hηB : 0 ≤ law.etaB) (hη0 : 0 ≤ law.eta0)
    {K : ℕ} (ρ ν a t : ℝ)
    (u : ∀ c : CompIn (G'.retained m Mn.H Mn.J).comps, ℝ → TorusHk K (hr c.1.root))
    (w : ∀ c : CompIn (G'.retained m Mn.H Mn.J).comps, ℝ → TorusHk (K + 1) (hr c.1.root))
    (hw : ∀ c, MemLp (w c) 2 (volume.restrict (Set.Icc a t))) :
    strongEnergy ρ ν (G.mass law) a t
      (fun v s => succReadout m (D.eps (m - 1)) law.eta0 K (fun c => u c s) v)
      (fun v s => succReadout m (D.eps (m - 1)) law.eta0 (K + 1) (fun c => w c s) v) ≤
        ENNReal.ofReal (Real.sqrt ((wordsUpTo Mn.A (Mn.J + 1)).card + 1)) *
          strongEnergy ρ ν ((G'.retained m Mn.H Mn.J).mass law) a t u w := by
  exact birth_readout_strongEnergy hq hΛ hm law hcH hηB hη0 hold
    (retained_comps_subset_succExt hactual hlevel) ρ ν a t u w hw

theorem actual_retained_marked_readout_strongEnergy {P : ProvParams} {Mn : SuccMenu}
    {G G' : GenStage D hr Dm b j₀} (hactual : IsActualSuccessor D P Mn G G')
    {m : ℕ} (hlevel : G.level = m) (hm : 1 ≤ m)
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, m ≤ e.scale)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (law : BirthLaw)
    (hcH : law.cH ≤ 1) (hηB : 0 ≤ law.etaB) (hη0 : 0 ≤ law.eta0) (hiota : 0 ≤ law.iota)
    {K : ℕ} (ρ ν a t : ℝ)
    (u : ∀ c : CompIn (G'.retained m Mn.H Mn.J).comps, ℝ → TorusHk K (hr c.1.root))
    (w : ∀ c : CompIn (G'.retained m Mn.H Mn.J).comps, ℝ → TorusHk (K + 1) (hr c.1.root))
    (hw : ∀ c, MemLp (w c) 2 (volume.restrict (Set.Icc a t))) :
    strongEnergy ρ ν (fun v => G.mass law v / G.marker law v ^ 2) a t
      (fun v s => succReadout m (D.eps (m - 1)) law.eta0 K (fun c => u c s) v)
      (fun v s => succReadout m (D.eps (m - 1)) law.eta0 (K + 1) (fun c => w c s) v) ≤
        ENNReal.ofReal (Real.sqrt ((wordsUpTo Mn.A (Mn.J + 1)).card + 1)) *
          strongEnergy ρ ν (fun c => (G'.retained m Mn.H Mn.J).mass law c /
            (G'.retained m Mn.H Mn.J).marker law c ^ 2) a t u w := by
  exact birth_marked_readout_strongEnergy hq hΛ hm law hcH hηB hη0 hiota hold
    (retained_comps_subset_succExt hactual hlevel) ρ ν a t u w hw
end

end AVRegularity.Construction.Preservation.FullLift
end
end
