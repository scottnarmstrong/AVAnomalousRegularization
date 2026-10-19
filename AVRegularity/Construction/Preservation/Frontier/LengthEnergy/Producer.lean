-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Frontier.LengthEnergy.AtData
public import AVRegularity.Construction.Preservation.Frontier.GradeSourceProduction
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.Frontier.GradeRows.ExtendedCertificates
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity

/-! Complete length-source energy production. The fixed word budget controls the finite
iteration of the fresh-prefix price; all constants precede the stage, solution and birth law. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier.LengthEnergy
open FullLift KernelEnergy AVRegularity.Construction.Preservation.Assembly RetainedEnergy
open scoped Classical

/-- The length-source estimate, with no extra hypotheses, with the frontier binder order.
The degenerate cases are included: empty and singleton families, J=0, k=0, identity metric, zero
datum and an edgeless seed. J=0 uses homogeneous contraction; positive lengths use forced
copied-block energy. -/
theorem length_source_energy_production {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    FrontierAnalyticProductionStatement α s q ζ false (fun _rows _readout source => source) := by
  classical
  obtain ⟨Λc, hΛc, hc⟩ := extended_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λl, hΛl, hlength⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  change UniformRecordLengths α q ζ Λl at hlength
  obtain ⟨Λr, hΛr, hradius⟩ := uniform_enhanced_radius_le_parent_molecular hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λd, hΛd, hdrift⟩ := actual_enhanced_drift_budget hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Cu, _hCu, Λp, hΛp, hscale⟩ := AVRegularity.Providers.CascadeInvariants.exists_passScales
    hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λc (max Λl (max Λr (max Λd Λp))), by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ (by omega)
  refine ⟨min cmax 1, lt_min hcmax zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨tc, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  let thr : InvConsts := { tc with cker := fun j => max (tc.cker j) 0 }
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  have hkIc := invariant_admissible_of_threshold_bounds (a := tc) (b := thr)
    le_rfl le_rfl le_rfl (fun _ => le_rfl) (fun j => le_max_left _ _) hkI
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkIc
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨mc, hc⟩ := hc CI Cw j₀ hledger hstart
  change ExtendedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ
    σ₀ kI CI Cw j₀ mc at hc
  obtain ⟨hc0I, hcrI, hprod⟩ := Buffer.invariantAdmissible_molecular_parameters hkI
  have hc0pos : 0 < kI.c₀ := hc0I.symm ▸ hc₀
  have hc0le : kI.c₀ ≤ 1 := hc0I.symm ▸ hc₀upper.trans (min_le_right _ _)
  have hcrpos : 0 < kI.cr := hcrI.symm ▸ hcr
  have hcrle : kI.cr ≤ 1 := hcrI.symm ▸ hcrupper
  have hDm : 2 ≤ succSchedD D₀ N p (H + 1) :=
    Buffer.preparation_schedule_order_ge_two D₀ N p H
  obtain ⟨mr, hmr, hradius⟩ := hradius Λ (by omega) kI.c₀ kI.cr hc0pos hcrpos
  change EnhancedRadiusAt α q ζ Λ kI.c₀ kI.cr mr at hradius
  obtain ⟨md, _hmd, hdrift⟩ := hdrift Λ (by omega) kI.cr hcrpos
  change EnhancedDriftAt α q ζ Λ kI.cr md at hdrift
  have hcker (j : ℕ) (_hj : j + 2 ≤ succSchedD D₀ N p (H + 1)) : 0 ≤ kI.cker j :=
    (le_max_right (tc.cker j) 0).trans (invariant_admissible_kernel_bounds hkI j).2
  obtain ⟨A, hA, mo, _hmo, hop⟩ := uniform_native_kernel_operator_of_certificates
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ h128 ζ hζ bw hbw Kres
    (succSchedD D₀ N p (H + 1)) hDm kI.cker hcker
  change NativeKernelOperatorsAt α q ζ Λ bw Kres (succSchedD D₀ N p (H + 1)) kI.cker A mo at hop
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ : 0 < min (ocDelta α q / 4) τe := lt_min (div_pos hδ (by norm_num)) hτe
  obtain ⟨ma, habs⟩ := retained_absorption_threshold hq.1 h128 hτ A CI
  have hscale' : ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ → ∀ m, 2 ≤ m → m ≤ D.term →
        AVRegularity.Providers.CascadeInvariants.PassScales D m Cu := by
    intro D hDα hDq hDΛ hDζ hband m hm hmM
    apply hscale D hDα hDq hDζ (by omega) _ m hm hmM
    simpa only [hDα, hDq, hDζ] using hband
  obtain ⟨_, _, _, _, _, hσeq, ha, haσ, _, _, _⟩ := hsched
  have hσ₀ : 0 ≤ σ₀ := by linarith only [hσeq, ha, haσ]
  exact length_source_energy_at_data hα₀ hα₁ hs₀ hs₁ hq hζ Λl Λ hlength (by omega) h128
    φ₀ hφ₀ bw hbw Q T₀ Ce τe kS r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀
    kI CI Cw j₀ CQ Cpr (zero_le_one.trans (hCe.trans hledger.1)) hledger.2.2.2.le
    hσ₀ hτe hcker mc hc hprod hc0pos hc0le hcrpos hcrle mr hmr hradius md hdrift
    Cu hscale' A hA mo hop ma habs


end AVRegularity.Construction.Preservation.Frontier.LengthEnergy
