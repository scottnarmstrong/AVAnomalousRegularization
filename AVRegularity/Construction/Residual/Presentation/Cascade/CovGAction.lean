-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Cascade.SeqMain
public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncPhysical
import AVRegularity.CycleComparison.LiftMeanEntrywise.Assembly
import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.ConvAssembly
import AVRegularity.EntryWeakAssembly.MolecularHigherTraceJetDerivative

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.EntryTerminal.Ingredients.Recon.Letters
open AVRegularity.CycleComparison.Assembly AVRegularity.CycleComparison.ActualMeans
open AVRegularity.CycleComparison.Lift AVRegularity.CycleComparison.LiftMeanEntrywise
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! The covariance G form native pulse adapter over general Hilbert component roots.
The high-order settings and supplied sequences share one Schur matrix over all
observed pulses. The existing finite-input coefficient and multiplier cores are reused.
Grade zero is included; empty families, zero fields and the empty
positive-grade range use the same sums. Constants depend on orders and setting
constants, never on the component count or datum. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
  (F : Frame D hr Dm b j₀) (law : BirthLaw) (Acl : ℕ)

/-- The exact G2 constant at the requested high-order window setting. -/
def CovGLetterConst (ell : ℕ) (CG CW : ℕ → ℝ) (Ca : ℝ) : ℝ :=
  ambientMeanGradeConstant (wKlift Dm F.depth F.N Acl ell) F.N
    (wLlift Dm F.depth F.N ell) (wLlift Dm F.depth F.N ell) Dm F.depth CG CW (fun _ _ => Ca)

abbrev CovGChart (k : ℤ) :=
  ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
    (ocPulseChartIndex D.α D.q D.Λ F.m k)

abbrev CovGLabel (k : ℤ) :=
  ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
    (ocPulseChartIndex D.α D.q D.Λ F.m k)

abbrev CovGLb (k : ℤ) := meanLetter (fLiftData F k) (F.CcT k)

abbrev CovGCE (Lb : ℤ → ℕ → ℕ → MeanCoeff (CompIn F.G.comps) (fun v => hr v.1.root)) :=
  ceLetter (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (fun k => F.G.actualFamily.weight (oddSlotOf k))
    (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F)
    (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) (F.N + Dm)
    (CovGChart F) (CovGLabel F) (fSeqStart F) (fSeqEnd F) Lb

/-- The actual atlas side of the native window. -/
def CovGFamily : Prop := ∃ T, FrameReconFamilyBody F 0 T reconCpart

/-- Window and chart facts used by the native coefficient estimate. All will be supplied
by the band, renewal-chart and context lemmas at the final producer. -/
structure CovGNativeWindow where
  window : F.tp ≤ F.tp + fTobs F
  rho_pos : 0 < fRho F
  B_pos : 0 < D.κ (F.m - 1)
  current_pos : 0 < D.κ F.m
  mass_pos : ∀ v, 0 < F.G.mass law v
  lambda : 128 ≤ D.Λ
  chart_jets : ∀ k : ℤ, ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F),
    (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2)⁻¹ * t ∈ Set.Icc (fSeqStart F k) (fSeqEnd F k) →
    ∀ j : ℕ, 1 ≤ j → ∀ y,
    ‖iteratedFDeriv ℝ j (CovGChart F k t) y‖ ≤
      CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)) j *
        (ocEpsilon D.q D.Λ (F.m - 1))⁻¹ ^ (j - 1) ∧
    ‖iteratedFDeriv ℝ j (CovGLabel F k t) y‖ ≤
      CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)) j *
        (ocEpsilon D.q D.Λ (F.m - 1))⁻¹ ^ (j - 1)

/-- A high-order input with the common source matrix of the lift settings. The pulse settings and sequences
are premises supplied by the lift settings and the lift sequences, respectively. -/
structure CovGNativePulse (Acl ell : ℕ) (CG CW : ℕ → ℝ) (Ca Sb : ℝ) where
  qs : ℕ
  qf : ℕ
  par : ℤ → Fin 2
  V : ℤ → ℝ → ℝ → ℝ
  edge : CompIn F.G.comps → CompIn F.G.comps → ℝ
  settings : ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
    IsLiftSetting (fLiftData F k) (F.G.mass law) (fSeqStart F k) (fSeqEnd F k)
      (ocEpsilon D.q D.Λ F.m) (D.κ F.m) (D.κ (F.m - 1)) (fRho F)
      (ocEpsilon D.q D.Λ (F.m - 1)) (ocEll D.q D.Λ F.m (D.κ F.m))
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)))
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F)
      (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) (par k) (V k) F.depth F.N
      (wKlift Dm F.depth F.N Acl ell) (wLlift Dm F.depth F.N ell) (wLlift Dm F.depth F.N ell) qs qf CG CW (fun _ _ => Ca) edge Sb
  sequences : FrameReconSeqAt F Acl ell

/-- The lift sequences and the lift settings supply the common pulse input. -/
theorem CovGNativePulse_of_setting (Acl ell : ℕ) (CG CW : ℕ → ℝ) (Ca Sb Cg : ℝ)
    (hs : FrameReconSeqAt F Acl ell) (hP : ∃ (qs qf : ℕ) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
      (edge : CompIn F.G.comps → CompIn F.G.comps → ℝ),
      FrameReconSettingBody F law Acl ell CG CW Ca Sb Cg qs qf par V edge) :
    Nonempty (CovGNativePulse F law Acl ell CG CW Ca Sb) := by
  obtain ⟨qs, qf, par, V, edge, hp, -⟩ := hP
  exact ⟨⟨qs, qf, par, V, edge, hp, hs⟩⟩

/-- All seven G2 clauses at the uniform explicit constant. -/
theorem CovGNativePulse_letters {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (k : ℤ)
    (hk : k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F)) :
    IsPulseLetters (fLiftData F k) (F.CcT k) (F.G.mass law) p.edge
      (fSeqStart F k) (fSeqEnd F k) (fRho F / ocEpsilon D.q D.Λ (F.m - 1))
      (CovGLetterConst F Acl ell CG CW Ca) F.N F.depth (wKlift Dm F.depth F.N Acl ell)
      (CovGLb F k) := by
  have hL := fun hh hhh n hn hnR => setting_meanLetter_entrywise
    (p.settings k hk) (F.CcT k) (p.sequences k hk) hh hhh n hn hnR
  exact {
    perm := fun r hr n hn hnR => (hL r hr n hn hnR).1
    smooth := fun r hr n hn hnR => (hL r hr n hn hnR).2.1
    meas := fun r hr n hn hnR => (hL r hr n hn hnR).2.2.1
    pres := fun r hr n hn hnR => (hL r hr n hn hnR).2.2.2.1
    bound := fun r hr n hn hnR => (hL r hr n hn hnR).2.2.2.2.1
    diag := fun n hn hnR => (hL 0 (Nat.zero_le _) n hn hnR).2.2.2.2.2.1 rfl
    shift := fun T hG hc r hr n hn hnR => (hL r hr n hn hnR).2.2.2.2.2.2 T hG hc
    explicit := fun _ _ => rfl }

/-- Joint measurability, finite-order smoothness and physical periodicity of every grade's
actual CE coefficient. The qualifier hh <= dW is required by the sequence definition. -/
theorem CovGNativeCE_regular {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (K : ℕ) (hK : K ≤ wKlift Dm F.depth F.N Acl ell + 1)
    (hfamily : CovGFamily F) (hh : ℕ) (hhh : hh ≤ F.depth) (v u : CompIn F.G.comps)
    (d : Finset.Icc 2 (F.N + Dm)) :
    (∀ t ∈ Set.Icc F.tp (F.tp + fTobs F),
      ContDiff ℝ (K : ℕ) (CovGCE F (CovGLb F) hh v u d t)) ∧
    Measurable (fun q : Set.Icc F.tp (F.tp + fTobs F) × Vec 2 =>
      CovGCE F (CovGLb F) hh v u d q.1 q.2) ∧
    (∀ t ∈ Set.Icc F.tp (F.tp + fTobs F),
      IsZ2Periodic (CovGCE F (CovGLb F) hh v u d t)) := by
  classical
  obtain ⟨T, hf⟩ := hfamily
  obtain ⟨-, hw, -, -⟩ := partition_stage_facts hf.2.2.2.2.2.2.2.2.1
  have hreg : (((K : ℕ) : ℕ∞) : WithTop ℕ∞) ≤
      (((wKlift Dm F.depth F.N Acl ell + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hK
  refine ⟨fun t _ => ?_, ?_, fun t _ => ?_⟩
  · exact_mod_cast contDiff_ceLetter _ _ _ _ _ _ _ _ _ _ _ K hh v u d t
      (fun k _ => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
        ((contDiff_const (c := t)).prodMk contDiff_id))
      (fun k _ => (CycleComparison.Charts.contDiff_ocChartInv_joint _ _ _ _ _ _).comp
        ((contDiff_const (c := t)).prodMk contDiff_id))
      (fun k hk n hn hnN d _ _ α l s hs =>
        ((CovGNativePulse_letters F law p k hk).smooth hh hhh n hn hnN d α l v u s hs).of_le hreg)
  · exact measurable_ceLetter _ _ _ _ _ _ _ _ _ _ _ F.tp (F.tp + fTobs F) hh v u d hw
      (fun k _ => CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _)
      (fun k _ => CycleComparison.Charts.contDiff_ocChartInv_joint _ _ _ _ _ _)
      (fun k hk n hn hnN d _ _ α l Y =>
        (CovGNativePulse_letters F law p k hk).meas hh hhh n hn hnN d α l v u Y)
      (fun k hk n hn hnN d _ _ α l s hs =>
        ((CovGNativePulse_letters F law p k hk).smooth hh hhh n hn hnN d α l v u s hs).continuous)
  · exact isZ2Periodic_ceLetter _ _ _ _ _ _ _ _ _ _ _ hh v u d t
      (fun k _ z y => CycleComparison.Charts.ocChart_latticeShift _ _ _ _ _ _ t z y)
      (fun k _ z y => CycleReference.streamFlow_lattice_equivariant (D.hΦ (F.m - 1))
        ((ocPulseChartIndex D.α D.q D.Λ F.m k : ℝ) * ocTauPP D.α D.q D.Λ F.m) t y z)
      (fun k hk n hn hnN d _ _ α l s hs z Y =>
        (CovGNativePulse_letters F law p k hk).shift ((fRho F)⁻¹ • latticeShift z)
          (fun t Y i j => pulseLiftData_G_shift D.α D.q D.Λ F.m D.ζ (D.hΦ (F.m - 1))
            (D.κ F.m) (D.κ (F.m - 1)) (p.settings k hk).ρ_pos.ne' _ k _ z t Y i j)
          (fun v u d γ hγ α t Y Z => liftEdges_fiber_coeff_shift
            (p.settings k hk).ρ_pos.ne' hf.2.1
            (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (oddSlotOf k) z hγ α t Y Z)
          hh hhh n hn hnN d α l v u s hs Y)

/-- One observed pulse suffices to read the common matrix's Schur budget and scale inequalities.
The nonempty observation window and partition guarantee that such a pulse exists. -/
theorem CovGNativePulse_scales {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (g : CovGNativeWindow F law)
    (hfamily : CovGFamily F) :
    ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) ≤ fRho F ∧
    fRho F ≤ ocEpsilon D.q D.Λ (F.m - 1) ∧ HasRealSchurBudget p.edge Sb := by
  obtain ⟨T, hf⟩ := hfamily
  have hsum := hf.2.2.2.2.2.2.2.2.1.2.2.1 F.tp ⟨le_rfl, g.window⟩
  obtain ⟨k, hk, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  have P := p.settings k hk
  exact ⟨(div_le_one P.ρ_pos).mp P.εc_le, (div_le_one P.E_pos).mp P.lam_le,
    ⟨P.envelope.nonneg, P.envelope.row_sum, P.envelope.col_sum⟩⟩

/-- Uniform G1 price for one grade, after undoing the mass conjugation. -/
def CovGNativeCEConst (N D K : ℕ) (C₂ : ℝ) : ℝ :=
  2 * ((N + D : ℕ) : ℝ) ^ 2 * ((K : ℝ) + 1) *
    (covTruncNativeTransferConst N D K * C₂)

/-- Both radii have a normalized entrywise budget controlled by the SAME physical matrix
power for every pulse. This includes grade zero; no source height is silently discarded. -/
theorem CovGNativeCE_budget {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (K : ℕ) (hK : K ≤ wKlift Dm F.depth F.N Acl ell + 1)
    (g : CovGNativeWindow F law) (hfamily : CovGFamily F) (hh : ℕ) (hhh : hh ≤ F.depth) (v u : CompIn F.G.comps) :
    ∑ d : Finset.Icc 2 (F.N + Dm),
      coefficientSeminorm (fRho F) K F.tp (F.tp + fTobs F)
        (CovGCE F (CovGLb F) hh v u d) *
        (ENNReal.ofReal (D.κ (F.m - 1) * fRho F ^ (d.val - 2)))⁻¹ ≤
      ENNReal.ofReal (CovGNativeCEConst F.N Dm K
        (CovGLetterConst F Acl ell CG CW Ca) *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix (F.G.mass law) p.edge) hh v u) := by
  classical
  have hΛ1 : 1 ≤ D.Λ := le_trans (by norm_num) g.lambda
  have hν : 0 < D.κ F.m := g.current_pos
  have hℓ : 0 < ocEll D.q D.Λ F.m (D.κ F.m) :=
    div_pos (Construction.Stream.ocEpsilon_pos hΛ1) (Real.sqrt_pos.mpr hν)
  obtain ⟨hdρ, hρE, hSchur⟩ := CovGNativePulse_scales F law p g hfamily
  obtain ⟨T, hf⟩ := hfamily
  obtain ⟨hϖ0, -, hϖ1, -⟩ := partition_stage_facts hf.2.2.2.2.2.2.2.2.1
  have hC₂ : 0 ≤ CovGLetterConst F Acl ell CG CW Ca :=
    ambientMeanGradeConstant_nonneg _ _ _ _ _ _ _ _ _
  have hM0 : 0 ≤ CovGLetterConst F Acl ell CG CW Ca *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix (F.G.mass law) p.edge) hh v u :=
    mul_nonneg hC₂ (finiteMatrixPower_nonneg _
      (physicalEdgeEnvelopeMatrix_nonneg _ _ hSchur.nonneg) hh v u)
  have hreg : (((K : ℕ) : ℕ∞) : WithTop ℕ∞) ≤
      (((wKlift Dm F.depth F.N Acl ell + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hK
  have hbound := (Classical.choose_spec (ceLetter_means_bound.{0, 0} F.N Dm K
    (CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ))))).2
      (ι := CompIn F.G.comps) (h := fun v => hr v.1.root)
  have hb := hbound
    (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (fun k => F.G.actualFamily.weight (oddSlotOf k))
    (ocEll D.q D.Λ F.m (D.κ F.m)) (D.κ (F.m - 1))
    (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1))) (fRho F)
    (ocEpsilon D.q D.Λ (F.m - 1)) F.tp (F.tp + fTobs F)
    (CovGChart F) (CovGLabel F) (fSeqStart F) (fSeqEnd F) (CovGLb F) hh v u
    (CovGLetterConst F Acl ell CG CW Ca *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix (F.G.mass law) p.edge) hh v u)
    hℓ g.B_pos g.rho_pos (CycleComparison.LiftSetting.dstar_eq _ _ _ hν.le _)
    hdρ hρE hM0 hϖ0 hϖ1
    (fun k _ t => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ t => (CycleComparison.Charts.contDiff_ocChartInv_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ t ht hwin j hj _ y => g.chart_jets k t ht hwin j hj y)
    (fun k hk n hn hnN d _ _ α l s hs =>
      ((CovGNativePulse_letters F law p k hk).smooth hh hhh n hn hnN d α l v u s hs).of_le hreg)
    (fun k hk n hn hnN d hd hdn α l i hi s hs Y =>
      (CovGNativePulse_letters F law p k hk).bound hh hhh n hn hnN d hd hdn α l v u i
        (hi.trans hK) s hs Y) K le_rfl
  refine (le_add_of_nonneg_left (by positivity)).trans (hb.trans_eq ?_)
  congr 1
  unfold CovGNativeCEConst covTruncNativeTransferConst
  ring

/-- The same price in real seminorms, with the diffusivity restored. -/
theorem CovGNativeCE_real_budget {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (K : ℕ) (hK : K ≤ wKlift Dm F.depth F.N Acl ell + 1)
    (g : CovGNativeWindow F law) (hfamily : CovGFamily F) (hh : ℕ) (hhh : hh ≤ F.depth) (v u : CompIn F.G.comps) :
    (∀ d : Finset.Icc 2 (F.N + Dm),
      coefficientSeminorm (fRho F) K F.tp (F.tp + fTobs F)
        (CovGCE F (CovGLb F) hh v u d) ≠ ⊤) ∧
    (∑ d : Finset.Icc 2 (F.N + Dm),
      (coefficientSeminorm (fRho F) K F.tp (F.tp + fTobs F)
        (CovGCE F (CovGLb F) hh v u d)).toReal / fRho F ^ (d.val - 2)) ≤
      D.κ (F.m - 1) * (CovGNativeCEConst F.N Dm K
        (CovGLetterConst F Acl ell CG CW Ca) *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix (F.G.mass law) p.edge) hh v u) := by
  have hb := CovGNativeCE_budget F law p K hK g hfamily hh hhh v u
  have hf := fun d => ne_top_of_sum_inv_le _ _ hb d
  refine ⟨hf, ?_⟩
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [CycleComparison.Coarse.toReal_sum_sem_div g.B_pos g.rho_pos _ hf] at hr
  have hC₂ : 0 ≤ CovGLetterConst F Acl ell CG CW Ca :=
    ambientMeanGradeConstant_nonneg _ _ _ _ _ _ _ _ _
  have hCt : 0 ≤ covTruncNativeTransferConst F.N Dm K :=
    (Classical.choose_spec (ceLetter_means_bound.{0, 0} F.N Dm K
      (CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ))))).1
  have hSchur := (CovGNativePulse_scales F law p g hfamily).2.2
  have hprice : 0 ≤ CovGNativeCEConst F.N Dm K
      (CovGLetterConst F Acl ell CG CW Ca) *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix (F.G.mass law) p.edge) hh v u := by
    unfold CovGNativeCEConst
    exact mul_nonneg (by positivity) (finiteMatrixPower_nonneg _
      (physicalEdgeEnvelopeMatrix_nonneg _ _ hSchur.nonneg) hh v u)
  rw [ENNReal.toReal_ofReal hprice] at hr
  have hmul := mul_le_mul_of_nonneg_left hr g.B_pos.le
  refine le_trans (le_of_eq ?_) hmul
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by field_simp [g.B_pos.ne']

/-- The actual scalar coefficients of a finite set of constrained source grades. -/
def CovGNativeGradeCoefficient (rs : Finset ℕ) (v u : CompIn F.G.comps)
    (d : Finset.Icc 2 (F.N + Dm)) (t : ℝ) (y : Vec 2) :=
  ∑ hh ∈ rs, CovGCE F (CovGLb F) hh v u d t y

/-- Sum the actual CE coefficients, keeping the individual suprema before the grade sum. -/
theorem CovGNativeGrade_regular {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (K : ℕ) (hK : K ≤ wKlift Dm F.depth F.N Acl ell + 1)
    (hfamily : CovGFamily F) (rs : Finset ℕ) (hrs : ∀ hh ∈ rs, hh ≤ F.depth)
    (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)) :
    (∀ t ∈ Set.Icc F.tp (F.tp + fTobs F),
      ContDiff ℝ (K : ℕ) (CovGNativeGradeCoefficient F rs v u d t)) ∧
    Measurable (fun q : Set.Icc F.tp (F.tp + fTobs F) × Vec 2 =>
      CovGNativeGradeCoefficient F rs v u d q.1 q.2) ∧
    (∀ t ∈ Set.Icc F.tp (F.tp + fTobs F),
      IsZ2Periodic (CovGNativeGradeCoefficient F rs v u d t)) := by
  have hreg := fun hh hhh => CovGNativeCE_regular F law p K hK hfamily hh (hrs hh hhh) v u d
  refine ⟨fun t ht => ContDiff.sum (fun hh hhh => (hreg hh hhh).1 t ht), ?_, ?_⟩
  · exact Finset.measurable_sum rs fun hh hhh => (hreg hh hhh).2.1
  · intro t ht z y
    exact Finset.sum_congr rfl fun hh hhh => (hreg hh hhh).2.2 t ht z y

/-- Grade sum's entrywise price, still before mass conjugation. -/
def CovGNativeGradePrice {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (K : ℕ) (rs : Finset ℕ)
    (v u : CompIn F.G.comps) : ℝ :=
  ∑ hh ∈ rs, D.κ (F.m - 1) * (CovGNativeCEConst F.N Dm K
    (CovGLetterConst F Acl ell CG CW Ca) *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix (F.G.mass law) p.edge) hh v u)

/-- The finite grade sum has the sum of the individual normalized prices, not a price
involving the number of components. -/
theorem CovGNativeGrade_budget {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (K : ℕ) (hK : K ≤ wKlift Dm F.depth F.N Acl ell + 1)
    (g : CovGNativeWindow F law) (hfamily : CovGFamily F) (rs : Finset ℕ) (hrs : ∀ hh ∈ rs, hh ≤ F.depth)
    (v u : CompIn F.G.comps) :
    (∀ d : Finset.Icc 2 (F.N + Dm),
      coefficientSeminorm (fRho F) K F.tp (F.tp + fTobs F)
        (CovGNativeGradeCoefficient F rs v u d) ≠ ⊤) ∧
    (∑ d : Finset.Icc 2 (F.N + Dm),
      (coefficientSeminorm (fRho F) K F.tp (F.tp + fTobs F)
        (CovGNativeGradeCoefficient F rs v u d)).toReal / fRho F ^ (d.val - 2)) ≤
      CovGNativeGradePrice F law p K rs v u := by
  classical
  have hb := fun hh hhh =>
    CovGNativeCE_real_budget F law p K hK g hfamily hh (hrs hh hhh) v u
  have hs := fun hh hhh d t ht =>
    (CovGNativeCE_regular F law p K hK hfamily hh (hrs hh hhh) v u d).1 t ht
  refine ⟨fun d => CycleJointProofs.coefficientSeminorm_sum_ne_top rs
    (fun hh => CovGCE F (CovGLb F) hh v u d) _ _ _ _
      (fun hh hhh => hs hh hhh d) (fun hh hhh => (hb hh hhh).1 d), ?_⟩
  calc
    _ ≤ ∑ d : Finset.Icc 2 (F.N + Dm), ∑ hh ∈ rs,
        (coefficientSeminorm (fRho F) K F.tp (F.tp + fTobs F)
          (CovGCE F (CovGLb F) hh v u d)).toReal / fRho F ^ (d.val - 2) := by
      refine Finset.sum_le_sum fun d _ => ?_
      rw [← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ (pow_nonneg g.rho_pos.le _)
      have hfinite : (∑ hh ∈ rs, coefficientSeminorm (fRho F) K F.tp (F.tp + fTobs F)
          (CovGCE F (CovGLb F) hh v u d)) ≠ ⊤ :=
        ENNReal.sum_ne_top.mpr (fun hh hhh => (hb hh hhh).1 d)
      have hle := ENNReal.toReal_mono hfinite (CycleJointProofs.coefficientSeminorm_sum_le rs
        (fun hh => CovGCE F (CovGLb F) hh v u d) _ _ _ _ (fun hh hhh => hs hh hhh d))
      rwa [ENNReal.toReal_sum (fun hh hhh => (hb hh hhh).1 d)] at hle
    _ = ∑ hh ∈ rs, ∑ d : Finset.Icc 2 (F.N + Dm),
        (coefficientSeminorm (fRho F) K F.tp (F.tp + fTobs F)
          (CovGCE F (CovGLb F) hh v u d)).toReal / fRho F ^ (d.val - 2) :=
      Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun hh hhh => (hb hh hhh).2)

private theorem native_schur_sum' {ι : Type} [Fintype ι] (rs : Finset ℕ)
    (matrix : ℕ → ι → ι → ℝ) (bound : ℕ → ℝ)
    (hb : ∀ hh ∈ rs, HasRealSchurBudget (matrix hh) (bound hh)) :
    HasRealSchurBudget (fun v u => ∑ hh ∈ rs, matrix hh v u) (∑ hh ∈ rs, bound hh) := by
  classical
  constructor
  · intro v u
    exact Finset.sum_nonneg fun hh hhh => (hb hh hhh).nonneg v u
  · intro v
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun hh hhh => (hb hh hhh).row_sum v
  · intro u
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun hh hhh => (hb hh hhh).col_sum u

/-- Weighted row and column prices of all grades. The source height only contributes the
finite sum of powers of Sb, which was fixed before the level and datum. -/
theorem CovGNativeGrade_schur {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (K : ℕ)
    (g : CovGNativeWindow F law) (hfamily : CovGFamily F) (hSb : 0 ≤ Sb) (rs : Finset ℕ) :
    HasRealSchurBudget
      (massConjugatedMatrix (F.G.mass law) (CovGNativeGradePrice F law p K rs))
      (D.κ (F.m - 1) * CovGNativeCEConst F.N Dm K
        (CovGLetterConst F Acl ell CG CW Ca) * ∑ hh ∈ rs, Sb ^ hh) := by
  have hC₂ : 0 ≤ CovGLetterConst F Acl ell CG CW Ca :=
    ambientMeanGradeConstant_nonneg _ _ _ _ _ _ _ _ _
  have hCt : 0 ≤ covTruncNativeTransferConst F.N Dm K :=
    (Classical.choose_spec (ceLetter_means_bound.{0, 0} F.N Dm K
      (CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ))))).1
  have hB : 0 ≤ D.κ (F.m - 1) := g.B_pos.le
  have hC : 0 ≤ D.κ (F.m - 1) * CovGNativeCEConst F.N Dm K
      (CovGLetterConst F Acl ell CG CW Ca) := by
    unfold CovGNativeCEConst
    positivity
  have hSchur := (CovGNativePulse_scales F law p g hfamily).2.2
  have hp := fun hh =>
    (physicalEdgeEnvelopeMatrix_power_schur_budget (F.G.mass law) g.mass_pos p.edge Sb hSb
      hSchur hh).const_mul _ hC
  have hs := native_schur_sum' rs _ _ (fun hh _ => hp hh)
  convert hs using 1
  · funext v u
    unfold massConjugatedMatrix CovGNativeGradePrice
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun hh _ => by ring
  · exact Finset.mul_sum _ _ _

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.EntryTerminal.Ingredients.Recon.Letters
open AVRegularity.CycleComparison.Assembly AVRegularity.CycleComparison.ActualMeans
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.Lift AVRegularity.CycleComparison.LiftMeanEntrywise
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! The exact finite-input action of the bill's native mean coefficients.
The supplied sequence is transferred by the data-agreement lemma;
the finite cell-mean action is used directly, without replacing a flux by
another having the same divergence. Grade zero keeps its molecular term.
Zero input and empty components have zero action; `N = 1` retains
its degree-two diagonal term; a point window is allowed. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
  (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The native/window identification facts, supplied at a context. -/
structure CovGNativeAgreement where
  one : F.Mn.lenFactor = 1
  cell_pos : 0 < D.cellScaleSq F.m
  scale_eq : ocEll D.q D.Λ F.m (D.κ F.m) ^ 2 = D.cellScaleSq F.m
  seq_agree : ∀ (k : ℤ) (hk : Odd k),
    (fSeqQ F k hk).η = (fLiftData F k).η ∧ ∀ t,
      D.cellScaleSq F.m * t ∈ ocPulseWindow D.α D.q D.Λ F.m k →
      Seq.SeqAgreeAt (fSeqQ F k hk) (fLiftData F k) t
  weight_eq : ∀ (k : ℤ), Odd k → ∀ t,
    F.G.actualFamily.weight (oddSlotOf k) t = ocCutoff D.α D.q D.Λ F.m k t

abbrev CovGFlow (k : ℤ) := fun s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m k)
abbrev CovGInvFlow (k : ℤ) := fun s y => D.flowOf (F.m - 1) (D.slotAnchor F.m k) y s

/-- One unweighted pulse of the physical menu flux. -/
def CovGPF (r : ℕ) (a : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root)
    (k : ℤ) (t : ℝ) (z : Vec 2) (v : CompIn F.G.comps) : Fin 2 → hr v.1.root :=
  ∑ n ∈ Finset.Icc 2 (F.N + Dm), if hk : Odd k then
    pulseMeanFluxEuler (D.cellScaleSq F.m) (liftLength D F.m)
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / liftLength D F.m) n r
      (familyLiftData D F.m k (nativeChain F.m k) (liftLength D F.m)
        (F.G.fam.fiber ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩))) (F.CcT k)
      (CovGFlow F k) (CovGInvFlow F k) a t z v else 0

private theorem CovG_mem_pulseWindow (g : CovGNativeWindow F law) (k : ℤ) {t : ℝ}
    (hw : ocCutoff D.α D.q D.Λ F.m k t ≠ 0) :
    t ∈ ocPulseWindow D.α D.q D.Λ F.m k := by
  by_contra hn
  exact hw (WeakEntryProofs.ocCutoff_zero_off_output _ _ _ _
    (Construction.Stream.ocTau_pos (le_trans (by norm_num) g.lambda)) k t hn)

private theorem CovG_window_mem (hA : CovGNativeAgreement F)
    (g : CovGNativeWindow F law) (k : ℤ) {t : ℝ}
    (ht : t ∈ Set.Icc F.tp (F.tp + fTobs F))
    (hw : ocCutoff D.α D.q D.Λ F.m k t ≠ 0) :
    (D.cellScaleSq F.m)⁻¹ * t ∈ Set.Icc (fSeqStart F k) (fSeqEnd F k) := by
  have hwin := CovG_mem_pulseWindow F law g k hw
  unfold fSeqStart fSeqEnd
  rw [hA.scale_eq]
  have he : (D.cellScaleSq F.m)⁻¹ * t * D.cellScaleSq F.m = t := by field_simp [hA.cell_pos.ne']
  refine ⟨(div_le_iff₀ hA.cell_pos).2 ?_, (le_div_iff₀ hA.cell_pos).2 ?_⟩
  · rw [he]; exact max_le hwin.1 ht.1
  · rw [he]; exact le_min hwin.2 ht.2

private theorem CovG_gluedMeanFlux_eq (hA : CovGNativeAgreement F)
    (g : CovGNativeWindow F law) (r : ℕ)
    (a : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root) {t : ℝ}
    (ht : t ∈ Set.Icc F.tp (F.tp + fTobs F)) (z : Vec 2) (v : CompIn F.G.comps) :
    gluedMeanFlux F.G F.m {r} (Finset.Icc 2 (F.N + Dm)) F.CcT a t z v =
      ∑ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
        F.G.actualFamily.weight (oddSlotOf k) t • CovGPF F r a k t z v := by
  classical
  have hτ : 0 < ocTau D.α D.q D.Λ F.m :=
    Construction.Stream.ocTau_pos (le_trans (by norm_num) g.lambda)
  unfold gluedMeanFlux
  simp only [Finset.sum_singleton]
  have h1 : ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m t t,
      (∑ n ∈ Finset.Icc 2 (F.N + Dm), if hk : Odd k then
        ocCutoff D.α D.q D.Λ F.m k t • pulseMeanFluxEuler (D.cellScaleSq F.m)
          (liftLength D F.m)
          (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / liftLength D F.m) n r
          (familyLiftData D F.m k (nativeChain F.m k) (liftLength D F.m)
            (F.G.fam.fiber ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩))) (F.CcT k)
          (CovGFlow F k) (CovGInvFlow F k) a t z v else 0) =
      ocCutoff D.α D.q D.Λ F.m k t • CovGPF F r a k t z v := by
    intro k _
    unfold CovGPF
    by_cases hodd : Odd k
    · simp only [hodd, dite_true, Finset.smul_sum]
    · simp [hodd]
  rw [Finset.sum_congr rfl h1]
  have hsub := obsPulses_time_subset D.α D.q D.Λ F.m hτ ht
  rw [Finset.sum_subset hsub fun k hk hnk => ?_]
  · exact Finset.sum_congr rfl fun k hk => by
      rw [hA.weight_eq k (CycleComparison.LiftSetting.obsPulse_odd hk) t]
  · have hodd := CycleComparison.LiftSetting.obsPulse_odd hk
    have hout : t ∉ ocPulseWindow D.α D.q D.Λ F.m k := fun hin =>
      hnk (mem_obsPulses_time D.α D.q D.Λ F.m hτ hodd hin)
    rw [WeakEntryProofs.ocCutoff_zero_off_output D.α D.q D.Λ F.m hτ k t hout, zero_smul]

/-- The renewal chart and the menu's native flow chart coincide. -/
theorem CovGNative_chart (hΛ : 1 ≤ D.Λ) (k : ℤ) :
    CovGChart F k = CovGFlow F k ∧ CovGLabel F k = CovGInvFlow F k := by
  have hτ : 0 < ocTauPP D.α D.q D.Λ F.m :=
    Construction.Stream.ocTauPP_pos hΛ
  constructor <;> funext t y
  · show _ = D.flowOf (F.m - 1) t y (D.slotAnchor F.m k)
    unfold CovGChart ocChart OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex D.α D.q D.Λ F.m k hτ]
  · show _ = D.flowOf (F.m - 1) (D.slotAnchor F.m k) y t
    unfold CovGLabel ocChartInv OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex D.α D.q D.Λ F.m k hτ]

/-- The literal flux of an active native pulse, from finite-regularity cell means and data
agreement on the pulse window. This does not invoke the divergence-only mean presentation. -/
theorem CovGNativePF_action {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (hA : CovGNativeAgreement F)
    (g : CovGNativeWindow F law) (hN : 1 ≤ F.N)
    (hh : ℕ) (hhh : hh ≤ F.depth)
    (f : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root) (t : ℝ)
    (hf : ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (f t))
    (ht : t ∈ Set.Icc F.tp (F.tp + fTobs F)) (k : ℤ)
    (hk : k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (hw : F.G.actualFamily.weight (oddSlotOf k) t ≠ 0)
    (y : Vec 2) (v : CompIn F.G.comps) (j : Fin 2) :
    CovGPF F hh f k t y v j =
      -∑ n ∈ Finset.Icc 2 (F.N + Dm),
        ((ocEll D.q D.Λ F.m (D.κ F.m) ^ 2)⁻¹ *
          (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) ^ n) •
          ∑ l : Fin 2, jacMatrix (CovGChart F k t) (CovGLabel F k t y) j l •
            ∑ d ∈ Finset.Icc 2 n, fRho F ^ d • ∑ α : DerivativeWord2 (d - 1), ∑ u,
              CovGLb F k hh n d α
                ((ocEll D.q D.Λ F.m (D.κ F.m) ^ 2)⁻¹ * t)
                ((fRho F)⁻¹ • CovGLabel F k t y) l v u
                (orderedDerivative α (fun z => f t (CovGChart F k t z)) (CovGLabel F k t y) u) := by
  classical
  have hodd : Odd k := CycleComparison.LiftSetting.obsPulse_odd hk
  have hcut : ocCutoff D.α D.q D.Λ F.m k t ≠ 0 := by
    rwa [hA.weight_eq k hodd t] at hw
  have hc := hA.scale_eq
  have hcs := hA.cell_pos
  have hmem := CovG_window_mem F law hA g k ht hcut
  have hwin := CovG_mem_pulseWindow F law g k hcut
  obtain ⟨hη, hag⟩ := hA.seq_agree k hodd
  have hag' := hag ((D.cellScaleSq F.m)⁻¹ * t)
    (by rw [mul_inv_cancel_left₀ hcs.ne']; exact hwin)
  have hQ : familyLiftData D F.m k (nativeChain F.m k) (liftLength D F.m)
      (F.G.fam.fiber ⟨k, hodd⟩ (F.G.actual ⟨k, hodd⟩)) = fSeqQ F k hodd := by
    simp only [fSeqQ, (congrArg (· * liftLength D F.m) hA.one).trans (one_mul _)]
  have hsz : max 2 Dm ≤ max (wLlift Dm F.depth F.N ell + 1) (wLlift Dm F.depth F.N ell + 2) := by
    have h1 : Dm * 1 * 1 ≤ Dm * (F.depth + 1) * F.N :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hN
    unfold wLlift
    omega
  have hsx : max 2 Dm ≤ wKlift Dm F.depth F.N Acl ell + Dm + 2 := by omega
  have P := p.settings k hk
  have hres : 0 + (F.N + Dm) ≤ p.qs := by
    have hr := setting_ambient_output_supported P
    omega
  unfold CovGPF
  simp only [hodd, dite_true, Finset.sum_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_Icc.mp hn
  rw [hQ]
  have he : pulseMeanFluxEuler (D.cellScaleSq F.m) (liftLength D F.m)
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / liftLength D F.m)
      n hh (fSeqQ F k hodd) (F.CcT k) (CovGFlow F k) (CovGInvFlow F k) f t y v j =
      pulseMeanFluxEuler (D.cellScaleSq F.m) (liftLength D F.m)
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / liftLength D F.m)
      n hh (fLiftData F k) (F.CcT k) (CovGFlow F k) (CovGInvFlow F k) f t y v j := by
    unfold pulseMeanFluxEuler
    rw [liftFluxX_congr_data (fSeqQ F k hodd) (fLiftData F k) hη (F.CcT k) _ hh n hag']
  rw [he, ← (CovGNative_chart F (le_trans (by norm_num) g.lambda) k).1, ← (CovGNative_chart F (le_trans (by norm_num) g.lambda) k).2, ← hc]
  have hmem' : (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2)⁻¹ * t ∈
      Set.Icc (fSeqStart F k) (fSeqEnd F k) := hc.symm ▸ hmem
  have hf' : ContDiff ℝ ((Dm + F.N : ℕ) : ℕ∞) (f t) := by simpa only [Nat.add_comm] using hf
  simpa only [neg_smul, liftLength, rRho, CovGLb] using covTruncMeanLetter_pulse_flux P _ _ hsx hsz (F.CcT k)
    (p.sequences k hk) 0 hres hh n hhh hn'.1 hn'.2
    (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2)
    (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F)
    (by rw [hc]; exact hcs.ne') (CovGChart F k) (CovGLabel F k)
    (fun s => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := s)).prodMk contDiff_id)) f t hf' hmem' y j v

/-- Exact action of a grade's physical CE coefficient on the finite classical field. -/
theorem CovGNativeCE_action {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (hA : CovGNativeAgreement F)
    (g : CovGNativeWindow F law) (hN : 1 ≤ F.N)
    (hh : ℕ) (hhh : hh ≤ F.depth)
    (f : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root) (t : ℝ)
    (hf : ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (f t))
    (ht : t ∈ Set.Icc F.tp (F.tp + fTobs F)) (y : Vec 2) (v : CompIn F.G.comps) :
    toFluxL (menuGluedMeanFlux F.Mn F.G F.m {hh}
      (Finset.Icc 2 (F.N + Dm)) F.CcT f t y v) =
      ∑ u, ∑ d : Finset.Icc 2 (F.N + Dm), CovGCE F (CovGLb F) hh v u d t y
        (WithLp.toLp 2 fun α => orderedDerivative α (fun z => f t z u) y) := by
  classical
  have hc := hA.scale_eq
  apply PiLp.ext
  intro j
  change menuGluedMeanFlux _ _ _ _ _ _ _ _ _ _ j = _
  rw [menuGluedMeanFlux_cascade _ hA.one, CovG_gluedMeanFlux_eq F law hA g hh f ht y v]
  simp only [Finset.sum_apply, Pi.smul_apply, WithLp.ofLp_sum]
  have he := covTruncMeanLetter_ce_action_finite
    (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (fun k => F.G.actualFamily.weight (oddSlotOf k))
    (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F)
    (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F)
    (F.N + Dm) (CovGChart F) (CovGLabel F) (fSeqStart F) (fSeqEnd F)
    (CovGLb F) hh t
    (fun k _ => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ z => CycleComparison.Charts.ocChart_ocChartInv _ _ _ _ _ _ _ t z)
    (fun k hk hw => hc.symm ▸ CovG_window_mem F law hA g k ht
      (by rwa [hA.weight_eq k (CycleComparison.LiftSetting.obsPulse_odd hk) t] at hw))
    (f t) hf y v j
  change (∑ u, ∑ d : Finset.Icc 2 (F.N + Dm),
    CovGCE F (CovGLb F) hh v u d t y
      (WithLp.toLp 2 fun α => orderedDerivative α (fun z => f t z u) y) j) = _ at he
  rw [he, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hw : F.G.actualFamily.weight (oddSlotOf k) t = 0
  · simp only [hw, zero_smul, neg_zero]
  · rw [CovGNativePF_action F law p hA g hN hh hhh f t hf ht k hk hw y v j, smul_neg]

/-- Exact finite grade-sum action, retaining the physical menu flux. -/
theorem CovGNativeGrade_action {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (hA : CovGNativeAgreement F)
    (g : CovGNativeWindow F law) (hN : 1 ≤ F.N)
    (rs : Finset ℕ) (hrs : ∀ hh ∈ rs, hh ≤ F.depth)
    (f : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root) (t : ℝ)
    (hf : ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (f t))
    (ht : t ∈ Set.Icc F.tp (F.tp + fTobs F)) (y : Vec 2) (v : CompIn F.G.comps) :
    toFluxL (menuGluedMeanFlux F.Mn F.G F.m rs
      (Finset.Icc 2 (F.N + Dm)) F.CcT f t y v) =
      ∑ u, ∑ d : Finset.Icc 2 (F.N + Dm), CovGNativeGradeCoefficient F rs v u d t y
        (WithLp.toLp 2 fun α => orderedDerivative α (fun z => f t z u) y) := by
  classical
  rw [gluedMeanFlux_sum_rs]
  have he : toFluxL (∑ hh ∈ rs, menuGluedMeanFlux F.Mn F.G F.m {hh}
      (Finset.Icc 2 (F.N + Dm)) F.CcT f t y v) =
      ∑ hh ∈ rs, toFluxL (menuGluedMeanFlux F.Mn F.G F.m {hh}
        (Finset.Icc 2 (F.N + Dm)) F.CcT f t y v) := by
    apply PiLp.ext
    intro j
    simp only [toFluxL, WithLp.ofLp_toLp, WithLp.ofLp_sum, Finset.sum_apply]
  rw [he]
  simp_rw [CovGNativeGradeCoefficient, sum_apply]
  calc
    _ = ∑ hh ∈ rs, ∑ u, ∑ d : Finset.Icc 2 (F.N + Dm),
      CovGCE F (CovGLb F) hh v u d t y
        (WithLp.toLp 2 fun α => orderedDerivative α (fun z => f t z u) y) :=
      Finset.sum_congr rfl fun hh hhh =>
        CovGNativeCE_action F law p hA g hN hh (hrs hh hhh) f t hf ht y v
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_comm

/-- The actual scalar letters, with all analytic fields and exact action discharged,
produce the gradient-carrier data of a finite set of native grades. -/
theorem CovGNativeGrade_data {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (hA : CovGNativeAgreement F)
    (K : ℕ) (hK : K ≤ wKlift Dm F.depth F.N Acl ell + 1) (g : CovGNativeWindow F law)
     (hN : 1 ≤ F.N)
    (hfamily : CovGFamily F) (hSb : 0 ≤ Sb)
    (rs : Finset ℕ) (hrs : ∀ hh ∈ rs, hh ≤ F.depth)
    (f : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root)
    (hf : ∀ v, ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F),
      ContDiff ℝ ((K + (F.N + Dm) + 1 : ℕ) : ℕ∞) (fun y => f t y v))
    (hp : ∀ v, ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), IsZ2Periodic (fun y => f t y v)) :
    Nonempty (CovTruncCoefficientData (h := fun v : CompIn F.G.comps => hr v.1.root)
      K (F.N + Dm) F.tp (F.tp + fTobs F) (fRho F)
      (covTruncGradientCoefficientConst K (F.N + Dm) *
        (D.κ (F.m - 1) * CovGNativeCEConst F.N Dm K
          (CovGLetterConst F Acl ell CG CW Ca) * ∑ hh ∈ rs, Sb ^ hh))
      (F.G.mass law) (fun v t y => toFluxL (gradE (fun z => f t z v) y))
      (fun v t y => toFluxL (menuGluedMeanFlux F.Mn F.G F.m rs
        (Finset.Icc 2 (F.N + Dm)) F.CcT f t y v))) := by
  classical
  have hreg := fun v u d => CovGNativeGrade_regular F law p K hK hfamily rs hrs v u d
  have hb := fun v u => CovGNativeGrade_budget F law p K hK g hfamily rs hrs v u
  have hSchur := CovGNativeGrade_schur F law p K g hfamily hSb rs
  apply covTruncCoefficientData_of_scalar_letters
    (h := fun v : CompIn F.G.comps => hr v.1.root)
    (CovGNativeGradeCoefficient F rs) g.rho_pos (F.G.mass law) _
    (CovGNativeGradePrice F law p K rs)
  · intro v u
    have hs : 0 < Real.sqrt ((F.G.mass law) u / (F.G.mass law) v) :=
      Real.sqrt_pos.mpr (div_pos (g.mass_pos u) (g.mass_pos v))
    exact nonneg_of_mul_nonneg_right (hSchur.nonneg v u) hs
  · exact fun v u d => (hreg v u d).1
  · exact fun v u d => (hreg v u d).2.2
  · exact fun v u d => (hreg v u d).2.1
  · exact fun v u => (hb v u).1
  · exact fun v u => (hb v u).2
  · exact hSchur.row_sum
  · exact hSchur.col_sum
  · exact hf
  · exact hp
  · intro v t ht y
    apply CovGNativeGrade_action F law p hA g hN rs hrs f t _ ht y v
    exact contDiff_pi.mpr fun u => (hf u t ht).of_le (by exact_mod_cast (by omega :
      F.N + Dm ≤ K + (F.N + Dm) + 1))

/-- Finite-input grade-zero native pulse flux vanishes above the diagonal cutoff. -/
theorem CovGNativePulse_cutoff {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (hA : CovGNativeAgreement F)
    (g : CovGNativeWindow F law) (hN : 1 ≤ F.N)
    (f : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root) (t : ℝ)
    (hf : ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (f t))
    (ht : t ∈ Set.Icc F.tp (F.tp + fTobs F)) (k : ℤ)
    (hk : k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (hw : ocCutoff D.α D.q D.Λ F.m k t ≠ 0)
    (n : ℕ) (hn : F.N + 1 < n) (hnR : n ≤ F.N + Dm)
    (y : Vec 2) (v : CompIn F.G.comps) :
    pulseMeanFluxEuler (D.cellScaleSq F.m) (F.Mn.lenFactor * liftLength D F.m)
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / (F.Mn.lenFactor * liftLength D F.m)) n 0
      (fSeqQ F k (CycleComparison.LiftSetting.obsPulse_odd hk)) (F.CcT k)
      (CovGFlow F k) (CovGInvFlow F k) f t y v = 0 := by
  classical
  have hodd := CycleComparison.LiftSetting.obsPulse_odd hk
  have hc := hA.scale_eq
  have hcs := hA.cell_pos
  have hmem := CovG_window_mem F law hA g k ht hw
  have hwin := CovG_mem_pulseWindow F law g k hw
  obtain ⟨hη, hag⟩ := hA.seq_agree k hodd
  have hag' := hag ((D.cellScaleSq F.m)⁻¹ * t)
    (by rw [mul_inv_cancel_left₀ hcs.ne']; exact hwin)
  have hsz : max 2 Dm ≤ max (wLlift Dm F.depth F.N ell + 1) (wLlift Dm F.depth F.N ell + 2) := by
    have h1 : Dm * 1 * 1 ≤ Dm * (F.depth + 1) * F.N :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hN
    unfold wLlift
    omega
  have hsx : max 2 Dm ≤ wKlift Dm F.depth F.N Acl ell + Dm + 2 := by omega
  have P := p.settings k hk
  have hres : 0 + (F.N + Dm) ≤ p.qs := by
    have hr := setting_ambient_output_supported P
    omega
  have hρ : F.Mn.lenFactor * liftLength D F.m = fRho F :=
    (congrArg (· * liftLength D F.m) hA.one).trans (one_mul _)
  funext j
  have he : pulseMeanFluxEuler (D.cellScaleSq F.m) (F.Mn.lenFactor * liftLength D F.m)
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / (F.Mn.lenFactor * liftLength D F.m)) n 0
      (fSeqQ F k hodd) (F.CcT k) (CovGFlow F k) (CovGInvFlow F k) f t y v j =
      pulseMeanFluxEuler (D.cellScaleSq F.m) (F.Mn.lenFactor * liftLength D F.m)
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / (F.Mn.lenFactor * liftLength D F.m)) n 0
      (fLiftData F k) (F.CcT k) (CovGFlow F k) (CovGInvFlow F k) f t y v j := by
    unfold pulseMeanFluxEuler
    rw [liftFluxX_congr_data (fSeqQ F k hodd) (fLiftData F k) hη (F.CcT k) _ 0 n hag']
  rw [he, hρ, ← (CovGNative_chart F (le_trans (by norm_num) g.lambda) k).1, ← (CovGNative_chart F (le_trans (by norm_num) g.lambda) k).2, ← hc]
  exact covTruncMeanLetter_pulse_cutoff P _ _ hsx hsz (F.CcT k) (p.sequences k hk) 0 hres
    n hn (by omega) hnR hN _ _ (by rw [hc]; exact hcs.ne') _ _
    (fun s => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := s)).prodMk contDiff_id)) f t
    (by simpa only [Nat.add_comm] using hf) (hc.symm ▸ hmem) y j v

/-- The menu's grade-zero degree range shortens at the actual finite input regularity. -/
theorem CovGNativeDiag_tail {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (hA : CovGNativeAgreement F)
    (g : CovGNativeWindow F law) (hN : 1 ≤ F.N) (hDm : 1 ≤ Dm)
    (f : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root) (t : ℝ)
    (hf : ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (f t))
    (ht : t ∈ Set.Icc F.tp (F.tp + fTobs F)) (y : Vec 2) (v : CompIn F.G.comps) :
    menuGluedMeanFlux F.Mn F.G F.m {0}
      (Finset.Icc 2 (F.N + Dm)) F.CcT f t y v =
    menuGluedMeanFlux F.Mn F.G F.m {0}
      (Finset.Icc 2 (F.N + 1)) F.CcT f t y v := by
  classical
  have hτ : 0 < ocTau D.α D.q D.Λ F.m :=
    Construction.Stream.ocTau_pos (le_trans (by norm_num) g.lambda)
  simp only [menuGluedMeanFlux, Finset.sum_singleton]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkobs := obsPulses_time_subset D.α D.q D.Λ F.m hτ ht hk
  have hD : 1 ≤ Dm := hDm
  have hsub : Finset.Icc 2 (F.N + 1) ⊆ Finset.Icc 2 (F.N + Dm) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  refine (Finset.sum_subset hsub fun n hn hnn => ?_).symm
  have hnR := (Finset.mem_Icc.mp hn).2
  have hnN : F.N + 1 < n := by
    have hn2 := (Finset.mem_Icc.mp hn).1
    simp only [Finset.mem_Icc, not_and, not_le] at hnn
    exact hnn hn2
  split_ifs with hodd
  · by_cases hw : ocCutoff D.α D.q D.Λ F.m k t = 0
    · rw [hw, zero_smul]
    · have hz := CovGNativePulse_cutoff F law p hA g hN f t hf ht k hkobs hw n hnN hnR y v
      exact (congrArg (fun Z : Fin 2 → hr v.1.root =>
        ocCutoff D.α D.q D.Λ F.m k t • Z) hz).trans (smul_zero _)
  · rfl

end AVRegularity.Construction.Residual.Presentation.Cascade
end
