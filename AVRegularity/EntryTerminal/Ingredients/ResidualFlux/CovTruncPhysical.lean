-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.SchurF
public import AVRegularity.EntryTerminal.Ingredients.Recon.Letters.Input
public import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.MacroSwapLettersReg
import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.ConvAssembly
import AVRegularity.EntryTerminal.Ingredients.Recon.Times.Times
public import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleComparison.LiftMeanEntrywise.Assembly
import AVRegularity.EntryTerminal.Ingredients.QuietEntrance.ZeroAssembly
import AVRegularity.EntryTerminal.Ingredients.Recon.Family.Main

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.EntryTerminal.Ingredients.Recon.Letters
open AVRegularity.CycleComparison.Assembly AVRegularity.CycleComparison.ActualMeans
open AVRegularity.CycleComparison.Lift AVRegularity.CycleComparison.LiftMeanEntrywise
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation

/-! The actual terminal pulse letters, with the single matrix of the lift setting shared by all pulses.
Constants are explicit functions of the orders and the lift-setting constants. Grade zero is retained
for the diagonal flux. Empty families and empty positive-grade ranges use the same sums. -/

/-- The letter construction's explicit constant, fixed before the context or pulse. -/
def covTruncNativeLetterConst {X : TermConstruction} (A : TermArgs X) (ell : ℕ)
    (CG CW : ℕ → ℝ) (Ca : ℝ) : ℝ :=
  ambientMeanGradeConstant (rKlift A ell) A.NT (rLlift A ell) (rLlift A ell)
    A.Dt A.dW CG CW (fun _ _ => Ca)

/-- The mean transport's constant depends only on the requested orders and the renewal chart bounds. -/
def covTruncNativeTransferConst (N D K : ℕ) : ℝ :=
  Classical.choose (ceLetter_means_bound.{0, 0} N D K
    (CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ))))

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- The geometry used by the coefficient proof, independent of drift-jet orders. -/
structure CovTruncNativeWindow where
  window : c.tp ≤ c.tp + rTobs c
  rho_pos : 0 < rRho c
  B_pos : 0 < c.D.κ (M - 1)
  mass_pos : ∀ v, 0 < c.Gw.mass c.lawW v

/-- The existing terminal context and reconstruction deadline give this geometry. -/
theorem covTruncNativeWindow_of_ctx (hΛ : 128 ≤ A.Λ) (hdl : c.tp ≤ c.a + A.T₀) :
    CovTruncNativeWindow c := by
  have hΛ1 : 1 ≤ c.D.Λ := c.data.2.2.1 ▸ (by omega : 1 ≤ A.Λ)
  have hB : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos (by omega) X.hζ
    c.data.2.2.2.2.2.1 (Nat.sub_le M 1)
  have hh : 0 < ocTauPP c.D.α c.D.q c.D.Λ M := Construction.Stream.ocTauPP_pos hΛ1
  refine ⟨?_, Real.sqrt_pos.mpr (mul_pos hB hh), hB, ?_⟩
  · have hend : c.tp + rTobs c = c.a + A.T₀ := by unfold rTobs; ring
    rwa [hend]
  · intro v
    exact Construction.Preservation.Buffer.birth_compMass_pos (c.data.2.1 ▸ X.hq.1)
      (c.data.2.2.1 ▸ hΛ) c.lawW v.1

/-- The canonical letters of the supplied sequences, without a newly chosen sequence. -/
abbrev covTruncNativeLb (k : ℤ) := meanLetter (rLiftData c k) (c.CcT k)

/-- A high-order input with the common source matrix of the lift setting. The pulse settings and sequences
are premises supplied by the lift-setting and lift-sequence steps, respectively. -/
structure CovTruncNativePulse (ell : ℕ) (CG CW : ℕ → ℝ) (Ca Sb : ℝ) where
  qs : ℕ
  qf : ℕ
  par : ℤ → Fin 2
  V : ℤ → ℝ → ℝ → ℝ
  edge : CompIn c.Gw.comps → CompIn c.Gw.comps → ℝ
  settings : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
    IsLiftSetting (rLiftData c k) (c.Gw.mass c.lawW) (rSeqStart c k) (rSeqEnd c k)
      (ocEpsilon c.D.q c.D.Λ M) (c.D.κ M) (c.D.κ (M - 1)) (rRho c)
      (ocEpsilon c.D.q c.D.Λ (M - 1)) (ocEll c.D.q c.D.Λ M (c.D.κ M))
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)))
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c)
      (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) (par k) (V k) A.dW A.NT
      (rKlift A ell) (rLlift A ell) (rLlift A ell) qs qf CG CW (fun _ _ => Ca) edge Sb
  sequences : ReconSeqAt c ell

/-- The lift-sequence and lift-setting steps supply the common pulse input. -/
theorem covTruncNativePulse_of_setting (ell : ℕ) (CG CW : ℕ → ℝ) (Ca Sb Cg : ℝ)
    (x : TermResAux c) (hs : ReconSeqAt c ell) (hP : ReconSettingAt c x ell CG CW Ca Sb Cg) :
    Nonempty (CovTruncNativePulse c ell CG CW Ca Sb) := by
  obtain ⟨qs, qf, par, V, edge, hp, -⟩ := hP
  exact ⟨⟨qs, qf, par, V, edge, hp, hs⟩⟩

/-- All seven letter clauses at the uniform explicit constant. -/
theorem covTruncNativePulse_letters {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (k : ℤ)
    (hk : k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c)) :
    IsPulseLetters (rLiftData c k) (c.CcT k) (c.Gw.mass c.lawW) p.edge
      (rSeqStart c k) (rSeqEnd c k) (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1))
      (covTruncNativeLetterConst A ell CG CW Ca) A.NT A.dW (rKlift A ell)
      (covTruncNativeLb c k) := by
  have hL := fun hh hhh n hn hnR => setting_meanLetter_entrywise
    (p.settings k hk) (c.CcT k) (p.sequences k hk) hh hhh n hn hnR
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
theorem covTruncNativeCE_regular {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (K : ℕ) (hK : K ≤ rKlift A ell + 1)
    (hfamily : ReconFamilyAt c 0) (hh : ℕ) (hhh : hh ≤ A.dW) (v u : CompIn c.Gw.comps)
    (d : Finset.Icc 2 (A.NT + A.Dt)) :
    (∀ t ∈ Set.Icc c.tp (c.tp + rTobs c),
      ContDiff ℝ (K : ℕ) (reconCE c (covTruncNativeLb c) hh v u d t)) ∧
    Measurable (fun q : Set.Icc c.tp (c.tp + rTobs c) × Vec 2 =>
      reconCE c (covTruncNativeLb c) hh v u d q.1 q.2) ∧
    (∀ t ∈ Set.Icc c.tp (c.tp + rTobs c),
      IsZ2Periodic (reconCE c (covTruncNativeLb c) hh v u d t)) := by
  classical
  obtain ⟨T, hf⟩ := hfamily
  obtain ⟨-, hw, -, -⟩ := partition_stage_facts hf.2.2.2.2.2.2.2.2.1
  have hreg : (((K : ℕ) : ℕ∞) : WithTop ℕ∞) ≤
      (((rKlift A ell + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hK
  refine ⟨fun t _ => ?_, ?_, fun t _ => ?_⟩
  · exact_mod_cast contDiff_ceLetter _ _ _ _ _ _ _ _ _ _ _ K hh v u d t
      (fun k _ => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
        ((contDiff_const (c := t)).prodMk contDiff_id))
      (fun k _ => (CycleComparison.Charts.contDiff_ocChartInv_joint _ _ _ _ _ _).comp
        ((contDiff_const (c := t)).prodMk contDiff_id))
      (fun k hk n hn hnN d _ _ α l s hs =>
        ((covTruncNativePulse_letters c p k hk).smooth hh hhh n hn hnN d α l v u s hs).of_le hreg)
  · exact measurable_ceLetter _ _ _ _ _ _ _ _ _ _ _ c.tp (c.tp + rTobs c) hh v u d hw
      (fun k _ => CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _)
      (fun k _ => CycleComparison.Charts.contDiff_ocChartInv_joint _ _ _ _ _ _)
      (fun k hk n hn hnN d _ _ α l Y =>
        (covTruncNativePulse_letters c p k hk).meas hh hhh n hn hnN d α l v u Y)
      (fun k hk n hn hnN d _ _ α l s hs =>
        ((covTruncNativePulse_letters c p k hk).smooth hh hhh n hn hnN d α l v u s hs).continuous)
  · exact isZ2Periodic_ceLetter _ _ _ _ _ _ _ _ _ _ _ hh v u d t
      (fun k _ z y => CycleComparison.Charts.ocChart_latticeShift _ _ _ _ _ _ t z y)
      (fun k _ z y => CycleReference.streamFlow_lattice_equivariant (c.D.hΦ (M - 1))
        ((ocPulseChartIndex c.D.α c.D.q c.D.Λ M k : ℝ) * ocTauPP c.D.α c.D.q c.D.Λ M) t y z)
      (fun k hk n hn hnN d _ _ α l s hs z Y =>
        (covTruncNativePulse_letters c p k hk).shift ((rRho c)⁻¹ • latticeShift z)
          (fun t Y i j => pulseLiftData_G_shift c.D.α c.D.q c.D.Λ M c.D.ζ (c.D.hΦ (M - 1))
            (c.D.κ M) (c.D.κ (M - 1)) (p.settings k hk).ρ_pos.ne' _ k _ z t Y i j)
          (fun v u d γ hγ α t Y Z => liftEdges_fiber_coeff_shift
            (p.settings k hk).ρ_pos.ne' hf.2.1
            (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (oddSlotOf k) z hγ α t Y Z)
          hh hhh n hn hnN d α l v u s hs Y)

/-- One observed pulse suffices to read the common matrix's Schur budget and scale inequalities.
The nonempty observation window and partition guarantee that such a pulse exists. -/
theorem covTruncNativePulse_scales {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (g : CovTruncNativeWindow c)
    (hfamily : ReconFamilyAt c 0) :
    ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) ≤ rRho c ∧
    rRho c ≤ ocEpsilon c.D.q c.D.Λ (M - 1) ∧ HasRealSchurBudget p.edge Sb := by
  obtain ⟨T, hf⟩ := hfamily
  have hsum := hf.2.2.2.2.2.2.2.2.1.2.2.1 c.tp ⟨le_rfl, g.window⟩
  obtain ⟨k, hk, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  have P := p.settings k hk
  exact ⟨(div_le_one P.ρ_pos).mp P.εc_le, (div_le_one P.E_pos).mp P.lam_le,
    ⟨P.envelope.nonneg, P.envelope.row_sum, P.envelope.col_sum⟩⟩

/-- Uniform mean-transport price for one grade, after undoing the mass conjugation. -/
def covTruncNativeCEConst (N D K : ℕ) (C₂ : ℝ) : ℝ :=
  2 * ((N + D : ℕ) : ℝ) ^ 2 * ((K : ℝ) + 1) *
    (covTruncNativeTransferConst N D K * C₂)

/-- Both radii have a normalized entrywise budget controlled by the SAME physical matrix
power for every pulse. This includes grade zero; no source height is silently discarded. -/
theorem covTruncNativeCE_budget {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (K : ℕ) (hK : K ≤ rKlift A ell + 1)
    (g : CovTruncNativeWindow c) (hΛ : 128 ≤ A.Λ) (hM : 2 ≤ M)
    (hfamily : ReconFamilyAt c 0) (hh : ℕ) (hhh : hh ≤ A.dW) (v u : CompIn c.Gw.comps) :
    ∑ d : Finset.Icc 2 (A.NT + A.Dt),
      coefficientSeminorm (rRho c) K c.tp (c.tp + rTobs c)
        (reconCE c (covTruncNativeLb c) hh v u d) *
        (ENNReal.ofReal (c.D.κ (M - 1) * rRho c ^ (d.val - 2)))⁻¹ ≤
      ENNReal.ofReal (covTruncNativeCEConst A.NT A.Dt K
        (covTruncNativeLetterConst A ell CG CW Ca) *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix (c.Gw.mass c.lawW) p.edge) hh v u) := by
  classical
  obtain ⟨hα, hq, hΛD, hζ, hseq, hband, -⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ (by omega : 1 ≤ A.Λ)
  have hν : 0 < c.D.κ M := CycleReference.bandChain_pos (by omega) X.hζ hband le_rfl
  have hℓ : 0 < ocEll c.D.q c.D.Λ M (c.D.κ M) :=
    div_pos (Construction.Stream.ocEpsilon_pos hΛ1) (Real.sqrt_pos.mpr hν)
  obtain ⟨hdρ, hρE, hSchur⟩ := covTruncNativePulse_scales c p g hfamily
  obtain ⟨T, hf⟩ := hfamily
  obtain ⟨hϖ0, -, hϖ1, -⟩ := partition_stage_facts hf.2.2.2.2.2.2.2.2.1
  have hC₂ : 0 ≤ covTruncNativeLetterConst A ell CG CW Ca :=
    ambientMeanGradeConstant_nonneg _ _ _ _ _ _ _ _ _
  have hM0 : 0 ≤ covTruncNativeLetterConst A ell CG CW Ca *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix (c.Gw.mass c.lawW) p.edge) hh v u :=
    mul_nonneg hC₂ (finiteMatrixPower_nonneg _
      (physicalEdgeEnvelopeMatrix_nonneg _ _ hSchur.nonneg) hh v u)
  have hreg : (((K : ℕ) : ℕ∞) : WithTop ℕ∞) ≤
      (((rKlift A ell + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hK
  have hbound := (Classical.choose_spec (ceLetter_means_bound.{0, 0} A.NT A.Dt K
    (CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ))))).2
      (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root)
  have hb := hbound
    (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (fun k => c.Gw.actualFamily.weight (oddSlotOf k))
    (ocEll c.D.q c.D.Λ M (c.D.κ M)) (c.D.κ (M - 1))
    (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1))) (rRho c)
    (ocEpsilon c.D.q c.D.Λ (M - 1)) c.tp (c.tp + rTobs c)
    (reconChart c) (reconLabel c) (rSeqStart c) (rSeqEnd c) (covTruncNativeLb c) hh v u
    (covTruncNativeLetterConst A ell CG CW Ca *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix (c.Gw.mass c.lawW) p.edge) hh v u)
    hℓ g.B_pos g.rho_pos (CycleComparison.LiftSetting.dstar_eq _ _ _ hν.le _)
    hdρ hρE hM0 hϖ0 hϖ1
    (fun k _ t => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ t => (CycleComparison.Charts.contDiff_ocChartInv_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ t ht hwin j hj hjK y => recon_chart_jets c hΛ hM _ k t ht hwin j hj hjK y)
    (fun k hk n hn hnN d _ _ α l s hs =>
      ((covTruncNativePulse_letters c p k hk).smooth hh hhh n hn hnN d α l v u s hs).of_le hreg)
    (fun k hk n hn hnN d hd hdn α l i hi s hs Y =>
      (covTruncNativePulse_letters c p k hk).bound hh hhh n hn hnN d hd hdn α l v u i
        (hi.trans hK) s hs Y) K le_rfl
  refine (le_add_of_nonneg_left (by positivity)).trans (hb.trans_eq ?_)
  congr 1
  unfold covTruncNativeCEConst covTruncNativeTransferConst
  ring

/-- The same price in real seminorms, with the diffusivity restored. -/
theorem covTruncNativeCE_real_budget {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (K : ℕ) (hK : K ≤ rKlift A ell + 1)
    (g : CovTruncNativeWindow c) (hΛ : 128 ≤ A.Λ) (hM : 2 ≤ M)
    (hfamily : ReconFamilyAt c 0) (hh : ℕ) (hhh : hh ≤ A.dW) (v u : CompIn c.Gw.comps) :
    (∀ d : Finset.Icc 2 (A.NT + A.Dt),
      coefficientSeminorm (rRho c) K c.tp (c.tp + rTobs c)
        (reconCE c (covTruncNativeLb c) hh v u d) ≠ ⊤) ∧
    (∑ d : Finset.Icc 2 (A.NT + A.Dt),
      (coefficientSeminorm (rRho c) K c.tp (c.tp + rTobs c)
        (reconCE c (covTruncNativeLb c) hh v u d)).toReal / rRho c ^ (d.val - 2)) ≤
      c.D.κ (M - 1) * (covTruncNativeCEConst A.NT A.Dt K
        (covTruncNativeLetterConst A ell CG CW Ca) *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix (c.Gw.mass c.lawW) p.edge) hh v u) := by
  have hb := covTruncNativeCE_budget c p K hK g hΛ hM hfamily hh hhh v u
  have hf := fun d => ne_top_of_sum_inv_le _ _ hb d
  refine ⟨hf, ?_⟩
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [CycleComparison.Coarse.toReal_sum_sem_div g.B_pos g.rho_pos _ hf] at hr
  have hC₂ : 0 ≤ covTruncNativeLetterConst A ell CG CW Ca :=
    ambientMeanGradeConstant_nonneg _ _ _ _ _ _ _ _ _
  have hCt : 0 ≤ covTruncNativeTransferConst A.NT A.Dt K :=
    (Classical.choose_spec (ceLetter_means_bound.{0, 0} A.NT A.Dt K
      (CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ))))).1
  have hSchur := (covTruncNativePulse_scales c p g hfamily).2.2
  have hprice : 0 ≤ covTruncNativeCEConst A.NT A.Dt K
      (covTruncNativeLetterConst A ell CG CW Ca) *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix (c.Gw.mass c.lawW) p.edge) hh v u := by
    unfold covTruncNativeCEConst
    exact mul_nonneg (by positivity) (finiteMatrixPower_nonneg _
      (physicalEdgeEnvelopeMatrix_nonneg _ _ hSchur.nonneg) hh v u)
  rw [ENNReal.toReal_ofReal hprice] at hr
  have hmul := mul_le_mul_of_nonneg_left hr g.B_pos.le
  refine le_trans (le_of_eq ?_) hmul
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by field_simp [g.B_pos.ne']

/-- The actual scalar coefficients of a finite set of constrained source grades. -/
def covTruncNativeGradeCoefficient (rs : Finset ℕ) (v u : CompIn c.Gw.comps)
    (d : Finset.Icc 2 (A.NT + A.Dt)) (t : ℝ) (y : Vec 2) :=
  ∑ hh ∈ rs, reconCE c (covTruncNativeLb c) hh v u d t y

/-- Sum the actual CE coefficients, keeping the individual suprema before the grade sum. -/
theorem covTruncNativeGrade_regular {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (K : ℕ) (hK : K ≤ rKlift A ell + 1)
    (hfamily : ReconFamilyAt c 0) (rs : Finset ℕ) (hrs : ∀ hh ∈ rs, hh ≤ A.dW)
    (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)) :
    (∀ t ∈ Set.Icc c.tp (c.tp + rTobs c),
      ContDiff ℝ (K : ℕ) (covTruncNativeGradeCoefficient c rs v u d t)) ∧
    Measurable (fun q : Set.Icc c.tp (c.tp + rTobs c) × Vec 2 =>
      covTruncNativeGradeCoefficient c rs v u d q.1 q.2) ∧
    (∀ t ∈ Set.Icc c.tp (c.tp + rTobs c),
      IsZ2Periodic (covTruncNativeGradeCoefficient c rs v u d t)) := by
  have hreg := fun hh hhh => covTruncNativeCE_regular c p K hK hfamily hh (hrs hh hhh) v u d
  refine ⟨fun t ht => ContDiff.sum (fun hh hhh => (hreg hh hhh).1 t ht), ?_, ?_⟩
  · exact Finset.measurable_sum rs fun hh hhh => (hreg hh hhh).2.1
  · intro t ht z y
    exact Finset.sum_congr rfl fun hh hhh => (hreg hh hhh).2.2 t ht z y

/-- Grade sum's entrywise price, still before mass conjugation. -/
def covTruncNativeGradePrice {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (K : ℕ) (rs : Finset ℕ)
    (v u : CompIn c.Gw.comps) : ℝ :=
  ∑ hh ∈ rs, c.D.κ (M - 1) * (covTruncNativeCEConst A.NT A.Dt K
    (covTruncNativeLetterConst A ell CG CW Ca) *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix (c.Gw.mass c.lawW) p.edge) hh v u)

/-- The finite grade sum has the sum of the individual normalized prices, not a price
involving the number of components. -/
theorem covTruncNativeGrade_budget {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (K : ℕ) (hK : K ≤ rKlift A ell + 1)
    (g : CovTruncNativeWindow c) (hΛ : 128 ≤ A.Λ) (hM : 2 ≤ M)
    (hfamily : ReconFamilyAt c 0) (rs : Finset ℕ) (hrs : ∀ hh ∈ rs, hh ≤ A.dW)
    (v u : CompIn c.Gw.comps) :
    (∀ d : Finset.Icc 2 (A.NT + A.Dt),
      coefficientSeminorm (rRho c) K c.tp (c.tp + rTobs c)
        (covTruncNativeGradeCoefficient c rs v u d) ≠ ⊤) ∧
    (∑ d : Finset.Icc 2 (A.NT + A.Dt),
      (coefficientSeminorm (rRho c) K c.tp (c.tp + rTobs c)
        (covTruncNativeGradeCoefficient c rs v u d)).toReal / rRho c ^ (d.val - 2)) ≤
      covTruncNativeGradePrice c p K rs v u := by
  classical
  have hb := fun hh hhh =>
    covTruncNativeCE_real_budget c p K hK g hΛ hM hfamily hh (hrs hh hhh) v u
  have hs := fun hh hhh d t ht =>
    (covTruncNativeCE_regular c p K hK hfamily hh (hrs hh hhh) v u d).1 t ht
  refine ⟨fun d => CycleJointProofs.coefficientSeminorm_sum_ne_top rs
    (fun hh => reconCE c (covTruncNativeLb c) hh v u d) _ _ _ _
      (fun hh hhh => hs hh hhh d) (fun hh hhh => (hb hh hhh).1 d), ?_⟩
  calc
    _ ≤ ∑ d : Finset.Icc 2 (A.NT + A.Dt), ∑ hh ∈ rs,
        (coefficientSeminorm (rRho c) K c.tp (c.tp + rTobs c)
          (reconCE c (covTruncNativeLb c) hh v u d)).toReal / rRho c ^ (d.val - 2) := by
      refine Finset.sum_le_sum fun d _ => ?_
      rw [← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ (pow_nonneg g.rho_pos.le _)
      have hfinite : (∑ hh ∈ rs, coefficientSeminorm (rRho c) K c.tp (c.tp + rTobs c)
          (reconCE c (covTruncNativeLb c) hh v u d)) ≠ ⊤ :=
        ENNReal.sum_ne_top.mpr (fun hh hhh => (hb hh hhh).1 d)
      have hle := ENNReal.toReal_mono hfinite (CycleJointProofs.coefficientSeminorm_sum_le rs
        (fun hh => reconCE c (covTruncNativeLb c) hh v u d) _ _ _ _ (fun hh hhh => hs hh hhh d))
      rwa [ENNReal.toReal_sum (fun hh hhh => (hb hh hhh).1 d)] at hle
    _ = ∑ hh ∈ rs, ∑ d : Finset.Icc 2 (A.NT + A.Dt),
        (coefficientSeminorm (rRho c) K c.tp (c.tp + rTobs c)
          (reconCE c (covTruncNativeLb c) hh v u d)).toReal / rRho c ^ (d.val - 2) :=
      Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun hh hhh => (hb hh hhh).2)

private theorem native_schur_sum {ι : Type} [Fintype ι] (rs : Finset ℕ)
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
theorem covTruncNativeGrade_schur {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (K : ℕ)
    (g : CovTruncNativeWindow c) (hfamily : ReconFamilyAt c 0) (hSb : 0 ≤ Sb) (rs : Finset ℕ) :
    HasRealSchurBudget
      (massConjugatedMatrix (c.Gw.mass c.lawW) (covTruncNativeGradePrice c p K rs))
      (c.D.κ (M - 1) * covTruncNativeCEConst A.NT A.Dt K
        (covTruncNativeLetterConst A ell CG CW Ca) * ∑ hh ∈ rs, Sb ^ hh) := by
  have hC₂ : 0 ≤ covTruncNativeLetterConst A ell CG CW Ca :=
    ambientMeanGradeConstant_nonneg _ _ _ _ _ _ _ _ _
  have hCt : 0 ≤ covTruncNativeTransferConst A.NT A.Dt K :=
    (Classical.choose_spec (ceLetter_means_bound.{0, 0} A.NT A.Dt K
      (CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ))))).1
  have hB : 0 ≤ c.D.κ (M - 1) := g.B_pos.le
  have hC : 0 ≤ c.D.κ (M - 1) * covTruncNativeCEConst A.NT A.Dt K
      (covTruncNativeLetterConst A ell CG CW Ca) := by
    unfold covTruncNativeCEConst
    positivity
  have hSchur := (covTruncNativePulse_scales c p g hfamily).2.2
  have hp := fun hh =>
    (physicalEdgeEnvelopeMatrix_power_schur_budget (c.Gw.mass c.lawW) g.mass_pos p.edge Sb hSb
      hSchur hh).const_mul _ hC
  have hs := native_schur_sum rs _ _ (fun hh _ => hp hh)
  convert hs using 1
  · funext v u
    unfold massConjugatedMatrix covTruncNativeGradePrice
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun hh _ => by ring
  · exact Finset.mul_sum _ _ _

/-- The renewal chart and the menu's native flow chart coincide. -/
theorem covTruncNative_chart (hΛ : 1 ≤ A.Λ) (k : ℤ) :
    reconChart c k = chart' c k ∧ reconLabel c k = label' c k := by
  have hτ : 0 < ocTauPP c.D.α c.D.q c.D.Λ M :=
    Construction.Stream.ocTauPP_pos (c.data.2.2.1 ▸ hΛ)
  constructor <;> funext t y
  · show _ = c.D.flowOf (M - 1) t y (c.D.slotAnchor M k)
    unfold reconChart ocChart OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex c.D.α c.D.q c.D.Λ M k hτ]
  · show _ = c.D.flowOf (M - 1) (c.D.slotAnchor M k) y t
    unfold reconLabel ocChartInv OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex c.D.α c.D.q c.D.Λ M k hτ]

/-- The literal flux of an active native pulse, from finite-regularity cell means and data
agreement on the pulse window. This does not invoke the divergence-only mean presentation. -/
theorem covTruncNativePF_action {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (xaux : TermResAux c)
    (hΛ : 1 ≤ A.Λ) (hM : 1 ≤ M) (hN : 1 ≤ A.NT)
    (hh : ℕ) (hhh : hh ≤ A.dW)
    (f : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root) (t : ℝ)
    (hf : ContDiff ℝ ((A.NT + A.Dt : ℕ) : ℕ∞) (f t))
    (ht : t ∈ Set.Icc c.tp (c.tp + rTobs c)) (k : ℤ)
    (hk : k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (hw : c.Gw.actualFamily.weight (oddSlotOf k) t ≠ 0)
    (y : Vec 2) (v : CompIn c.Gw.comps) (j : Fin 2) :
    corePulseFlux c hh f k t y v j =
      -∑ n ∈ Finset.Icc 2 (A.NT + A.Dt),
        ((ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)⁻¹ *
          (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) ^ n) •
          ∑ l : Fin 2, jacMatrix (reconChart c k t) (reconLabel c k t y) j l •
            ∑ d ∈ Finset.Icc 2 n, rRho c ^ d • ∑ α : DerivativeWord2 (d - 1), ∑ u,
              covTruncNativeLb c k hh n d α
                ((ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)⁻¹ * t)
                ((rRho c)⁻¹ • reconLabel c k t y) l v u
                (orderedDerivative α (fun z => f t (reconChart c k t z)) (reconLabel c k t y) u) := by
  classical
  have hodd : Odd k := CycleComparison.LiftSetting.obsPulse_odd hk
  have hcut : ocCutoff c.D.α c.D.q c.D.Λ M k t ≠ 0 := by
    rwa [weight_eq' c k hodd t] at hw
  have hc := ocEll_sq_eq' c hΛ
  have hcs := cellScaleSq_pos c hΛ
  have hmem := window_mem c hΛ k ht hcut
  have hwin := mem_pulseWindow c hΛ k hcut
  obtain ⟨hη, hag⟩ := Seq.seq_agree c xaux.one hΛ hM hodd
  have hag' := hag ((c.D.cellScaleSq M)⁻¹ * t)
    (by rw [mul_inv_cancel_left₀ hcs.ne']; exact hwin)
  have hQ : familyLiftData c.D M k (nativeChain M k) (liftLength c.D M)
      (c.Gw.fam.fiber ⟨k, hodd⟩ (c.Gw.actual ⟨k, hodd⟩)) = Seq.seqQ c k hodd := by
    simp only [Seq.seqQ, (congrArg (· * liftLength c.D M) xaux.one).trans (one_mul _)]
  have hsz : max 2 A.Dt ≤ max (rLlift A ell + 1) (rLlift A ell + 2) := by
    have hDt : 2 ≤ A.Dt := le_max_left _ _
    have h1 : A.Dt * 1 * 1 ≤ A.Dt * (A.dW + 1) * A.NT :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hN
    unfold rLlift
    omega
  have hsx : max 2 A.Dt ≤ rKlift A ell + A.Dt + 2 := by omega
  have P := p.settings k hk
  have hres : 0 + (A.NT + A.Dt) ≤ p.qs := by
    have hr := setting_ambient_output_supported P
    omega
  unfold corePulseFlux
  simp only [hodd, dite_true, Finset.sum_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_Icc.mp hn
  rw [hQ]
  have he : pulseMeanFluxEuler (c.D.cellScaleSq M) (liftLength c.D M)
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / liftLength c.D M)
      n hh (Seq.seqQ c k hodd) (c.CcT k) (chart' c k) (label' c k) f t y v j =
      pulseMeanFluxEuler (c.D.cellScaleSq M) (liftLength c.D M)
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / liftLength c.D M)
      n hh (rLiftData c k) (c.CcT k) (chart' c k) (label' c k) f t y v j := by
    unfold pulseMeanFluxEuler
    rw [liftFluxX_congr_data (Seq.seqQ c k hodd) (rLiftData c k) hη (c.CcT k) _ hh n hag']
  rw [he, ← (covTruncNative_chart c hΛ k).1, ← (covTruncNative_chart c hΛ k).2, ← hc]
  have hmem' : (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)⁻¹ * t ∈
      Set.Icc (rSeqStart c k) (rSeqEnd c k) := hc.symm ▸ hmem
  have hf' : ContDiff ℝ ((A.Dt + A.NT : ℕ) : ℕ∞) (f t) := by simpa only [Nat.add_comm] using hf
  simpa only [neg_smul, liftLength, rRho, covTruncNativeLb] using covTruncMeanLetter_pulse_flux P _ _ hsx hsz (c.CcT k)
    (p.sequences k hk) 0 hres hh n hhh hn'.1 hn'.2
    (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)
    (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c)
    (by rw [hc]; exact hcs.ne') (reconChart c k) (reconLabel c k)
    (fun s => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := s)).prodMk contDiff_id)) f t hf' hmem' y j v

/-- Exact action of a grade's physical CE coefficient on the finite classical field. -/
theorem covTruncNativeCE_action {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (xaux : TermResAux c)
    (hΛ : 1 ≤ A.Λ) (hM : 1 ≤ M) (hN : 1 ≤ A.NT)
    (hh : ℕ) (hhh : hh ≤ A.dW)
    (f : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root) (t : ℝ)
    (hf : ContDiff ℝ ((A.NT + A.Dt : ℕ) : ℕ∞) (f t))
    (ht : t ∈ Set.Icc c.tp (c.tp + rTobs c)) (y : Vec 2) (v : CompIn c.Gw.comps) :
    toFluxL (menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {hh}
      (Finset.Icc 2 (A.NT + A.Dt)) c.CcT f t y v) =
      ∑ u, ∑ d : Finset.Icc 2 (A.NT + A.Dt), reconCE c (covTruncNativeLb c) hh v u d t y
        (WithLp.toLp 2 fun α => orderedDerivative α (fun z => f t z u) y) := by
  classical
  have hc := ocEll_sq_eq' c hΛ
  apply PiLp.ext
  intro j
  change menuGluedMeanFlux _ _ _ _ _ _ _ _ _ _ j = _
  rw [menuGluedMeanFlux_cascade _ xaux.one, gluedMeanFlux_eq c hΛ hh f ht y v]
  simp only [Finset.sum_apply, Pi.smul_apply, WithLp.ofLp_sum]
  have he := covTruncMeanLetter_ce_action_finite
    (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (fun k => c.Gw.actualFamily.weight (oddSlotOf k))
    (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c)
    (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c)
    (A.NT + A.Dt) (reconChart c) (reconLabel c) (rSeqStart c) (rSeqEnd c)
    (covTruncNativeLb c) hh t
    (fun k _ => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ z => CycleComparison.Charts.ocChart_ocChartInv _ _ _ _ _ _ _ t z)
    (fun k hk hw => hc.symm ▸ window_mem c hΛ k ht
      (by rwa [weight_eq' c k (CycleComparison.LiftSetting.obsPulse_odd hk) t] at hw))
    (f t) hf y v j
  change (∑ u, ∑ d : Finset.Icc 2 (A.NT + A.Dt),
    reconCE c (covTruncNativeLb c) hh v u d t y
      (WithLp.toLp 2 fun α => orderedDerivative α (fun z => f t z u) y) j) = _ at he
  rw [he, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hw : c.Gw.actualFamily.weight (oddSlotOf k) t = 0
  · simp only [hw, zero_smul, neg_zero]
  · rw [covTruncNativePF_action c p xaux hΛ hM hN hh hhh f t hf ht k hk hw y v j, smul_neg]

/-- Exact finite grade-sum action, retaining the physical menu flux. -/
theorem covTruncNativeGrade_action {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (xaux : TermResAux c)
    (hΛ : 1 ≤ A.Λ) (hM : 1 ≤ M) (hN : 1 ≤ A.NT)
    (rs : Finset ℕ) (hrs : ∀ hh ∈ rs, hh ≤ A.dW)
    (f : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root) (t : ℝ)
    (hf : ContDiff ℝ ((A.NT + A.Dt : ℕ) : ℕ∞) (f t))
    (ht : t ∈ Set.Icc c.tp (c.tp + rTobs c)) (y : Vec 2) (v : CompIn c.Gw.comps) :
    toFluxL (menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M rs
      (Finset.Icc 2 (A.NT + A.Dt)) c.CcT f t y v) =
      ∑ u, ∑ d : Finset.Icc 2 (A.NT + A.Dt), covTruncNativeGradeCoefficient c rs v u d t y
        (WithLp.toLp 2 fun α => orderedDerivative α (fun z => f t z u) y) := by
  classical
  rw [gluedMeanFlux_sum_rs]
  have he : toFluxL (∑ hh ∈ rs, menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {hh}
      (Finset.Icc 2 (A.NT + A.Dt)) c.CcT f t y v) =
      ∑ hh ∈ rs, toFluxL (menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {hh}
        (Finset.Icc 2 (A.NT + A.Dt)) c.CcT f t y v) := by
    apply PiLp.ext
    intro j
    simp only [toFluxL, WithLp.ofLp_toLp, WithLp.ofLp_sum, Finset.sum_apply]
  rw [he]
  simp_rw [covTruncNativeGradeCoefficient, sum_apply]
  calc
    _ = ∑ hh ∈ rs, ∑ u, ∑ d : Finset.Icc 2 (A.NT + A.Dt),
      reconCE c (covTruncNativeLb c) hh v u d t y
        (WithLp.toLp 2 fun α => orderedDerivative α (fun z => f t z u) y) :=
      Finset.sum_congr rfl fun hh hhh =>
        covTruncNativeCE_action c p xaux hΛ hM hN hh (hrs hh hhh) f t hf ht y v
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_comm

/-- The actual scalar letters, with all analytic fields and exact action discharged,
produce the gradient-carrier data of a finite set of native grades. -/
theorem covTruncNativeGrade_data {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (xaux : TermResAux c)
    (K : ℕ) (hK : K ≤ rKlift A ell + 1) (g : CovTruncNativeWindow c)
    (hΛ : 128 ≤ A.Λ) (hM : 2 ≤ M) (hN : 1 ≤ A.NT)
    (hfamily : ReconFamilyAt c 0) (hSb : 0 ≤ Sb)
    (rs : Finset ℕ) (hrs : ∀ hh ∈ rs, hh ≤ A.dW)
    (f : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root)
    (hf : ∀ v, ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c),
      ContDiff ℝ ((K + (A.NT + A.Dt) + 1 : ℕ) : ℕ∞) (fun y => f t y v))
    (hp : ∀ v, ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), IsZ2Periodic (fun y => f t y v)) :
    Nonempty (CovTruncCoefficientData (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
      K (A.NT + A.Dt) c.tp (c.tp + rTobs c) (rRho c)
      (covTruncGradientCoefficientConst K (A.NT + A.Dt) *
        (c.D.κ (M - 1) * covTruncNativeCEConst A.NT A.Dt K
          (covTruncNativeLetterConst A ell CG CW Ca) * ∑ hh ∈ rs, Sb ^ hh))
      (c.Gw.mass c.lawW) (fun v t y => toFluxL (gradE (fun z => f t z v) y))
      (fun v t y => toFluxL (menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M rs
        (Finset.Icc 2 (A.NT + A.Dt)) c.CcT f t y v))) := by
  classical
  have hreg := fun v u d => covTruncNativeGrade_regular c p K hK hfamily rs hrs v u d
  have hb := fun v u => covTruncNativeGrade_budget c p K hK g hΛ hM hfamily rs hrs v u
  have hSchur := covTruncNativeGrade_schur c p K g hfamily hSb rs
  apply covTruncCoefficientData_of_scalar_letters
    (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
    (covTruncNativeGradeCoefficient c rs) g.rho_pos (c.Gw.mass c.lawW) _
    (covTruncNativeGradePrice c p K rs)
  · intro v u
    have hs : 0 < Real.sqrt ((c.Gw.mass c.lawW) u / (c.Gw.mass c.lawW) v) :=
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
    apply covTruncNativeGrade_action c p xaux (by omega) (by omega) hN rs hrs f t _ ht y v
    exact contDiff_pi.mpr fun u => (hf u t ht).of_le (by exact_mod_cast (by omega :
      A.NT + A.Dt ≤ K + (A.NT + A.Dt) + 1))

/-- Finite-input grade-zero native pulse flux vanishes above the diagonal cutoff. -/
theorem covTruncNativePulse_cutoff {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (xaux : TermResAux c)
    (hΛ : 1 ≤ A.Λ) (hM : 1 ≤ M) (hN : 1 ≤ A.NT)
    (f : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root) (t : ℝ)
    (hf : ContDiff ℝ ((A.NT + A.Dt : ℕ) : ℕ∞) (f t))
    (ht : t ∈ Set.Icc c.tp (c.tp + rTobs c)) (k : ℤ)
    (hk : k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (hw : ocCutoff c.D.α c.D.q c.D.Λ M k t ≠ 0)
    (n : ℕ) (hn : A.NT + 1 < n) (hnR : n ≤ A.NT + A.Dt)
    (y : Vec 2) (v : CompIn c.Gw.comps) :
    pulseMeanFluxEuler (c.D.cellScaleSq M) (cr * liftLength c.D M)
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / (cr * liftLength c.D M)) n 0
      (Seq.seqQ c k (CycleComparison.LiftSetting.obsPulse_odd hk)) (c.CcT k)
      (chart' c k) (label' c k) f t y v = 0 := by
  classical
  have hodd := CycleComparison.LiftSetting.obsPulse_odd hk
  have hc := ocEll_sq_eq' c hΛ
  have hcs := cellScaleSq_pos c hΛ
  have hmem := window_mem c hΛ k ht hw
  have hwin := mem_pulseWindow c hΛ k hw
  obtain ⟨hη, hag⟩ := Seq.seq_agree c xaux.one hΛ hM hodd
  have hag' := hag ((c.D.cellScaleSq M)⁻¹ * t)
    (by rw [mul_inv_cancel_left₀ hcs.ne']; exact hwin)
  have hsz : max 2 A.Dt ≤ max (rLlift A ell + 1) (rLlift A ell + 2) := by
    have hDt : 2 ≤ A.Dt := le_max_left _ _
    have h1 : A.Dt * 1 * 1 ≤ A.Dt * (A.dW + 1) * A.NT :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hN
    unfold rLlift
    omega
  have hsx : max 2 A.Dt ≤ rKlift A ell + A.Dt + 2 := by omega
  have P := p.settings k hk
  have hres : 0 + (A.NT + A.Dt) ≤ p.qs := by
    have hr := setting_ambient_output_supported P
    omega
  have hρ : cr * liftLength c.D M = rRho c :=
    (congrArg (· * liftLength c.D M) xaux.one).trans (one_mul _)
  funext j
  have he : pulseMeanFluxEuler (c.D.cellScaleSq M) (cr * liftLength c.D M)
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / (cr * liftLength c.D M)) n 0
      (Seq.seqQ c k hodd) (c.CcT k) (chart' c k) (label' c k) f t y v j =
      pulseMeanFluxEuler (c.D.cellScaleSq M) (cr * liftLength c.D M)
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / (cr * liftLength c.D M)) n 0
      (rLiftData c k) (c.CcT k) (chart' c k) (label' c k) f t y v j := by
    unfold pulseMeanFluxEuler
    rw [liftFluxX_congr_data (Seq.seqQ c k hodd) (rLiftData c k) hη (c.CcT k) _ 0 n hag']
  rw [he, hρ, ← (covTruncNative_chart c hΛ k).1, ← (covTruncNative_chart c hΛ k).2, ← hc]
  exact covTruncMeanLetter_pulse_cutoff P _ _ hsx hsz (c.CcT k) (p.sequences k hk) 0 hres
    n hn (by omega) hnR hN _ _ (by rw [hc]; exact hcs.ne') _ _
    (fun s => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := s)).prodMk contDiff_id)) f t
    (by simpa only [Nat.add_comm] using hf) (hc.symm ▸ hmem) y j v

/-- The menu's grade-zero degree range shortens at the actual finite input regularity. -/
theorem covTruncNativeDiag_tail {ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovTruncNativePulse c ell CG CW Ca Sb) (xaux : TermResAux c)
    (hΛ : 1 ≤ A.Λ) (hM : 1 ≤ M) (hN : 1 ≤ A.NT)
    (f : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root) (t : ℝ)
    (hf : ContDiff ℝ ((A.NT + A.Dt : ℕ) : ℕ∞) (f t))
    (ht : t ∈ Set.Icc c.tp (c.tp + rTobs c)) (y : Vec 2) (v : CompIn c.Gw.comps) :
    menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {0}
      (Finset.Icc 2 (A.NT + A.Dt)) c.CcT f t y v =
    menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {0}
      (Finset.Icc 2 (A.NT + 1)) c.CcT f t y v := by
  classical
  have hτ := ocTau_pos' c hΛ
  simp only [menuGluedMeanFlux, Finset.sum_singleton]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkobs := obsPulses_time_subset c.D.α c.D.q c.D.Λ M hτ ht hk
  have hD : 2 ≤ A.Dt := le_max_left _ _
  have hsub : Finset.Icc 2 (A.NT + 1) ⊆ Finset.Icc 2 (A.NT + A.Dt) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  refine (Finset.sum_subset hsub fun n hn hnn => ?_).symm
  have hnR := (Finset.mem_Icc.mp hn).2
  have hnN : A.NT + 1 < n := by
    have hn2 := (Finset.mem_Icc.mp hn).1
    simp only [Finset.mem_Icc, not_and, not_le] at hnn
    exact hnn hn2
  split_ifs with hodd
  · by_cases hw : ocCutoff c.D.α c.D.q c.D.Λ M k t = 0
    · rw [hw, zero_smul]
    · have hz := covTruncNativePulse_cutoff c p xaux hΛ hM hN f t hf ht k hkobs hw n hnN hnR y v
      exact (congrArg (fun F => ocCutoff c.D.α c.D.q c.D.Λ M k t • F) hz).trans (smul_zero _)
  · rfl

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.EntryTerminal.CovOp
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! Uniform terminal physical diagonal and inherited mean flux bounds. The lift-sequence and lift-setting steps are used at an offset chosen from the
actual output order. ReconPrefixU lets us test their order-independent At clauses at a
separate coarse index above that offset's threshold. All constants precede j0, M and data.
Special cases: empty family, zero datum and empty positive-grade range have zero action;
the supplied c_r=1 identifies the observation and native physical radii. -/

section FluxOrder
variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Lowering the carrier order preserves the actual flux and its factorial mass budget. -/
theorem covTruncFluxBound_lower {K L : ℕ} (hKL : K ≤ L) {I : Set ℝ}
    (hI : MeasurableSet I) {ν ρ : ℝ} {π : ι → ℝ} (hν : 0 < ν) (hπ : ∀ v, 0 < π v)
    {F : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} {Y : ℝ}
    (hF : HasFluxBound L I ν ρ π F Y) : HasFluxBound K I ν ρ π F Y := by
  obtain ⟨U, hr, hm⟩ := hF
  let W := fun v t => truncateTorusHk hKL (U v t)
  refine ⟨W, ?_, ?_⟩
  · intro v t ht
    have he := AVRegularity.KernelEnergy.truncateTorusHk_toFunction_jet_ae hKL (U v t) (valueIndex2 K)
    have hidx : truncateJetIndex hKL (valueIndex2 K) = valueIndex2 L := rfl
    rw [hidx] at he
    exact he.trans (hr v t ht)
  · have hmass := covOp_fluxMassLe_of_comparison (K := fun _ => L) (K' := fun _ => K)
      I hI ν ρ π hν hπ (Cb := 1) (Cn := 1) zero_le_one U W hm
      (fun v => ((truncateTorusHk hKL).comp_memLp' (hm.1 v)).aestronglyMeasurable)
      (fun v t _ => by simpa only [one_mul] using truncateTorusHk_norm_le hKL (U v t))
      (fun v t _ => by
        simp only [one_pow, one_mul]
        exact (Real.sqrt_le_sqrt_iff (factorialNormSq_nonneg ρ _)).mp
          (AVRegularity.CycleComparison.Coarse.sqrt_fNSq_truncate_le ρ hKL (U v t).val))
    simpa only [one_mul] using hmass

end FluxOrder

/-- Source grades of the raw branch, before reference subtraction. -/
def covTruncNativeRawGrades {X : TermConstruction} (A : TermArgs X) (diagonal : Bool) : Finset ℕ :=
  if diagonal then {0} else Finset.Icc 1 A.dW

/-- Uniform common-matrix price of either raw branch. -/
def covTruncNativeRawPrice {X : TermConstruction} (A : TermArgs X) (diagonal : Bool)
    (kc ell : ℕ) (CG CW : ℕ → ℝ) (Ca Sb : ℝ) : ℝ :=
  covTruncGradientCoefficientConst (kc + 4 * A.pT) (A.NT + A.Dt) *
    covTruncNativeCEConst A.NT A.Dt (kc + 4 * A.pT)
      (covTruncNativeLetterConst A ell CG CW Ca) * ∑ hh ∈ covTruncNativeRawGrades A diagonal, Sb ^ hh

section Context
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- Exact raw flux of either branch, with the diagonal range shortened by the proved cutoff. -/
def covTruncRawTarget (diagonal : Bool) (x : TermResAux c) (v : CompIn c.Gw.comps)
    (t : ℝ) (y : Vec 2) : PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root) :=
  toFluxL (menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M (covTruncNativeRawGrades A diagonal)
    (if diagonal then Finset.Icc 2 (A.NT + 1) else Finset.Icc 2 (A.NT + A.Dt)) c.CcT
    (menuCovPRep (A.Mt M sXT sZT c.tp cr) c.D M A.pT x.aZ) t y v)

/-- Coefficients of the raw native menu flux over the full cell-degree range. -/
def CovTruncRawPhysicalAt (diagonal : Bool) (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  Nonempty (CovTruncCoefficientData (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
    (kc + 4 * A.pT) (A.NT + A.Dt) c.tp (c.a + A.T₀) (c.D.termRho cr M)
    (C * c.D.κ (M - 1)) (c.Gw.mass c.lawW) (covTruncCovGradientInput c x)
    (covTruncRawTarget c diagonal x))

/-- The covariance-filtered finite representative has exactly the scalar regularity used
by the actual physical coefficient constructor. -/
theorem covTruncNativeInput_regular (x : TermResAux c) (kc : ℕ)
    (ho : covTruncMeanInputOrder A kc + 3 ≤ A.Khat Kout) :
    ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      ContDiff ℝ ((kc + 4 * A.pT + (A.NT + A.Dt) + 1 : ℕ) : ℕ∞)
        (fun y => menuCovPRep (A.Mt M sXT sZT c.tp cr) c.D M A.pT x.aZ t y v) ∧
      IsZ2Periodic (fun y => menuCovPRep (A.Mt M sXT sZT c.tp cr) c.D M A.pT x.aZ t y v) := by
  intro v t ht
  have hf : ContDiff ℝ ((A.Khat Kout - 2 : ℕ) : ℕ∞) (fun y => x.aZ t y v) := by
    exact_mod_cast (x.repZ v t ht).2.1
  have hneed : kc + 4 * A.pT + (A.NT + A.Dt) + 1 + 2 * A.pT ≤ A.Khat Kout - 2 := by
    dsimp [covTruncMeanInputOrder] at ho
    omega
  refine ⟨covOp_contDiff_P _ A.pT _ (hf.of_le (by exact_mod_cast hneed)), ?_⟩
  exact covOp_periodic_P _ A.pT (hf.of_le (by exact_mod_cast (by omega : 2 * A.pT ≤ A.Khat Kout - 2)))
    (x.repZ v t ht).2.2.1

/-- The common native pulse input gives the exact original positive physical coefficients. -/
theorem covTruncRawPhysical_of_native (diagonal : Bool) (x : TermResAux c) (kc ell : ℕ)
    (CG CW : ℕ → ℝ) (Ca Sb : ℝ) (p : CovTruncNativePulse c ell CG CW Ca Sb)
    (hΛ : 128 ≤ A.Λ) (hM : 2 ≤ M) (hN : 1 ≤ A.NT) (hSb : 0 ≤ Sb)
    (hfamily : ReconFamilyAt c 0) (hdl : c.tp ≤ c.a + A.T₀)
    (horder : kc + 4 * A.pT ≤ rKlift A ell + 1)
    (ho : covTruncMeanInputOrder A kc + 3 ≤ A.Khat Kout) (C : ℝ)
    (hC : covTruncNativeRawPrice A diagonal kc ell CG CW Ca Sb ≤ C) :
    CovTruncRawPhysicalAt c diagonal x kc C := by
  let f := menuCovPRep (A.Mt M sXT sZT c.tp cr) c.D M A.pT x.aZ
  have hend : c.tp + rTobs c = c.a + A.T₀ := by unfold rTobs; ring
  have hρ : c.D.termRho cr M = rRho c :=
    (congrArg (· * rRho c) x.one).trans (one_mul _)
  have hf := covTruncNativeInput_regular c x kc ho
  have g := covTruncNativeWindow_of_ctx c hΛ hdl
  obtain ⟨P⟩ := covTruncNativeGrade_data c p x (kc + 4 * A.pT) horder g hΛ hM hN hfamily hSb
    (covTruncNativeRawGrades A diagonal) (fun hh hhh => by
      cases diagonal <;> simp only [covTruncNativeRawGrades, ↓reduceIte] at hhh
      · exact (Finset.mem_Icc.mp hhh).2
      · have hz := Finset.mem_singleton.mp hhh
        subst hh; exact Nat.zero_le _) f
    (fun v t ht => (hf v t (hend ▸ ht)).1) (fun v t ht => (hf v t (hend ▸ ht)).2)
  have hc : covTruncGradientCoefficientConst (kc + 4 * A.pT) (A.NT + A.Dt) *
      (c.D.κ (M - 1) * covTruncNativeCEConst A.NT A.Dt (kc + 4 * A.pT)
        (covTruncNativeLetterConst A ell CG CW Ca) * ∑ hh ∈ covTruncNativeRawGrades A diagonal, Sb ^ hh) =
      covTruncNativeRawPrice A diagonal kc ell CG CW Ca Sb * c.D.κ (M - 1) := by
    unfold covTruncNativeRawPrice
    ring
  rw [hc] at P
  have hCb := mul_le_mul_of_nonneg_right hC g.B_pos.le
  have P' : CovTruncCoefficientData (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
      (kc + 4 * A.pT) (A.NT + A.Dt) c.tp (c.tp + rTobs c) (rRho c)
      (C * c.D.κ (M - 1)) (c.Gw.mass c.lawW)
      (fun v t y => toFluxL (gradE (fun z => f t z v) y))
      (fun v t y => toFluxL (menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M
        (covTruncNativeRawGrades A diagonal) (Finset.Icc 2 (A.NT + A.Dt)) c.CcT f t y v)) :=
    { P with row := fun v => (P.row v).trans hCb, col := fun u => (P.col u).trans hCb }
  unfold CovTruncRawPhysicalAt
  rw [hρ, ← hend]
  refine ⟨{ P' with action := fun v t ht y => ?_ }⟩
  cases diagonal
  · exact P'.action v t ht y
  · change toFluxL (menuGluedMeanFlux _ _ _ {0} (Finset.Icc 2 (A.NT + 1)) _ f t y v) = _
    rw [← covTruncNativeDiag_tail c p x (by omega) (by omega) hN f t
      (contDiff_pi.mpr fun u => ((hf u t (hend ▸ ht)).1).of_le (by
        exact_mod_cast (by omega : A.NT + A.Dt ≤ kc + 4 * A.pT + (A.NT + A.Dt) + 1))) ht y v]
    exact P'.action v t ht y

/-- Grade-zero native flux before subtracting the reference matrix. -/
def CovTruncRawDiagAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  HasFluxBound (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root) (kc + 4 * A.pT)
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
    (fun v t y => toFluxL (menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {0}
      (Finset.Icc 2 (A.NT + 1)) c.CcT (menuCovPRep (A.Mt M sXT sZT c.tp cr) c.D M A.pT x.aZ)
      t y v)) (C * c.normF)

/-- The reference flux acting on the same covariance-filtered representative. -/
def CovTruncReferenceAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  HasFluxBound (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root) (kc + 4 * A.pT)
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
    (fun v t y => toFluxL (fun j => ∑ l : Fin 2,
      ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M) t j l •
        gradE (fun z => menuCovPRep (A.Mt M sXT sZT c.tp cr) c.D M A.pT x.aZ t z v) y l))
    (C * c.normF)

/-- Uniform reference-matrix size and continuity, independent of the field or pulse letters. -/
def CovTruncReferenceMatrixAt (C : ℝ) : Prop :=
  Continuous (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) ∧ 0 ≤ C ∧
    ∀ t, ∑ jl : Fin 2 × Fin 2,
      |ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M) t jl.1 jl.2| ≤ C * c.D.κ (M - 1)

/-- Finite regularity reserve of the covariance-filtered input. -/
def CovTruncPhysicalFieldOrderAt (_x : TermResAux c) (kc : ℕ) : Prop :=
  covTruncMeanInputOrder A kc + 3 ≤ A.Khat Kout

/-- Filtered gradient at the output order, retaining the finite scalar regularity floor. -/
def CovTruncFilteredGradientAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  covTruncMeanInputOrder A kc + 3 ≤ A.Khat Kout ∧
  HasFluxBound (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root) (kc + 4 * A.pT)
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
    (covTruncCovGradientInput c x) (C * c.normF / c.D.κ (M - 1))

/-- The matrix-gradient calculus at p=0 acts on the filtered gradient. -/
theorem covTruncReference_of_filtered (x : TermResAux c) (kc : ℕ) (C₁ C : ℝ)
    (hΛ : 128 ≤ A.Λ) (hC₁ : 0 ≤ C₁) (hC : C₁ ^ 2 ≤ C)
    (hg : CovTruncFilteredGradientAt c x kc C₁) (hJ : CovTruncReferenceMatrixAt c C₁) :
    CovTruncReferenceAt c x kc C := by
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos (by omega) X.hζ
    c.data.2.2.2.2.2.1 (Nat.sub_le M 1)
  obtain ⟨hρ, hπ⟩ := covTruncPhysical_geometry c x hΛ
  let u := fun v t y => menuCovPRep (A.Mt M sXT sZT c.tp cr) c.D M A.pT x.aZ t y v
  have hf := covTruncNativeInput_regular c x kc hg.1
  have hr : ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      ContDiff ℝ ((kc + 4 * A.pT + 2 * 0 + 1 : ℕ) : WithTop ℕ∞) (u v t) ∧
      IsZ2Periodic (u v t) := by
    intro v t ht
    have hsmall : ContDiff ℝ ((kc + 4 * A.pT + 1 : ℕ) : ℕ∞) (u v t) :=
      ((hf v t ht).1).of_le (by exact_mod_cast (by omega :
        kc + 4 * A.pT + 1 ≤ kc + 4 * A.pT + (A.NT + A.Dt) + 1))
    exact ⟨by exact_mod_cast hsmall, (hf v t ht).2⟩
  have hb := AVRegularity.EntryTerminal.CovGrad.covGrad_flux
    (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root) (kc + 4 * A.pT) 0
    measurableSet_Icc (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW) hν hρ hπ
    (fun _ => 0) (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) 0
    (C₁ * c.D.κ (M - 1)) continuousOn_const hJ.1.continuousOn le_rfl
    (fun t _ => by simp [CycleComparison.Coarse.covBound])
    (fun t _ => hJ.2.2 t) (mul_nonneg hC₁ hν.le) u
    (C₁ * c.normF / c.D.κ (M - 1)) hr hg.2
  simp only [Nat.mul_zero, Nat.add_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_mul, Function.iterate_zero, id_eq, one_smul] at hb
  change CovTruncReferenceAt c x kc C at ⊢
  refine hasFluxBound_mono_Y hb ?_
  calc
    (C₁ * c.D.κ (M - 1)) * (C₁ * c.normF / c.D.κ (M - 1)) = C₁ ^ 2 * c.normF := by
      field_simp [hν.ne']
    _ ≤ C * c.normF := mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _)

/-- Restore the molecular identity to the existing N=J-BI ledger. -/
theorem covTruncReferenceMatrix_of_ledger (Cn C : ℝ) (hCn : 0 ≤ Cn) (hC : Cn + 2 ≤ C)
    (hB : 0 < c.D.κ (M - 1)) (hc : Continuous (covGradN c.D M))
    (hb : ∀ t, ∑ jl : Fin 2 × Fin 2, |covGradN c.D M t jl.1 jl.2| ≤ Cn * c.D.κ (M - 1)) :
    CovTruncReferenceMatrixAt c C := by
  have he : ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M) =
      fun t => covGradN c.D M t + c.D.κ (M - 1) • 1 := by
    funext t
    unfold covGradN
    abel
  refine ⟨by rw [he]; exact hc.add continuous_const, (by linarith), fun t => ?_⟩
  rw [he]
  have hId : ∑ jl : Fin 2 × Fin 2,
      |(c.D.κ (M - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) jl.1 jl.2| = 2 * c.D.κ (M - 1) := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
      abs_of_pos hB, two_mul]
  calc
    _ ≤ ∑ jl : Fin 2 × Fin 2,
        (|covGradN c.D M t jl.1 jl.2| + |(c.D.κ (M - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) jl.1 jl.2|) :=
      Finset.sum_le_sum fun jl _ => abs_add_le _ _
    _ = (∑ jl : Fin 2 × Fin 2, |covGradN c.D M t jl.1 jl.2|) + 2 * c.D.κ (M - 1) := by
      rw [Finset.sum_add_distrib, hId]
    _ ≤ Cn * c.D.κ (M - 1) + 2 * c.D.κ (M - 1) := add_le_add (hb t) le_rfl
    _ = (Cn + 2) * c.D.κ (M - 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC hB.le

end Context

/-- Both raw coefficient branches, with constants uniform before data. -/
theorem covTruncRawPhysical (diagonal : Bool) :
    TermResPrefix fun c x kc _ C _ _ => CovTruncRawPhysicalAt c diagonal x kc C := by
  have hU := (((termReconSeq.and termReconTimes).and termReconFloors).and termReconSetting)
  intro X
  obtain ⟨Λ₀, h128, hu⟩ := hU X
  refine ⟨Λ₀, h128, fun A hΛ hV => ?_⟩
  have hΛ128 : 128 ≤ A.Λ := h128.trans hΛ
  have hN : 1 ≤ A.NT := AVRegularity.EntryTerminal.QuietEntrance.qe_one_le_NT A hV
  refine ⟨0, fun kc _ => ?_⟩
  let ell := kc + 4 * A.pT
  obtain ⟨kd, hu⟩ := hu A hΛ hV ell
  obtain ⟨SX, SZ, Kf, hu⟩ := hu kd le_rfl
  refine ⟨SX, SZ, max Kf (covTruncMeanInputOrder A kc + 3), fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn, hu⟩ := hu sXT sZT hX hZ Kout ((le_max_left _ _).trans hK)
  refine ⟨Kn, ?_⟩
  intro Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hone hkS hc0 hKs hKan hLan hJm
    cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP Cfl
  obtain ⟨k, CH, Υ, hCH, hΥ, hu⟩ := hu Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hone
    hkS hc0 hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP
  let CG := k.2.1.1
  let CW := k.2.1.2.1
  let Ca := k.2.1.2.2.1
  let Sb := k.2.1.2.2.2.1
  refine ⟨covTruncNativeRawPrice A diagonal kc ell CG CW Ca Sb, 1, 1, one_pos,
    CH, Υ, hCH, hΥ, fun C hC j₀ hj₀ => ?_⟩
  obtain ⟨M₀, hu⟩ := hu j₀ hj₀
  refine ⟨max M₀ 2, fun M hM c x => ?_⟩
  obtain ⟨⟨⟨hs, ht⟩, hf⟩, hset⟩ := hu M ((le_max_left _ _).trans hM) c x
  obtain ⟨p⟩ := covTruncNativePulse_of_setting c ell CG CW Ca Sb k.2.1.2.2.2.2 x
    (hs hf.1 hf.2 ht.1) hset
  obtain ⟨T, hfamily⟩ := Family.reconFamilyAt_of_ctx c hcP (by omega) 0 ht.2
  apply covTruncRawPhysical_of_native c diagonal x kc ell CG CW Ca Sb p hΛ128
    ((le_max_right _ _).trans hM) hN k.2.2.1 ⟨T, hfamily⟩ ht.2.le _ _ C hC
  · dsimp [ell, rKlift, rKmax]
    omega
  · exact ((le_max_right _ _).trans hK).trans (le_max_left _ _)

/-- The exact positive-grade coefficient statement, recovered from the shared raw branch. -/
theorem covTruncMeanPhysical : CovTruncMeanPhysicalCoefficientsStatement :=
  covTruncRawPhysical false

/-- The exact inherited mean flux has its uniform realized energy bound. -/
theorem covTruncMean : CovTruncMeanStatement := covTruncMean_of_physical covTruncMeanPhysical

/-- Exact remaining raw diagonal input; it is the grade-zero instance of the native
coefficient construction, followed by its finite degree cutoff. -/
def CovTruncRawDiagStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => CovTruncRawDiagAt c x kc C

/-- Exact remaining reference input, supplied by the constant-matrix adjoint
calculus and the terminal diffusivity ledger. -/
def CovTruncReferenceStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => CovTruncReferenceAt c x kc C

/-- The diagonal flux from the raw native flux and reference action. Subtraction is
already proved, and both inputs keep all constants before data. -/
theorem covTruncDiag_of_raw_reference (hRaw : CovTruncRawDiagStatement)
    (hRef : CovTruncReferenceStatement) : CovTruncDiagStatement := by
  have hj := termFluxPrefix_and
    (P₁ := fun c x kc C => CovTruncRawDiagAt c x kc C)
    (P₂ := fun c x kc C => CovTruncReferenceAt c x kc C) hRaw hRef
  refine termFluxPrefix_map
    (P := fun c x kc C => CovTruncRawDiagAt c x kc C ∧ CovTruncReferenceAt c x kc C)
    (R := fun c x kc C => CovTruncDiagAt c x kc C) ?_ hj
  intro X A kc C₁ hΛ hC₁
  refine ⟨2 * C₁, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hp C hC
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos (by omega) X.hζ
    c.data.2.2.2.2.2.1 (Nat.sub_le M 1)
  have hπ := (covTruncPhysical_geometry c x hΛ).2
  have hs := covTruncSub (kc + 4 * A.pT) (Set.Icc c.tp (c.a + A.T₀))
    (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW) hν hπ _ _ _ _ hp.1 hp.2
  have he : (fun v t y => toFluxL
      (gDiagTerm (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT c.CcT x.aZ v t y)) =
      fun v t y => toFluxL (menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {0}
        (Finset.Icc 2 (A.NT + 1)) c.CcT
        (menuCovPRep (A.Mt M sXT sZT c.tp cr) c.D M A.pT x.aZ) t y v) -
        toFluxL (fun j => ∑ l : Fin 2,
          ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M) t j l •
            gradE (fun z => menuCovPRep (A.Mt M sXT sZT c.tp cr) c.D M A.pT x.aZ t z v) y l) := by
    funext v t y
    exact WithLp.toLp_sub 2 _ _
  unfold CovTruncDiagAt
  rw [he]
  refine hasFluxBound_mono_Y hs ?_
  calc
    C₁ * c.normF + C₁ * c.normF = (2 * C₁) * c.normF := by ring
    _ ≤ C * c.normF := mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _)

/-- The reference matrix has a uniform price from the terminal diffusivity ledger. -/
theorem covTruncReferenceMatrix :
    TermResPrefix fun c _ _ _ C _ _ => CovTruncReferenceMatrixAt c C := by
  refine termFluxPrefix_of_simple (P := fun c _ _ C => CovTruncReferenceMatrixAt c C) ?_
  intro X
  obtain ⟨Λ₀, hΛ₀, hled⟩ := covGrad_ledger X
  refine ⟨Λ₀, hΛ₀, fun A hΛ => ?_⟩
  obtain ⟨Ccov, Cn, hCcov, hCn, hLed⟩ := hled A hΛ
  refine ⟨Cn + 2, fun C hC => ⟨2, ?_⟩⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M hM c x kc
  obtain ⟨-, -, hb, hc⟩ := hLed hM c x
  exact covTruncReferenceMatrix_of_ledger c Cn C hCn hC
    (CycleReference.bandChain_pos (by omega) X.hζ c.data.2.2.2.2.2.1 (Nat.sub_le M 1))
    hc hb

private theorem covTruncPhysical_fieldOrder :
    TermResPrefix fun c x kc _ _ _ _ => CovTruncPhysicalFieldOrderAt c x kc := by
  intro X
  refine ⟨128, le_rfl, fun A _ _ => ⟨0, fun kc _ => ⟨0, 0, covTruncMeanInputOrder A kc + 3,
    fun sXT sZT _ _ Kout hK => ⟨0, ?_⟩⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker _ Cfl
  refine ⟨0, 1, 1, one_pos, 1, 1, le_rfl, one_pos, fun C _ j₀ _ => ⟨0, fun M _ c x => ?_⟩⟩
  exact hK.trans (le_max_left _ _)

/-- The covariance factor and strong energy supply the filtered gradient at the output order. -/
theorem covTruncFilteredGradient :
    TermResPrefix fun c x kc _ C _ _ => CovTruncFilteredGradientAt c x kc C := by
  have hj := termFluxPrefix_and
    (P₁ := fun c x kc C => CovTruncCovGradientAt c x kc C)
    (P₂ := fun c x kc C => CovTruncMeanGradientAt c x kc C)
    covTruncCovGradient covTruncMeanGradient
  have ho := termFluxPrefix_and
    (P₁ := fun c x kc C => CovTruncCovGradientAt c x kc C ∧ CovTruncMeanGradientAt c x kc C)
    (P₂ := fun c x kc _ => CovTruncPhysicalFieldOrderAt c x kc)
    hj covTruncPhysical_fieldOrder
  refine termFluxPrefix_map
    (P := fun c x kc C => (CovTruncCovGradientAt c x kc C ∧ CovTruncMeanGradientAt c x kc C) ∧
      CovTruncPhysicalFieldOrderAt c x kc)
    (R := fun c x kc C => CovTruncFilteredGradientAt c x kc C) ?_ ho
  intro X A kc C₁ hΛ hC₁
  refine ⟨C₁ ^ 2, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hp C hC
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos (by omega) X.hζ
    c.data.2.2.2.2.2.1 (Nat.sub_le M 1)
  have hπ := (covTruncPhysical_geometry c x hΛ).2
  obtain ⟨T⟩ := hp.1.1
  have hg := T.hasFluxBound measurableSet_Icc hν hπ hC₁ hp.1.2
  have hl := covTruncFluxBound_lower (K := kc + 4 * A.pT)
    (L := covTruncCovGradientOrder A kc) (by dsimp [covTruncCovGradientOrder]; omega)
    measurableSet_Icc hν hπ hg
  refine ⟨hp.2, hasFluxBound_mono_Y hl ?_⟩
  calc
    C₁ * (C₁ * c.normF / c.D.κ (M - 1)) = C₁ ^ 2 * c.normF / c.D.κ (M - 1) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _)) hν.le

/-- The reference flux bound with the exact uniform prefix. -/
theorem covTruncReference : CovTruncReferenceStatement := by
  have hj := termFluxPrefix_and
    (P₁ := fun c x kc C => CovTruncFilteredGradientAt c x kc C)
    (P₂ := fun c _ _ C => CovTruncReferenceMatrixAt c C)
    covTruncFilteredGradient covTruncReferenceMatrix
  refine termFluxPrefix_map
    (P := fun c x kc C => CovTruncFilteredGradientAt c x kc C ∧ CovTruncReferenceMatrixAt c C)
    (R := fun c x kc C => CovTruncReferenceAt c x kc C) ?_ hj
  intro X A kc C₁ hΛ hC₁
  refine ⟨C₁ ^ 2, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hp C hC
  exact covTruncReference_of_filtered c x kc C₁ C hΛ hC₁ hC hp.1 hp.2

/-- The shortened raw diagonal flux has the required mass bound, from the native grade-zero
coefficient factory, the covariance operator and the strong gradient energy. -/
theorem covTruncRawDiag : CovTruncRawDiagStatement := by
  have he := termFluxPrefix_and
    (P₁ := fun c x kc C => CovTruncCovGradientAt c x kc C)
    (P₂ := fun c x kc C => CovTruncMeanGradientAt c x kc C)
    covTruncCovGradient covTruncMeanGradient
  have hj := termFluxPrefix_and
    (P₁ := fun c x kc C => CovTruncRawPhysicalAt c true x kc C)
    (P₂ := fun c x kc C => CovTruncCovGradientAt c x kc C ∧ CovTruncMeanGradientAt c x kc C)
    (covTruncRawPhysical true) he
  refine termFluxPrefix_map
    (P := fun c x kc C => CovTruncRawPhysicalAt c true x kc C ∧
      (CovTruncCovGradientAt c x kc C ∧ CovTruncMeanGradientAt c x kc C))
    (R := fun c x kc C => CovTruncRawDiagAt c x kc C) ?_ hj
  intro X A kc C₁ hΛ hC₁
  refine ⟨C₁ ^ 3, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hp C hC
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos (by omega) X.hζ
    c.data.2.2.2.2.2.1 (Nat.sub_le M 1)
  obtain ⟨hρ, hπ⟩ := covTruncPhysical_geometry c x hΛ
  obtain ⟨P⟩ := hp.1
  obtain ⟨T⟩ := hp.2.1
  have hg := T.hasFluxBound measurableSet_Icc hν hπ hC₁ hp.2.2
  have hR : kc + 4 * A.pT + (A.NT + A.Dt) = covTruncCovGradientOrder A kc := by
    dsimp [covTruncCovGradientOrder]
    omega
  rw [← hR] at hg
  have hb := (P.toFluxOperator hρ hπ).hasFluxBound measurableSet_Icc hν hπ
    (mul_nonneg hC₁ hν.le) hg
  change CovTruncRawDiagAt c x kc C at ⊢
  refine hasFluxBound_mono_Y hb ?_
  calc
    (C₁ * c.D.κ (M - 1)) * (C₁ * (C₁ * c.normF / c.D.κ (M - 1))) = C₁ ^ 3 * c.normF := by
      field_simp [hν.ne']
    _ ≤ C * c.normF := mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _)

/-- The exact diagonal flux, with its reference subtraction and uniform mass bound. -/
theorem covTruncDiag : CovTruncDiagStatement :=
  covTruncDiag_of_raw_reference covTruncRawDiag covTruncReference

/-- The entire pre-truncation flux has its exact realized uniform energy bound. -/
theorem covTruncG : CovTruncGStatement :=
  covTruncG_of_terms covTruncGReg covTruncComm covTruncDiag covTruncMean

/-- The terminal covariance truncation residual, with every named input discharged. -/
theorem termCovTrunc : TermCovTruncStatement := termCovTrunc_of_G covTruncG

end AVRegularity.Construction.Residual.Presentation
end
