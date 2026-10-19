-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.RetainedEnergy.UniformInputs
import AVRegularity.IterationPassage.Amplitude.UniformPlan
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees
import AVRegularity.Proofs.Results.Construction.ContextCertified.Assemble
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.CycleReference.TorusStreamFluxEquation
import AVRegularity.Construction.Preservation.Assembly.FullLiftFromInputs
public import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.RetainedEnergy

/-! The preparation bounds and the near-identity covariance estimate give
one trace at every reserved order, with a sharp marked order-zero initial norm. -/

open CycleComparison.Coarse FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm j₀ : ℕ} {bw : ℝ}

/-- The scalar last step uses absolute preparation constants, including negative inputs. -/
private theorem trace_budget_algebra {e d CQ Cp A n : ℝ} {p : ℕ}
    (he : 0 ≤ e) (hd : 0 ≤ d) (hCp : 0 ≤ Cp) (hn : 0 ≤ n) (hA : n ≤ A) :
    (1 + CQ * e) * n + p * (Cp * d) * (CQ * n) ≤
      (1 + (|CQ| + p * Cp * |CQ|) * (e + d)) * A := by
  have hq := le_abs_self CQ
  have hnA : 0 ≤ A := hn.trans hA
  have heq := mul_le_mul_of_nonneg_right hq he
  have hdq := mul_le_mul_of_nonneg_right hq
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg p) hCp) hd)
  have hcross : 0 ≤ |CQ| * d + (p : ℝ) * Cp * |CQ| * e := by positivity
  have hcoeff : 1 + CQ * e + (p : ℝ) * (Cp * d) * CQ ≤
      1 + (|CQ| + p * Cp * |CQ|) * (e + d) := by
    nlinarith only [heq, hdq, hcross]
  calc
    _ = (1 + CQ * e + (p : ℝ) * (Cp * d) * CQ) * n := by ring
    _ ≤ (1 + (|CQ| + p * Cp * |CQ|) * (e + d)) * n :=
      mul_le_mul_of_nonneg_right hcoeff hn
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)

/-- No classical representative is requested at the largest allowed output order. -/
theorem prepared_retained_trace_budget
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (law : BirthLaw) (hiota : 0 ≤ law.iota)
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (G Gr : GenStage D hr Dm bw j₀) (hST : G.comps ⊆ Gr.comps)
    {m p k Nout Naux : ℕ} {cr Q CQ Cpr s tf tp Cp : ℝ}
    (hlevel : G.level = m) (hρ : 0 < rhoEnh D cr m) (hCp : 0 ≤ Cp)
    (hM : fbCovConst (rhoEnh D cr m) (covPrimitive D m tp) Nout ≤
      Cp * D.eps (m - 1) ^ ocDelta D.α D.q)
    (hsmall : Cp * D.eps (m - 1) ^ ocDelta D.α D.q ≤ 1)
    (horder : k + 2 * p ≤ Nout)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ Cpr p Nout Naux s tf tp Preg)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ)
    (hf : weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain) :
    ∃ Y0 : ∀ v : CompIn Gr.comps, TorusHk k (hr v.1.root),
      IsRetainedTrace G Gr m p tp (Preg f) Y0 ∧
      (∀ w : CompIn Gr.comps → ℝ, (w = fun _ => 1) ∨ w = Gr.marker law →
        weightedNorm (rhoEnh D cr m) (Gr.mass law) w Y0 ≤ ((p : ℝ) + 1) * |CQ| * Ain) ∧
      weightedNorm 1 (Gr.mass law) (Gr.marker law)
          (fun v => truncateTorusHk (Nat.zero_le k) (Y0 v)) ≤
        (1 + (|CQ| + p * Cp * |CQ|) *
          (D.eps (m - 1) ^ Q + D.eps (m - 1) ^ ocDelta D.α D.q)) * Ain := by
  have he : 0 < D.eps (m - 1) := (Scales.epsilon_basic hq hΛ).1
  obtain ⟨Y0, htrace, hb⟩ := retained_trace_exists_bounded law G Gr hST m p tp horder hρ
    (hM.trans hsmall) (Preg f)
  have hpos (v : Comp) : 0 < compMass D.q D.Λ law v := Buffer.birth_compMass_pos hq hΛ law v
  have hdpos (v : Comp) : 0 < compMarker D.q D.Λ law v := Buffer.birth_compMarker_pos hq hΛ law v
  have hnorm : weightedNorm (rhoEnh D cr m) (G.mass law) (G.marker law) (Preg f) ≤
      CQ * weightedNorm 1 (G.mass law) (G.marker law) f := by
    simpa only [hlevel] using (hprep.2.2.2.2 _ (Or.inr rfl) f).2.2.1
  have hzero : weightedNorm 1 (G.mass law) (G.marker law)
      (fun v => truncateTorusHk (Nat.zero_le Nout) (Preg f v)) ≤
      (1 + CQ * D.eps (m - 1) ^ Q) * weightedNorm 1 (G.mass law) (G.marker law) f := by
    simpa only [hlevel] using (hprep.2.2.2.2 _ (Or.inr rfl) f).2.1
  refine ⟨Y0, htrace, ?_, ?_⟩
  · intro w hw
    rcases hw with rfl | rfl
    · have hweight : ∀ v : CompIn G.comps, 0 < G.mass law v / (1 : ℝ) ^ 2 := by
        intro v; simpa only [one_pow, div_one, GenStage.mass] using hpos v.1
      have hpre := (hprep.2.2.2.2 _ (Or.inl rfl) f).2.2.1
      rw [hlevel] at hpre
      have hfi := ordinary_input_from_marked G hq hΛ law hiota 1 f hf
      have hn : weightedNorm (rhoEnh D cr m) (G.mass law) (fun _ => 1) (Preg f) ≤ |CQ| * Ain :=
        hpre.trans ((mul_le_mul_of_nonneg_right (le_abs_self CQ) (Real.sqrt_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hfi (abs_nonneg CQ)))
      exact (hb (fun _ => 1) hweight).trans
        ((mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (by ring))
    · have hweight : ∀ v : CompIn G.comps, 0 < G.mass law v /
          compMarker D.q D.Λ law v.1 ^ 2 :=
        fun v => div_pos (hpos v.1) (sq_pos_of_pos (hdpos v.1))
      have hn : weightedNorm (rhoEnh D cr m) (G.mass law) (G.marker law) (Preg f) ≤ |CQ| * Ain :=
        hnorm.trans ((mul_le_mul_of_nonneg_right (le_abs_self CQ) (Real.sqrt_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hf (abs_nonneg CQ)))
      exact (hb (compMarker D.q D.Λ law) hweight).trans
        ((mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (by ring))
  · have htrace0 : IsRetainedTrace G Gr m p tp (Preg f)
        (fun v => truncateTorusHk (Nat.zero_le k) (Y0 v)) := by
      constructor
      · intro v hv
        exact covImage_truncate (Nat.zero_le k) _ _ _ (htrace.1 v hv)
      · intro v hv
        dsimp only
        rw [htrace.2 v hv, map_zero]
    have hnear := IterationPassage.Amplitude.amplitude_retained_trace_near_identity law G Gr hST
      p Nout m tp hρ (by omega) hM hsmall (compMarker D.q D.Λ law)
      (fun v => div_pos (hpos v.1) (sq_pos_of_pos (hdpos v.1))) (Preg f) _ htrace0
    have hpM : 0 ≤ (p : ℝ) * (Cp * D.eps (m - 1) ^ ocDelta D.α D.q) := by positivity
    have hh := hnear.trans (add_le_add hzero (mul_le_mul_of_nonneg_left hnorm hpM))
    exact hh.trans (trace_budget_algebra (Real.rpow_nonneg he.le _) (Real.rpow_nonneg he.le _)
      hCp (Real.sqrt_nonneg _) hf)

end AVRegularity.Construction.Preservation.RetainedEnergy
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.RetainedEnergy

/-! Assemble the prepared retained family at fixed data. Every analytic price comes
from one certificate-derived operator at the largest requested order. -/

section
open FullLift CycleComparison.Coarse
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Literal prepared energy conclusions from the certified operator and scalar trace price.
Special cases include empty families, singleton roots, edgeless seeds, k = 0 and Ain = 0.
The bounds use |CQ|, so no sign assumption on CQ or Cpr is added. -/
theorem prepared_retained_energy_at_stage
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (law : BirthLaw)
    (hη : 0 < law.eta0) (hηB : law.etaB = law.eta0 / 2) (hiota : 0 ≤ law.iota)
    (hcH : law.cH = (1 - (128 : ℝ) ^ (-law.etaB)) / 2)
    (P : ProvParams) (Mn : SuccMenu) (hTw : law.wordCount = (wordsUpTo Mn.A (Mn.J + 1)).card)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (kI : InvConsts) (seed G Gr : GenStage D hr Dm bw j₀)
    (hcascade : IsCascadeStage D P Mn seed Gr)
    {m Kres Nout Naux : ℕ} {Q CQ Cpr s a b Cp θ : ℝ}
    (hm : 1 ≤ m) (hlevel : G.level = m) (hctx : Gr.IsContextCertified kI)
    (hST : G.comps ⊆ Gr.comps) (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, m ≤ e.scale)
    (hsub : Gr.comps ⊆ succExtComps m Mn.A Mn.J G.comps)
    (hρ : 0 < rhoEnh D kI.cr m) (hCp : 0 ≤ Cp) (hθ : θ ≤ 1 / 8)
    (hM : fbCovConst (rhoEnh D kI.cr m) (covPrimitive D m a) Nout ≤
      Cp * D.eps (m - 1) ^ ocDelta D.α D.q)
    (hM1 : Cp * D.eps (m - 1) ^ ocDelta D.α D.q ≤ 1)
    (horder : Kres + 2 * Mn.p ≤ Nout)
    (hSzero : ∀ v u γ, IsSpatialRegularizerTorus (rhoEnh D kI.cr m) 0 Dm a b kI.cker
      (Gr.kernelOf P seedK freshK v u γ).width (Gr.sysS P seedK freshK φ₀ hφ₀ v u γ))
    (hop : ∀ w : CompIn Gr.comps → ℝ, (w = fun _ => 1) ∨ w = Gr.marker law →
      ∃ R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn Gr.comps => hr v.1.root)
          (Γ := Gr.fam.Γ) (G := fun _ u _ => hr u.1.root) a b (rhoEnh D kI.cr m)
          (D.κ (m - 1)) Kres Dm,
        R.B = (fun (v u : CompIn Gr.comps) (γ : Gr.fam.Γ v u)
          (d : ↥(Finset.Icc 2 Dm)) => Gr.physCoeff v u γ d.1) ∧
        R.C = (fun (v u : CompIn Gr.comps) (_ : Gr.fam.Γ v u) =>
          ContinuousLinearMap.id ℝ (hr u.1.root)) ∧
        R.S = Gr.sysS P seedK freshK φ₀ hφ₀ ∧
        R.π = (fun v => Gr.mass law v / w v ^ 2) ∧
        R.r = (fun v u γ => (Gr.kernelOf P seedK freshK v u γ).width) ∧
        R.c = kI.cker ∧ R.θ = θ)
    (hφ : IsAdmissibleStream (D.Φ (m - 1)))
    (αv B lam : ℝ) (hαv : 0 ≤ αv) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * rhoEnh D kI.cr m / lam ≤ 1 / 2)
    (hstrain : αv * B * rhoEnh D kI.cr m ^ 2 ≤ D.κ (m - 1) / 8)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kres → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel (D.Φ (m - 1)) t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G kI.cr Q CQ Cpr Mn.p Nout Naux s b a Preg) :
    let C := ((Mn.p : ℝ) + 1) * |CQ| + (|CQ| + Mn.p * Cp * |CQ|)
    NextFamilyClauses law P seedK freshK kI seed G Gr m law.eta0 Kres
      (wordsUpTo Mn.A (Mn.J + 1)).card a b ∧
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
      ∀ k ≤ Kres, ∃ Y0 : ∀ v : CompIn Gr.comps, TorusHk k (hr v.1.root),
        IsRetainedTrace G Gr m Mn.p a (Preg f) Y0 ∧
        RetainedSolutionClauses law P seedK freshK φ₀ hφ₀ Gr m k kI.cr C Q Ain a b Y0 := by
  classical
  dsimp only
  have hoplower (k : ℕ) (hk : k ≤ Kres) (w : CompIn Gr.comps → ℝ)
      (hw : (w = fun _ => 1) ∨ w = Gr.marker law) :
      NativeEnergyOperatorAt P seedK freshK φ₀ hφ₀ Gr a b (rhoEnh D kI.cr m)
        (D.κ (m - 1)) k (fun v => Gr.mass law v / w v ^ 2) := by
    obtain ⟨R, hB, hC, hS, hπ, hr, hc, _⟩ := hop w hw
    let Rk := kernelOperator_order_restrict R hk (fun v u γ => by
      rw [hc, hr, hS]
      exact spatial_regularizer_all_orders _ _ _ _ _ _ _ (hSzero v u γ) k)
    exact ⟨Rk, hB, hC, hS, hπ⟩
  constructor
  · refine ⟨hctx.isGenerated, ?_, ?_, ?_⟩
    · intro k hk w hw
      obtain ⟨R, hB, hC, hS, hπ, hr, hc, hθR⟩ := hop w hw
      have hs := kernelSchurBound_order_mono R hk
      rw [hB, hC, hπ, hr, hc, hθR] at hs
      exact ⟨fun v => (hs.1 v).trans hθ, fun u => (hs.2 u).trans hθ⟩
    · exact cascade_mass_sum_le_twice hq hΛ law (by rw [hηB]; positivity)
        hcH P Mn hTw seed Gr hcascade
    · intro k X
      have hcH1 : law.cH ≤ 1 := by
        rw [hcH]
        have hr : 0 ≤ (128 : ℝ) ^ (-law.etaB) := Real.rpow_nonneg (by norm_num) _
        linarith only [hr]
      have hr := birth_readout_near_identity hq hΛ hm law hcH1 hη.le hold hsub k
        (rhoEnh D kI.cr m) X
      unfold GenStage.mass
      simpa only [OCData.eps, hηB, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hr
  · intro f Ain hf k hk
    obtain ⟨Y0, htrace, hinit, hnear⟩ := prepared_retained_trace_budget (k := k) hq hΛ law hiota
      P seedK freshK φ₀ hφ₀ G Gr hST hlevel hρ hCp hM hM1 (by omega) Preg hprep f Ain hf
    refine ⟨Y0, htrace, retained_solution_clauses_of_operators law P seedK freshK φ₀ hφ₀ Gr
      (hoplower k hk) (hoplower 0 (Nat.zero_le Kres) _ (Or.inr rfl)) hφ
      αv B lam hαv hBdrift hlam hsmall hstrain (fun t ht l hl hlk => hjets t ht l hl (hlk.trans hk))
      Y0 ?_ ?_⟩
    · intro w hw
      exact (hinit w hw).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (by positivity)) ((Real.sqrt_nonneg _).trans hf))
    · apply hnear.trans
      apply mul_le_mul_of_nonneg_right _ ((Real.sqrt_nonneg _).trans hf)
      apply add_le_add (le_refl (1 : ℝ))
      apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity))
        (add_nonneg (Real.rpow_nonneg (Scales.epsilon_basic hq hΛ).1.le _)
          (Real.rpow_nonneg (Scales.epsilon_basic hq hΛ).1.le _))
end

/-! Uniform thresholds instantiate the fixed-stage retained-energy assembly. -/

section
open AVRegularity.Construction.Preservation.Assembly FullLift CycleComparison.Coarse

/-- The normalized covariance bound used by the prepared trace. -/
def CovarianceEntriesAt (α q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (Ccov : ℝ) : Prop :=
  ∀ M, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
    ∀ m, 2 ≤ m → m ≤ M → ∀ t i j,
      |ocCovariance α q Λ ζ m (κ m) (κ (m - 1)) 0 t i j| /
        ocRh α q Λ m (κ (m - 1)) ^ 2 ≤ Ccov * ocEpsilon q Λ (m - 1) ^ ocDelta α q

/-- Prepared energy with thresholds fixed before OCData, the law and the component spaces.
Special cases: empty families and edgeless seeds use the same thresholds; k = 0 and Ain = 0
require no extra reserve. Signed preparation constants enter only through |CQ|. -/
theorem prepared_retained_energy_at_data {α s q : ℝ}
    (hq : IsAdmissibleQ α s q) (hη : 0 < succEta0 α q s)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Λl Λ : ℕ)
    (hlength : UniformRecordLengths α q ζ Λl) (hΛ : Λl ≤ Λ) (h128 : 128 ≤ Λ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw : ℝ)
    (Q T₀ Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ : ℕ)
    (σ₀ : ℝ) (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr : ℝ) (mc : ℕ)
    (horder : Kres + 2 * p ≤ Nout)
    (hc : RetainedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
      r₀ D₀ H J N p nk npad sX sZ σ₀ kI CI Cw j₀ mc)
    (hprod : kI.Hprod = kI.G0 + H + 1) (hc0pos : 0 < kI.c₀) (hc0le : kI.c₀ ≤ 1)
    (hcrpos : 0 < kI.cr) (hcrle : kI.cr ≤ 1) (mr : ℕ) (hmr : 2 ≤ mr)
    (hradius : EnhancedRadiusAt α q ζ Λ kI.c₀ kI.cr mr) (md : ℕ)
    (hdrift : EnhancedDriftAt α q ζ Λ kI.cr md) (A : ℝ) (mo : ℕ)
    (hop : NativeKernelOperatorsAt α q ζ Λ bw Kres (succSchedD D₀ N p (H + 1)) kI.cker A mo)
    (ma : ℕ)
    (habs : ∀ m, ma ≤ m → A * (CI * ocEpsilon q Λ (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8)
    (Ccov : ℝ) (hCcov : 0 ≤ Ccov) (hcov : CovarianceEntriesAt α q ζ Λ Ccov)
    (ms : ℕ) (hcovsmall : ∀ m, ms ≤ m →
      (4 * Ccov * (Nout : ℝ) ^ 2 / kI.cr ^ 2) *
        ocEpsilon q Λ (m - 1) ^ ocDelta α q ≤ 1) :
    PreparedRetainedEnergyProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
      r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀
      (((p : ℝ) + 1) * |CQ| + (|CQ| + p * (4 * Ccov * (Nout : ℝ) ^ 2 / kI.cr ^ 2) * |CQ|))
      (max mc (max mr (max md (max (mo + 3) (max ma (max ms (j₀ + 3))))))) := by
  classical
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow _hT G G' hcascade hlevel hG hactual tp Preg hprep
  have hmc : mc ≤ m := by omega
  have hmr' : mr ≤ m := by omega
  have hmd' : md ≤ m := by omega
  have hmo' : mo + 1 ≤ m - 1 := by omega
  have hma : ma ≤ m := by omega
  have hms : ms ≤ m := by omega
  have hjGr' : j₀ ≤ m - 1 := by omega
  have hm2 : 2 ≤ m := by omega
  have hiGr' : 1 ≤ m - 1 := by omega
  have hm1 : 1 ≤ m := by omega
  have hmterm : m ≤ D.term := by rw [hterm]; exact hn.trans hnM.le
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact h128
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  let P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p
  let Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)
  let Gr := G'.retained m H J
  have hGrlevel : Gr.level = m - 1 := by
    change G'.level = m - 1
    rw [hactual.2.1, hlevel]
  have hGrlevelterm : Gr.level ≤ D.term := by omega
  have hGrI := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hmc hn hnM tA htA G G' hcascade hlevel hG hactual
  obtain ⟨hnat, hshift, hslot, hctx, hled, hker⟩ := hGrI
  have hcGr : IsCascadeStage D P Mn seed Gr := by
    simpa only [hlevel, succMenu, Mn, Gr, P] using IsCascadeStage.step hcascade hactual
  have hprod' : kI.Hprod = kI.G0 + Mn.H + 1 := hprod
  have hmGr v : 0 ≤ compReserve kI (v : CompIn Gr.comps).1 :=
    (Buffer.cascade_component_reserve_pos hseed.2.1 hcGr kI hprod' v).le
  have hm2Gr v : compReserve kI (v : CompIn Gr.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hseedI := hseed.2.2.2.2.2.2.2.1
  have hlens : ∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level := by
    intro v u γ hb
    simpa only [hseed.1] using (hseed.2.2.2.2.2.1 v u γ).2.2 hb
  have hlenGr := hlength hr D hDα hDq hDζ (by rw [hDΛ]; omega) hbandD
    _ bw j₀ Mn Cw kI.cr σ₀ (succEta0 α q s) N p hcrle seed Gr hseedI.2.1 hlens
    (by rw [hseed.1, hterm]; exact hnM.le) hcGr (hGrlevel.symm ▸ hiGr')
  have he (l : ℕ) : 0 < D.eps l := Construction.Stream.ocEpsilon_pos (by omega)
  have hκ (l : ℕ) (hl : l ≤ D.term) : 0 < D.κ l :=
    CycleReference.bandChain_pos (by omega) hζD hbandD hl
  have ha (l : ℕ) : 0 < ocA D.α D.q D.Λ l := Real.rpow_pos_of_pos (he l) _
  have hrs (l : ℕ) (hl : l ≤ D.term) :
      0 < rhoStar D kI.c₀ l ∧ rhoStar D kI.c₀ l ≤ D.eps l := by
    have hh := Buffer.molecular_radius_bounds hc0pos (he l) (hκ l hl) (ha l)
    exact ⟨hh.1, hh.2.1.trans (mul_le_of_le_one_left (he l).le hc0le)⟩
  have hrhos := hradius D hDα hDq hDΛ hDζ hbandD m hmr' hmterm
  have hρe : rhoEnh D kI.cr m ≤ D.eps Gr.level := by
    rw [hGrlevel]
    exact hrhos.trans (hrs (m - 1) (by omega)).2
  have hρE : rhoEnh D kI.cr m ≤ D.eps (Gr.level - 1) :=
    hρe.trans (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hd := hdrift D.Φ hseq M D.κ hband m hmd' (hn.trans hnM.le)
  have hρpos : 0 < rhoEnh D kI.cr m := by
    simpa only [rhoEnh, hDα, hDq, hDΛ] using hd.2.1
  have htptf : tp ≤ tf := by
    have hh := hprep.2.2.1
    rw [hlevel, hDα, hDq, hDΛ] at hh
    exact hh.trans hwindow
  have hsub : Set.Icc tp tf ⊆ Set.Icc (tA + 3 * ocTau α q Λ m) tf := by
    intro t ht
    exact ⟨(hdelay.trans hprep.2.1).trans ht.1, ht.2⟩
  have hSzero : ∀ v u (γ : Gr.fam.Γ v u), IsSpatialRegularizerTorus (rhoEnh D kI.cr m) 0
      (succSchedD D₀ N p (H + 1)) tp tf kI.cker
      (Gr.kernelOf P seedK freshK v u γ).width (Gr.sysS P seedK freshK φ₀ hφ₀ v u γ) := by
    intro v u γ
    exact Buffer.spatialRegularizerTorus_time_restrict ((hker v u γ).2 _ hρpos) hsub
  have hkap : D.kap Gr.level = D.κ (m - 1) := by
    change D.κ (min Gr.level D.term) = _
    rw [Nat.min_eq_left hGrlevelterm, hGrlevel]
  have hsmall : A * (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8 := by
    simpa only [OCData.eps, hDq, hDΛ] using habs m hma
  have hlengthop : ∀ v u (γ : Gr.fam.Γ v u), 3 ≤ (Gr.fam.identity v u γ).maxOrder →
      (Gr.fam.identity v u γ).record.length ≤ D.eps (Gr.level - 1) := by
    intro v u γ hj
    have hb : 1 ≤ (Gr.fam.identity v u γ).record.birthExcess := by
      have hh := (Gr.fam.identity v u γ).le_birth
      omega
    exact (hlenGr v u γ hb).trans
      (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hop' := hop hr D hDα hDq hDΛ hDζ hseq j₀ Mnat Gr kI hctx hnat hshift
    (hGrlevel.symm ▸ hmo') (hGrlevel.symm ▸ hiGr') (hGrlevel.symm ▸ hjGr')
    (he _) (he _) (by rw [hkap]; exact hd.1)
    hslot hmGr hm2Gr P seedK freshK (fun v u γ => (hker v u γ).1) φ₀ hφ₀ tp tf
    (rhoEnh D kI.cr m) (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe)
    (Gr.mass law) (Gr.marker law) htptf hρpos hρE hρe hlengthop
    (fun v => Buffer.birth_compMass_pos hqD hΛD law v.1)
    (fun v => Buffer.birth_compMarker_pos hqD hΛD law v.1) hled hsmall.le hSzero
  rw [hkap] at hop'
  have hφ : IsAdmissibleStream (D.Φ (m - 1)) := (hseq.2 m hm1).choose
  let αv := Buffer.actualDriftJetConstant * ocA α q Λ (m - 1)
  have hαv : 0 ≤ αv := mul_nonneg Buffer.actualDriftJetConstant_nonneg
    (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hsmallD : 1024 * rhoEnh D kI.cr m / D.eps (m - 1) ≤ 1 / 2 := by
    simpa only [rhoEnh, OCData.eps, hDα, hDq, hDΛ] using hd.2.2.1
  have hstrain : αv * 1024 * rhoEnh D kI.cr m ^ 2 ≤ D.κ (m - 1) / 8 := by
    simpa only [αv, rhoEnh, hDα, hDq, hDΛ] using hd.2.2.2.1
  have hjets : ∀ t ∈ Set.Icc tp tf, ∀ j, 1 ≤ j → j ≤ Kres → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel (D.Φ (m - 1)) t)) j x‖ ≤
        αv * 1024 ^ j * (j.factorial : ℝ) * D.eps (m - 1) ^ ((1 : ℤ) - j) := by
    intro t _ j hj _ x
    simpa only [αv, OCData.eps, hDq, hDΛ] using hd.2.2.2.2 t j hj x
  let Cp := 4 * Ccov * (Nout : ℝ) ^ 2 / kI.cr ^ 2
  have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
  have hRh : 0 < ocRh D.α D.q D.Λ m (D.κ (m - 1)) := by
    exact Real.sqrt_pos.mpr (mul_pos (hκ (m - 1) (by omega))
      (Construction.Stream.ocTauPP_pos (by omega)))
  have hentry (i j : Fin 2) : |covPrimitive D m tp i j| ≤
      (Ccov / kI.cr ^ 2 * D.eps (m - 1) ^ ocDelta D.α D.q) * rhoEnh D kI.cr m ^ 2 := by
    have heD : |covPrimitive D m tp i j| / ocRh D.α D.q D.Λ m (D.κ (m - 1)) ^ 2 ≤
        Ccov * D.eps (m - 1) ^ ocDelta D.α D.q := by
      simpa only [covPrimitive, OCData.eps, hDα, hDq, hDΛ, hDζ] using
        hcov M (by omega) D.κ hband m hm2 (hn.trans hnM.le) tp i j
    have hh := (div_le_iff₀ (sq_pos_of_pos hRh)).mp heD
    convert hh using 1
    unfold rhoEnh ocRh
    field_simp
  have hcovprice : fbCovConst (rhoEnh D kI.cr m) (covPrimitive D m tp) Nout ≤
      Cp * D.eps (m - 1) ^ ocDelta D.α D.q := by
    have hp := fbCovConst_le_of_radius_entries hρpos (covPrimitive D m tp)
      (Ccov / kI.cr ^ 2 * D.eps (m - 1) ^ ocDelta D.α D.q) Nout hentry
    convert hp using 1
    dsimp [Cp]
    ring
  have hcovsmallD : Cp * D.eps (m - 1) ^ ocDelta D.α D.q ≤ 1 := by
    simpa only [Cp, OCData.eps, hDq, hDΛ, hDα] using hcovsmall m hms
  have hST : G.comps ⊆ Gr.comps :=
    incoming_mem_retained_of_cascade hseed.2.1 hcascade hactual hlevel
  have hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, m ≤ e.scale := by
    intro v hv e he
    rw [← hlevel]
    exact (InitialValue.cascade_invariant hseed.2.1 hcascade v hv).1 e he
  have hsubGr : Gr.comps ⊆ succExtComps m Mn.A Mn.J G.comps := by
    intro v hv
    have hh := (Finset.mem_filter.1 hv).1
    simpa only [hactual.2.2.1, hlevel] using hh
  have hηlaw : 0 < law.eta0 := hlaw.1.symm ▸ hη
  have hηB : law.etaB = law.eta0 / 2 := hlaw.2.1.trans (congrArg (fun z : ℝ => z / 2) hlaw.1.symm)
  have hcH : law.cH = (1 - (128 : ℝ) ^ (-law.etaB)) / 2 := by
    rw [hlaw.2.2.2.1, hlaw.2.1]
  have hiota : 0 ≤ law.iota := by rw [hlaw.2.2.1]; exact (div_pos hη (by norm_num)).le
  have hf := prepared_retained_energy_at_stage hqD hΛD law hηlaw hηB hiota hcH P Mn
    hlaw.2.2.2.2 seedK freshK φ₀ hφ₀ kI seed G Gr hcGr hm1 hlevel hctx hST hold hsubGr
    hρpos hCp hsmall.le hcovprice hcovsmallD horder hSzero hop' hφ
    αv 1024 (D.eps (m - 1)) hαv (by norm_num) (he _) hsmallD hstrain hjets Preg hprep
  simpa only [Cp, hlaw.1, Mn, succMenu] using hf
end

/-! Prepared retained energy from the certificates and a single compiled kernel price. -/

section
open AVRegularity.Construction.Preservation.Assembly FullLift

/-- Uniform prepared energy, with all constants chosen before the data and birth law.
CQ and Cpr may have either sign; only |CQ| enters the energy constant. -/
theorem prepared_retained_energy_production {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    PreparedRetainedEnergyProductionStatement α s q ζ := by
  classical
  obtain ⟨Λc, hΛc, hc⟩ := retained_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λl, hΛl, hlength⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  change UniformRecordLengths α q ζ Λl at hlength
  obtain ⟨Λr, hΛr, hradius⟩ := uniform_enhanced_radius_le_parent_molecular hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λd, hΛd, hdrift⟩ := actual_enhanced_drift_budget hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Ccov, hCcov, Λv, hΛv, hcov⟩ := CycleReference.bandChain_covariance_estimates
    hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λc (max Λl (max Λr (max Λd Λv))), by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ (by omega)
  refine ⟨min cmax 1, lt_min hcmax zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad
    σ₀ a σ hsched hNaux hNout sX sZ hsX hsZ Ce kS hCe hc₀ hc₀upper hcr hcrupper
    hσf hlamC halloc
  have hsched' : IsSuccessorSchedule α q s Q σ₀ a σ
      (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout := by
    simpa only [hσf, hlamC] using hsched
  obtain ⟨tc, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper
    (by rw [hσf]; exact hσE) (by rw [hlamC]; exact hlamE)
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched'
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
  change RetainedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ
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
  obtain ⟨A, _hA, mo, _hmo, hop⟩ := uniform_native_kernel_operator_of_certificates
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ h128 ζ hζ bw hbw Kres
    (succSchedD D₀ N p (H + 1)) hDm kI.cker hcker
  change NativeKernelOperatorsAt α q ζ Λ bw Kres (succSchedD D₀ N p (H + 1)) kI.cker A mo at hop
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ : 0 < min (ocDelta α q / 4) τe := lt_min (div_pos hδ (by norm_num)) hτe
  obtain ⟨ma, habs⟩ := retained_absorption_threshold hq.1 h128 hτ A CI
  let Cp := 4 * Ccov * (Nout : ℝ) ^ 2 / kI.cr ^ 2
  obtain ⟨ms, hsmall⟩ := retained_absorption_threshold hq.1 h128 hδ 1 Cp
  have hcovsmall (m : ℕ) (hm : ms ≤ m) : Cp * ocEpsilon q Λ (m - 1) ^ ocDelta α q ≤ 1 := by
    exact (by simpa only [one_mul] using hsmall m hm :
      Cp * ocEpsilon q Λ (m - 1) ^ ocDelta α q < 1 / 8).le.trans (by norm_num)
  have hcov' : CovarianceEntriesAt α q ζ Λ Ccov := fun M hM κ hband m hm hmM t i j =>
    (hcov Λ (by omega) M hM κ hband m hm hmM 0 t i j).2.2.2
  refine ⟨((p : ℝ) + 1) * |CQ| + (|CQ| + p * Cp * |CQ|),
    max mc (max mr (max md (max (mo + 3) (max ma (max ms (j₀ + 3)))))), ?_⟩
  exact prepared_retained_energy_at_data hq (successor_eta0_pos hα₀ hα₁ hs₀ hs₁ hq)
    hζ Λl Λ hlength (by omega) h128 φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk
    Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr mc hNout hc hprod
    hc0pos hc0le hcrpos hcrle mr hmr hradius md hdrift A mo hop ma habs Ccov
    ((by norm_num : (0 : ℝ) ≤ 1).trans hCcov) hcov' ms hcovsmall
end

end AVRegularity.Construction.Preservation.RetainedEnergy
end
