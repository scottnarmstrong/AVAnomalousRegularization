-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ForcedEnergy.StageForced
import AVRegularity.EntryTerminal.Ingredients.ForcedEnergy.ComponentStrong
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
import Mathlib.Algebra.Order.Star.Real

/-! **Forced energy on the weak stage, with the reserve premise**.
`TerminalForcedEnergyReserveStatement` is `TerminalForcedEnergyStatement` with the premise
`kW.G0 ≤ kW.Hprod + 1` placed after `A.k₀ ≤ kW.Ks` and before `∃ Ca`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Route

def TerminalForcedEnergyReserveStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∀ (nW : ℕ+) (cK CL Cχ : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK → A.k₀ ≤ kW.Ks →
    kW.G0 ≤ kW.Hprod + 1 →
  ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ D : OCData, IsTermData X A.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
      Gw aM →
  ∀ tp : ℝ, aM ≤ tp → tp ≤ a + A.T₀ →
  ∀ (e₀ : ∀ v : CompIn Gw.comps, TorusHk A.k₀ (ScalarH v.1.root))
    (F : ∀ v : CompIn Gw.comps, ℝ → TorusHk A.k₀ (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (g U : ∀ v : CompIn Gw.comps, ℝ → TorusHk A.k₀ (ScalarH v.1.root))
    (W : ∀ v : CompIn Gw.comps, ℝ → TorusHk (A.k₀ + 1) (ScalarH v.1.root))
    (Y : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (A.k₀ + A.Dt - 1) (ScalarH u.1.root)),
    (∀ v, AEStronglyMeasurable (F v) (volume.restrict (Set.Icc tp (a + A.T₀)))) →
    (∀ v, AEStronglyMeasurable (g v) (volume.restrict (Set.Icc tp (a + A.T₀)))) →
    Gw.IsRegSolution PW (A.Kw_ D M nW) (A.Kw_ D M nW) A.φ₀ A.hφ₀ (D.κ M) (streamVel (D.Φ M))
      A.k₀ tp (a + A.T₀) e₀ F g U W Y →
  ∀ Xr : ℝ, 0 ≤ Xr →
    (∀ j, j ≤ A.k₀ → ∀ β : DerivativeWord2 j,
      residualNorm (D.κ M) (Gw.mass lawW) (Set.Icc tp (a + A.T₀))
          (fun t x i v => D.termRStar cK M ^ j • (torusJetOrder (F v t) j β x) i)
          (fun t x v => D.termRStar cK M ^ j • torusJetOrder (g v t) j β x) ≤
        ENNReal.ofReal Xr) →
    strongEnergy (D.termRStar cK M) (D.κ M) (Gw.mass lawW) tp (a + A.T₀) U W ≤
      ENNReal.ofReal (Ca * (weightedNorm (D.termRStar cK M) (Gw.mass lawW) (fun _ => 1) e₀ + Xr))

theorem grad_aemeasurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {k : ℕ} (ρ : ℝ)
    {μ : Measure ℝ} {w : ℝ → TorusHk (k + 1) E} (hw : MemLp w 2 μ) :
    AEMeasurable (fun t => ENNReal.ofReal (gradFactorialNormSq ρ (w t).val)) μ := by
  have hc := ((AVRegularity.KernelEnergy.torusFactorialGradientReadout (E := E) ρ k).continuous.comp_aestronglyMeasurable
    hw.aestronglyMeasurable).norm.pow 2
  have h2 : AEMeasurable (fun t => ‖AVRegularity.KernelEnergy.torusFactorialGradientReadout (E := E) ρ k (w t)‖ ^ 2) μ :=
    hc.aemeasurable
  simpa only [AVRegularity.KernelEnergy.torusFactorialGradientReadout_normSq] using h2.ennreal_ofReal

theorem sqrt_massNormSq_mono_radius {ι : Type*} [Fintype ι] {S : ι → Type*}
    [∀ i, NormedAddCommGroup (S i)] [∀ i, InnerProductSpace ℝ (S i)] [∀ i, MeasurableSpace (S i)]
    [∀ i, BorelSpace (S i)] [∀ i, CompleteSpace (S i)] {k : ℕ} (ρ R : ℝ) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (f : ∀ i, TorusHk k (S i)) :
    Real.sqrt (massNormSq (E := S) (K := fun _ => k) ρ π (fun i => (f i).val)) ≤
      Real.sqrt (massNormSq (E := S) (K := fun _ => k) R π (fun i => (f i).val)) := by
  refine Real.sqrt_le_sqrt ?_
  unfold massNormSq
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
    (AVRegularity.CycleJointProofs.factorialNormSq_mono_radius hρ hρR _) (inv_nonneg.2 (hπ i).le)

theorem term_stage_bound {X : TermConstruction} (A : TermArgs X) (nW : ℕ+) (cK Cχ : ℝ)
    (kW : InvConsts) (D : OCData) (j₀ M : ℕ) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM tp : ℝ)
    (hI : IsStageInvariant lawW PW (A.Kw_ D M nW) (A.Kw_ D M nW) A.φ₀ A.hφ₀ (M + A.Jw) kW aM
      (a + A.T₀) (Cχ * D.eps M ^ A.χw) (Cχ * D.eps M ^ A.χw) Gw)
    (hlev : Gw.level = M)
    (hres0 : ∀ v : CompIn Gw.comps, 0 ≤ compReserve kW v.1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hM1 : 1 ≤ M) (hMj : j₀ ≤ M) (hbw : 0 < A.bw)
    (hε1 : 0 < D.eps (M - 1)) (hab : aM ≤ a + A.T₀) (hκ : 0 < D.κ M)
    (hkap : D.kap Gw.level = D.κ M)
    (hRpos : 0 < D.termRStar cK M) (hRε : D.termRStar cK M ≤ D.eps (M - 1))
    (hrho : D.termRStar cK M = rhoStar D kW.c₀ Gw.level)
    (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ D.termRStar cK M)
    (hθ : Cχ * D.eps M ^ A.χw ≤ 1 / 8) (hKs : A.k₀ ≤ kW.Ks)
    (haMtp : aM ≤ tp) (htp : tp ≤ a + A.T₀) (αd lam : ℝ) (hα : 0 ≤ αd) (hlam : 0 < lam)
    (hsmall : 1024 * ρ / lam ≤ 1 / 2) (hstrain : αd * 1024 * ρ ^ 2 ≤ D.κ M / 8)
    (hjets : ∀ t ∈ Set.Icc tp (a + A.T₀), ∀ l, 1 ≤ l → l ≤ A.k₀ → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel (D.Φ M) t)) l x‖ ≤
        αd * 1024 ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (e₀ : ∀ v : CompIn Gw.comps, TorusHk A.k₀ (ScalarH v.1.root))
    (F : ∀ v : CompIn Gw.comps, ℝ → TorusHk A.k₀ (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (g U : ∀ v : CompIn Gw.comps, ℝ → TorusHk A.k₀ (ScalarH v.1.root))
    (W : ∀ v : CompIn Gw.comps, ℝ → TorusHk (A.k₀ + 1) (ScalarH v.1.root))
    (Y : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (A.k₀ + A.Dt - 1) (ScalarH u.1.root))
    (hFm : ∀ v, AEStronglyMeasurable (F v) (volume.restrict (Set.Icc tp (a + A.T₀))))
    (hgm : ∀ v, AEStronglyMeasurable (g v) (volume.restrict (Set.Icc tp (a + A.T₀))))
    (hsol : Gw.IsRegSolution PW (A.Kw_ D M nW) (A.Kw_ D M nW) A.φ₀ A.hφ₀ (D.κ M)
      (streamVel (D.Φ M)) A.k₀ tp (a + A.T₀) e₀ F g U W Y)
    (Xr : ℝ) (hXr : 0 ≤ Xr)
    (hFw : ∀ j : Fin (A.k₀ + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc tp (a + A.T₀), ∑ v, ENNReal.ofReal (Gw.mass lawW v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube, ∑ r : Fin 2,
          ‖D.termRStar cK M ^ j.val • (torusJetOrder (F v t) j.val β x) r‖ₑ ^ 2 ≤
        ENNReal.ofReal (D.kap Gw.level * Xr ^ 2))
    (hgw : ∀ j : Fin (A.k₀ + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc tp (a + A.T₀), (∑ v, ENNReal.ofReal (Gw.mass lawW v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube,
          ‖D.termRStar cK M ^ j.val • torusJetOrder (g v t) j.val β x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal Xr) :
    AVRegularity.strongEnergy ρ (D.κ M) (Gw.mass lawW) tp (a + A.T₀) U W ≤
      ENNReal.ofReal ((3 + 8 * ForcedEnergy.wordCount A.k₀) *
        (Real.sqrt (massNormSq ρ (Gw.mass lawW) (fun v => (e₀ v).val)) + Xr)) := by
  have hkap' := hkap
  have h := ForcedEnergy.stage_forced_energy lawW PW (A.Kw_ D M nW) (A.Kw_ D M nW) A.φ₀ A.hφ₀
    (M + A.Jw) kW aM (a + A.T₀) _ _ Gw hI hres0 hq hΛ (by rw [hlev]; exact hM1)
    (by rw [hlev]; exact hMj) hbw (by rw [hlev]; exact hε1) hab (by rw [hkap]; exact hκ)
    (D.termRStar cK M) hRpos (by rw [hlev]; exact hRε) hrho ρ hρ hρR
    (le_max_left _ _) hθ A.k₀ hKs tp haMtp htp (D.hΦ M) αd lam hα hlam hsmall
    (by rw [hkap]; exact hstrain) hjets e₀ F g U W Y (by rw [hkap]; exact hsol) hFm hgm Xr hXr hFw hgw
  rw [hkap] at h
  exact h


theorem terminalForcedEnergy_of_reserve : TerminalForcedEnergyReserveStatement := by
  intro X
  refine ⟨128, le_rfl, ?_⟩
  intro A hΛ hValid nW cK CL Cχ kW hcK hc0 hKs hG0
  obtain ⟨-, -, ⟨hbw, -⟩, ⟨-, -, -, -, -, -, hχw, -, -⟩, -⟩ := hValid
  set c' : ℝ := min cK (1 / 2048) with hc'
  have hc'pos : 0 < c' := lt_min hcK (by norm_num)
  have hc'K : c' ≤ cK := min_le_left _ _
  have hc'2 : c' ≤ 1 / 2048 := min_le_right _ _
  set Aq : ℝ := cK / c' with hAq
  have hAq1 : 1 ≤ Aq := (one_le_div hc'pos).2 hc'K
  have hW0 := ForcedEnergy.wordCount_nonneg A.k₀
  refine ⟨Aq ^ A.k₀ * (3 + 8 * ForcedEnergy.wordCount A.k₀), by positivity, ?_⟩
  intro j₀
  obtain ⟨M₁, hM₁, hfl⟩ := ForcedEnergy.term_level_floor X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq (Λ := A.Λ) hΛ
    cK Cχ A.χw Construction.Preservation.Buffer.actualDriftJetConstant hcK hχw
    Construction.Preservation.Buffer.actualDriftJetConstant_nonneg
  refine ⟨max M₁ j₀, ?_⟩
  intro M hM D hD a lawW PW Gw aM hW tp haMtp htp e₀ F g U W Y hFm hgm hsol Xr hXr hres
  obtain ⟨hDα, hDq, hDΛ, hDζ, hΦ, hband, hterm⟩ := hD
  obtain ⟨haaM, haMb, hlev, -, hbirth, -, -, -, -, hI⟩ := hW
  have hM1 : M₁ ≤ M := le_trans (le_max_left _ _) hM
  have hMj : j₀ ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨hθle, hcKε, hγ2, hγCd⟩ := hfl M hM1
  have hεD : D.eps M = ocEpsilon X.q A.Λ M := by simp only [OCData.eps, hDq, hDΛ]
  have hεD1 : D.eps (M - 1) = ocEpsilon X.q A.Λ (M - 1) := by simp only [OCData.eps, hDq, hDΛ]
  have hkap : D.kap Gw.level = D.κ M := by simp [OCData.kap, hlev, hterm]
  obtain ⟨hεpos, hκpos, hεa, hstrain0⟩ := ForcedEnergy.term_scale_facts M X.hq.1 hΛ hband.1
    Construction.Preservation.Buffer.actualDriftJetConstant c'
    Construction.Preservation.Buffer.actualDriftJetConstant_nonneg hc'pos.le hc'2 hγ2 hγCd
  set ε := ocEpsilon X.q A.Λ M with hεdef
  have hapos : 0 < ocA X.α X.q A.Λ M := Real.rpow_pos_of_pos hεpos _
  have hmin : min (D.eps M) (Real.sqrt (D.κ M / ocA D.α D.q D.Λ M)) = ε := by
    rw [hεD, hDα, hDq, hDΛ]
    refine min_eq_left ((Real.le_sqrt' hεpos).2 ?_)
    rw [le_div_iff₀ hapos]
    exact hεa
  have hrho : rhoStar D kW.c₀ Gw.level = cK * ε := by
    rw [hlev, hc0]
    unfold rhoStar
    rw [hmin]
  have hRdef : D.termRStar cK M = cK * ε := by
    rw [OCData.termRStar, hεD]
  have hres0 : ∀ v : CompIn Gw.comps, 0 ≤ compReserve kW v.1 := by
    intro v
    unfold compReserve compGrade
    rw [hbirth v]
    simp only [List.length_nil, add_zero]
    rw [sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast hG0
  have hE1 : 0 < ocEpsilon X.q A.Λ (M - 1) := (AVRegularity.Scales.epsilon_basic (m := M - 1) X.hq.1 hΛ).1
  have hFw : ∀ j : Fin (A.k₀ + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc tp (a + A.T₀), ∑ v, ENNReal.ofReal (Gw.mass lawW v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube, ∑ r : Fin 2,
          ‖D.termRStar cK M ^ j.val • (torusJetOrder (F v t) j.val β x) r‖ₑ ^ 2 ≤
        ENNReal.ofReal (D.kap Gw.level * Xr ^ 2) := by
    intro j β
    have h1 := hres j.val (Nat.lt_succ_iff.mp j.2) β
    unfold residualNorm at h1
    have h2 := ForcedEnergy.lintegral_le_of_inv_sqrt_mul_rpow_le (ν := D.κ M) hκpos hXr
      (le_self_add.trans h1)
    rw [hkap]
    exact h2
  have hgw : ∀ j : Fin (A.k₀ + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc tp (a + A.T₀), (∑ v, ENNReal.ofReal (Gw.mass lawW v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube,
          ‖D.termRStar cK M ^ j.val • torusJetOrder (g v t) j.val β x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal Xr := by
    intro j β
    have h1 := hres j.val (Nat.lt_succ_iff.mp j.2) β
    unfold residualNorm at h1
    exact le_add_self.trans h1
  have hbound := term_stage_bound A nW cK Cχ kW D j₀ M a lawW PW Gw aM tp hI hlev hres0
    (hDq ▸ X.hq.1) (hDΛ ▸ hΛ) (by omega) hMj hbw (by rw [hεD1]; exact hE1) (haMtp.trans htp) hκpos
    hkap
    (by rw [hRdef]; positivity) (by rw [hRdef, hεD1]; exact hcKε)
    (by rw [hRdef]; exact hrho.symm)
    (c' * ε) (by positivity) (by rw [hRdef]; exact mul_le_mul_of_nonneg_right hc'K hεpos.le)
    (by rw [hεD]; exact hθle) hKs haMtp htp
    (Construction.Preservation.Buffer.actualDriftJetConstant * ocA X.α X.q A.Λ M) ε
    (mul_nonneg Construction.Preservation.Buffer.actualDriftJetConstant_nonneg hapos.le) hεpos
    (by rw [div_le_iff₀ hεpos]; nlinarith [hεpos])
    hstrain0
    (fun t _ l hl _ x => Construction.Preservation.Buffer.actual_stream_drift_arrays X.α X.s X.hα₀
      X.hα₁ X.hs₀ X.hs₁ X.q X.hq X.ζ X.hζ A.Λ hΛ D.Φ hΦ M (by omega) t l hl x)
    e₀ F g U W Y hFm hgm hsol Xr hXr hFw hgw
  have hπ : ∀ v : CompIn Gw.comps, 0 < Gw.mass lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos (hDq ▸ X.hq.1) (hDΛ ▸ hΛ) lawW v.1
  have hw : ∀ i, AEMeasurable (fun t => ENNReal.ofReal (gradFactorialNormSq (c' * ε) (W i t).val))
      (volume.restrict (Set.Icc tp (a + A.T₀))) := fun i => grad_aemeasurable _ (hsol.2.1 i)
  have hrad : D.termRStar cK M = Aq * (c' * ε) := by
    rw [hRdef, hAq]; field_simp
  have hwn : weightedNorm (D.termRStar cK M) (Gw.mass lawW) (fun _ => 1) e₀ =
      Real.sqrt (massNormSq (E := fun v : CompIn Gw.comps => ScalarH v.1.root) (K := fun _ => A.k₀)
        (D.termRStar cK M) (Gw.mass lawW) (fun v => (e₀ v).val)) := by
    unfold weightedNorm
    simp only [one_pow, div_one]
  have hs12 := sqrt_massNormSq_mono_radius (S := fun v : CompIn Gw.comps => ScalarH v.1.root)
    (c' * ε) (D.termRStar cK M) (by positivity) (by rw [hRdef]; exact mul_le_mul_of_nonneg_right hc'K hεpos.le)
    (Gw.mass lawW) hπ e₀
  rw [← hwn] at hs12
  have hAk : 0 ≤ Aq ^ A.k₀ := pow_nonneg (by linarith) _
  calc strongEnergy (D.termRStar cK M) (D.κ M) (Gw.mass lawW) tp (a + A.T₀) U W
      = strongEnergy (Aq * (c' * ε)) (D.κ M) (Gw.mass lawW) tp (a + A.T₀) U W := by rw [hrad]
    _ ≤ ENNReal.ofReal (Aq ^ A.k₀) * strongEnergy (c' * ε) (D.κ M) (Gw.mass lawW) tp (a + A.T₀) U W :=
        Construction.Preservation.FullLift.strongEnergy_mul_radius_le hAq1 _ _ _ _ _ hπ U W hw
    _ ≤ ENNReal.ofReal (Aq ^ A.k₀) * ENNReal.ofReal ((3 + 8 * ForcedEnergy.wordCount A.k₀) *
        (Real.sqrt (massNormSq (c' * ε) (Gw.mass lawW) (fun v => (e₀ v).val)) + Xr)) :=
        mul_le_mul_right hbound _
    _ = ENNReal.ofReal (Aq ^ A.k₀ * ((3 + 8 * ForcedEnergy.wordCount A.k₀) *
        (Real.sqrt (massNormSq (c' * ε) (Gw.mass lawW) (fun v => (e₀ v).val)) + Xr))) :=
        (ENNReal.ofReal_mul hAk).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc _ = (Aq ^ A.k₀ * (3 + 8 * ForcedEnergy.wordCount A.k₀)) *
              (Real.sqrt (massNormSq (c' * ε) (Gw.mass lawW) (fun v => (e₀ v).val)) + Xr) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end AVRegularity.EntryTerminal.Route

