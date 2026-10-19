-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Cascade.FilterCtx
public import AVRegularity.Construction.Residual.Presentation.Cascade.FilterRows
import AVRegularity.Construction.Residual.Presentation.Cascade.PointwiseEnvelope

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux AVRegularity.Analysis.Convolution
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **K3.1: the filter-defect form at a context, assembled from its inputs.**

`filterForm_at_ctx`: at a context, from (R) the regularity of the coefficients of the full
successor `G'`, (S) the Schur bound `1/8` of its root coefficients, (SM) the smoothness of its
coefficients, the kernel facts of `G'` (admissible, positive width at most `ε_o ρ`), (EN) a
representative of the zero extension of the readout of order `k_c + 2p + (D_m - 2) + L_c + 1`
with energy at most `E_n`, the classical representative of the readout of order `N_aux`, and
`ε_o ≤ 1`:
`FilterDefectForm … (√(|W_{J+1}| + 1) (ε_o^{L_c} M_c (1/8) E_n))` (`ε_o^{L_c}` is
`succFilterPrice`). The rows are `rootFlux_hasFluxBound'`, the readout
`filterDefectForm_of_rows` with `filterReadoutFacts`, the smoothness
`rootFluxDefect_smooth`.

Special cases: `L_c = 0`; `E_n = 0`; a successor without new components. -/

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]

/-- **The filter-defect form at a context from its inputs.** -/
theorem filterForm_at_ctx [∀ r, Nontrivial (hr r)] (hη : 0 < succEta0 α q s) (hq1 : 1 < q)
    (h128 : 128 ≤ Λ) (hζ : IsFastProfile ζ) (hcr : 0 < kI.cr)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnn : ∀ z, 0 ≤ φ₀ z) (hm : ∫ z, φ₀ z = 1)
    (hs : Function.support φ₀ ⊆ closedEuclideanUnitBall)
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr) (hm1 : 1 ≤ c.m)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
    (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
      (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
      (fun x => aZ t x v) Naux)
    {kc Lc : ℕ} (hNaux : kc + 2 * p + succSchedD D₀ N p (H + 1) ≤ Naux) {Γ' : ℝ} (hΓ' : 0 ≤ Γ')
    (hreg : CoeffReg c.G' c.tp c.tf (rhoEnh c.D kI.cr c.m) (kc + 2 * p))
    (hS : SchurBound (1 / 8) (kernelSchurMatrix (G := fun _ j _ => hr j.1.root)
      (c.D.κ (c.m - 1)) (rhoEnh c.D kI.cr c.m) (c.G'.mass c.law) (kc + 2 * p)
      (succSchedD D₀ N p (H + 1)) c.tp c.tf (fun _ => 1)
      (fun v u γ => (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
        c.seedK c.freshK v u γ).width)
      (fun _ j _ => ContinuousLinearMap.id ℝ (hr j.1.root))
      (filtCoeff c.G' (fun _ u _ => u.1 ∈ c.G.comps))))
    (hsm : ∀ (v u : CompIn c.G'.comps) (γ : c.G'.fam.Γ v u) (d : ℕ) (t : ℝ),
      ContDiff ℝ ((kc + 2 * p : ℕ) : ℕ) (c.G'.physCoeff v u γ d t) ∧
        IsZ2Periodic (c.G'.physCoeff v u γ d t))
    (hker : ∀ v u (γ : c.G'.fam.Γ v u),
      (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        v u γ).IsAdmissible Γ' Lc ∧
      0 < (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        v u γ).width ∧
      (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        v u γ).width ≤ FilterBase c.D c.G c.m kI.cr σ₀ * rhoEnh c.D kI.cr c.m)
    (hbase : FilterBase c.D c.G c.m kI.cr σ₀ ≤ 1) {En : ℝ}
    (hEn : ∃ V : ∀ j : CompIn c.G'.comps,
        ℝ → TorusHk (kc + 2 * p + (succSchedD D₀ N p (H + 1) - 2) + Lc + 1) (hr j.1.root),
      (∀ j, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep (V j t) (extAZ c.G c.G' aZ j t)
        (kc + 2 * p + (succSchedD D₀ N p (H + 1) - 2) + Lc + 1)) ∧
      (∀ j, AEStronglyMeasurable (V j) (volume.restrict (Set.Icc c.tp c.tf))) ∧
      Integrable (fun t => massGradNormSq (E := fun j : CompIn c.G'.comps => hr j.1.root)
        (K := fun _ => kc + 2 * p + (succSchedD D₀ N p (H + 1) - 2) + Lc)
        (rhoEnh c.D kI.cr c.m) (c.G'.mass c.law) (fun j => (V j t).val))
        (volume.restrict (Set.Icc c.tp c.tf)) ∧
      Real.sqrt (c.D.κ (c.m - 1) * ∫ s in Set.Icc c.tp c.tf,
        massGradNormSq (E := fun j : CompIn c.G'.comps => hr j.1.root)
          (K := fun _ => kc + 2 * p + (succSchedD D₀ N p (H + 1) - 2) + Lc)
          (rhoEnh c.D kI.cr c.m) (c.G'.mass c.law) (fun j => (V j s).val)) ≤ En) :
    FilterDefectForm (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀
      c.G c.G' c.m p kc (c.D.eps (c.m - 1)) (succEta0 α q s) aZ (c.G.mass c.law) c.tp c.tf
      (rhoEnh c.D kI.cr c.m)
      (Real.sqrt (((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card : ℝ) + 1) *
        (FilterBase c.D c.G c.m kI.cr σ₀ ^ Lc *
          FilterMc φ₀ Lc (kc + 2 * p) (succSchedD D₀ N p (H + 1)) Γ' * (1 / 8) * En)) := by
  obtain ⟨V, hcl, hmeas, hint, hE⟩ := hEn
  obtain ⟨hpar, hent, hfib⟩ := filterReadoutFacts hη hq1 h128 c hm1
  have hqD : 1 < c.D.q := c.q_gt hq1
  have hΛD : 128 ≤ c.D.Λ := c.lambda_ge h128
  have hν : 0 < c.D.κ (c.m - 1) := c.kappa_pred_pos (by omega) hζ
  have hρ : 0 < rhoEnh c.D kI.cr c.m := by
    unfold rhoEnh
    exact mul_pos hcr (Real.sqrt_pos.2 (mul_pos hν (Construction.Stream.ocTauPP_pos (by omega))))
  have hE0 : 0 ≤ c.D.eps (c.m - 1) := (Scales.epsilon_basic (m := c.m - 1) hqD hΛD).1.le
  have hσ : ∀ x : CompIn c.G'.comps, 0 < c.G'.mass c.law x := fun x =>
    Buffer.birth_compMass_pos hqD hΛD c.law x.1
  have hπ : ∀ v : CompIn c.G.comps, 0 < c.G.mass c.law v := fun v =>
    Buffer.birth_compMass_pos hqD hΛD c.law v.1
  have hrows := rootFlux_hasFluxBound' (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
    c.seedK c.freshK φ₀ hφ₀ hd hnn hm hs c.G c.G' aZ c.tp c.tf (rhoEnh c.D kI.cr c.m)
    (c.D.κ (c.m - 1)) hρ hν c.tp_le_tf (kc + 2 * p)
    (Buffer.preparation_schedule_order_ge_two D₀ N p H) Lc Γ' hΓ'
    (FilterBase c.D c.G c.m kI.cr σ₀) (FilterBase_nonneg c.D c.G c.m kI.cr σ₀ hE0) hbase
    (c.G'.mass c.law) hσ hreg (fun v u γ => (hker v u γ).1) (fun v u γ => (hker v u γ).2.1)
    (fun v u γ => (hker v u γ).2.2) (1 / 8) (by norm_num) hS le_rfl V hcl hmeas hint hE
  have hsm' : ∀ v' : CompIn c.G'.comps, ∀ t ∈ Set.Icc c.tp c.tf,
      ContDiff ℝ ((kc + 2 * p : ℕ) : ℕ∞)
          (fun y => rootFluxDefect (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK
            c.freshK φ₀ c.G c.G' aZ v' t y) ∧
        IsZ2Periodic (fun y => rootFluxDefect (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
          c.seedK c.freshK φ₀ c.G c.G' aZ v' t y) := by
    intro v' t ht
    exact rootFluxDefect_smooth (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK
      c.freshK φ₀ hd hs c.G c.G' aZ t (kc + 2 * p) (fun v u γ d => hsm v u γ d t)
      (fun u => by
        obtain ⟨-, h1, h2, -⟩ := hZ u t ht
        exact ⟨h1.of_le (WithTop.coe_le_coe.2 (Nat.cast_le.2 hNaux)), h2⟩) v'
  exact filterDefectForm_of_rows (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
    c.seedK c.freshK φ₀ c.G c.G' c.m p kc (c.D.eps (c.m - 1)) (succEta0 α q s) aZ
    (c.G.mass c.law) (c.G'.mass c.law) c.tp c.tf (rhoEnh c.D kI.cr c.m) _
    (((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card : ℝ) + 1) hν hE0
    (by positivity) hπ hσ hpar hent hfib hsm' hrows

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation
open AVRegularity.Construction.Preservation.Assembly AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.RetainedEnergy
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **K3.1: the inputs of the filter-defect form at every context, in the common prefix.**

* `KernelsAt`: the conclusion of `successorKernels` after the choice of `Λ` (named, so the
  prefix proof passes it as one hypothesis).
* `filterKernels_at_ctx`: at a context of large level, the kernels of the full successor are
  admissible with `L_c` moments, of positive width at most `ε_o ρ`, and `ε_o ≤ 1` (the records
  of `G` are at most `C_wid ρ ε_{m-1}^{λ_C} ≤ ρ` above a level threshold).
* `FilterInputsCtxAt`: (R), (S), (SM), the kernel facts and `ε_o ≤ 1` at every context of
  level `≥ m_*`; `filterInputs_at_ctx` proves it from the constants chosen before the stage,
  `succPrefix_w31FilterInputs` in the common prefix (the route of `grade_rows_production`).

Special cases: a context without identities (all clauses about edges are empty); `L_c = 0`. -/

/-- The conclusion of `successorKernels` after the choice of `Λ`. -/
def KernelsAt (α q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (Γ : ℝ) (m₀ : ℕ) : Prop :=
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (P : ProvParams) (Mn : SuccMenu) (law : BirthLaw)
      (seedK freshK : ℕ → KernelSpec) (kI : InvConsts) (cr σ₀ : ℝ) (nk : ℕ+), 0 < cr →
      (∀ l, 1 ≤ l → l < D.term → IsFreshKernel D cr σ₀ nk l (freshK l)) →
    ∀ (M : ℕ) (G G' : GenStage D hr Dm bw j₀) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
      (tA tB S θK : ℝ),
      IsStageInvariant law P seedK freshK φ₀ hφ₀ M kI tA tB S θK G →
      IsActualSuccessor D P Mn G G' → m₀ ≤ G.level → G.level ≤ D.term →
    ∀ L : ℕ, L ≤ kI.Lker → L + 1 ≤ 2 * (nk : ℕ) →
    ∀ qr ρ : ℝ, freshWidth D cr σ₀ (G.level - 1) ≤ qr * ρ →
      (∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).record.width ≤ qr * ρ) →
    ∀ v u (γ : G'.fam.Γ v u),
      (G'.kernelOf P seedK freshK v u γ).IsAdmissible (max kI.Γk (max Γ 2)) L ∧
        0 < (G'.kernelOf P seedK freshK v u γ).width ∧
        (G'.kernelOf P seedK freshK v u γ).width ≤ qr * ρ

section Ctx

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]

/-- **The kernels of the full successor and `ε_o ≤ 1` at a context.** -/
theorem filterKernels_at_ctx (hq1 : 1 < q) (h128 : 128 ≤ Λ) (hζ : IsFastProfile ζ)
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr)
    (hcr : 0 < kI.cr) (hσ₀ : 0 ≤ σ₀) {Γ : ℝ} {m₀ : ℕ} (hkern : KernelsAt α q ζ Λ Γ m₀)
    {Lc : ℕ} (hLker : Lc ≤ kI.Lker) (hLnk : kI.Lker + 1 ≤ 2 * nk) (mw : ℕ)
    (hmw : ∀ m, mw ≤ m → 8 * (kI.Cwid * ocEpsilon q Λ (m - 1) ^ kI.lamC) < 1 / 8)
    (hm : max m₀ (mw + 1) ≤ c.m) :
    (∀ v u (γ : c.G'.fam.Γ v u),
      (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        v u γ).IsAdmissible (max kI.Γk (max Γ 2)) Lc ∧
      0 < (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        v u γ).width ∧
      (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        v u γ).width ≤ FilterBase c.D c.G c.m kI.cr σ₀ * rhoEnh c.D kI.cr c.m) ∧
    FilterBase c.D c.G c.m kI.cr σ₀ ≤ 1 := by
  have hm1 : 1 ≤ c.m := by omega
  have hqD : 1 < c.D.q := c.q_gt hq1
  have hΛD : 128 ≤ c.D.Λ := c.lambda_ge h128
  have hν : 0 < c.D.κ (c.m - 1) := c.kappa_pred_pos (by omega) hζ
  have hρ : 0 < rhoEnh c.D kI.cr c.m := by
    unfold rhoEnh
    exact mul_pos hcr (Real.sqrt_pos.2 (mul_pos hν (Construction.Stream.ocTauPP_pos (by omega))))
  have hE := Scales.epsilon_basic (m := c.m - 1) hqD hΛD
  have hnk : kI.Lker + 1 ≤ 2 * ((nk.toPNat' : ℕ)) := by
    have : nk ≤ (nk.toPNat' : ℕ) := by
      change nk ≤ nk - 1 + 1
      omega
    omega
  refine ⟨?_, ?_⟩
  · exact hkern hr c.D c.hα c.hq c.hΛ c.hζ c.hseq c.bandD _ bw j₀ _
      (succMenu c.Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) c.law c.seedK c.freshK kI
      kI.cr σ₀ nk.toPNat' hcr (fun l h1 h2 => c.hfresh l h1 (c.hterm ▸ h2)) c.Mnat c.G c.G' φ₀ hφ₀
      c.tA c.tf _ _ c.hinv c.hactual (by rw [c.hlevel]; omega) (by rw [c.hlevel]; exact c.m_le_term)
      Lc hLker (by omega)
      (FilterBase c.D c.G c.m kI.cr σ₀) (rhoEnh c.D kI.cr c.m)
      (by rw [c.hlevel]; exact freshWidth_le_base c.D c.G hm1 kI.cr σ₀ hρ.le)
      (fun v u γ => width_le_base c.D c.G c.m kI.cr σ₀ hρ v u γ)
  · refine FilterBase_le_one c.D c.G c.m kI.cr σ₀ hρ hE.1.le hE.2.1 hσ₀ fun v u γ => ?_
    obtain ⟨_, _, _, _, _, _, _, _, hkernels, _⟩ := c.hinv
    have hc := (hkernels v u γ).2.2.2.1
    have hρ' : rhoEnh c.D kI.cr c.G.level = rhoEnh c.D kI.cr c.m := by rw [c.hlevel]
    have hε' : c.D.eps (c.G.level - 1) = c.D.eps (c.m - 1) := by rw [c.hlevel]
    rw [hρ', hε'] at hc
    have hsmall : kI.Cwid * c.D.eps (c.m - 1) ^ kI.lamC ≤ 1 := by
      have h := hmw c.m (by omega)
      have h' : kI.Cwid * ocEpsilon q Λ (c.m - 1) ^ kI.lamC < 1 / 64 := by linarith
      have he : c.D.eps (c.m - 1) = ocEpsilon q Λ (c.m - 1) := by
        simp only [OCData.eps, c.hq, c.hΛ]
      rw [he]
      linarith
    calc (c.G.fam.identity v u γ).record.width
        ≤ kI.Cwid * rhoEnh c.D kI.cr c.m * c.D.eps (c.m - 1) ^ kI.lamC := hc
      _ = (kI.Cwid * c.D.eps (c.m - 1) ^ kI.lamC) * rhoEnh c.D kI.cr c.m := by ring
      _ ≤ 1 * rhoEnh c.D kI.cr c.m := mul_le_mul_of_nonneg_right hsmall hρ.le
      _ = rhoEnh c.D kI.cr c.m := one_mul _

end Ctx

end AVRegularity.Construction.Residual.Presentation.Cascade
end
