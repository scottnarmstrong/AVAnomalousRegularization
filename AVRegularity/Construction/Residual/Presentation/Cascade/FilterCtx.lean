-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Residual.Presentation.Cascade.PointwiseEnvelope
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.CycleComparison.Reconstruction.ReconForcePieces
public import AVRegularity.Construction.Residual.Presentation.Cascade.CovGAssembly
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic
import AVRegularity.EntryWeakAssembly.MolecularHigherTraceJetDerivative
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.InitialValue.Cascade
public import AVRegularity.Construction.Preservation.Frontier.GradeRows.Producer
public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.RowMaster
import AVRegularity.CycleComparison.Coarse.Energy.Word
import AVRegularity.CycleComparison.Coarse.Energy.Zero

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The bounds of the residual at a frame with separate constants** (cascade side of the bill
residual).

`frameResidualBound_of_parts` asks the three flux bounds at a
common constant `C_fl`, and the reconstruction and the fine tail at a common constant `C`. The
pieces come with their own constants; this module raises them.

* Monotonicity in the constant: `frameCovTruncAt_mono`, `frameFrontierAt_mono`,
  `frameFilterAt_mono`, `frameFineTailAt_mono`, `reconBound_mono'`,
  `frameReconAt_mono` (antitone in the flux constant, monotone in the bill constant), and of
  the four flux forms (`covGForm_mono`, `covGradForm_mono`,
  `frontierInnerForm_mono`, `filterDefectForm_mono'`).
* `frameResidualBound_of_bounds`: `FrameResidualBoundAt` with the constant `3·0!·C_c` from
  the three flux bounds at `C₁, C₂, C₃ ≤ C_fl`, the reconstruction at `(C_fl, C_r)` and the fine
  tail at `C_f`, with `C_r, C_f ≤ C_c`.

The prices are nonnegative as soon as `ε_{m−1}, ε_m ≥ 0` and `c_r, c₀ ≥ 0`; `A_in ≥ 0`.

When all the constants vanish, or `A_in = 0`, the bounds are `0`. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-! ### The prices are nonnegative -/

omit [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem succCovPrice_nonneg (m : ℕ) (cr : ℝ) (p : ℕ) (tp tf : ℝ) :
    0 ≤ succCovPrice D m cr p tp tf := by
  have hω : 0 ≤ (⨆ t : Set.Icc tp tf, ∑ a : Fin 2, ∑ a' : Fin 2,
      |covPrimitive D m t a a'|) / rhoEnh D cr m ^ 2 :=
    div_nonneg (Real.iSup_nonneg fun _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _) (sq_nonneg _)
  unfold succCovPrice
  exact add_nonneg (pow_nonneg hω _) (pow_nonneg hω _)

omit [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem succFrontPrice_nonneg {m : ℕ} (η₀ : ℝ) (J H : ℕ) (θ₁ θ₂ : ℝ)
    (hE : 0 ≤ D.eps (m - 1)) : 0 ≤ succFrontPrice D m η₀ J H θ₁ θ₂ :=
  add_nonneg (Real.rpow_nonneg hE _) (Real.rpow_nonneg hE _)

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem succFilterPrice_nonneg (G : GenStage D hr Dm b j₀) {m : ℕ} (cr σ₀ : ℝ) (Lc : ℕ)
    (hE : 0 ≤ D.eps (m - 1)) : 0 ≤ succFilterPrice D G m cr σ₀ Lc :=
  pow_nonneg ((Real.rpow_nonneg hE _).trans (le_max_left _ _)) _

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem succFineBill_nonneg (G : GenStage D hr Dm b j₀) {m : ℕ} {c₀ : ℝ} (Lf : ℕ)
    (he : 0 ≤ D.eps m) (hc₀ : 0 ≤ c₀) : 0 ≤ succFineBill D G m c₀ Lf := by
  have hρs : 0 ≤ rhoStar D c₀ m := mul_nonneg hc₀ (le_min he (Real.sqrt_nonneg _))
  exact pow_nonneg (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
    div_nonneg (ConstituentRecord.width_pos _).le hρs) _

/-! ### Monotonicity of the forms -/

section Forms

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A smooth form with a flux bound is monotone in the bound. -/
theorem smoothFlux_mono {P : Prop} {k : ℕ} {I : Set ℝ} {ν ρ : ℝ} {π : ι → ℝ}
    {Fl : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} {Y Y' : ℝ}
    (hF : P ∧ HasFluxBound k I ν ρ π Fl Y) (hY : Y ≤ Y') : P ∧ HasFluxBound k I ν ρ π Fl Y' :=
  ⟨hF.1, hasFluxBound_mono_Y hF.2 hY⟩

end Forms

theorem covGForm_mono {Mn : SuccMenu} {G : GenStage D hr Dm b j₀} {m N p depth kc : ℕ}
    {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    {aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root} {π : CompIn G.comps → ℝ}
    {tp tf ρ Y Y' : ℝ} (h : CovGForm Mn G m N p depth kc CcT aZ π tp tf ρ Y) (hY : Y ≤ Y') :
    CovGForm Mn G m N p depth kc CcT aZ π tp tf ρ Y' :=
  smoothFlux_mono h hY

theorem covGradForm_mono {Mn : SuccMenu} {G : GenStage D hr Dm b j₀} {m p kc : ℕ}
    {aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root} {π : CompIn G.comps → ℝ}
    {tp tf ρ Y Y' : ℝ} (h : CovGradForm Mn G m p kc aZ π tp tf ρ Y) (hY : Y ≤ Y') :
    CovGradForm Mn G m p kc aZ π tp tf ρ Y' :=
  hasFluxBound_mono_Y h hY

theorem frontierInnerForm_mono {P : ProvParams} {seedK freshK : ℕ → KernelSpec}
    {φ₀ : Vec 2 → ℝ} {G G' Gr : GenStage D hr Dm b j₀} {m p H J kc : ℕ} {E η₀ : ℝ}
    {aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root} {π : CompIn G.comps → ℝ}
    {tp tf ρ Y Y' : ℝ}
    (h : FrontierInnerForm P seedK freshK φ₀ G G' Gr m p H J kc E η₀ aY π tp tf ρ Y)
    (hY : Y ≤ Y') : FrontierInnerForm P seedK freshK φ₀ G G' Gr m p H J kc E η₀ aY π tp tf ρ Y' :=
  smoothFlux_mono h hY

theorem filterDefectForm_mono' {P : ProvParams} {seedK freshK : ℕ → KernelSpec}
    {φ₀ : Vec 2 → ℝ} {G G' : GenStage D hr Dm b j₀} {m p kc : ℕ} {E η₀ : ℝ}
    {aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root} {π : CompIn G.comps → ℝ}
    {tp tf ρ Y Y' : ℝ} (h : FilterDefectForm P seedK freshK φ₀ G G' m p kc E η₀ aZ π tp tf ρ Y)
    (hY : Y ≤ Y') : FilterDefectForm P seedK freshK φ₀ G G' m p kc E η₀ aZ π tp tf ρ Y' :=
  smoothFlux_mono h hY

/-! ### Monotonicity of the bounds at a frame -/

section Frame

variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

theorem frameCovTruncAt_mono {kc : ℕ} {cr Ain C C' : ℝ}
    (h : FrameCovTruncAt F law kc cr Ain C) (hC : C ≤ C') (hA : 0 ≤ Ain) :
    FrameCovTruncAt F law kc cr Ain C' := by
  unfold FrameCovTruncAt CovTruncBound at h ⊢
  exact hasFluxBound_mono_Y h (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC (succCovPrice_nonneg _ _ _ _ _)) hA)

theorem frameFrontierAt_mono {kc : ℕ} {cr θ₁ θ₂ Ain C C' : ℝ}
    (h : FrameFrontierAt F law kc cr θ₁ θ₂ Ain C) (hC : C ≤ C') (hA : 0 ≤ Ain)
    (hE : 0 ≤ D.eps (F.m - 1)) : FrameFrontierAt F law kc cr θ₁ θ₂ Ain C' := by
  unfold FrameFrontierAt FrontierBound at h ⊢
  exact hasFluxBound_mono_Y h (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC (succFrontPrice_nonneg _ _ _ _ _ hE)) hA)

theorem frameFilterAt_mono {kc : ℕ} {cr σ₀ : ℝ} {Lc : ℕ} {Ain C C' : ℝ}
    (h : FrameFilterAt F law kc cr σ₀ Lc Ain C) (hC : C ≤ C') (hA : 0 ≤ Ain)
    (hE : 0 ≤ D.eps (F.m - 1)) : FrameFilterAt F law kc cr σ₀ Lc Ain C' := by
  unfold FrameFilterAt FilterBound at h ⊢
  exact hasFluxBound_mono_Y h (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC (succFilterPrice_nonneg _ _ _ _ hE)) hA)

theorem frameFineTailAt_mono {c₀ : ℝ} {Lf : ℕ} {Ain C C' : ℝ}
    (h : FrameFineTailAt F law c₀ Lf Ain C) (hC : C ≤ C') (hA : 0 ≤ Ain)
    (he : 0 ≤ D.eps F.m) (hc₀ : 0 ≤ c₀) : FrameFineTailAt F law c₀ Lf Ain C' := by
  unfold FrameFineTailAt FineTailBound at h ⊢
  exact hasFluxBound_mono_Y h (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC (succFineBill_nonneg _ _ he hc₀)) hA)

end Frame

/-- A reconstruction bound is monotone in its bound. -/
theorem reconBound_mono' {Mn : SuccMenu} {G : GenStage D hr Dm b j₀} {m N depth k : ℕ}
    {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    {aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root} {π : CompIn G.comps → ℝ}
    {tp tf rs X X' : ℝ} (h : ReconBound Mn G m N depth k CcT aRep π tp tf rs X) (hX : X ≤ X') :
    ReconBound Mn G m N depth k CcT aRep π tp tf rs X' := by
  obtain ⟨K, hK, uK, wK, RK, qK, hr'⟩ := h
  exact ⟨K, hK, uK, wK, RK, qK,
    { desc := hr'.desc, value := hr'.value, plain := hr'.plain,
      flux := ⟨hr'.flux.1, hr'.flux.2.trans hX⟩, scalar := ⟨hr'.scalar.1, hr'.scalar.2.trans hX⟩ }⟩

section Frame

variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- **The reconstruction bound at a frame is antitone in the flux constant and monotone in the bill
constant.** -/
theorem frameReconAt_mono {kc : ℕ} {c₀ cr c σ₀ : ℝ} {Lc Acl : ℕ} {θ₁ θ₂ Ain Cfl Cfl' C C' : ℝ}
    (h : FrameReconAt F law kc c₀ cr c σ₀ Lc Acl θ₁ θ₂ Ain Cfl C) (hCfl : Cfl' ≤ Cfl)
    (hC : C ≤ C') (hA : 0 ≤ Ain) (hE : 0 ≤ D.eps (F.m - 1)) (he : 0 ≤ D.eps F.m)
    (hcr : 0 ≤ cr) : FrameReconAt F law kc c₀ cr c σ₀ Lc Acl θ₁ θ₂ Ain Cfl' C' := by
  intro h2a h2b h3
  refine reconBound_mono' (h (frameCovTruncAt_mono F law h2a hCfl hA)
    (frameFrontierAt_mono F law h2b hCfl hA hE) (frameFilterAt_mono F law h3 hCfl hA hE))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC ?_) hA)
  exact succReconBill_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE he hcr

/-- **The bounds of the residual at a frame from bounds with separate constants.** -/
theorem frameResidualBound_of_bounds (hW : ResidualWordsOfMassStatement)
    (hπ : ∀ v, 0 < F.G.mass law v) {kc : ℕ} {c₀ cr c σ₀ : ℝ} {Lc Lf Acl : ℕ}
    {θ₁ θ₂ Ain C₁ C₂ C₃ Cfl Cr Cf Cc : ℝ} (hA : 0 ≤ Ain) (hE : 0 ≤ D.eps (F.m - 1))
    (he : 0 ≤ D.eps F.m) (hcr : 0 ≤ cr) (hc₀ : 0 ≤ c₀) (h₁ : C₁ ≤ Cfl) (h₂ : C₂ ≤ Cfl)
    (h₃ : C₃ ≤ Cfl) (hr' : Cr ≤ Cc) (hf : Cf ≤ Cc)
    (h2a : FrameCovTruncAt F law kc cr Ain C₁) (h2b : FrameFrontierAt F law kc cr θ₁ θ₂ Ain C₂)
    (h3 : FrameFilterAt F law kc cr σ₀ Lc Ain C₃)
    (hrec : FrameReconAt F law kc c₀ cr c σ₀ Lc Acl θ₁ θ₂ Ain Cfl Cr)
    (hfine : FrameFineTailAt F law c₀ Lf Ain Cf) :
    FrameResidualBoundAt F law c₀ cr c σ₀ Lc Lf Acl θ₁ θ₂ Ain
      (3 * ((0 : ℕ).factorial : ℝ) * Cc) :=
  frameResidualBound_of_parts F law hW hπ (frameCovTruncAt_mono F law h2a h₁ hA)
    (frameFrontierAt_mono F law h2b h₂ hA hE) (frameFilterAt_mono F law h3 h₃ hA hE)
    (frameReconAt_mono F law hrec le_rfl hr' hA hE he hcr)
    (frameFineTailAt_mono F law hfine hf hA he hc₀)

end Frame

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.KernelDefect AVRegularity.KernelEnergy
open AVRegularity.EntryTerminal.ForcedEnergy AVRegularity.Construction.Preservation.Buffer
open AVRegularity.Construction.Residual.Presentation AVRegularity.Analysis.Convolution
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The defect step of the fine tail at a cascade stage.**

The generic form `StageFineDefectForm` from the stage invariant, the cascade form of the terminal
`fineDefectAt_of`. What replaces the terminal context: the kernel clause and the Schur clause are
read from `IsStageInvariant` (the kernels are `G.kernelOf`, of arbitrary orders: the defect data
`FDData` carries the order-uniform moment constant), the width ratio is `succFineBill`'s base, and
the positivity of `cker` is a named hypothesis (`thr.cker = 1` at a cascade stage). -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The price constant of the defect step: `∑_{m ≤ D_m - 2} C₀ ((k+L_f+m)!/k!)/c_m`. -/
def stageFineMconst (φ₀ : Vec 2 → ℝ) (Lf Dm k : ℕ) (Γk : ℝ) (cker : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (Dm - 1),
    kdUniformMomentConst φ₀ Lf Γk * (((k + (Lf + m)).factorial : ℝ) / k.factorial) / cker m

theorem stageFineMconst_nonneg (φ₀ : Vec 2 → ℝ) (Lf Dm k : ℕ) {Γk : ℝ} (hΓ : 0 ≤ Γk)
    {cker : ℕ → ℝ} (hc : ∀ m, m + 2 ≤ Dm → 0 < cker m) :
    0 ≤ stageFineMconst φ₀ Lf Dm k Γk cker := by
  unfold stageFineMconst
  refine Finset.sum_nonneg fun m hm => ?_
  have := kdUniformMomentConst_nonneg φ₀ Lf hΓ
  have h2 : 0 < cker m := hc m (by have := Finset.mem_range.1 hm; omega)
  positivity

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The width ratio of the kernels of the stage: the base of `succFineBill`. -/
theorem width_div_le (G : GenStage D hr Dm b j₀) (rs : ℝ) (v u : CompIn G.comps)
    (γ : G.fam.Γ v u) :
    (G.fam.identity v u γ).record.width / rs ≤
      ⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
        (G.fam.identity v u γ).record.width / rs := by
  classical
  have h1 : (G.fam.identity v u γ).record.width / rs ≤
      ⨆ γ' : G.fam.Γ v u, (G.fam.identity v u γ').record.width / rs :=
    le_ciSup (f := fun γ' : G.fam.Γ v u => (G.fam.identity v u γ').record.width / rs)
      (Set.finite_range _).bddAbove γ
  have h2 : (⨆ γ' : G.fam.Γ v u, (G.fam.identity v u γ').record.width / rs) ≤
      ⨆ (u' : CompIn G.comps) (γ' : G.fam.Γ v u'), (G.fam.identity v u' γ').record.width / rs :=
    le_ciSup (f := fun u' : CompIn G.comps =>
      ⨆ γ' : G.fam.Γ v u', (G.fam.identity v u' γ').record.width / rs)
      (Set.finite_range _).bddAbove u
  have h3 : (⨆ (u' : CompIn G.comps) (γ' : G.fam.Γ v u'),
        (G.fam.identity v u' γ').record.width / rs) ≤
      ⨆ (v' : CompIn G.comps) (u' : CompIn G.comps) (γ' : G.fam.Γ v' u'),
        (G.fam.identity v' u' γ').record.width / rs :=
    le_ciSup (f := fun v' : CompIn G.comps => ⨆ (u' : CompIn G.comps) (γ' : G.fam.Γ v' u'),
      (G.fam.identity v' u' γ').record.width / rs) (Set.finite_range _).bddAbove v
  exact h1.trans (h2.trans h3)

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem fineBase_nonneg (G : GenStage D hr Dm b j₀) {rs : ℝ} (hrs : 0 < rs) :
    0 ≤ ⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
        (G.fam.identity v u γ).record.width / rs :=
  Real.iSup_nonneg fun v => Real.iSup_nonneg fun u => Real.iSup_nonneg fun γ =>
    div_nonneg (G.fam.identity v u γ).record.width_pos.le hrs.le

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem fineBase_le_one (G : GenStage D hr Dm b j₀) {rs : ℝ} (hrs : 0 < rs)
    (hw : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).record.width ≤ rs) :
    (⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
        (G.fam.identity v u γ).record.width / rs) ≤ 1 :=
  Real.iSup_le (fun v => Real.iSup_le (fun u => Real.iSup_le (fun γ =>
    (div_le_one hrs).2 (hw v u γ)) zero_le_one) zero_le_one) zero_le_one


/-- The defect data of a stage: the kernels `G.kernelOf` (of arbitrary orders, all admissible at
`Γk` with `L` moments), the coefficients and the radius of the operator `R2`. -/
def stageDefectData (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G : GenStage D hr Dm b j₀) (hφ : Integrable φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnn : ∀ z, 0 ≤ φ₀ z) (hm : ∫ z, φ₀ z = 1) (hs : Function.support φ₀ ⊆ closedEuclideanUnitBall)
    (tp tf rs ν : ℝ) (k : ℕ) (hD : 2 ≤ Dm) (Lf : ℕ) (Γk : ℝ) (hΓk : 0 ≤ Γk) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hrs : 0 < rs)
    (R2 : TorusKernelOperator tp tf rs ν k Dm (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root))
    (hadm : ∀ v u (γ : G.fam.Γ v u), (G.kernelOf P seedK freshK v u γ).IsAdmissible Γk Lf)
    (hwpos : ∀ v u (γ : G.fam.Γ v u), 0 < (G.kernelOf P seedK freshK v u γ).width)
    (hwq : ∀ v u (γ : G.fam.Γ v u), (G.kernelOf P seedK freshK v u γ).width ≤ q * rs) :
    FDData (CompIn G.comps) (fun v => hr v.1.root) G.fam.Γ where
  φ₀ := φ₀
  hφ := hφ
  hd := hd
  hnonneg := hnn
  hmass := hm
  hsupp := hs
  t₀ := tp
  t₁ := tf
  ρ := rs
  hρ := hrs
  k := k
  D := Dm
  hD := hD
  L := Lf
  Γk := Γk
  hΓk := hΓk
  q := q
  hq0 := hq0
  hq1 := hq1
  B := R2.B
  hB_meas := R2.hB_meas
  hB_smooth := R2.hB_smooth
  hB_per := R2.hB_per
  hB_fin := R2.hB_fin
  Kern := fun v u γ => G.kernelOf P seedK freshK v u γ
  hadm := hadm
  hwpos := hwpos
  hwq := hwq

/-- A value-jet representative of a classical field is a classical representative. -/
theorem classicalRep {K : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (W : TorusHk (K + 1) E) (a : Vec 2 → E)
    (hC : ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) a) (hp : IsZ2Periodic a)
    (hW : W.toFunction.jet (valueIndex2 (K + 1)) =ᵐ[volume.restrict unitCube] a) :
    IsClassicalRep W a (K + 1) :=
  AVRegularity.Construction.Preservation.FullLift.classicalRep_of_value_ae W _ a
    (AVRegularity.CycleComparison.Reconstruction.periodicHk_isClassicalRep (K + 1) hC hp le_rfl) hW


/-- **The defect step at a stage** (generic form): from the stage invariant, the reserves,
`k ≤ Ks`, `θ_K ≤ 1/8`, the kernel widths below the radius, the fine defect of every represented
classical field `uh` of order `K + 1` costs `C·(max_γ w_γ/ρ_⋆)^{L_f}` times its gradient energy,
for `C ≥ M·max(θ_K, 0)` with `M` the moment sum `stageFineMconst`. -/
theorem stageFineDefect [∀ r, Nontrivial (hr r)]
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnn : ∀ z, 0 ≤ φ₀ z)
    (hm : ∫ z, φ₀ z = 1) (hs : Function.support φ₀ ⊆ closedEuclideanUnitBall)
    (M : ℕ) (kS : InvConsts) (tA tB S θK : ℝ) (G : GenStage D hr Dm b j₀)
    (hI : IsStageInvariant law P seedK freshK φ₀ hφ₀ M kS tA tB S θK G)
    (hres0 : ∀ v : CompIn G.comps, 0 ≤ compReserve kS v.1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < b)
    (hε1 : 0 < D.eps (G.level - 1)) (hκ : 0 < D.kap G.level) (hD2 : 2 ≤ Dm)
    (hθ : θK ≤ 1 / 8) (m k K Lf : ℕ) (c₀ tp tf : ℝ)
    (hlev : G.level = m) (hkap : D.kap G.level = D.κ m) (hc₀ : kS.c₀ = c₀)
    (hRpos : 0 < rhoStar D c₀ m) (hRε : rhoStar D c₀ m ≤ D.eps (G.level - 1))
    (hKs : k ≤ kS.Ks) (hLf : Lf ≤ kS.Lker) (hK : k + (Dm - 2) + Lf ≤ K)
    (hsmall : kS.Cwid * D.eps G.level ^ kS.σf ≤ 1)
    (hcpos : ∀ j, j + 2 ≤ Dm → 0 < kS.cker j) (hA : tA ≤ tp) (hB : tf ≤ tB) (C : ℝ)
    (hC : stageFineMconst φ₀ Lf Dm k (max kS.Γk 0) kS.cker * max θK 0 ≤ C) :
    StageFineDefectForm P seedK freshK φ₀ G m k K (G.mass law) tp tf (rhoStar D c₀ m)
      (C * succFineBill D G m c₀ Lf) := by
  have hrs : rhoStar D kS.c₀ G.level = rhoStar D c₀ m := by rw [hc₀, hlev]
  have hMnn : 0 ≤ stageFineMconst φ₀ Lf Dm k (max kS.Γk 0) kS.cker :=
    stageFineMconst_nonneg φ₀ Lf Dm k (le_max_right _ _) hcpos
  have hC0 : 0 ≤ C := (mul_nonneg hMnn (le_max_right _ _)).trans hC
  unfold StageFineDefectForm succFineBill
  rw [← hkap, ← hrs]
  rw [← hrs] at hRpos hRε
  intro uh Û E hreal hen
  by_cases hw : tp ≤ tf
  · have hbase0 := fineBase_nonneg G hRpos
    have hI' := hI
    obtain ⟨-, -, -, -, -, -, -, -, hkernel, hschur, -⟩ := hI
    have hker : ∀ v u (γ : G.fam.Γ v u), (G.kernelOf P seedK freshK v u γ).IsAdmissible
        kS.Γk kS.Lker := fun v u γ => (hkernel v u γ).1
    have hsch := hschur k hKs (fun _ => 1) (Or.inl rfl)
    set R2 := kernelOperator_time_restrict
      (reserveKernelOperator law P seedK freshK φ₀ hφ₀ M kS tA tB S θK G hI' hres0 hq hΛ hi hj hb
        hε1 (hA.trans (hw.trans hB)) hκ (rhoStar D kS.c₀ G.level) hRpos hRε hD2 hθ k hKs hsch)
      (Set.Icc_subset_Icc hA hB) hw with hR2
    have hπ : R2.π = G.mass law := by
      funext v
      show G.mass law v / (fun _ => (1 : ℝ)) v ^ 2 = _
      simp
    have hmassPos : ∀ v : CompIn G.comps, 0 < G.mass law v := fun v =>
      birth_compMass_pos hq hΛ law v.1
    set q := ⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
      (G.fam.identity v u γ).record.width / rhoStar D kS.c₀ G.level with hqdef
    have hwle : ∀ v u (γ : G.fam.Γ v u),
        (G.fam.identity v u γ).record.width ≤ rhoStar D kS.c₀ G.level := by
      intro v u γ
      have h1 := (hkernel v u γ).2.2.1
      refine h1.trans ?_
      calc kS.Cwid * rhoStar D kS.c₀ G.level * D.eps G.level ^ kS.σf
          = rhoStar D kS.c₀ G.level * (kS.Cwid * D.eps G.level ^ kS.σf) := by ring
        _ ≤ rhoStar D kS.c₀ G.level * 1 := mul_le_mul_of_nonneg_left hsmall hRpos.le
        _ = _ := mul_one _
    have hq1 : q ≤ 1 := fineBase_le_one G hRpos hwle
    have hwq : ∀ v u (γ : G.fam.Γ v u),
        (G.kernelOf P seedK freshK v u γ).width ≤ q * rhoStar D kS.c₀ G.level := by
      intro v u γ
      rw [(hkernel v u γ).2.1]
      exact (div_le_iff₀ hRpos).1 (width_div_le G (rhoStar D kS.c₀ G.level) v u γ)
    have hadm : ∀ v u (γ : G.fam.Γ v u),
        (G.kernelOf P seedK freshK v u γ).IsAdmissible (max kS.Γk 0) Lf := by
      intro v u γ
      obtain ⟨h1, h2, h3, h4⟩ := hker v u γ
      exact ⟨h1, h2, fun t => ⟨(h3 t).1.trans (le_max_left _ _),
        (h3 t).2.1.trans (le_max_left _ _), (h3 t).2.2.1,
        (h3 t).2.2.2.trans (le_max_left _ _)⟩, by omega⟩
    set FD := stageDefectData P seedK freshK φ₀ G hφ₀ hd hnn hm hs tp tf (rhoStar D kS.c₀ G.level) (D.kap G.level)
      k hD2 Lf (max kS.Γk 0) (le_max_right _ _) q hbase0 hq1 hRpos R2 hadm
      (fun v u γ => by rw [(hkernel v u γ).2.1]; exact (G.fam.identity v u γ).record.width_pos)
      hwq with hFD
    set θ' := max θK 0 with hθ'
    have hθ'0 : 0 ≤ θ' := le_max_right _ _
    have hschur' : SchurBound θ' (kernelSchurMatrix (G := fun _ j _ => hr j.1.root)
        (D.kap G.level) FD.ρ (G.mass law) FD.k FD.D FD.t₀ FD.t₁ kS.cker
        (fun i j α => (FD.Kern i j α).width)
        (fun _ j _ => ContinuousLinearMap.id ℝ (hr j.1.root)) FD.B) := by
      have h0 : SchurBound θK (kernelSchurMatrix (G := fun _ j _ => hr j.1.root)
          (D.kap G.level) FD.ρ R2.π FD.k FD.D FD.t₀ FD.t₁ kS.cker
          (fun i j α => (FD.Kern i j α).width)
          (fun _ j _ => ContinuousLinearMap.id ℝ (hr j.1.root)) FD.B) := R2.hschur
      rw [hπ] at h0
      exact ⟨fun i => (h0.1 i).trans (le_max_left _ _), fun j => (h0.2 j).trans (le_max_left _ _)⟩
    have hOK : FD.OrderOK K := by
      show k + (Dm - 2) + Lf ≤ K
      exact hK
    obtain ⟨Fk, hFr, hFm, hFb⟩ := FDData.timeBound FD hw (G.mass law) hmassPos (D.kap G.level) hκ
      kS.cker hcpos θ' hθ'0 hschur' hOK Û (fun j t x => uh t x j)
      (fun j t ht => classicalRep (Û j t) (fun x => uh t x j)
        (hreal.2.2 j t ht).1 (hreal.2.2 j t ht).2 (hreal.2.1 j t ht))
      (fun j => (hreal.1 j).aestronglyMeasurable) hen.1
    refine ⟨Fk, ?_, hFm, ?_⟩
    · intro v t ht
      exact (hFr v t ht).trans (Filter.Eventually.of_forall fun x => rfl)
    · refine hFb.trans ?_
      have hX : FD.Mconst kS.cker * θ' ≤ C := hC
      have hqL : 0 ≤ FD.q ^ FD.L := pow_nonneg hbase0 _
      have hs0 : Real.sqrt (D.kap G.level * ∫ s in Set.Icc tp tf,
          massGradNormSq (E := fun v : CompIn G.comps => hr v.1.root) (K := fun _ => K)
            (rhoStar D kS.c₀ G.level) (G.mass law) (fun v => (Û v s).val)) ≤ E := hen.2
      calc FD.q ^ FD.L * FD.Mconst kS.cker * θ' * _
          = FD.q ^ FD.L * (FD.Mconst kS.cker * θ') * _ := by rw [mul_assoc (FD.q ^ FD.L)]; rfl
        _ ≤ FD.q ^ FD.L * C * E :=
          mul_le_mul (mul_le_mul_of_nonneg_left hX hqL) hs0 (Real.sqrt_nonneg _)
            (mul_nonneg hqL hC0)
        _ = _ := by
          change q ^ Lf * C * E = _
          ring
  · have hE : 0 ≤ E := (Real.sqrt_nonneg _).trans hen.2
    have hemp : Set.Icc tp tf = ∅ := Set.Icc_eq_empty hw
    refine ⟨fun v t => 0, fun v t ht => ?_, fun v => ?_, ?_⟩
    · rw [hemp] at ht; exact absurd ht (Set.notMem_empty t)
    · rw [hemp]; simp [Measure.restrict_empty]
    · rw [hemp]
      simp only [Measure.restrict_empty, integral_zero_measure, mul_zero, Real.sqrt_zero]
      exact mul_nonneg (mul_nonneg hC0 (pow_nonneg (fineBase_nonneg G hRpos) _)) hE

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
open AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! Frame conversion reduced to the Hilbert-valued glued mean identity. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The remaining statement, with the exact lift sequence and setting premises. -/
def GluedMeanStatement (Acl ℓ : ℕ) (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ) : Prop :=
  FrameReconSeqAt F Acl ℓ →
  (∃ (qs qf : ℕ) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
    (bM : CompIn F.G.comps → CompIn F.G.comps → ℝ),
    FrameReconSettingBody F law Acl ℓ CGl Cwl Ca Sb Cgr qs qf par V bM) →
  ∀ r ∈ Finset.range (F.depth + 1), GluedMeanAt F r

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The filter defect, input (K): the kernels of the actual successor of a stage with the stage
invariant** (constants chosen before the stage).

`successorKernels`: above a base and a level chosen from `(α, s, q, ζ)`, there is `Γ` such
that for a stage `G` with the stage invariant and an actual successor `G'`, every kernel of `G'`
is admissible at `(max k_I.Γ_k (max Γ 2), L)` for `L ≤ k_I.L_ker`, `L + 1 ≤ 2 n_k`, has positive
width, and width at most `q ρ` as soon as the records of `G` and the fresh kernel of the level
`G.level - 1` do. The old kernels are admissible by the kernel clause of the invariant of `G`
(width = width of the record); the fresh kernel by `uniform_fresh_axes_norm_bound` and
`uniform_fresh_spanning_inverse_bound` (the route of `successor_kernel_admissibility`, which
states the clause for the retained family only); `kernelOf_property` carries both to `G'`.

The degenerate cases are included: `G` without identities; `L = 0`. -/

/-- Admissibility is monotone in the matrix bound and antitone in the number of moments. -/
theorem isAdmissible_mono {S : KernelSpec} {Γ Γ' : ℝ} {L L' : ℕ}
    (h : S.IsAdmissible Γ L) (hΓ : Γ ≤ Γ') (hL : L' ≤ L) : S.IsAdmissible Γ' L' :=
  ⟨h.1, h.2.1, fun t => ⟨(h.2.2.1 t).1.trans hΓ, (h.2.2.1 t).2.1.trans hΓ, (h.2.2.1 t).2.2.1,
    (h.2.2.1 t).2.2.2.trans hΓ⟩, by have := h.2.2.2; omega⟩

/-- **The kernels of the actual successor of a stage with the stage invariant.** -/
theorem successorKernels (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ Γ : ℝ, 0 < Γ ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
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
        (G'.kernelOf P seedK freshK v u γ).width ≤ qr * ρ := by
  obtain ⟨Λ₀, hΛ₀, haxes⟩ := uniform_fresh_axes_norm_bound α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ => ?_⟩
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  obtain ⟨Γ, hΓ, ma, hma, haxes⟩ := haxes Λ hΛ
  obtain ⟨mi, _hmi, hinv⟩ := uniform_fresh_spanning_inverse_bound α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
    Λ h128
  refine ⟨Γ, hΓ, max ma mi, hma.trans (le_max_left _ _), ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq hband Dm bw j₀ P Mn law seedK freshK kI cr σ₀ nk hcr
    hfresh M G G' φ₀ hφ₀ tA tB S θK hI hact hlevel hterm L hLker hLnk qr ρ hfw hrec
  have hm2 : 2 ≤ G.level := (hma.trans (le_max_left _ _)).trans hlevel
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hlt : G.level - 1 < D.term := by omega
  have hspec := hfresh (G.level - 1) (by omega) hlt
  have hκ : 0 < D.κ (G.level - 1) := CycleReference.bandChain_pos hΛD hζD hband hlt.le
  have hwidth : 0 < (freshK (G.level - 1)).width := by
    rw [hspec.1]
    unfold freshWidth freshLength
    exact mul_pos (mul_pos hcr (Real.sqrt_pos.2
      (mul_pos hκ (Construction.Stream.ocTauPP_pos hΛD))))
      (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛD) _)
  have hupper := haxes D hDα hDq hDΛ hDζ hseq hband (G.level - 1)
    (by have := (le_max_left ma mi).trans hlevel; omega) (by omega) (freshK (G.level - 1))
    hspec.2.2
  have hinverse := hinv D hDα hDq hDΛ hDζ hseq hband (G.level - 1)
    (by have := (le_max_right ma mi).trans hlevel; omega) (by omega) (freshK (G.level - 1))
    hspec.2.2
  have hmeas := fresh_axes_measurable D (G.level - 1) (by rw [hDΛ]; omega)
    (freshK (G.level - 1)).H₁ (freshK (G.level - 1)).H₂ hspec.2.2
  have hnew : (freshK (G.level - 1)).IsAdmissible (max kI.Γk (max Γ 2)) L := by
    refine ⟨hmeas.1, hmeas.2, fun t => ?_, ?_⟩
    · exact ⟨(hupper t).1.trans ((le_max_left _ _).trans (le_max_right _ _)),
        (hupper t).2.trans ((le_max_left _ _).trans (le_max_right _ _)), (hinverse t).1,
        (hinverse t).2.trans ((le_max_right _ _).trans (le_max_right _ _))⟩
    · rw [hspec.2.1]
      exact hLnk
  obtain ⟨_, _, _, _, _, _, _, _, hker, _⟩ := hI
  exact kernelOf_property P Mn seedK freshK G G' hact
    (fun κ => κ.IsAdmissible (max kI.Γk (max Γ 2)) L ∧ 0 < κ.width ∧ κ.width ≤ qr * ρ)
    (fun v u γ => ⟨isAdmissible_mono (hker v u γ).1 (le_max_left _ _) hLker,
      by rw [(hker v u γ).2.1]; exact (G.fam.identity v u γ).record.width_pos,
      by rw [(hker v u γ).2.1]; exact hrec v u γ⟩)
    ⟨hnew, hwidth, by rw [hspec.1]; exact hfw⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
open AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! Frame conversion reduced to the Hilbert-valued glued mean identity. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- Genuine incoming frame facts needed to compare pulse and native menu data. -/
structure GluedIncomingFacts : Prop where
  natural : ∃ Mnat, F.G.IsNatural Mnat
  level : F.G.level = F.m
  length : F.Mn.lenFactor = 1
  lower : 1 ≤ F.m
  upper : F.m ≤ D.term
  base : 1 ≤ D.Λ
  profile : IsFastProfile D.ζ
  band : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ

/-- Corrected interface: the incoming context facts are genuine named premises. -/
def NativeGluedMeanStatement (Acl ℓ : ℕ) (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ) : Prop :=
  GluedIncomingFacts F → GluedMeanStatement F law Acl ℓ CGl Cwl Ca Sb Cgr

omit law in
/-- Incoming naturality identifies the actual weights with the pulse cutoffs. -/
theorem glued_weight_eq (h : GluedIncomingFacts F) (k : ℤ) (hk : Odd k) (t : ℝ) :
    F.G.actualFamily.weight (oddSlotOf k) t = ocCutoff D.α D.q D.Λ F.m k t := by
  obtain ⟨Mnat, hnat⟩ := h.natural
  rw [oddSlotOf_of_odd hk]
  exact (hnat.2.1 ⟨k, hk⟩ t).trans (by rw [h.level])

omit law in
theorem glued_rho_pos (h : GluedIncomingFacts F) : 0 < fRho F := by
  exact Real.sqrt_pos.2 (mul_pos
    (CycleReference.bandChain_pos h.base h.profile h.band ((Nat.sub_le _ _).trans h.upper))
    (Construction.Stream.ocTauPP_pos h.base))

omit law in
/-- A weighted pulse lies in the clipped lift window. -/
theorem glued_window_mem (h : GluedIncomingFacts F) (k : ℤ) {t : ℝ}
    (ht : t ∈ Set.Icc F.tp (F.tp + fTobs F))
    (hw : ocCutoff D.α D.q D.Λ F.m k t ≠ 0) :
    (D.cellScaleSq F.m)⁻¹ * t ∈ Set.Icc (fSeqStart F k) (fSeqEnd F k) := by
  obtain ⟨hcs, hc⟩ := cellScale_facts F h.base h.profile h.band h.upper
  have hwin : t ∈ ocPulseWindow D.α D.q D.Λ F.m k := by
    by_contra hn
    exact hw (WeakEntryProofs.ocCutoff_zero_off_output _ _ _ _
      (Construction.Stream.ocTau_pos h.base) k t hn)
  unfold fSeqStart fSeqEnd
  rw [hc]
  have e : (D.cellScaleSq F.m)⁻¹ * t * D.cellScaleSq F.m = t := by field_simp
  refine ⟨(div_le_iff₀ hcs).2 ?_, (le_div_iff₀ hcs).2 ?_⟩
  · rw [e]; exact max_le hwin.1 ht.1
  · rw [e]; exact le_min hwin.2 ht.2

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux AVRegularity.EntryTerminal.CovGrad
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The filter defect, input (EN): the energy of the zero extension of the readout** (the cascade
form of the `energyAt`).

* `zeroExt_energy` (generic over the stages): if `(u, w)` has strong energy at most `E` on
  the masses of `G`, `w` is square integrable, and a field `X` (of order `L ≥ K + 1`, with
  classical representatives `aZ`) truncates to `w` almost everywhere, then the zero extension of
  the truncation of `X` to the components of `G'` has classical representatives
  `extAZ G G' aZ`, is measurable and has gradient energy `(ν ∫ |∇V|²_{ρ,K;π'})^{1/2} ≤ E`
  on the masses of `G'` (the two stages share the law, so the masses agree on `G`).
* `filterEnergy_at_ctx`: at a context, from the full-lift clauses at an order `k`
  (`FullLiftClauses`, the readout energy `≤ C_k A_in`) for every `K ≤ k + N + 2p`, `K + 1 ≤ N_aux`.

The cases `G' = G` (no new component), `E = 0` (zero energy) and `K = 0` are allowed. -/

section Stage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The zero extension to the components of `G'` of the truncation of a field on `G`. -/
def ZeroExt (G G' : GenStage D hr Dm bw j₀) {K L : ℕ} (hKL : K ≤ L)
    (X : ∀ v : CompIn G.comps, ℝ → TorusHk L (hr v.1.root)) (j : CompIn G'.comps) (t : ℝ) :
    TorusHk K (hr j.1.root) :=
  if h : j.1 ∈ G.comps then truncateTorusHk hKL (X ⟨j.1, h⟩ t) else 0

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The classical representative of the zero extension. -/
theorem zeroExt_rep (G G' : GenStage D hr Dm bw j₀) {K L : ℕ} (hKL : K ≤ L)
    (X : ∀ v : CompIn G.comps, ℝ → TorusHk L (hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ)
    (hrep : ∀ v, IsClassicalRep (X v t) (fun x => aZ t x v) L) (j : CompIn G'.comps) :
    IsClassicalRep (ZeroExt G G' hKL X j t) (extAZ G G' aZ j t) K := by
  unfold ZeroExt extAZ
  by_cases h : j.1 ∈ G.comps
  · simp only [h, dite_true]
    exact classicalRep_truncate hKL le_rfl _ _
      (CycleComparison.Reconstruction.isClassicalRep_of_le (hrep ⟨j.1, h⟩) hKL)
  · simp only [h, dite_false]
    exact classicalRep_zero le_rfl

/-- **The energy of the zero extension.** -/
theorem zeroExt_energy (G G' : GenStage D hr Dm bw j₀) (hsub : G.comps ⊆ G'.comps)
    (law : BirthLaw) {a b ρ ν E : ℝ} (hν : 0 < ν) (hE : 0 ≤ E) (hπ : ∀ v, 0 < G.mass law v)
    {K L : ℕ} (hKL : K + 1 ≤ L)
    (u : ∀ v : CompIn G.comps, ℝ → TorusHk K (hr v.1.root))
    (w : ∀ v : CompIn G.comps, ℝ → TorusHk (K + 1) (hr v.1.root))
    (hw : ∀ v, MemLp (w v) 2 (volume.restrict (Set.Icc a b)))
    (hen : strongEnergy ρ ν (G.mass law) a b u w ≤ ENNReal.ofReal E)
    (X : ∀ v : CompIn G.comps, ℝ → TorusHk L (hr v.1.root))
    (hXw : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncateTorusHk hKL (X v t) = w v t)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hrep : ∀ v, ∀ t ∈ Set.Icc a b, IsClassicalRep (X v t) (fun x => aZ t x v) L) :
    ∃ V : ∀ j : CompIn G'.comps, ℝ → TorusHk (K + 1) (hr j.1.root),
      (∀ j, ∀ t ∈ Set.Icc a b, IsClassicalRep (V j t) (extAZ G G' aZ j t) (K + 1)) ∧
      (∀ j, AEStronglyMeasurable (V j) (volume.restrict (Set.Icc a b))) ∧
      Integrable (fun t => massGradNormSq (E := fun j : CompIn G'.comps => hr j.1.root)
        (K := fun _ => K) ρ (G'.mass law) (fun j => (V j t).val))
        (volume.restrict (Set.Icc a b)) ∧
      Real.sqrt (ν * ∫ s in Set.Icc a b,
        massGradNormSq (E := fun j : CompIn G'.comps => hr j.1.root) (K := fun _ => K) ρ
          (G'.mass law) (fun j => (V j s).val)) ≤ E := by
  classical
  let V := ZeroExt G G' hKL X
  have hreindex : ∀ f : CompIn G'.comps → ℝ, (∀ j : CompIn G'.comps, j.1 ∉ G.comps → f j = 0) →
      ∑ j, f j = ∑ v : CompIn G.comps, f ⟨v.1, hsub v.2⟩ := by
    intro f hf
    symm
    refine Fintype.sum_of_injective (fun v : CompIn G.comps => (⟨v.1, hsub v.2⟩ :
      CompIn G'.comps)) (fun x y hxy => Subtype.ext (Subtype.mk.inj hxy)) _ _
      (fun j hj => hf j fun hjw => hj ⟨⟨j.1, hjw⟩, rfl⟩) fun v => rfl
  have hzero : ∀ (j : CompIn G'.comps) (s : ℝ), j.1 ∉ G.comps →
      (G'.mass law j)⁻¹ * gradFactorialNormSq ρ (V j s).val = 0 := by
    intro j s hj
    simp [V, ZeroExt, hj, gradFactorialNormSq]
  have hpt : ∀ s, massGradNormSq (E := fun j : CompIn G'.comps => hr j.1.root)
      (K := fun _ => K) ρ (G'.mass law) (fun j => (V j s).val) =
      ∑ v : CompIn G.comps, (G.mass law v)⁻¹ *
        gradFactorialNormSq ρ (V ⟨v.1, hsub v.2⟩ s).val := by
    intro s
    unfold massGradNormSq
    rw [hreindex _ (fun j hj => hzero j s hj)]
    rfl
  have hVae : ∀ v : CompIn G.comps, ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      V ⟨v.1, hsub v.2⟩ t = w v t := by
    intro v
    filter_upwards [hXw v] with t ht
    simp only [V, ZeroExt, v.2, dite_true]
    exact ht
  have hall : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      ∀ v : CompIn G.comps, V ⟨v.1, hsub v.2⟩ s = w v s :=
    Filter.eventually_all.2 hVae
  have hM : (fun s => massGradNormSq (E := fun j : CompIn G'.comps => hr j.1.root)
      (K := fun _ => K) ρ (G'.mass law) (fun j => (V j s).val)) =ᵐ[volume.restrict
      (Set.Icc a b)] fun s => ∑ v : CompIn G.comps, (G.mass law v)⁻¹ *
        gradFactorialNormSq ρ (w v s).val := by
    filter_upwards [hall] with s hs
    rw [hpt]
    exact Finset.sum_congr rfl fun v _ => by rw [hs v]
  have hintW : Integrable (fun s => ∑ v : CompIn G.comps, (G.mass law v)⁻¹ *
      gradFactorialNormSq ρ (w v s).val) (volume.restrict (Set.Icc a b)) :=
    integrable_finsetSum _ fun v _ =>
      (CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hw v)).const_mul _
  have hdis := covGrad_dissipation_le hν hE (G.mass law) hπ u w hw hen
  refine ⟨V, fun j t ht => zeroExt_rep G G' hKL X aZ t (fun v => hrep v t ht) j, ?_,
    hintW.congr hM.symm, ?_⟩
  · intro j
    by_cases hj : j.1 ∈ G.comps
    · refine (hw ⟨j.1, hj⟩).aestronglyMeasurable.congr ?_
      filter_upwards [hVae ⟨j.1, hj⟩] with t ht
      exact ht.symm
    · have : V j = fun _ => 0 := by
        funext t
        simp [V, ZeroExt, hj]
      rw [this]
      exact aestronglyMeasurable_const
  · rw [integral_congr_ae hM, integral_finsetSum _ (fun i _ =>
      (CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hw i)).const_mul _)]
    simp only [integral_const_mul]
    exact Real.sqrt_le_iff.2 ⟨hE, hdis⟩

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The truncated readout of a square integrable family is square integrable. -/
theorem readout_trunc_memLp {S S' : Finset Comp} (m : ℕ) (E η : ℝ) {K K' L : ℕ}
    (h₁ : K ≤ K') (h₂ : K' ≤ L) {μ : Measure ℝ} (Yw : ∀ c : CompIn S', ℝ → TorusHk L (hr c.1.root))
    (hYw : ∀ c, MemLp (Yw c) 2 μ) (v : CompIn S) :
    MemLp (fun t => truncateTorusHk h₁ (truncateTorusHk h₂
      (succReadout (hr := hr) m E η L (fun c => Yw c t) v))) 2 μ :=
  (truncateTorusHk (E := hr v.1.root) h₁).comp_memLp'
    ((truncateTorusHk (E := hr v.1.root) h₂).comp_memLp' (memLp_succReadout m E η Yw hYw v))

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The readout of `Y` truncates almost everywhere to the truncated readout of `Y_w`. -/
theorem readout_trunc_ae {S S' : Finset Comp} (m : ℕ) (E η : ℝ) {K K' L : ℕ}
    (hKL : K + 1 ≤ L) (h₁ : K ≤ K') (h₂ : K' ≤ L) {μ : Measure ℝ}
    (Y : ∀ c : CompIn S', ℝ → TorusHk L (hr c.1.root))
    (Yw : ∀ c : CompIn S', ℝ → TorusHk (L + 1) (hr c.1.root))
    (hT : ∀ c, ∀ᵐ t ∂μ, truncateTorusHk (Nat.le_succ L) (Yw c t) = Y c t) (v : CompIn S) :
    ∀ᵐ t ∂μ, truncateTorusHk hKL (succReadout (hr := hr) m E η L (fun c => Y c t) v) =
      truncateTorusHk (Nat.succ_le_succ h₁) (truncateTorusHk (Nat.succ_le_succ h₂)
        (succReadout (hr := hr) m E η (L + 1) (fun c => Yw c t) v)) := by
  filter_upwards [Filter.eventually_all.2 hT] with t ht
  have hX : succReadout (hr := hr) m E η L (fun c => Y c t) v =
      truncateTorusHk (Nat.le_succ L) (succReadout (hr := hr) m E η (L + 1)
        (fun c => Yw c t) v) := by
    rw [AVRegularity.Construction.Preservation.FullLift.truncate_succReadout]
    congr 1
    funext c
    exact (ht c).symm
  rw [hX, CycleComparison.Coarse.truncateTorusHk_truncateTorusHk,
    CycleComparison.Coarse.truncateTorusHk_truncateTorusHk]

end Stage

section Ctx

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]

/-- The square integrability and the truncation identity of the retained solution. -/
theorem hsol_facts
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr) :
    (∀ v, MemLp (c.Yw v) 2 (volume.restrict (Set.Icc c.tp c.tf))) ∧
      ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp c.tf)),
        truncateTorusHk (Nat.le_succ Naux) (c.Yw v t) = c.Y v t :=
  ⟨c.hsol.2.1, c.hsol.2.2.1⟩

/-- **(EN) at a context**, from the full-lift clauses at the order `k`. -/
theorem filterEnergy_at_ctx
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr)
    {k : ℕ} (hk : k + N + 2 * p ≤ Naux) {Ck : ℝ}
    (hfl : FullLiftClauses c.law c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX
      sZ k hk (succEta0 α q s) kI.c₀ kI.cr c.tp c.tf Ck c.Ain c.Y c.Yw)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
    (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
      (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
      (fun x => aZ t x v) Naux)
    (hν : 0 < c.D.κ (c.m - 1)) (hπ : ∀ v, 0 < c.G.mass c.law v) (hE : 0 ≤ Ck * c.Ain)
    {K : ℕ} (hKk : K ≤ k + N + 2 * p) (hKN : K + 1 ≤ Naux) :
    ∃ V : ∀ j : CompIn c.G'.comps, ℝ → TorusHk (K + 1) (hr j.1.root),
      (∀ j, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep (V j t) (extAZ c.G c.G' aZ j t) (K + 1)) ∧
      (∀ j, AEStronglyMeasurable (V j) (volume.restrict (Set.Icc c.tp c.tf))) ∧
      Integrable (fun t => massGradNormSq (E := fun j : CompIn c.G'.comps => hr j.1.root)
        (K := fun _ => K) (rhoEnh c.D kI.cr c.m) (c.G'.mass c.law) (fun j => (V j t).val))
        (volume.restrict (Set.Icc c.tp c.tf)) ∧
      Real.sqrt (c.D.κ (c.m - 1) * ∫ s in Set.Icc c.tp c.tf,
        massGradNormSq (E := fun j : CompIn c.G'.comps => hr j.1.root) (K := fun _ => K)
          (rhoEnh c.D kI.cr c.m) (c.G'.mass c.law) (fun j => (V j s).val)) ≤ Ck * c.Ain := by
  classical
  obtain ⟨CcT, PZ, aRep, û, ŵ, hW⟩ := hfl.1
  have hen0 := (hfl.2 CcT PZ aRep û ŵ hW (fun _ => 1) (Or.inl rfl)).2
  have hπ1 : (fun v => c.G.mass c.law v / (fun _ : CompIn c.G.comps => (1 : ℝ)) v ^ 2) =
      c.G.mass c.law := funext fun v => by simp
  have hen : strongEnergy (rhoEnh c.D kI.cr c.m) (c.D.κ (c.m - 1)) (c.G.mass c.law) c.tp c.tf
      (fun v t => truncateTorusHk hk (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux
        (fun v' => c.Y v' t) v))
      (fun v t => truncateTorusHk (Nat.succ_le_succ hk) (succReadout c.m (c.D.eps (c.m - 1))
        (succEta0 α q s) (Naux + 1) (fun v' => c.Yw v' t) v)) ≤
      ENNReal.ofReal (Ck * c.Ain) := by
    have h1 := hen0
    unfold readoutEnergy at h1
    rw [hπ1] at h1
    exact h1
  have hen' := (strongEnergy_truncate_le hKk (rhoEnh c.D kI.cr c.m) (c.D.κ (c.m - 1))
    (c.G.mass c.law) c.tp c.tf
    (fun v t => truncateTorusHk hk (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux
      (fun v' => c.Y v' t) v))
    (fun v t => truncateTorusHk (Nat.succ_le_succ hk) (succReadout c.m (c.D.eps (c.m - 1))
      (succEta0 α q s) (Naux + 1) (fun v' => c.Yw v' t) v))).trans hen
  have hsub : c.G.comps ⊆ c.G'.comps := fun u hu => by
    rw [c.hactual.2.2.1]
    exact Finset.mem_union_left _ hu
  obtain ⟨hYwM, hYwT⟩ := hsol_facts c
  have hw := readout_trunc_memLp (S := c.G.comps) c.m (c.D.eps (c.m - 1)) (succEta0 α q s)
    (Nat.succ_le_succ hKk) (Nat.succ_le_succ hk) c.Yw hYwM
  have hXw := readout_trunc_ae (S := c.G.comps) c.m (c.D.eps (c.m - 1)) (succEta0 α q s)
    hKN hKk hk c.Y c.Yw hYwT
  exact zeroExt_energy c.G c.G' hsub c.law hν hE hπ hKN
    (fun v t => truncateTorusHk hKk (truncateTorusHk hk (succReadout c.m (c.D.eps (c.m - 1))
      (succEta0 α q s) Naux (fun v' => c.Y v' t) v)))
    (fun v t => truncateTorusHk (Nat.succ_le_succ hKk) (truncateTorusHk (Nat.succ_le_succ hk)
      (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) (Naux + 1) (fun v' => c.Yw v' t) v)))
    hw hen'
    (fun v t => succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
    hXw aZ hZ

end Ctx

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux AVRegularity.Analysis.Convolution
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The filter-defect form at a context from its inputs.**

* `FilterBase`: the base `ε_o = max(E^{σ₀}, max_γ r_γ/ρ)` of `succFilterPrice`
  (`succFilterPrice … = ε_o^{L_c}` by definition); `width_le_base`, `freshWidth_le_base`:
  the record widths of `G` and the width of the fresh kernel of the level `m - 1` are at most
  `ε_o ρ`; `FilterBase_le_one` when the records of `G` are not wider than `ρ`.
* `filterCoeffSmooth_at_ctx` (input (SM)): the coefficients of the full successor are smooth
  and periodic at every order (from the extended certificates).
* `filterReadoutFacts`: the three facts of the readout from the rows of `G'` to the rows of
  `G` (parents in `G`, child weight at most `1`, at most `|W_{J+1}| + 1` children).
* `filterForm_at_ctx`: `FilterDefectForm … (√C_f (ε_o^{L_c} M_c (1/8) E_n))` at a context
  from (R), (S), (SM), the kernels of `G'`, (EN) and the readout facts.

The degenerate cases are included: no identity in `G` (`ε_o = E^{σ₀}`); `L_c = 0` (`ε_o^0 = 1`). -/

section Base

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The base of the price of the coarse filter tails. -/
def FilterBase (D : OCData) (G : GenStage D hr Dm bw j₀) (m : ℕ) (cr σ₀ : ℝ) : ℝ :=
  max (D.eps (m - 1) ^ σ₀) (⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
    (G.fam.identity v u γ).record.width / rhoEnh D cr m)

theorem FilterBase_pow (D : OCData) (G : GenStage D hr Dm bw j₀) (m : ℕ) (cr σ₀ : ℝ)
    (Lc : ℕ) : succFilterPrice D G m cr σ₀ Lc = FilterBase D G m cr σ₀ ^ Lc := rfl

theorem FilterBase_nonneg (D : OCData) (G : GenStage D hr Dm bw j₀) (m : ℕ) (cr σ₀ : ℝ)
    (hE : 0 ≤ D.eps (m - 1)) : 0 ≤ FilterBase D G m cr σ₀ :=
  le_max_of_le_left (Real.rpow_nonneg hE _)

theorem width_le_base (D : OCData) (G : GenStage D hr Dm bw j₀) (m : ℕ) (cr σ₀ : ℝ)
    (hρ : 0 < rhoEnh D cr m) (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    (G.fam.identity v u γ).record.width ≤ FilterBase D G m cr σ₀ * rhoEnh D cr m :=
  (div_le_iff₀ hρ).1 ((width_div_le G (rhoEnh D cr m) v u γ).trans (le_max_right _ _))

theorem freshWidth_le_base (D : OCData) (G : GenStage D hr Dm bw j₀) {m : ℕ} (hm : 1 ≤ m)
    (cr σ₀ : ℝ) (hρ : 0 ≤ rhoEnh D cr m) :
    freshWidth D cr σ₀ (m - 1) ≤ FilterBase D G m cr σ₀ * rhoEnh D cr m := by
  rw [freshWidth_eq D cr σ₀ hm, mul_comm]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) hρ

theorem FilterBase_le_one (D : OCData) (G : GenStage D hr Dm bw j₀) (m : ℕ) (cr σ₀ : ℝ)
    (hρ : 0 < rhoEnh D cr m) (hE0 : 0 ≤ D.eps (m - 1)) (hE1 : D.eps (m - 1) ≤ 1) (hσ : 0 ≤ σ₀)
    (hw : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).record.width ≤ rhoEnh D cr m) :
    FilterBase D G m cr σ₀ ≤ 1 :=
  max_le (Real.rpow_le_one hE0 hE1 hσ) (fineBase_le_one G hρ hw)

end Base

/-- A filter-defect form passes to a larger bound. -/
theorem filterDefectForm_mono {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {P : ProvParams} {seedK freshK : ℕ → KernelSpec}
    {φ₀ : Vec 2 → ℝ} {G G' : GenStage D hr Dm bw j₀} {m p kc : ℕ} {E η₀ : ℝ}
    {aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root} {π : CompIn G.comps → ℝ}
    {tp tf ρ Y Y' : ℝ} (h : FilterDefectForm P seedK freshK φ₀ G G' m p kc E η₀ aZ π tp tf ρ Y)
    (hY : Y ≤ Y') : FilterDefectForm P seedK freshK φ₀ G G' m p kc E η₀ aZ π tp tf ρ Y' :=
  ⟨h.1, hasFluxBound_mono_Y h.2 hY⟩

section Ctx

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]

/-- **(SM) at a context**: the coefficients of the full successor are smooth and periodic. -/
theorem filterCoeffSmooth_at_ctx [∀ r, Nontrivial (hr r)]
    (h128 : 128 ≤ Λ) (hbw : 0 < bw)
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr)
    (hprod : kI.Hprod = kI.G0 + H + 1) (mc : ℕ)
    (hcert : Frontier.ExtendedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p
      nk npad sX sZ σ₀ kI CI Cw j₀ mc)
    (hm : max mc (j₀ + 3) ≤ c.m) (n : ℕ) :
    ∀ (v u : CompIn c.G'.comps) (γ : c.G'.fam.Γ v u) (d : ℕ) (t : ℝ),
      ContDiff ℝ (n : ℕ) (c.G'.physCoeff v u γ d t) ∧ IsZ2Periodic (c.G'.physCoeff v u γ d t) := by
  have hmc : mc ≤ c.m := le_trans (le_max_left _ _) hm
  obtain ⟨hnat, hshift, hslot, hctx, -, -⟩ := hcert c.D c.hα c.hq c.hΛ c.hζ c.hseq c.M c.hband
    c.hterm c.Mnat c.hMnat c.law c.hlaw c.seedK c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed
    c.m hmc c.hmn c.hnM c.tA c.htA c.G c.G' c.hcascade c.hlevel c.hinv c.hactual
  have hGrlevel : c.G'.level = c.m - 1 := by rw [c.hactual.2.1, c.hlevel]
  have hj : j₀ + 3 ≤ c.m := le_trans (le_max_right _ _) hm
  intro v u γ d t
  have hres : 0 ≤ compReserve kI v.1 :=
    AVRegularity.Providers.CascadeInvariants.compReserve_nonneg_of_succ kI (H := H) hprod
      (AVRegularity.Providers.CascadeInvariants.grade_le_of_succ
        (AVRegularity.Providers.CascadeInvariants.grade_le_of_cascade c.hseed.2.1 c.hcascade) c.hactual v)
  refine ⟨native_physCoeff_all_order_smooth hctx hslot hnat (by omega) (by omega) hbw
    (Construction.Stream.ocEpsilon_pos (by rw [c.hΛ]; omega)) t t v u γ hres
    ((Buffer.compReserve_le_one kI v.1).trans (by norm_num)) n d t ⟨le_rfl, le_rfl⟩,
    Buffer.native_physCoeff_periodic hnat hshift v u γ d t⟩

/-- **The facts of the readout at a context.** -/
theorem filterReadoutFacts (hη : 0 < succEta0 α q s) (hq1 : 1 < q) (h128 : 128 ≤ Λ)
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr) (hm1 : 1 ≤ c.m) :
    (∀ x : CompIn c.G'.comps, compParent c.m x.1 ∈ c.G.comps) ∧
    (∀ (v : CompIn c.G.comps) (x : CompIn c.G'.comps), compParent c.m x.1 = v.1 →
      (Real.sqrt (c.G.mass c.law v))⁻¹ / (Real.sqrt (c.G'.mass c.law x))⁻¹ *
        c.D.eps (c.m - 1) ^ (succEta0 α q s * (compWord c.m x.1).length) ≤ 1) ∧
    (∀ v : CompIn c.G.comps,
      (((Finset.univ : Finset (CompIn c.G'.comps)).filter
        fun x => compParent c.m x.1 = v.1).card : ℝ) ≤
        ((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card : ℝ) + 1) := by
  have hold : ∀ v ∈ c.G.comps, ∀ e ∈ v.births, c.m ≤ e.scale := fun v hv => by
    have h := (InitialValue.cascade_invariant c.hseed.2.1 c.hcascade v hv).1
    rwa [c.hlevel] at h
  have hsubExt : c.G'.comps ⊆ succExtComps c.m (succAlphabetOf r₀ D₀ H J N p npad) J
      c.G.comps := by
    have h := c.hactual.2.2.1
    rw [c.hlevel] at h
    rw [h]
    exact subset_refl _
  have hlaw := successor_readout_law_facts hη c.hlaw
  have hqD : 1 < c.D.q := c.q_gt hq1
  have hΛD : 128 ≤ c.D.Λ := c.lambda_ge h128
  have hE := Scales.epsilon_basic (m := c.m - 1) hqD hΛD
  refine ⟨fun x => readout_parent_mem hm1 hold (hsubExt x.2), ?_, fun v => ?_⟩
  · intro v x hvx
    have hmass : c.G'.mass c.law x ≤ c.G.mass c.law v := by
      unfold GenStage.mass
      rw [← hvx]
      exact readout_parent_mass_le hqD hΛD c.law hlaw.1 hlaw.2.1 c.m x.1
    have hπv : 0 < c.G.mass c.law v := Buffer.birth_compMass_pos hqD hΛD c.law v.1
    have h1 : (Real.sqrt (c.G.mass c.law v))⁻¹ / (Real.sqrt (c.G'.mass c.law x))⁻¹ ≤ 1 := by
      rw [inv_div_inv]
      exact (div_le_one (Real.sqrt_pos.mpr hπv)).mpr (Real.sqrt_le_sqrt hmass)
    have h2 : c.D.eps (c.m - 1) ^ (succEta0 α q s * (compWord c.m x.1).length) ≤ 1 :=
      Real.rpow_le_one hE.1.le hE.2.1 (mul_nonneg hη.le (Nat.cast_nonneg _))
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (Real.rpow_nonneg hE.1.le _) zero_le_one
      _ = 1 := one_mul 1
  · exact_mod_cast readout_indexed_fiber_card_le hm1 hold hsubExt v.1

end Ctx

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
