-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Residual.Presentation.Cascade.Budget
import AVRegularity.EntryTerminal.Ingredients.Recon.Partition.Scale
import AVRegularity.Definitions.Finite.FiniteLiftBridge
public import AVRegularity.Construction.Residual.Presentation.Cascade.ReconCoarseParts
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerWrappers
public import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.MacroSwapLettersReg
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The partition step at a cascade frame: the partition terms from the partition bound**
(cascade side of the bill residual).

`frameReconPartitionAt`: `FrameReconPartitionAt F law A_cl k_c 0 hW ρ_⋆ C_px 𝔅` for the bill
`𝔅 = succReconBill …` and `ρ_⋆ = rhoStar D c₀ m`, from `partition_window_input` on the window
`mkFrameReconWindow` of the frame, with the lift settings at the window's orders lowered to the
partition orders (`liftSettingMono`) and the gluing factor of the partition bound bounded by the
third term of `𝔅` (`gateLevel`). It is the terminal `reconPartitionAt_of_gate` at a frame.

**Constants before the frame.** `Λ₀` first; then, from the schedule numbers `(A_cl, N, D_m, depth,
C_Gl, C_w, C_a, S_b, T₀)`, the rate `c_g > 0`, the constant `C_px` and the level `m₀`; the bill's
gluing rate `c` is any `c ≤ c_g`. `C_px = C_gate (1 + S_b)^{depth} K_c`, with `(C_gate, c_gate)`
the constants of `partition_window_input` (at the uniform cutoff constant `reconCpart`) and
`c_g = c_gate/2`.

**Inputs at the frame** (named hypotheses, in the forms of the bodies of the window): the family
body at `reconCpart`, the lift settings at the window's orders (`frameReconSettingBody`), the
lift sequences, and the coarse body at realizations `F₁, F₂, F₃` of the flux (the window
`ReconWindow` contains the coarse defect; `FrameReconPartitionAt` itself does not mention them,
so the consumer derives it after the realizations).

With no observed pulse the gluing factor is `0`. -/

/-- **The partition step.** -/
theorem frameReconPartitionAt {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ (Acl N Dm depth : ℕ) (CGl Cwl : ℕ → ℝ)
      (Ca Sb T₀ : ℝ), 1 ≤ Acl → 0 ≤ Sb →
      2 - (1 + α) + 8 * ocDelta α q ≤ (q * ocGamma α q + 3 * ocDelta α q) * Acl →
      ∃ (cg Cpx : ℝ) (m₀ : ℕ), 0 < cg ∧ 0 ≤ Cpx ∧ 2 ≤ m₀ ∧
      ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
        [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
        [∀ r, CompleteSpace (hr r)] {D : OCData} {b : ℝ} {j₀ : ℕ} (F : Frame D hr Dm b j₀)
        (law : BirthLaw),
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ D.term D.κ → F.N = N → F.depth = depth → m₀ ≤ F.m → F.m < D.term →
      0 < fTobs F → fTobs F ≤ T₀ →
      ∀ (c₀ cr c σ₀ : ℝ) (Lc : ℕ) (θ₁ θ₂ : ℝ), 0 < c₀ → c₀ ≤ 1 → 0 < cr → cr ≤ 1 → c ≤ cg →
      ∀ (kc : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p), 1 ≤ kc →
      ∀ (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ →
          TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
        (T : F.G.actualFamily.Atlas) (qs qf : ℕ) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
        (bM : CompIn F.G.comps → CompIn F.G.comps → ℝ) (Cgr aC B₀C lamC : ℝ) (pc Jc : ℕ)
        (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
        (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
          (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
            (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
        (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ)
        (f0 : ∀ v : CompIn F.G.comps,
          TorusHk (kc + (Jc + F.depth + 3) * ((F.N + Dm) + 8 * pc + 4)) (hr v.1.root)),
      FrameReconFamilyBody F 0 T reconCpart →
      FrameReconSettingBody F law Acl 0 CGl Cwl Ca Sb Cgr qs qf par V bM →
      FrameReconSeqAt F Acl 0 →
      FrameReconCoarseBody F law kc hW F1 F2 F3 aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0 →
      FrameReconPartitionAt F law Acl kc 0 hW (rhoStar D c₀ F.m) Cpx
        (succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂) := by
  obtain ⟨Λ₁, hΛ₁, hscl⟩ := frameReconScaleBody hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Λ₂, hΛ₂, hlev⟩ := levels hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Λ₃, hΛ₃, hgl⟩ := gateLevel hα0 hα1 hs0 hs1 hq hζ
  refine ⟨max (max Λ₁ Λ₂) Λ₃, le_trans hΛ₁ ((le_max_left _ _).trans (le_max_left _ _)),
    fun Λ hΛ Acl N Dm depth CGl Cwl Ca Sb T₀ hAcl hSb hsched => ?_⟩
  have hΛ1 : Λ₁ ≤ Λ := ((le_max_left _ _).trans (le_max_left _ _)).trans hΛ
  have hΛ2 : Λ₂ ≤ Λ := ((le_max_right _ _).trans (le_max_left _ _)).trans hΛ
  have hΛ3 : Λ₃ ≤ Λ := (le_max_right _ _).trans hΛ
  obtain ⟨C₁, m₁, hC₁, hm₁, hscale⟩ := hscl Λ hΛ1 Acl T₀ hsched
  obtain ⟨C₂, m₂, hC₂, hm₂, hlevel⟩ := hlev Λ hΛ2 Acl T₀ hsched
  obtain ⟨Cg, cgate, hCg, hcgate, hPT⟩ := partition_window_input.{0, 0, 0, 0} Acl N Dm depth
    (wKmax Dm depth 0) (wKlift Dm depth N Acl 0) (wLlift Dm depth N 0) CGl Cwl Ca reconCpart hAcl
  obtain ⟨Kc, hKc, hKcb⟩ := hgl Λ hΛ3 T₀ cgate hcgate
  refine ⟨cgate / 2, Cg * (1 + Sb) ^ depth * Kc, max m₁ m₂, half_pos hcgate,
    mul_nonneg (mul_nonneg hCg (pow_nonneg (by linarith) _)) hKc, le_trans hm₁ (le_max_left _ _),
    ?_⟩
  intro hr _ _ _ _ _ _ D b j₀ F law hDα hDq hDΛ hDζ hΦ hband hN hd hm hmt hTobs hT c₀ cr c σ₀ Lc
    θ₁ θ₂ hc₀ hc₀1 hcr hcr1 hcg kc hW hkc F1 F2 F3 T qs qf par V bM Cgr aC B₀C lamC pc Jc AD CE
    Aedge Cstar Θc f0 hfam hset hseq hco
  have hmm₁ : m₁ ≤ F.m := le_trans (le_max_left _ _) hm
  have hmm₂ : m₂ ≤ F.m := le_trans (le_max_right _ _) hm
  have hsc := hscale F hDα hDq hDΛ hDζ hΦ hband hmm₁ hmt hTobs hT c₀ cr c σ₀ Lc θ₁ θ₂ hc₀ hc₀1
    hcr hcr1
  subst hDα hDq hDΛ hDζ hN hd
  obtain ⟨hκm, -, hlo, -, -, -, -⟩ := hlevel D.term D.κ hband F.m hmm₂ hmt
  obtain ⟨hα₀, hα₁, hs₀, hs₁, hq', hζ', hΛ', hΦ', hm', hν, hB, hrs, hrse, hrsρ, hRE, -⟩ := hsc
  have hq1 : 1 < D.q := hq.1
  have h128 : 128 ≤ D.Λ := hΛ'
  have hΛ1' : 1 ≤ D.Λ := by omega
  have hτ : 0 < ocTau D.α D.q D.Λ F.m := Construction.Stream.ocTau_pos hΛ1'
  have he : 0 < ocEpsilon D.q D.Λ F.m := Applications.eps_pos hq1 h128
  have hE0 : 0 < ocEpsilon D.q D.Λ (F.m - 1) := Applications.eps_pos hq1 h128
  have hkap : D.kap F.m = D.κ F.m := by simp [OCData.kap, min_eq_left hmt.le]
  have hcell : Real.sqrt (D.cellScaleSq F.m) = ocEll D.q D.Λ F.m (D.κ F.m) := by
    simp only [OCData.cellScaleSq, hkap, ocEll, OCData.eps]
    rw [Real.sqrt_div' _ hκm.le, Real.sqrt_sq he.le]
  have w := mkFrameReconWindow F law (s := s) Acl kc 0 hW F1 F2 F3 T reconCpart qs qf par V bM
    CGl Cwl Ca Sb Cgr aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0 (rhoStar D c₀ F.m) hfam hset
    hseq hco hα₀ hα₁ hs₀ hs₁ hq' hζ' hΛ' hΦ' hm' hν hB hrs hrse hrsρ hRE hTobs hkc
    (frameReconFc F F1 F2 F3) (fun _ => Filter.EventuallyEq.rfl)
  have hsetP := fun k hk => liftSettingMono (hset.1 k hk)
    (Acl + 2 + wKmax Dm F.depth 0 + Dm * (F.depth + 1) * F.N)
    (2 + wKmax Dm F.depth 0 + Dm * (F.depth + 1) * F.N)
    (0 + wKmax Dm F.depth 0 + Dm * (F.depth + 1) * F.N)
    (by simp only [wKlift]; omega) (by simp only [wLlift]; omega) (by simp only [wLlift]; omega)
  have hbill := gluing_le_bill F cr c σ₀ Lc Acl θ₁ θ₂ hcr.le hE0.le he.le
  have hglue := hKcb D.term D.κ hband F.m hm' hmt.le F.tp (fTobs F) hTobs hT c hcg
  refine ⟨Cg * (1 + Sb) ^ F.depth * ((ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F)).card : ℝ) *
      ocEll D.q D.Λ F.m (D.κ F.m) * Real.sqrt (1 / ocTau D.α D.q D.Λ F.m) *
      Real.exp (-(cgate * ocTau D.α D.q D.Λ F.m / ocEll D.q D.Λ F.m (D.κ F.m) ^ 2)),
    ?_, ?_, fun n => ?_⟩
  · have hℓ : 0 < ocEll D.q D.Λ F.m (D.κ F.m) := div_pos he (Real.sqrt_pos.2 hκm)
    have h1 : 0 ≤ Cg * (1 + Sb) ^ F.depth := mul_nonneg hCg (pow_nonneg (by linarith) _)
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 (Nat.cast_nonneg _)) hℓ.le)
      (Real.sqrt_nonneg _)) (Real.exp_pos _).le
  · have hℓ : 0 < ocEll D.q D.Λ F.m (D.κ F.m) := div_pos he (Real.sqrt_pos.2 hκm)
    have h1 : 0 ≤ Cg * (1 + Sb) ^ F.depth := mul_nonneg hCg (pow_nonneg (by linarith) _)
    have h2 : 0 ≤ Cg * (1 + Sb) ^ F.depth * Kc := mul_nonneg h1 hKc
    rw [hcell] at hbill
    calc Cg * (1 + Sb) ^ F.depth *
          ((ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F)).card : ℝ) *
          ocEll D.q D.Λ F.m (D.κ F.m) * Real.sqrt (1 / ocTau D.α D.q D.Λ F.m) *
          Real.exp (-(cgate * ocTau D.α D.q D.Λ F.m / ocEll D.q D.Λ F.m (D.κ F.m) ^ 2))
        = Cg * (1 + Sb) ^ F.depth *
          (((ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F)).card : ℝ) *
            Real.exp (-(cgate * ocTau D.α D.q D.Λ F.m / ocEll D.q D.Λ F.m (D.κ F.m) ^ 2)) *
            (ocEll D.q D.Λ F.m (D.κ F.m) * Real.sqrt (1 / ocTau D.α D.q D.Λ F.m))) := by ring
      _ ≤ Cg * (1 + Sb) ^ F.depth * (Kc * (ocEll D.q D.Λ F.m (D.κ F.m) *
            Real.sqrt ((1 + fTobs F / ocTau D.α D.q D.Λ F.m) / ocTau D.α D.q D.Λ F.m) *
            Real.exp (-(c * ocTau D.α D.q D.Λ F.m / ocEll D.q D.Λ F.m (D.κ F.m) ^ 2)))) :=
          mul_le_mul_of_nonneg_left hglue h1
      _ = Cg * (1 + Sb) ^ F.depth * Kc * (ocEll D.q D.Λ F.m (D.κ F.m) *
            Real.sqrt ((1 + fTobs F / ocTau D.α D.q D.Λ F.m) / ocTau D.α D.q D.Λ F.m) *
            Real.exp (-(c * ocTau D.α D.q D.Λ F.m / ocEll D.q D.Λ F.m (D.κ F.m) ^ 2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbill h2
  · exact hPT w par V _ _ hsetP (by simp only [wKlift]; omega) (by simp only [wLlift]; omega)
      hSb (hlo) (rhoStar D c₀ F.m) hrs hrse n

/-- `FrameReconPartitionAt` is monotone in the bill (for `C_px ≥ 0`): the partition piece for
`𝔅` gives it for `C₁·𝔅` (the bill of the scale body `frameReconScaleBody`). -/
theorem partitionAt_mono_bill {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (F : Frame D hr Dm b j₀) (law : BirthLaw)
    (Acl kc ℓ : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p) (ρs Cpx bill bill' : ℝ)
    (hCpx : 0 ≤ Cpx) (hb : bill ≤ bill') (h : FrameReconPartitionAt F law Acl kc ℓ hW ρs Cpx bill) :
    FrameReconPartitionAt F law Acl kc ℓ hW ρs Cpx bill' := by
  obtain ⟨Xp, hX0, hX, hn⟩ := h
  exact ⟨Xp, hX0, hX.trans (mul_le_mul_of_nonneg_left hb hCpx), hn⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The scales and the partition of the window (the scale step, the partition step) at every context** (cascade side
of the bill residual, the discharge of `frameReconScaleBody` and
`frameReconPartitionAt`).

`succPrefix_reconScalePartition`: in the common prefix form, at every context of level `≥ m_*`
with a nondegenerate window `t_p < t_f`, at the frame of every lifted field with classical
representatives,

* `FrameReconScaleBody F s A_cl ρ_⋆ 𝔱 (C₁·𝔅)` for every gluing rate of the bill (the hypothesis
  `hR6d` of `frameReconAt_of_steps`), with `1 ≤ C₁`;
* for all setting constants `(C_G, C_w, C_a, C_g)`, the partition step
  `FrameReconPartitionStepAt F law A_cl k_c hW ρ_⋆ C_px C_G C_w C_a C_I C_g (C₁·𝔅)` at the rate
  `c_g` of the bill (the hypothesis `hR6c`), at every coarse order `k_c ≥ 1`.

**The order of the constants.** The `(c_g, C_px, m₀)` depend on the constants of the lift
setting, which another statement (the lift settings, `succPrefix_reconSetting`) chooses. Two prefix forms
cannot be joined when the second needs the first one's constants, so the constants of the
partition are here FUNCTIONS of `(C_G, C_w, C_a)` (chosen with `choose`), and the assembly
evaluates them at the constants of the lift settings. The price bound is `S_b = C_I`, a letter of the prefix.

The seed's radius factor satisfies `k_S.c₀ ≤ 1` by the choice `c₀max = 1`
(`SuccPrefix.of_scale_radius`); `1 ≤ A_cl` follows from the schedule
(`(qγ + 3δ)A_cl ≥ 2 − (1+α) + 8δ > 0`).

The case `t_p = t_f` is excluded (the pieces divide by the length; the degenerate window is
treated separately); a stage without identities is allowed. -/

/-- **The scale step at every context of level `≥ m_*` with `t_p < t_f`**, with the factor `C₁` of the
bill. -/
def ReconScaleCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl Lc : ℕ) (C₁ : ℝ) (mStar : ℕ) :
    Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m → c.tp < c.tf →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux) (cg : ℝ),
      FrameReconScaleBody (c.frame CcT PZ aRep û hlift aZ aY hZ hY) s Acl
        (rhoStar c.D kI.c₀ c.m)
        (fTT (c.frame CcT PZ aRep û hlift aZ aY hZ hY) kI.cr σ₀ Lc
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)))
        (C₁ * succReconBill c.D c.G c.m kI.cr cg σ₀ (succEta0 α q s) p N Lc Acl J H c.tp c.tf
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)))

/-- **The partition step at every context of level `≥ m_*` with `t_p < t_f`**, for the setting constants
`(C_G, C_w, C_a, C_g)` and the price bound `C_I`, at the rate `c_g` of the bill. -/
def ReconPartitionCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl Lc : ℕ) (CGl Cwl : ℕ → ℝ)
    (Ca Cgr cg Cpx C₁ : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m → c.tp < c.tf →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux)
      (kc : ℕ) (hW : kc + 1 + (N + succSchedD D₀ N p (H + 1)) ≤ Naux - 2 * p), 1 ≤ kc →
      FrameReconPartitionStepAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law Acl kc hW
        (rhoStar c.D kI.c₀ c.m) Cpx CGl Cwl Ca CI Cgr
        (C₁ * succReconBill c.D c.G c.m kI.cr cg σ₀ (succEta0 α q s) p N Lc Acl J H c.tp c.tf
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)))

/-- The cleanup order of a successor schedule is positive. -/
theorem succSchedule_one_le_Acl {α q s Q σ₀ a σ σf lamC : ℝ}
    {D₀ H J N p nk Lc Lf Lpr Acl Naux Nout : ℕ} (hα₁ : α < 1 / 3) (hδ : 0 < ocDelta α q)
    (h : IsSuccessorSchedule α q s Q σ₀ a σ σf lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout) :
    1 ≤ Acl := by
  have hA : 2 - (1 + α) + 8 * ocDelta α q ≤ (q * ocGamma α q + 3 * ocDelta α q) * Acl :=
    h.2.2.2.2.1
  by_contra hne
  have h0 : Acl = 0 := by omega
  rw [h0, Nat.cast_zero, mul_zero] at hA
  linarith

/-- **The scale step and the partition step in the common prefix form**; the constants are `(C₁, m_*)` with `1 ≤ C₁`
and the functions `(C_G, C_w, C_a) ↦ (c_g, C_px, m_*')` with `0 < c_g`, `0 ≤ C_px`. -/
theorem succPrefix_reconScalePartition (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℝ × ℕ × ((ℕ → ℝ) → (ℕ → ℝ) → ℝ → ℝ × ℝ × ℕ))
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        1 ≤ x.1 ∧
        ReconScaleCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ Acl Lc x.1 x.2.1 ∧
        ∀ (CGl Cwl : ℕ → ℝ) (Ca Cgr : ℝ),
          0 < (x.2.2 CGl Cwl Ca).1 ∧ 0 ≤ (x.2.2 CGl Cwl Ca).2.1 ∧
          ReconPartitionCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
            σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Acl Lc CGl Cwl Ca Cgr (x.2.2 CGl Cwl Ca).1
            (x.2.2 CGl Cwl Ca).2.1 x.1 (max x.2.1 (x.2.2 CGl Cwl Ca).2.2)) := by
  obtain ⟨Λ₁, hΛ₁, hscl⟩ := frameReconScaleBody (s := s) hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λ₂, hΛ₂, hpart⟩ := frameReconPartitionAt (s := s) hα₀ hα₁ hs₀ hs₁ hq hζ
  refine SuccPrefix.of_scale_radius ⟨max Λ₁ Λ₂, le_trans hΛ₁ (le_max_left _ _), fun Λ hΛ =>
    And.intro (hscl Λ (le_trans (le_max_left _ _) hΛ))
      (hpart Λ (le_trans (le_max_right _ _) hΛ))⟩ ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ hfacts hc₀le htail CQ Cpr
  obtain ⟨hsclΛ, hpartΛ⟩ := htail
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  have hδ : 0 < ocDelta α q := ocDelta_pos_of_admissible hα₀ hq
  have hAcl : 2 - (1 + α) + 8 * ocDelta α q ≤ (q * ocGamma α q + 3 * ocDelta α q) * Acl :=
    hfacts.sched.2.2.2.2.1
  have hA1 : 1 ≤ Acl := succSchedule_one_le_Acl hα₁ hδ hfacts.sched
  have hCI : 0 ≤ CI := by
    obtain ⟨CIthr, Cwthr, hled⟩ := hfacts.ledger
    exact le_trans (le_trans zero_le_one hfacts.hCe) hled.1
  have hc₀ : 0 < kI.c₀ := by rw [hkI.1]; exact hfacts.hc₀
  have hc₀1 : kI.c₀ ≤ 1 := by rw [hkI.1]; exact hc₀le
  have hcr : 0 < kI.cr := by rw [hkI.2.1]; exact hfacts.hcr
  have hcr1 : kI.cr ≤ 1 := by rw [hkI.2.1]; exact hfacts.hcr_le
  obtain ⟨C₁, m₁, hC₁, -, hscale⟩ := hsclΛ Acl T₀ hAcl
  choose cgf Cpxf m₀f hcg hCpx hm₀ hP using fun (CGl Cwl : ℕ → ℝ) (Ca : ℝ) =>
    hpartΛ Acl N (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) CGl Cwl Ca CI T₀ hA1 hCI hAcl
  have hsc : ReconScaleCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
      σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Acl Lc C₁ m₁ := by
    intro hr _ _ _ _ _ _ _ c hm htt CcT PZ aRep û hlift aZ aY hZ hY cg
    exact hscale (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.hα c.hq c.hΛ c.hζ c.hseq
      (by rw [c.hterm]; exact c.hband) hm c.m_lt_term (sub_pos.2 htt) c.window_le kI.c₀ kI.cr
      cg σ₀ Lc _ _ hc₀ hc₀1 hcr hcr1
  refine ⟨(C₁, m₁, fun CGl Cwl Ca => (cgf CGl Cwl Ca, Cpxf CGl Cwl Ca, m₀f CGl Cwl Ca)), hC₁,
    hsc, ?_⟩
  intro CGl Cwl Ca Cgr
  refine ⟨hcg CGl Cwl Ca, hCpx CGl Cwl Ca, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm htt CcT PZ aRep û hlift aZ aY hZ hY kc hW hkc
  have hm1 : m₁ ≤ c.m := le_trans (le_max_left _ _) hm
  have hm0 : m₀f CGl Cwl Ca ≤ c.m := le_trans (le_max_right _ _) hm
  have hscF := hsc c hm1 htt CcT PZ aRep û hlift aZ aY hZ hY (cgf CGl Cwl Ca)
  have hbill₁ : 0 ≤ C₁ * succReconBill c.D c.G c.m kI.cr (cgf CGl Cwl Ca) σ₀ (succEta0 α q s) p
      N Lc Acl J H c.tp c.tf (succTheta1 α q s σ₀ (succDstar D₀ N p H))
      (succTheta2 α q s σ₀ (succDstar D₀ N p H)) :=
    le_trans (mul_nonneg (Real.sqrt_nonneg _) hscF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      hscF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbill := nonneg_of_mul_nonneg_right hbill₁ (lt_of_lt_of_le one_pos hC₁)
  intro F1 F2 F3 T qs qf par V bM aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0 hfam hset hseq hco
  exact partitionAt_mono_bill (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law Acl kc 0 hW _
    _ _ _ (hCpx CGl Cwl Ca) (le_mul_of_one_le_left hbill hC₁)
    (hP CGl Cwl Ca (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law c.hα c.hq c.hΛ c.hζ c.hseq
      (by rw [c.hterm]; exact c.hband) rfl rfl hm0 c.m_lt_term (sub_pos.2 htt) c.window_le
      kI.c₀ kI.cr (cgf CGl Cwl Ca) σ₀ Lc _ _ hc₀ hc₀1 hcr hcr1 le_rfl kc hW hkc F1 F2 F3 T qs qf
      par V bM Cgr aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0 hfam hset hseq hco)

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Analysis.Convolution AVRegularity.Construction.Residual.Presentation
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The residual presentation of the comparison clauses at a frame (the residual half)**
(cascade side of the bill residual).

`comparisonResidual_at_frame`: from the bounds of the residual at a frame
(`FrameResidualBoundAt`: a reconstruction `uK` of the lifted field in the plain coupled system
with the residual pair `(RK, qK)`, a realization `Ff` of the fine tail, and the residual clause
with the bill `C·𝔅·A_in`), the second clause of `ComparisonClauses` without its error bound: a
gradient carrier `ŵ`, a kernel input `ŷ` and a forcing `(R_res, q_res)` such that the given
lifted field `û` of the frame is a regular solution of the kernel system of the stage on
`[t_p, t_f]` from `û(t_p)`, the forcing is measurable in time, and its residual norm is at most
`C·𝔅·A_in`.

Steps, one lemma each (each step elaborates in its own declaration): `frame_ident` (the
truncation of `uK` to the order `0` IS `û` on the window, because both have the value of the
lifted field); `frame_kernelSolution` (the plain-to-kernel
statement `plainToKernelStatementR`, which asks the lifted field `C^{D_m − 1}` and
periodic at every time of the window, the hypothesis `hreg`, then the congruence
`regSolution_congr_init`); the forcing is `(trunc RK + Ff, trunc qK)` and the residual
clause is converted by `residualNorm_of_wordsClause`.

For a stage without identities `Ff = 0`. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The identification of the field at a frame**: on the window the lifted field `û` of the
frame is the truncation of the trajectory of a reconstruction. -/
theorem frame_ident (F : Frame D hr Dm b j₀) {π : CompIn F.G.comps → ℝ} {rs Xr : ℝ}
    {K : CompIn F.G.comps → ℕ} {hK : ∀ v, 0 ≤ K v}
    {uK : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K v) (hr v.1.root)}
    {wK : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root)}
    {RK : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    {qK : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K v) (hr v.1.root)}
    (hrec : IsStageRecon F.G F.m 0 π F.tp F.tf rs
      (menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep) Xr K hK uK wK RK qK) :
    ∀ v, ∀ t ∈ Set.Icc F.tp F.tf, F.û v t = truncateTorusHk (hK v) (uK v t) := by
  intro v t ht
  symm
  apply TorusHk.ext_value
  apply value_eq_of_jet_ae
  exact (hrec.value t ht v).trans (F.lift.2.2 v t ht).symm

/-- **The kernel system at a frame from a reconstruction and a realization of the fine tail**:
the plain-to-kernel statement with the trajectory replaced by the lifted field `û`. -/
theorem frame_kernelSolution (F : Frame D hr Dm b j₀) (law : BirthLaw) (hD2 : 2 ≤ Dm)
    (hφ₀ : Integrable F.φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) F.φ₀)
    (hs : Function.support F.φ₀ ⊆ closedEuclideanUnitBall)
    (Mnat : ℕ) (kI : InvConsts) (tA tB S θK : ℝ)
    (hI : IsStageInvariant law F.P F.seedK F.freshK F.φ₀ hφ₀ Mnat kI tA tB S θK F.G)
    (hlev : F.G.level = F.m) (hkap : D.kap F.G.level = D.κ F.m) (hA : tA ≤ F.tp)
    (hB : F.tf ≤ tB) (htt : F.tp ≤ F.tf)
    (hreg : ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((Dm - 1 : ℕ) : ℕ∞)
          (fun x => menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep t x v) ∧
        IsZ2Periodic (fun x => menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep t x v))
    {π : CompIn F.G.comps → ℝ} {rs Xr : ℝ}
    {K : CompIn F.G.comps → ℕ} {hK : ∀ v, 0 ≤ K v}
    {uK : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K v) (hr v.1.root)}
    {wK : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root)}
    {RK : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    {qK : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K v) (hr v.1.root)}
    (hrec : IsStageRecon F.G F.m 0 π F.tp F.tf rs
      (menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep) Xr K hK uK wK RK qK)
    (Ff : ∀ v : CompIn F.G.comps, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (hFf : IsFluxRealization (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) 0
      (Set.Icc F.tp F.tf)
      (fineFluxF F.P F.seedK F.freshK F.φ₀ F.G
        (menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep)) Ff)
    (hFm : ∀ v, MemLp (Ff v) 2 (volume.restrict (Set.Icc F.tp F.tf))) :
    ∃ ŷ : ∀ v u (_ : F.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root),
      F.G.IsRegSolution F.P F.seedK F.freshK F.φ₀ hφ₀ (D.κ F.m) (streamVel (D.Φ F.m)) 0 F.tp
        F.tf (fun v => F.û v F.tp)
        (fun v t => truncateTorusHk (hK v) (RK v t) + Ff v t)
        (fun v t => truncateTorusHk (hK v) (qK v t)) F.û
        (fun v t => truncateTorusHk (Nat.succ_le_succ (hK v)) (wK v t)) ŷ := by
  obtain ⟨ŷ, hsol⟩ := plainToKernelStatementR hD2 law F.P F.seedK F.freshK F.φ₀ hφ₀ hd hs Mnat kI
    tA tB S θK F.G F.m 0 hI hlev hkap (Nat.zero_le _) π F.tp F.tf rs Xr hA hB
    (menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep) K hK uK wK RK qK hreg hrec Ff hFf hFm
  have hEq := frame_ident F hrec
  exact ⟨ŷ, regSolution_congr_init hsol htt F.û hEq _
    (funext fun v => hEq v F.tp ⟨le_rfl, htt⟩)⟩

/-- **The residual half of the comparison clauses at a frame.** -/
theorem comparisonResidual_at_frame (F : Frame D hr Dm b j₀) (law : BirthLaw) (hD2 : 2 ≤ Dm)
    (hφ₀ : Integrable F.φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) F.φ₀)
    (hs : Function.support F.φ₀ ⊆ closedEuclideanUnitBall)
    (Mnat : ℕ) (kI : InvConsts) (tA tB S θK : ℝ)
    (hI : IsStageInvariant law F.P F.seedK F.freshK F.φ₀ hφ₀ Mnat kI tA tB S θK F.G)
    (hlev : F.G.level = F.m) (hkap : D.kap F.G.level = D.κ F.m) (hA : tA ≤ F.tp)
    (hB : F.tf ≤ tB) (htt : F.tp ≤ F.tf)
    (hreg : ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((Dm - 1 : ℕ) : ℕ∞)
          (fun x => menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep t x v) ∧
        IsZ2Periodic (fun x => menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep t x v))
    {c₀ cr c σ₀ : ℝ} {Lc Lf Acl : ℕ} {θ₁ θ₂ Ain C : ℝ}
    (hres : FrameResidualBoundAt F law c₀ cr c σ₀ Lc Lf Acl θ₁ θ₂ Ain C) :
    ∃ (ŵ : ∀ v : CompIn F.G.comps, ℝ → TorusHk 1 (hr v.1.root))
      (ŷ : ∀ v u (_ : F.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root))
      (Rres : ∀ v : CompIn F.G.comps, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
      (qres : ∀ v : CompIn F.G.comps, ℝ → TorusHk 0 (hr v.1.root)),
      F.G.IsRegSolution F.P F.seedK F.freshK F.φ₀ hφ₀ (D.κ F.m) (streamVel (D.Φ F.m)) 0 F.tp
          F.tf (fun v => F.û v F.tp) Rres qres F.û ŵ ŷ ∧
        (∀ v, AEStronglyMeasurable (Rres v) (volume.restrict (Set.Icc F.tp F.tf))) ∧
        (∀ v, AEStronglyMeasurable (qres v) (volume.restrict (Set.Icc F.tp F.tf))) ∧
        residualNorm (D.κ F.m) (F.G.mass law) (Set.Icc F.tp F.tf)
            (fun t x k v => ((Rres v t).toFunction.jet (valueIndex2 0) x) k)
            (fun t x v => (qres v t).toFunction.jet (valueIndex2 0) x) ≤
          ENNReal.ofReal (C * succBill D F.G F.m c₀ cr c σ₀ F.η₀ F.p F.N Lc Lf Acl F.J F.H F.tp
            F.tf θ₁ θ₂ * Ain) := by
  obtain ⟨K, hK, uK, wK, RK, qK, Ff, Xr, hrec, hFf, hFm, hcl⟩ := hres
  obtain ⟨ŷ, hsol⟩ := frame_kernelSolution F law hD2 hφ₀ hd hs Mnat kI tA tB S θK hI hlev
    hkap hA hB htt hreg hrec Ff hFf hFm
  obtain ⟨hm1, hm2⟩ := measurable_of_wordsClause _ _ _ _ _ _ _ _ hcl
  exact ⟨_, ŷ, _, _, hsol, hm1, hm2, residualNorm_of_wordsClause _ _ _ _ _ _ _ _ hcl⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Coarse
open AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! Frame conversion: exact smooth-test ingredients and the transfer/density assembly. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

def MacroSwapConc (kc : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) : Prop :=
  ∀ v : CompIn F.G.comps, ∀ s ∈ Set.Icc F.tp (F.tp + fTobs F),
    ∀ φ : Vec 2 → hr v.1.root, ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
    let Pm : Vec 2 → ℝ := fun y => ∑ k : Fin 2, inner ℝ (toFluxL (menuMacroFlux
      F.Mn F.G F.m F.N F.depth F.CcT F.aRep v s y) k) (gradE φ y k)
    let Pc : Vec 2 → ℝ := fun y => ∑ k : Fin 2, inner ℝ (AVRegularity.coarseDefectFlux
      (D.κ (F.m - 1)) (F.N + Dm) F.depth AD CE (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m))
      (frameReconW F kc hW) v s y k) (gradE φ y k)
    Integrable Pm (volume.restrict unitCube) ∧ Integrable Pc (volume.restrict unitCube) ∧
      ∫ y in unitCube, Pm y = ∫ y in unitCube, Pc y

def SmoothDefect (kc : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (hf : fNc F kc ≤ F.Naux - 2 * F.p)
    (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) : Prop :=
  ∀ v : CompIn F.G.comps, ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F),
    ∀ ψ : Vec 2 → hr v.1.root, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
    IntegrableOn (fun s => ∫ y in unitCube, wIntegrand (D.κ (F.m - 1))
        (streamVel (D.Φ (F.m - 1))) (F.N + Dm) F.depth AD CE
        (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) (frameReconW F kc hW) (frameReconFc F F1 F2 F3)
        v ψ s y) (Set.Ioc F.tp t) ∧
    cellInner (tval (frameReconW F kc hW v t)) ψ -
        cellInner (fun y => (truncateTorusHk hf (F.PZ v F.tp)).toFunction.jet
          (valueIndex2 (fNc F kc)) y) ψ =
      ∫ s in Set.Ioc F.tp t, ∫ y in unitCube, wIntegrand (D.κ (F.m - 1))
        (streamVel (D.Φ (F.m - 1))) (F.N + Dm) F.depth AD CE
        (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) (frameReconW F kc hW) (frameReconFc F F1 F2 F3)
        v ψ s y



/-- Mean flux identification needed by the transfer, without any mass bound. -/
def MeanFluxConc (kc : ℕ)
    (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) : Prop :=
  ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
    (frameReconFc F F1 F2 F3 v t).toFunction.jet (valueIndex2 kc) =ᵐ[volume.restrict unitCube]
      F.mean v t

/-- Open macro-swap ingredient, including the lift sequences and setting it consumes. -/
def MacroSwapStatement (Acl kc ℓ : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ) : Prop :=
  FrameReconSeqAt F Acl ℓ →
  (∃ (qs qf : ℕ) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
    (bM : CompIn F.G.comps → CompIn F.G.comps → ℝ),
    FrameReconSettingBody F law Acl ℓ CGl Cwl Ca Sb Cgr qs qf par V bM) →
  ∀ (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ),
    FrameReconLettersBody F law kc aC B₀C lamC AD CE Aedge Cstar Θc →
    MacroSwapConc F kc hW AD CE

/-- Open mean-flux identification ingredient. -/
def MeanFluxStatement (kc : ℕ) : Prop :=
  ∀ (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))),
    FrameReconFluxRealizations F kc F1 F2 F3 → MeanFluxConc F kc F1 F2 F3

private theorem window' : F.tp + fTobs F = F.tf := by
  simp [fTobs]

private theorem jets (kc : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p) :
    ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      IsClassicalRep (frameReconW F kc hW v t) (fun y => F.aRep t y v) (F.N + Dm) := by
  intro v t ht
  exact Construction.Preservation.FullLift.classicalRep_truncate hW (by omega) (F.PZ v t)
    (fun y => F.aRep t y v) (rdJets_classicalRep_mono (F.lift.2.1 v t ht).2 (by omega))

/-- Transfer of the frame's macro weak equation to smooth-test coarse defect. -/
theorem transfer' (kc : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (hf : fNc F kc ≤ F.Naux - 2 * F.p)
    (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ)
    (hlet : FrameReconLettersBody F law kc aC B₀C lamC AD CE Aedge Cstar Θc)
    (hweak : F.macroWeak) (hswap : MacroSwapConc F kc hW AD CE)
    (hmean : MeanFluxConc F kc F1 F2 F3) :
    SmoothDefect F kc hW hf F1 F2 F3 AD CE := by
  intro v t ht ψ hψ hp
  have htw : t ∈ Set.Icc F.tp F.tf := by rw [← window' F]; exact ht
  have hr1 : 1 ≤ F.N + Dm := by have := hlet.1.D_ge; omega
  obtain ⟨-, -, hI3, hI4, hid⟩ := hweak v t htw ψ hψ hp
  have key : ∀ s ∈ Set.Ioc F.tp t, _ := fun s hs => by
    have hsw : s ∈ Set.Icc F.tp F.tf := ⟨hs.1.le, hs.2.trans htw.2⟩
    have hsw' : s ∈ Set.Icc F.tp (F.tp + fTobs F) := by rw [window' F]; exact hsw
    obtain ⟨hPm, hPc, hint⟩ := hswap v s hsw' ψ hψ hp
    have hdu := grad_ae (jets F kc hW v s hsw) hr1
    have hF := hmean v s hsw
    exact TransferPoint (μ := volume.restrict unitCube) (D.κ (F.m - 1))
      (streamVel (D.Φ (F.m - 1)) s) ψ (fun k y => gradE ψ y k)
      (fun k y => gradE (fun y' => F.aRep s y' v) y k)
      (fun k y => torusJetOrder (frameReconW F kc hW v s) 1 (fun _ => k) y) _ _ _ _ hdu hF
      (hI3 s hs) hPm hPc hint
  have hct : cellInner (tval (frameReconW F kc hW v t)) ψ =
      ∫ y in unitCube, inner ℝ (F.aRep t y v) (ψ y) := by
    refine integral_congr_ae ?_
    filter_upwards [tval_ae' (jets F kc hW v t htw)] with y hy
    rw [hy]
  have hinit : IsClassicalRep (truncateTorusHk hf (F.PZ v F.tp))
      (fun y => F.aRep F.tp y v) 0 :=
    Construction.Preservation.FullLift.classicalRep_truncate hf (Nat.zero_le _) (F.PZ v F.tp)
      (fun y => F.aRep F.tp y v)
      (rdJets_classicalRep_mono (F.lift.2.1 v F.tp ⟨le_rfl, htw.1.trans htw.2⟩).2 (Nat.zero_le _))
  have hc0 : cellInner (fun y => (truncateTorusHk hf (F.PZ v F.tp)).toFunction.jet
      (valueIndex2 (fNc F kc)) y) ψ = ∫ y in unitCube, inner ℝ (F.aRep F.tp y v) (ψ y) := by
    refine integral_congr_ae ?_
    filter_upwards [tval_ae' hinit] with y hy
    exact congrArg (fun z => inner ℝ z (ψ y)) hy
  refine ⟨hI4.congr_fun (fun s hs => ((key s hs).2).symm) measurableSet_Ioc, ?_⟩
  rw [hct, hc0]
  refine hid.trans ?_
  exact (setIntegral_congr_fun measurableSet_Ioc (fun s hs => (key s hs).2)).symm

theorem W_bounded (kc : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (hcont : ∀ v, ContinuousOn (frameReconW F kc hW v) (Set.Icc F.tp (F.tf))) :
    ∃ MW : ℝ, ∀ s ∈ Set.Icc F.tp (F.tf), ∀ v, ‖frameReconW F kc hW v s‖ ≤ MW := by
  have h1 : ∀ v, ∃ Mv : ℝ, ∀ s ∈ Set.Icc F.tp (F.tf), ‖frameReconW F kc hW v s‖ ≤ Mv :=
    fun v => isCompact_Icc.exists_bound_of_continuousOn (hcont v)
  choose Mv hMv using h1
  refine ⟨∑ v, |Mv v|, fun s hs v => ?_⟩
  exact (hMv v s hs).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun v => |Mv v|) (fun v _ => abs_nonneg _) (Finset.mem_univ v)))

/-- `‖F_c s‖` is integrable on the window. -/
theorem Fc_integrable (kc : ℕ)
    (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (v : CompIn F.G.comps)
    (h1 : MemLp (F1 v) 2 (volume.restrict (Set.Icc F.tp (F.tf))))
    (h2 : MemLp (F2 v) 2 (volume.restrict (Set.Icc F.tp (F.tf))))
    (h3 : MemLp (F3 v) 2 (volume.restrict (Set.Icc F.tp (F.tf)))) :
    IntegrableOn (fun s => ‖frameReconFc F F1 F2 F3 v s‖) (Set.Icc F.tp (F.tf)) := by
  have i1 := (h1.integrable one_le_two).norm
  have i2 := (h2.integrable one_le_two).norm
  have i3 := (h3.integrable one_le_two).norm
  have hm : AEStronglyMeasurable (fun s => frameReconFc F F1 F2 F3 v s)
      (volume.restrict (Set.Icc F.tp (F.tf))) :=
    (h1.aestronglyMeasurable.sub h3.aestronglyMeasurable).sub h2.aestronglyMeasurable
  refine Integrable.mono' ((i1.add i3).add i2) hm.norm (Filter.Eventually.of_forall fun s => ?_)
  simp only [frameReconFc, Real.norm_eq_abs, abs_norm, Pi.add_apply]
  exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)


/-- Density application with explicit square-integrability inputs. -/
theorem density (kc : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (hf : fNc F kc ≤ F.Naux - 2 * F.p)
    (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ)
    (hlet : FrameReconLettersBody F law kc aC B₀C lamC AD CE Aedge Cstar Θc)
    (h1 : ∀ v, MemLp (F1 v) 2 (volume.restrict (Set.Icc F.tp F.tf)))
    (h2 : ∀ v, MemLp (F2 v) 2 (volume.restrict (Set.Icc F.tp F.tf)))
    (h3 : ∀ v, MemLp (F3 v) 2 (volume.restrict (Set.Icc F.tp F.tf)))
    (hc : ∀ v, ContinuousOn (frameReconW F kc hW v) (Set.Icc F.tp (F.tp + fTobs F)))
    (hsm : SmoothDefect F kc hW hf F1 F2 F3 AD CE) :
    IsCoarseDefect F.tp (F.tp + fTobs F) (D.κ (F.m - 1)) (streamVel (D.Φ (F.m - 1)))
      (F.N + Dm) F.depth kc (fNc F kc) AD CE (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m))
      (fun v => truncateTorusHk hf (F.PZ v F.tp)) (frameReconW F kc hW) (frameReconFc F F1 F2 F3) := by
  have hc' : ∀ v, ContinuousOn (frameReconW F kc hW v) (Set.Icc F.tp F.tf) := by
    rw [← window' F]; exact hc
  obtain ⟨MW, hMW⟩ := W_bounded F kc hW hc'
  have hFc : ∀ v, IntegrableOn (fun s => ‖frameReconFc F F1 F2 F3 v s‖)
      (Set.Icc F.tp (F.tp + fTobs F)) := fun v => by
    rw [window' F]
    exact Fc_integrable F kc F1 F2 F3 v (h1 v) (h2 v) (h3 v)
  rw [← window' F] at hMW
  exact CoarseDefectOfSmooth hlet.1 hMW hFc hsm

theorem defect_from_swap (kc : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (hf : fNc F kc ≤ F.Naux - 2 * F.p)
    (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ)
    (hlet : FrameReconLettersBody F law kc aC B₀C lamC AD CE Aedge Cstar Θc)
    (h1 : ∀ v, MemLp (F1 v) 2 (volume.restrict (Set.Icc F.tp F.tf)))
    (h2 : ∀ v, MemLp (F2 v) 2 (volume.restrict (Set.Icc F.tp F.tf)))
    (h3 : ∀ v, MemLp (F3 v) 2 (volume.restrict (Set.Icc F.tp F.tf)))
    (hc : ∀ v, ContinuousOn (frameReconW F kc hW v) (Set.Icc F.tp (F.tp + fTobs F)))
    (hw : F.macroWeak)
    (hswap : MacroSwapConc F kc hW AD CE)
    (hmean : MeanFluxConc F kc F1 F2 F3) :
    IsCoarseDefect F.tp (F.tp + fTobs F) (D.κ (F.m - 1)) (streamVel (D.Φ (F.m - 1)))
      (F.N + Dm) F.depth kc (fNc F kc) AD CE (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m))
      (fun v => truncateTorusHk hf (F.PZ v F.tp)) (frameReconW F kc hW) (frameReconFc F F1 F2 F3) := by
  exact density F law kc hW hf F1 F2 F3 aC B₀C lamC AD CE Aedge Cstar Θc hlet h1 h2 h3 hc
    (transfer' F law kc hW hf F1 F2 F3 aC B₀C lamC AD CE Aedge Cstar Θc hlet hw hswap hmean)
end

/-! Frame conversion: exact smooth-test ingredients and the transfer/density assembly. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- Extract the covariance time integrability separately to bound projection elaboration. -/
private theorem covLp {kc : ℕ} {cr Ain Cfl : ℝ}
    {F1 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    (h : FrameCovTruncReal F law kc cr Ain Cfl F1) :
    ∀ v, MemLp (F1 v) 2 (volume.restrict (Set.Icc F.tp F.tf)) := h.2.1

private theorem frontLp {kc : ℕ} {cr θ₁ θ₂ Ain Cfl : ℝ}
    {F2 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    (h : FrameFrontierReal F law kc cr θ₁ θ₂ Ain Cfl F2) :
    ∀ v, MemLp (F2 v) 2 (volume.restrict (Set.Icc F.tp F.tf)) := h.2.1

private theorem filterLp {kc : ℕ} {cr σ₀ Ain Cfl : ℝ} {Lc : ℕ}
    {F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    (h : FrameFilterReal F law kc cr σ₀ Lc Ain Cfl F3) :
    ∀ v, MemLp (F3 v) 2 (volume.restrict (Set.Icc F.tp F.tf)) := h.2.1

/-- The reconstruction defect statement from the two named remaining frame ingredients. -/
theorem frameReconDefectConvAt_of_ingredients (Acl kc ℓ : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (hf : fNc F kc ≤ F.Naux - 2 * F.p) (cr σ₀ : ℝ) (Lc : ℕ) (θ₁ θ₂ Ain Cfl : ℝ)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ)
    (hswap : MacroSwapStatement F law Acl kc ℓ hW CGl Cwl Ca Sb Cgr)
    (hmean : MeanFluxStatement F kc) :
    FrameReconDefectConvAt F law Acl kc ℓ hW hf cr σ₀ Lc θ₁ θ₂ Ain Cfl CGl Cwl Ca Sb Cgr := by
  exact fun hw F1 F2 F3 h1 h2 h3 hc hseq hset aC B₀C lamC AD CE Aedge Cstar Θc hlet => defect_from_swap F law kc hW hf F1 F2 F3 aC B₀C lamC AD CE Aedge Cstar Θc hlet
    (covLp F law h1) (frontLp F law h2) (filterLp F law h3) hc hw
    (hswap hseq hset aC B₀C lamC AD CE Aedge Cstar Θc hlet)
    (hmean F1 F2 F3 ⟨h1.1, h2.1, h3.1⟩)
end

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **Smoothness and periodicity of the frontier readout at a frame**
(generic content of `termInnerSmoothAt_of_certificate`).

`frontierSmooth`: at a frame `F`, for every order `kc` (the readout is `C^{kc+2p}`), from the
certificate `F.G'.IsContextCertified kI`, slot transversality, naturality and shift invariance of
the outgoing stage (all named hypotheses), and a classical representative `F.aY` that is
`C^{kc+2p+D_m}` and `ℤ²`-periodic at each time of the window, the classical readout of the omitted
flux is `C^{kc+2p}` and periodic at each time of the window: this is the first clause of
`FrontierInnerForm`.

For `aY = 0` everything is `0`, and with no retained row the sums are empty. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The readout of the omitted flux is smooth and periodic at a frame.** -/
theorem frontierSmooth (F : Frame D hr Dm b j₀) (kc : ℕ) {kI : InvConsts} {M : ℕ}
    (hcert : F.G'.IsContextCertified kI) (hST : F.G'.IsSlotTransverse)
    (hnat : F.G'.IsNatural M) (hSH : F.G'.IsShiftInvariant)
    (hlev : 1 ≤ F.G'.level) (hj : j₀ ≤ F.G'.level) (hb : 0 < b)
    (hε : 0 < D.eps (F.G'.level - 1)) (hres : ∀ v : CompIn F.G'.comps, 0 ≤ compReserve kI v.1)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) F.φ₀)
    (hφsupp : Function.support F.φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (hY : ∀ t ∈ Set.Icc F.tp F.tf, ∀ u : CompIn F.Gr.comps,
      ContDiff ℝ ((kc + 2 * F.p + Dm : ℕ) : ℕ∞) (fun y => F.aY t y u) ∧
        IsZ2Periodic (fun y => F.aY t y u)) :
    ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((kc + 2 * F.p : ℕ) : ℕ∞)
          (fun y => frontierReadout F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m F.H F.J
            (D.eps (F.m - 1)) F.η₀ F.aY v t y) ∧
        IsZ2Periodic
          (fun y => frontierReadout F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m F.H F.J
            (D.eps (F.m - 1)) F.η₀ F.aY v t y) := by
  intro v t ht
  have hflux := omittedFluxClassical_smooth F.P F.seedK F.freshK F.φ₀ hφs hφsupp F.G' F.Gr F.aY
    t (kc + 2 * F.p)
    (fun v u γ d => ⟨native_physCoeff_all_order_smooth hcert hST hnat hlev hj hb hε t t v u γ
      (hres v) ((compReserve_le_one' kI v.1).trans (by norm_num)) _ d t ⟨le_rfl, le_rfl⟩,
      Construction.Preservation.Buffer.native_physCoeff_periodic hnat hSH v u γ d t⟩)
    (fun u => hY t ht u)
  have hro := readoutFlux_smooth (hr := hr) F.m (D.eps (F.m - 1)) F.η₀
    (S := F.G.comps) (S' := F.G'.comps) (fun c' => ¬ IsRetained F.m F.H F.J c')
    (fun v' s y' => omittedFluxClassical F.P F.seedK F.freshK F.φ₀ F.G' F.Gr F.aY v' s y') t
    (kc + 2 * F.p) (fun v' => hflux v') v
  exact ⟨PiLp.contDiff_ofLp.comp hro.1, fun k y => congrArg WithLp.ofLp (hro.2 k y)⟩

/-- **The assembly**: `FrontierInnerForm` at a frame is the smoothness clause (`frontierSmooth`)
together with the bound clause (`frontierInner_bound`). -/
theorem frontierInnerForm_of (F : Frame D hr Dm b j₀) (law : BirthLaw) (kc : ℕ)
    (cr Y : ℝ)
    (hsm : ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((kc + 2 * F.p : ℕ) : ℕ∞)
          (fun y => frontierReadout F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m F.H F.J
            (D.eps (F.m - 1)) F.η₀ F.aY v t y) ∧
        IsZ2Periodic
          (fun y => frontierReadout F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m F.H F.J
            (D.eps (F.m - 1)) F.η₀ F.aY v t y))
    (hb : HasFluxBound (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) (kc + 2 * F.p)
      (Set.Icc F.tp F.tf) (D.κ (F.m - 1)) (rhoEnh D cr F.m) (F.G.mass law)
      (fun v t y => toFluxL
        (frontierReadout F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m F.H F.J
          (D.eps (F.m - 1)) F.η₀ F.aY v t y)) Y) :
    FrontierInnerForm F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m F.p F.H F.J kc
      (D.eps (F.m - 1)) F.η₀ F.aY (F.G.mass law) F.tp F.tf (rhoEnh D cr F.m) Y :=
  ⟨hsm, hb⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Coarse
open AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! Macro swap from classical divergence equality, with letters regularity discharged. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The pointwise regularity of the menu macro flux used by torus integration by parts. -/
def MacroReg : Prop :=
  ∀ v, ∀ s ∈ Set.Icc F.tp (F.tp + fTobs F),
    (∀ k : Fin 2, ContDiff ℝ 1 (fun y => menuMacroFlux F.Mn F.G F.m F.N F.depth F.CcT F.aRep v s y k)) ∧
    (∀ k : Fin 2, IsZ2Periodic (fun y => menuMacroFlux F.Mn F.G F.m F.N F.depth F.CcT F.aRep v s y k))

/-- Equal classical divergences, before replacement of classical jets by Sobolev jets. -/
def MacroDivConc
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) : Prop :=
  ∀ v, ∀ s ∈ Set.Icc F.tp (F.tp + fTobs F), ∀ x : Vec 2,
    divE (fun y k => menuMacroFlux F.Mn F.G F.m F.N F.depth F.CcT F.aRep v s y k) x =
    divE (fun y k => ClassicalDefectFlux (D.κ (F.m - 1)) (F.N + Dm) F.depth AD CE
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) F.aRep v s y k) x

/-- Classical letters flux regularity follows from the setting and the lift representative. -/
theorem letters_regular (kc : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ)
    (hlet : FrameReconLettersBody F law kc aC B₀C lamC AD CE Aedge Cstar Θc) :
    ∀ v, ∀ s ∈ Set.Icc F.tp (F.tp + fTobs F),
      (∀ k : Fin 2, ContDiff ℝ 1 (fun y => ClassicalDefectFlux (D.κ (F.m - 1))
        (F.N + Dm) F.depth AD CE (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) F.aRep v s y k)) ∧
      (∀ k : Fin 2, IsZ2Periodic (fun y => ClassicalDefectFlux (D.κ (F.m - 1))
        (F.N + Dm) F.depth AD CE (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) F.aRep v s y k)) := by
  have hset := hlet.1
  have hD : 2 ≤ F.N + Dm := hset.D_ge
  have hN : 1 ≤ fNc F kc := by
    have hpos : 0 < (0 + F.depth + 3) * ((F.N + Dm) + 8 * 1 + 4) := by positivity
    change 1 ≤ kc + (0 + F.depth + 3) * ((F.N + Dm) + 8 * 1 + 4)
    omega
  intro v s hs
  have hs' : s ∈ Set.Icc F.tp F.tf := by simpa [fTobs] using hs
  have hrep : ∀ w, ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (fun y => F.aRep s y w) ∧
      IsZ2Periodic (fun y => F.aRep s y w) := fun w => by
    obtain ⟨-, hd, hp, -⟩ := (F.lift.2.1 w s hs').2
    exact ⟨(by exact_mod_cast hd : ContDiff ℝ ((F.Naux - 2 * F.p : ℕ) : ℕ∞) _).of_le
      (by exact_mod_cast (by omega : F.N + Dm ≤ F.Naux - 2 * F.p)), hp⟩
  have hADs : ∀ d, ContDiff ℝ 1 (AD d s) := fun d =>
    (hset.AD_smooth d s hs).of_le (by exact_mod_cast hN)
  have hCEs : ∀ r ∈ Finset.Icc 1 F.depth, ∀ v u d, ContDiff ℝ 1 (CE r v u d s) := fun r hr v u d =>
    (hset.CE_smooth r hr v u d s hs).of_le (by exact_mod_cast hN)
  exact ⟨fun k => classicalFlux_contDiff _ _ _ hD AD CE _ F.aRep v s
      (fun u => (hrep u).1) hADs hCEs k,
    fun k => classicalFlux_periodic _ _ _ hD AD CE _ F.aRep v s (fun u => (hrep u).1)
      (fun u => (hrep u).2) (fun d => hset.AD_per d s hs)
      (fun r hr v u d => hset.CE_per r hr v u d s hs) k⟩

/-- Integration by parts and the a.e. jet identity give the macro swap at a frame. -/
theorem swap_of_divergence (kc : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ)
    (hlet : FrameReconLettersBody F law kc aC B₀C lamC AD CE Aedge Cstar Θc)
    (hM : MacroReg F) (hDiv : MacroDivConc F AD CE) :
    MacroSwapConc F kc hW AD CE := by
  intro v s hs φ hφ hper
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hs' : s ∈ Set.Icc F.tp F.tf := by simpa [fTobs] using hs
  obtain ⟨hMc, hMp⟩ := hM v s hs
  obtain ⟨hLc, hLp⟩ := letters_regular F law kc hW aC B₀C lamC AD CE Aedge Cstar Θc hlet v s hs
  have hd := funext (hDiv v s hs)
  have e1 := torus_ibp _ φ hMc hMp hφ1 hper
  have e2 := torus_ibp _ φ hLc hLp hφ1 hper
  rw [hd] at e1
  have hD : 1 ≤ F.N + Dm := le_trans (by norm_num) hlet.1.D_ge
  have hj : ∀ u, IsClassicalRep (frameReconW F kc hW u s) (fun y => F.aRep s y u) (F.N + Dm) :=
    fun u => Construction.Preservation.FullLift.classicalRep_truncate hW (by omega) (F.PZ u s)
      (fun y => F.aRep s y u) (rdJets_classicalRep_mono (F.lift.2.1 u s hs').2 (by omega))
  have hae := pairing_ae_eq (D.κ (F.m - 1)) (F.N + Dm) F.depth hD AD CE
    (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) (frameReconW F kc hW) F.aRep v s φ
    (fun u m w hm => (hj u).2.2.2 m hm w)
  exact ⟨pairing_integrable _ φ hMc hφ1,
    (integrable_congr hae).2 (pairing_integrable _ φ hLc hφ1),
    (e1.trans e2.symm).trans (integral_congr_ae hae).symm⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
