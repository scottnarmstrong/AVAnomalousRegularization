-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.Recon.PartitionGate
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleComparison.Reconstruction.PartitionBound
import AVRegularity.EntryTerminal.Ingredients.SeedQuiet.Proof
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.Preservation.FullLift
open scoped ENNReal
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! **The assembly of the terminal reconstruction at a context**.

`termReconAt_of_steps`: at a context of the terminal residual, the named steps
(lift sequences, lift settings, family side, coarse side, analytic facts, conversion)
give `TermReconAt` at the common order `k₀ + ℓ`: the window `ReconWindow` is assembled from the
steps, `ReconWindow.physical_lift` is applied at `W = P_pZ`, `F_c = F_cov - F_filter - F_front`,
`X = C_s‖f‖₂`, `Y = C_fl‖f‖₂𝔱`, `M = ‖f‖₂`, the bill `𝔅_rec`, and Conv turns its output into
`ReconBound` at `r_* = c_K x` with the constant `max(1, c_K)^{K_max}·reconBillConst`.

Premises beyond the steps: the orders (`2 ≤ D_t`, `1 ≤ N_T`, `k_c` above the orders of the window,
the truncation order of `P_pZ`), the lift floors, the entrance `a_M + τ'_M ≤ t_p` and the deadline
`t_p < a + T₀` (the prefix supplies them for `M` large), and the constant `C`.

Degenerate cases:
- `ℓ = 0`: the common order of the terminal residual.
- `C_fl = 0`: the coarse flux vanishes; `Y = 0`.
- `c_K ≤ 1`: no radius conversion (`max 1 c_K = 1`). -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- Truncation to the same order is the identity. -/
theorem truncateTorusHk_le_refl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} (y : TorusHk K E) :
    truncateTorusHk (le_refl K) y = y := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  rfl

/-- `ReconBound` is monotone in its bound. -/
theorem reconBound_mono {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {Mn : SuccMenu} {G : GenStage D hr Dm b j₀}
    {m N depth k : ℕ} {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    {aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root} {π : CompIn G.comps → ℝ}
    {tp tf rs Xr Xr' : ℝ} (hle : Xr ≤ Xr')
    (h : ReconBound Mn G m N depth k CcT aRep π tp tf rs Xr) :
    ReconBound Mn G m N depth k CcT aRep π tp tf rs Xr' := by
  obtain ⟨K, hK, uK, wK, RK, qK, hrec⟩ := h
  exact ⟨K, hK, uK, wK, RK, qK, ⟨hrec.desc, hrec.value, hrec.plain,
    ⟨hrec.flux.1, hrec.flux.2.trans hle⟩, ⟨hrec.scalar.1, hrec.scalar.2.trans hle⟩⟩⟩

/-- **The orders of the window** from the order premises. -/
theorem reconOrders_of (A : TermArgs X) (kc ℓ Jc pc : ℕ) (hD2 : 2 ≤ A.Dt) (hN1 : 1 ≤ A.NT)
    (hkc : rm' A ℓ + rkres A ℓ + A.NT + 4 ≤ kc) :
    ReconOrders A.Dt A.NT A.dW (rKlift A ℓ) (rLlift A ℓ) kc Jc pc (rr₀ A kc) (rKmax A ℓ)
      (rAcl A) (rm' A ℓ) (rkres A ℓ) (rNχ A ℓ) := by
  have hA1 : 1 ≤ rAcl A := le_max_left _ _
  have hDH : A.Dt ≤ A.Dt * (A.dW + 1) * A.NT := by
    rw [mul_assoc]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.succ_pos _) hN1)
  have hJ : 0 ≤ (Jc + A.dW + 3) * ((A.NT + A.Dt) + 8 * pc + 4) := Nat.zero_le _
  simp only [rm', rkres, rNχ, rKlift, rLlift, rr₀, rKmax] at hkc ⊢
  exact
    { hD2 := hD2, hAcl := hA1, hK := by omega, hrL := by omega, hJL := by omega,
      hDL := by omega, hK2 := by omega, hord := by omega, hk := by omega, hNχ := by omega,
      hNχ' := by omega, hkres := by omega, hmr := by omega, hrW := by omega,
      hNco := by omega, hordd := by omega, hrK := by omega }

/-- **The window from the bodies of the steps.** -/
theorem mkReconWindow
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (kc ℓ : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (T : c.Gw.actualFamily.Atlas) (Cpart : ℝ) (qs qf : ℕ) (par : ℤ → Fin 2)
    (V : ℤ → ℝ → ℝ → ℝ) (bM : CompIn c.Gw.comps → CompIn c.Gw.comps → ℝ)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ) (aC B₀C lamC : ℝ) (pc Jc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn c.Gw.comps,
      TorusHk (kc + (Jc + A.dW + 3) * ((A.NT + A.Dt) + 8 * pc + 4)) (ScalarH v.1.root))
    (cgap Cg : ℝ)
    (hfam : ReconFamilyBody c ℓ T Cpart)
    (hset : ReconSettingBody c ℓ CGl Cwl Ca Sb Cgr qs qf par V bM) (hseq : ReconSeqAt c ℓ)
    (hco : ReconCoarseBody c kc hW F1 F2 F3 aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0)
    (hsc : ReconScaleBody c cgap Cg) (hTobs : 0 < rTobs c) (hkc : 1 ≤ kc)
    (Fc : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (hFc : ∀ v, Fc v =ᵐ[volume.restrict (Set.Icc c.tp (c.tp + rTobs c))] reconFc c F1 F2 F3 v) :
    ReconWindow c.D.α X.s c.D.q c.D.Λ c.D.ζ c.D.Φ M (c.D.hΦ (M - 1)) (c.D.κ M)
      (c.D.κ (M - 1)) c.tp (rTobs c) (ocEpsilon c.D.q c.D.Λ M) c.Gw.actualFamily (fun _ => ())
      (rK c ℓ) T oddSlotOf (c.Gw.mass c.lawW) Cpart A.dW A.NT (rKlift A ℓ) (rLlift A ℓ) qs qf
      c.CcT par V CGl Cwl Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 (reconW c kc hW)
      Fc c.aRep (rr₀ A kc) := by
  have hcd := isCoarseDefect_congr_ae hco.2.1 hFc
  obtain ⟨hdesc, htorus, hTcons, hTcov, hTq, hTact, hpp, hppinj, hpart, hquiet⟩ := hfam
  obtain ⟨hα₀, hα₁, hs₀, hs₁, hq, hζ, hΛ, hΦ, hm, hν, hB, he, heρ, hρE, -⟩ := hsc
  have htf : c.tp + rTobs c = c.a + A.T₀ := by simp only [rTobs]; ring
  have hrep : ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), ∀ v,
      IsClassicalRep (reconW c kc hW v t) (fun y => c.aRep t y v) (rr₀ A kc) := by
    intro t ht v
    rw [htf] at ht
    have h1 : rr₀ A kc ≤ A.Khat Kout - 2 * A.pT := by
      show kc + (A.NT + A.Dt) - 1 ≤ _
      omega
    have h2 : rr₀ A kc ≤ kc + 1 + (A.NT + A.Dt) := by
      show kc + (A.NT + A.Dt) - 1 ≤ _
      omega
    exact classicalRep_truncate hW h2 _ _ (isClassicalRep_of_le (c.lift.2.1 v t ht).2 h1)
  have hr₀ : rr₀ A kc ≤ kc + 1 + (A.NT + A.Dt) := by
    show kc + (A.NT + A.Dt) - 1 ≤ _
    omega
  have hDr : A.NT + A.Dt ≤ rr₀ A kc := by
    show _ ≤ kc + (A.NT + A.Dt) - 1
    omega
  exact
    { hα₀ := hα₀, hα₁ := hα₁, hs₀ := hs₀, hs₁ := hs₁, hq := hq, hζ := hζ, hΛ := hΛ, hΦ := hΦ,
      hm := hm, hν := hν, hB := hB, hTobs := hTobs, hρs := he, hρs_e := le_rfl, hρs_R := heρ,
      hRE := hρE, hdesc := hdesc, htorus := htorus, hTcons := hTcons, hTcov := hTcov, hTq := hTq,
      hTact := hTact, hpp := hpp, hppinj := hppinj, hpart := hpart, hquiet := hquiet,
      hsetting := hset.1, hseq := hseq, hcs := hco.1, hcd := hcd, hrep := hrep, hr₀ := hr₀,
      hDr := hDr, hmean := hco.2.2 }

/-- **The window theorem at the context** (`ReconWindow.physical_lift` and Conv). -/
theorem reconBound_of_window
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (T : c.Gw.actualFamily.Atlas) (Cpart : ℝ) (qs qf : ℕ) (par : ℤ → Fin 2)
    (V : ℤ → ℝ → ℝ → ℝ) (bM : CompIn c.Gw.comps → CompIn c.Gw.comps → ℝ)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ) (aC B₀C lamC : ℝ) (pc Jc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn c.Gw.comps,
      TorusHk (kc + (Jc + A.dW + 3) * ((A.NT + A.Dt) + 8 * pc + 4)) (ScalarH v.1.root))
    (Cfl Cs Cpx cgap Cg : ℝ)
    (hfam : ReconFamilyBody c ℓ T Cpart) (hseq : ReconSeqAt c ℓ)
    (hco : ReconCoarseBody c kc hW F1 F2 F3 aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0)
    (hTobs : 0 < rTobs c)
    (o : ReconOrders A.Dt A.NT A.dW (rKlift A ℓ) (rLlift A ℓ) kc Jc pc (rr₀ A kc) (rKmax A ℓ)
      (rAcl A) (rm' A ℓ) (rkres A ℓ) (rNχ A ℓ))
    (hSb : 0 ≤ Sb) (hCgr : 0 ≤ Cgr) (hCs : 0 ≤ Cs) (hCpx : 0 ≤ Cpx)
    (hkc : rm' A ℓ + rkres A ℓ + A.NT + 4 ≤ kc) (hkp : rpord A ℓ ≤ kc + (A.NT + A.Dt))
    (hset : ReconSettingBody c ℓ CGl Cwl Ca Sb Cgr qs qf par V bM)
    (hR6a : ReconEnergyAt c x kc ℓ hW Cs) (hR6b : ReconCoeffAt c ℓ)
    (hR6c : ReconPartitionAt c x kc ℓ hW Cpx cgap Cg) (hsc : ReconScaleBody c cgap Cg)
    (hle : c.tp ≤ c.tp + rTobs c) (hfs : ReconFluxSumBody c kc Cfl hle F1 F2 F3)
    (hConv : ReconConvAt c x ℓ) :
    ReconBound (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW (A.k₀ + ℓ) c.CcT c.aRep
      (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRStar cK M)
      (max 1 cK ^ rKmax A ℓ * (reconBillConst A.dW A.NT A.Dt (rAcl A) (rKmax A ℓ) (rm' A ℓ)
        (rkres A ℓ) (rNχ A ℓ) (rKlift A ℓ) (rLlift A ℓ) CGl Cwl Ca Sb Cgr Cs (max Cfl 0) (Cpx * Cs) *
          c.reconBill cgap Cg * c.normF)) := by
  -- a strongly measurable version `Fc` of the coarse flux
  obtain ⟨hFcm, hY⟩ := hfs
  obtain ⟨Fc, hFc, hFcs⟩ := exists_fluxVersion hFcm
  have w := mkReconWindow c kc ℓ hW F1 F2 F3 T Cpart qs qf par V bM CGl Cwl Ca Sb Cgr aC B₀C lamC
    pc Jc AD CE Aedge Cstar Θc f0 cgap Cg hfam hset hseq hco hsc hTobs (by omega) Fc hFc
  have hFm : ∀ n r', Measurable fun s =>
      coarseModeCoeff n (fun v => Fc v (Set.projIcc c.tp (c.tp + rTobs c) hle s)) r' :=
    fun n r' => measurable_coarseModeCoeff_comp hFcs
      (continuous_subtype_val.comp continuous_projIcc).measurable n r'
  obtain ⟨hWc, hEn⟩ := hR6a
  obtain ⟨Vb, CA, hCA, hbm, hVb, hAb, hAm⟩ := hR6b
  obtain ⟨Xp, hXp, hXpb, hPB⟩ := hR6c
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, he, heρ, -, hrs, htt, hb1, hb2, hb3, hb4, hb5⟩ := hsc
  have hKmax : ∀ v, rK c ℓ v ≤ rKmax A ℓ := fun v => by
    have := descSlots_le c.Gw.actualFamily A.dW A.Dt v
    show A.k₀ + ℓ + descSlots c.Gw.actualFamily A.dW A.Dt v ≤ A.k₀ + ℓ + A.Dt * A.dW
    omega
  have hn0 : 0 ≤ c.normF := Real.sqrt_nonneg _
  have hrse : rRs c ≤ ocEpsilon c.D.q c.D.Λ M :=
    mul_le_of_le_one_left he.le (min_le_right _ _)
  have hrsρ : rRs c ≤ rRho c := hrse.trans heρ
  have hKM : ∀ v, rK c ℓ v ≤ kc + (Jc + A.dW + 3) * ((A.NT + A.Dt) + 8 * pc + 4) := fun v => by
    have := hKmax v
    simp only [rm', rkres, rKmax] at hkc this ⊢
    omega
  have hCfl : (0 : ℝ) ≤ max Cfl 0 := le_max_right _ _
  have hY' := (fluxBound_le_of_ae hFc hY).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left Cfl 0) hn0) htt))
  obtain ⟨û, ŵ, Rres, qres, hval, hplain, -, -, hRm, hqi, hRb, hqb⟩ :=
    w.physical_lift o hKmax hSb hCgr hset.2 hrs hrse hrsρ hWc hFm
      (fun v => (hFcs v).aestronglyMeasurable) hbm hVb hCA hAb hAm
      (X := Cs * c.normF) (Y := max Cfl 0 * c.normF * rTT c) (M := c.normF) (tt := rTT c)
      (bill := c.reconBill cgap Cg) (Cs := Cs) (Cy := max Cfl 0) (Cpx := Cpx)
      (mul_nonneg hCs hn0) (mul_nonneg (mul_nonneg hCfl hn0) htt) hn0 htt hCs hCfl hCpx
      (ord := rpord A ℓ) (by omega) hXp hPB hEn
      ((strongEnergyUpTo_mono_order (by simp only [rm', rpord]; omega) _ _ _ _ _ _).trans hEn)
      hY' le_rfl
      le_rfl hXpb hb1 hb2 hb3 hb4 hb5
      (fun _ => kc + (Jc + A.dW + 3) * ((A.NT + A.Dt) + 8 * pc + 4)) f0 (fun _ => le_rfl) hKM
      (fun _ => truncateTorusHk_le_refl _)
  have hXb : 0 ≤ reconBillConst A.dW A.NT A.Dt (rAcl A) (rKmax A ℓ) (rm' A ℓ) (rkres A ℓ)
      (rNχ A ℓ) (rKlift A ℓ) (rLlift A ℓ) CGl Cwl Ca Sb Cgr Cs (max Cfl 0) (Cpx * Cs) *
        c.reconBill cgap Cg * c.normF :=
    le_trans (integral_nonneg fun _ => Real.sqrt_nonneg _) hqb
  exact hConv w.hdesc _ hXb û ŵ Rres qres hval hplain hRm hqi hRb hqb

/-- **The partition terms on the window from the partition bound**: `partition_window_input` on
the window, with the lift settings lowered to the partition orders and its factor bounded
by `C_px 𝔅_rec`. -/
theorem reconPartitionAt_of_gate
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (T : c.Gw.actualFamily.Atlas) (qs qf : ℕ) (par : ℤ → Fin 2)
    (V : ℤ → ℝ → ℝ → ℝ) (bM : CompIn c.Gw.comps → CompIn c.Gw.comps → ℝ)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ) (aC B₀C lamC : ℝ) (pc Jc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn c.Gw.comps,
      TorusHk (kc + (Jc + A.dW + 3) * ((A.NT + A.Dt) + 8 * pc + 4)) (ScalarH v.1.root))
    (Cpx cgap Cg : ℝ)
    (hfam : ReconFamilyBody c ℓ T reconCpart)
    (hset : ReconSettingBody c ℓ CGl Cwl Ca Sb Cgr qs qf par V bM) (hseq : ReconSeqAt c ℓ)
    (hco : ReconCoarseBody c kc hW F1 F2 F3 aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0)
    (hsc : ReconScaleBody c cgap Cg) (hTobs : 0 < rTobs c) (hkc : 1 ≤ kc)
    (hmono : LiftSettingMonoStatement) (hSb : 0 ≤ Sb) (hdl : c.tp < c.a + A.T₀)
    (hscale : ReconPartitionScaleAt c x (recPartC A ℓ CGl Cwl Ca) (recPartc A ℓ CGl Cwl Ca) Sb Cpx
      cgap Cg) :
    ReconPartitionAt c x kc ℓ hW Cpx cgap Cg := by
  have w := mkReconWindow c kc ℓ hW F1 F2 F3 T reconCpart qs qf par V bM CGl Cwl Ca Sb Cgr aC B₀C
    lamC pc Jc AD CE Aedge Cstar Θc f0 cgap Cg hfam hset hseq hco hsc hTobs hkc
    (reconFc c F1 F2 F3) (fun _ => Filter.EventuallyEq.rfl)
  obtain ⟨-, -, -, -, -, -, -, -, -, hν, -, he, heρ, -, hrs, -⟩ := hsc
  have hrse : rRs c ≤ ocEpsilon c.D.q c.D.Λ M :=
    mul_le_of_le_one_left he.le (min_le_right _ _)
  have he0 : 0 < ocEpsilon c.D.q c.D.Λ M := lt_of_lt_of_le hrs hrse
  have hℓ : 0 < ocEll c.D.q c.D.Λ M (c.D.κ M) := div_pos he0 (Real.sqrt_pos.2 hν)
  have hsetP := fun k hk => hmono (hset.1 k hk)
    (rAcl A + 2 + rKmax A ℓ + A.Dt * (A.dW + 1) * A.NT) (2 + rKmax A ℓ + A.Dt * (A.dW + 1) * A.NT)
    (0 + rKmax A ℓ + A.Dt * (A.dW + 1) * A.NT) (by simp only [rKlift]; omega)
    (by simp only [rLlift]; omega) (by simp only [rLlift]; omega)
  refine ⟨_, mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (recPartC_nonneg A ℓ CGl Cwl Ca) (pow_nonneg (by linarith) _)) (Nat.cast_nonneg _)) hℓ.le)
      (Real.sqrt_nonneg _)) (Real.exp_pos _).le, hscale hdl, fun n => ?_⟩
  exact (Classical.choose_spec (Classical.choose_spec (partition_window_input.{0, 0, 0, 0}
    (rAcl A) A.NT A.Dt A.dW (rKmax A ℓ) (rKlift A ℓ) (rLlift A ℓ) CGl Cwl Ca reconCpart
      (le_max_left _ _)))).2.2 w par V _ _ hsetP (by simp only [rKlift]; omega)
    (by simp only [rLlift]; omega) hSb heρ (rRs c) hrs hrse n

/-- The constant of B-recon from the window's constant (`ReconBound` is monotone). -/
theorem reconBound_final
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (ℓ : ℕ) (Cfl C cgap Cg : ℝ) (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr Cs Cpx : ℝ)
    (hsc : ReconScaleBody c cgap Cg)
    (hC : max 1 cK ^ rKmax A ℓ * reconBillConst A.dW A.NT A.Dt (rAcl A) (rKmax A ℓ) (rm' A ℓ)
      (rkres A ℓ) (rNχ A ℓ) (rKlift A ℓ) (rLlift A ℓ) CGl Cwl Ca Sb Cgr Cs (max Cfl 0) (Cpx * Cs) ≤
        C)
    (hb : ReconBound (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW (A.k₀ + ℓ) c.CcT c.aRep
      (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRStar cK M)
      (max 1 cK ^ rKmax A ℓ * (reconBillConst A.dW A.NT A.Dt (rAcl A) (rKmax A ℓ) (rm' A ℓ)
        (rkres A ℓ) (rNχ A ℓ) (rKlift A ℓ) (rLlift A ℓ) CGl Cwl Ca Sb Cgr Cs (max Cfl 0) (Cpx * Cs) *
          c.reconBill cgap Cg * c.normF))) :
    ReconBound (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW (A.k₀ + ℓ) c.CcT c.aRep
      (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRStar cK M) (C * c.reconBill cgap Cg * c.normF) := by
  refine reconBound_mono ?_ hb
  have hn0 : 0 ≤ c.normF := Real.sqrt_nonneg _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htt, -, -, hb3, -, -⟩ := hsc
  have hbill : 0 ≤ c.reconBill cgap Cg := le_trans (mul_nonneg (sq_nonneg _) htt) hb3
  calc max 1 cK ^ rKmax A ℓ * (reconBillConst A.dW A.NT A.Dt (rAcl A) (rKmax A ℓ) (rm' A ℓ)
        (rkres A ℓ) (rNχ A ℓ) (rKlift A ℓ) (rLlift A ℓ) CGl Cwl Ca Sb Cgr Cs (max Cfl 0)
          (Cpx * Cs) * c.reconBill cgap Cg * c.normF)
      = (max 1 cK ^ rKmax A ℓ * reconBillConst A.dW A.NT A.Dt (rAcl A) (rKmax A ℓ) (rm' A ℓ)
        (rkres A ℓ) (rNχ A ℓ) (rKlift A ℓ) (rLlift A ℓ) CGl Cwl Ca Sb Cgr Cs (max Cfl 0)
          (Cpx * Cs)) *
          (c.reconBill cgap Cg * c.normF) := by ring
    _ ≤ C * (c.reconBill cgap Cg * c.normF) :=
        mul_le_mul_of_nonneg_right hC (mul_nonneg hbill hn0)
    _ = C * c.reconBill cgap Cg * c.normF := by ring


/-- **The window theorem at the context with the partition bound.** -/
theorem reconBound_of_gate
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (T : c.Gw.actualFamily.Atlas) (qs qf : ℕ) (par : ℤ → Fin 2)
    (V : ℤ → ℝ → ℝ → ℝ) (bM : CompIn c.Gw.comps → CompIn c.Gw.comps → ℝ)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ) (aC B₀C lamC : ℝ) (pc Jc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn c.Gw.comps,
      TorusHk (kc + (Jc + A.dW + 3) * ((A.NT + A.Dt) + 8 * pc + 4)) (ScalarH v.1.root))
    (Cfl Cs Cpx cgap Cg : ℝ)
    (hfam : ReconFamilyBody c ℓ T reconCpart) (hseq : ReconSeqAt c ℓ)
    (hco : ReconCoarseBody c kc hW F1 F2 F3 aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0)
    (hTobs : 0 < rTobs c)
    (o : ReconOrders A.Dt A.NT A.dW (rKlift A ℓ) (rLlift A ℓ) kc Jc pc (rr₀ A kc) (rKmax A ℓ)
      (rAcl A) (rm' A ℓ) (rkres A ℓ) (rNχ A ℓ))
    (hSb : 0 ≤ Sb) (hCgr : 0 ≤ Cgr) (hCs : 0 ≤ Cs) (hCpx : 0 ≤ Cpx)
    (hkc : rm' A ℓ + rkres A ℓ + A.NT + 4 ≤ kc) (hkp : rpord A ℓ ≤ kc + (A.NT + A.Dt))
    (hset : ReconSettingBody c ℓ CGl Cwl Ca Sb Cgr qs qf par V bM)
    (hR6a : ReconEnergyAt c x kc ℓ hW Cs) (hR6b : ReconCoeffAt c ℓ)
    (hmono : LiftSettingMonoStatement) (hdl : c.tp < c.a + A.T₀)
    (hscale : ReconPartitionScaleAt c x (recPartC A ℓ CGl Cwl Ca) (recPartc A ℓ CGl Cwl Ca) Sb Cpx
      cgap Cg) (hsc : ReconScaleBody c cgap Cg)
    (hle : c.tp ≤ c.tp + rTobs c) (hfs : ReconFluxSumBody c kc Cfl hle F1 F2 F3)
    (hConv : ReconConvAt c x ℓ) (C : ℝ)
    (hC : max 1 cK ^ rKmax A ℓ * reconBillConst A.dW A.NT A.Dt (rAcl A) (rKmax A ℓ) (rm' A ℓ)
      (rkres A ℓ) (rNχ A ℓ) (rKlift A ℓ) (rLlift A ℓ) CGl Cwl Ca Sb Cgr Cs (max Cfl 0) (Cpx * Cs) ≤
        C) :
    ReconBound (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW (A.k₀ + ℓ) c.CcT c.aRep
      (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRStar cK M) (C * c.reconBill cgap Cg * c.normF) :=
  reconBound_final c ℓ Cfl C cgap Cg CGl Cwl Ca Sb Cgr Cs Cpx hsc hC <| reconBound_of_window c x kc ℓ hW F1 F2 F3 T reconCpart qs qf par V bM CGl Cwl Ca Sb Cgr aC B₀C
    lamC pc Jc AD CE Aedge Cstar Θc f0 Cfl Cs Cpx cgap Cg hfam hseq hco hTobs o hSb hCgr hCs hCpx
    hkc hkp hset hR6a hR6b
    (reconPartitionAt_of_gate c x kc ℓ hW F1 F2 F3 T qs qf par V bM CGl Cwl Ca Sb Cgr aC B₀C lamC pc
      Jc AD CE Aedge Cstar Θc f0 Cpx cgap Cg hfam hset hseq hco hsc hTobs
      (by simp only [rm', rkres] at hkc; omega) hmono hSb hdl hscale) hsc hle hfs hConv

/-- **The time regularity of the coarse data** from the flux bounds and the analytic facts. -/
theorem reconTimeReg_of
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Cs : ℝ) (h1 : ∀ v, MemLp (F1 v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀))))
    (h2 : ∀ v, MemLp (F2 v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀))))
    (h3 : ∀ v, MemLp (F3 v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀))))
    (hR6a : ReconEnergyAt c x kc ℓ hW Cs) : ReconTimeRegAt c kc hW F1 F2 F3 := by
  have htf : c.tp + rTobs c = c.a + A.T₀ := by simp only [rTobs]; ring
  refine ⟨h1, h2, h3, fun v => ?_⟩
  have h := hR6a.1 v
  rw [htf] at h
  exact h

/-- **The coarse side applied** with the time regularity from the flux bounds. -/
theorem reconCoarse_of_steps
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Cs : ℝ) (hR5 : ReconCoarseAt c x kc ℓ hW F1 F2 F3) (hr : ReconFluxRealizations c x kc F1 F2 F3)
    {ν₁ ρ₁ Y₁ ν₂ ρ₂ Y₂ ν₃ ρ₃ Y₃ : ℝ} {π₁ π₂ π₃ : CompIn c.Gw.comps → ℝ}
    (hF1m : FluxMassLe (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (K := fun _ => kc)
      ν₁ ρ₁ π₁ (Set.Icc c.tp (c.a + A.T₀)) F1 Y₁)
    (hF2m : FluxMassLe (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (K := fun _ => kc)
      ν₂ ρ₂ π₂ (Set.Icc c.tp (c.a + A.T₀)) F2 Y₂)
    (hF3m : FluxMassLe (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (K := fun _ => kc)
      ν₃ ρ₃ π₃ (Set.Icc c.tp (c.a + A.T₀)) F3 Y₃)
    (hR6a : ReconEnergyAt c x kc ℓ hW Cs) (hseq : ReconSeqAt c ℓ) (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ)
    (hR3 : ReconSettingAt c x ℓ CGl Cwl Ca Sb Cgr) : ReconCoarseResult c kc hW F1 F2 F3 :=
  hR5 hr (reconTimeReg_of c x kc ℓ hW F1 F2 F3 Cs hF1m.1 hF2m.1 hF3m.1 hR6a) hseq CGl Cwl Ca Sb Cgr hR3

/-- **B-recon at a context from the steps, for given flux realizations.** -/
theorem termReconAt_of_flux
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ) (Cfl C cgap Cg : ℝ)
    (hD2 : 2 ≤ A.Dt) (hN1 : 1 ≤ A.NT) (hkc : rm' A ℓ + rkres A ℓ + A.NT + 4 ≤ kc)
    (hkp : rpord A ℓ ≤ kc + (A.NT + A.Dt))
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (hfX : rKlift A ℓ + A.Dt + 2 ≤ sXT) (hfZ : max (rLlift A ℓ + 1) (rLlift A ℓ + 2) ≤ sZT)
    (hent : c.aM + ocTauP c.D.α c.D.q c.D.Λ M ≤ c.tp) (hdl : c.tp < c.a + A.T₀)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr Cs Cpx : ℝ) (hSb : 0 ≤ Sb) (hCgr : 0 ≤ Cgr) (hCs : 0 ≤ Cs)
    (hCpx : 0 ≤ Cpx)
    (hR2 : ReconSeqStep c x ℓ) (hR3 : ReconSettingAt c x ℓ CGl Cwl Ca Sb Cgr)
    (hR4 : ReconFamilyStep c ℓ) (hR5 : ∀ F1 F2 F3, ReconCoarseAt c x kc ℓ hW F1 F2 F3)
    (hR6a : ReconEnergyAt c x kc ℓ hW Cs) (hR6b : ReconCoeffAt c ℓ)
    (hmono : LiftSettingMonoStatement)
    (hR6c : ReconPartitionScaleAt c x (recPartC A ℓ CGl Cwl Ca) (recPartc A ℓ CGl Cwl Ca) Sb Cpx
      cgap Cg) (hR6d : ReconScaleAt c x cgap Cg)
    (hR6e : ∀ hle F1 F2 F3, ReconFluxSumAt c x kc Cfl hle F1 F2 F3)
    (hConv : ReconConvAt c x ℓ)
    (hC : max 1 cK ^ rKmax A ℓ * reconBillConst A.dW A.NT A.Dt (rAcl A) (rKmax A ℓ) (rm' A ℓ)
      (rkres A ℓ) (rNχ A ℓ) (rKlift A ℓ) (rLlift A ℓ) CGl Cwl Ca Sb Cgr Cs (max Cfl 0) (Cpx * Cs) ≤
        C)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (hr : ReconFluxRealizations c x kc F1 F2 F3)
    (hF1m : FluxMassLe (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (K := fun _ => kc)
      (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW) (Set.Icc c.tp (c.a + A.T₀)) F1
      (Cfl * c.covPrice * c.normF))
    (hF2m : FluxMassLe (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (K := fun _ => kc)
      (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW) (Set.Icc c.tp (c.a + A.T₀)) F2
      (Cfl * c.frontPrice * c.normF))
    (hF3m : FluxMassLe (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (K := fun _ => kc)
      (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW) (Set.Icc c.tp (c.a + A.T₀)) F3
      (Cfl * c.filterPrice * c.normF)) :
    ReconBound (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW (A.k₀ + ℓ) c.CcT c.aRep
      (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRStar cK M) (C * c.reconBill cgap Cg * c.normF) := by
  obtain ⟨aC, B₀C, lamC, pc, Jc, AD, CE, Aedge, Cstar, Θc, f0, hco⟩ :=
    reconCoarse_of_steps c x kc ℓ hW F1 F2 F3 Cs (hR5 F1 F2 F3) hr hF1m hF2m hF3m hR6a
      (hR2 hfX hfZ hent) CGl Cwl Ca Sb Cgr hR3
  obtain ⟨T, hfam⟩ := hR4 hdl
  obtain ⟨qs, qf, par, V, bM, hset⟩ := hR3
  have hsc := hR6d hdl
  have hTobs : 0 < rTobs c := by simp only [rTobs]; linarith
  have hle : c.tp ≤ c.tp + rTobs c := by linarith
  have hb := reconBound_of_gate c x kc ℓ hW F1 F2 F3 T qs qf par V bM CGl Cwl Ca Sb Cgr aC B₀C
    lamC pc Jc AD CE Aedge Cstar Θc f0 Cfl Cs Cpx cgap Cg hfam (hR2 hfX hfZ hent) hco hTobs
    (reconOrders_of A kc ℓ Jc pc hD2 hN1 hkc) hSb hCgr hCs hCpx hkc hkp hset hR6a hR6b hmono hdl
    hR6c hsc hle (hR6e hle F1 F2 F3 hF1m hF2m hF3m) hConv C hC
  exact hb


/-- **B-recon at a context from the steps.** -/
theorem termReconAt_of_steps
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ) (Cfl C cgap Cg : ℝ)
    (hD2 : 2 ≤ A.Dt) (hN1 : 1 ≤ A.NT) (hkc : rm' A ℓ + rkres A ℓ + A.NT + 4 ≤ kc)
    (hkp : rpord A ℓ ≤ kc + (A.NT + A.Dt))
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (hfX : rKlift A ℓ + A.Dt + 2 ≤ sXT) (hfZ : max (rLlift A ℓ + 1) (rLlift A ℓ + 2) ≤ sZT)
    (hent : c.aM + ocTauP c.D.α c.D.q c.D.Λ M ≤ c.tp) (hdl : c.tp < c.a + A.T₀)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr Cs Cpx : ℝ) (hSb : 0 ≤ Sb) (hCgr : 0 ≤ Cgr) (hCs : 0 ≤ Cs)
    (hCpx : 0 ≤ Cpx)
    (hR2 : ReconSeqStep c x ℓ) (hR3 : ReconSettingAt c x ℓ CGl Cwl Ca Sb Cgr)
    (hR4 : ReconFamilyStep c ℓ) (hR5 : ∀ F1 F2 F3, ReconCoarseAt c x kc ℓ hW F1 F2 F3)
    (hR6a : ReconEnergyAt c x kc ℓ hW Cs) (hR6b : ReconCoeffAt c ℓ)
    (hmono : LiftSettingMonoStatement)
    (hR6c : ReconPartitionScaleAt c x (recPartC A ℓ CGl Cwl Ca) (recPartc A ℓ CGl Cwl Ca) Sb Cpx
      cgap Cg) (hR6d : ReconScaleAt c x cgap Cg)
    (hR6e : ∀ hle F1 F2 F3, ReconFluxSumAt c x kc Cfl hle F1 F2 F3)
    (hConv : ReconConvAt c x ℓ)
    (hC : max 1 cK ^ rKmax A ℓ * reconBillConst A.dW A.NT A.Dt (rAcl A) (rKmax A ℓ) (rm' A ℓ)
      (rkres A ℓ) (rNχ A ℓ) (rKlift A ℓ) (rLlift A ℓ) CGl Cwl Ca Sb Cgr Cs (max Cfl 0) (Cpx * Cs) ≤
        C) :
    TermReconAt c x kc ℓ Cfl C cgap Cg := by
  intro h2a h2b h3
  obtain ⟨F1, hF1r, hF1m⟩ := h2a
  obtain ⟨F2, hF2r, hF2m⟩ := h2b
  obtain ⟨F3, hF3r, hF3m⟩ := h3
  exact termReconAt_of_flux c x kc ℓ Cfl C cgap Cg hD2 hN1 hkc hkp hW hfX hfZ hent hdl CGl Cwl Ca Sb Cgr Cs Cpx hSb hCgr hCs hCpx hR2 hR3 hR4 hR5 hR6a hR6b hmono hR6c hR6d hR6e hConv hC F1 F2 F3 ⟨hF1r, hF2r, hF3r⟩ hF1m hF2m hF3m

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! **The terminal reconstruction with the prefix of `entry_terminal_residual`**.

Each named step is stated with the prefix `ReconPrefix` of
`entry_terminal_residual`, with its uniform constants (`κ`) chosen after the plan and the weak and
preparation constants and before `j₀` and `M`. `ReconPrefix.and` joins two steps (thresholds and
floors by maxima, carrier starts by `IsCarrierStart.mono`); `termRecon_of_steps` gives
`TermReconStatement` from the eleven steps (lift sequences, lift settings, family, coarse, energy, coefficients, scale facts, flux sum, conversion, partition and the times step), with
`C₀ = max(1, c_K)^{K_max}·reconBillConst`, the coarse order `k_c ≥ m' + k_res + N_T + 4`, the floors
`K_out ≥ k_c + 1 + N_T + D_t + 2p_T`, `s_X ≥ K_lift + D_t + 2`, `s_Z ≥ L_lift + 2`.

Degenerate cases:
- `ℓ = 0`: the statement of the terminal residual.
- One step with `κ = Unit`: the prefix is that of `entry_terminal_residual` without constants.
- Constant order: `C₀` depends on `ℓ`, `A`, `c_K`, `C_fl` and the step constants, never on `j₀` or `M`. -/

/-- **The prefix of the steps of B-recon.** The prefix of `entry_terminal_residual` (as in
`TermResPrefix`, without the flux constant and with `ℓ` outermost) around a predicate on the context,
the auxiliary data, the coarse order `k_c`, the offset `ℓ` and the step constants `k : κ`. -/
def ReconPrefix {κ : Type}
    (Q : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℕ → κ → Prop) : Prop :=
  ∀ ℓ : ℕ, ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∃ kc₀ : ℕ, ∀ kc : ℕ, kc₀ ≤ kc →
  ∃ (SX SZ Kfloor : ℕ), ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT → ∀ Kout : ℕ, Kfloor ≤ Kout →
  ∃ Kneed : ℕ,
  ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (_ : A.Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
    Kneed ≤ Kw → A.L0w ≤ Lt → A.LpT ≤ Lt → Lt + 1 ≤ 2 * (nW : ℕ) →
    IsTerminalKernelOrders nW A.LoT A.LfT A.LpT A.Lpr A.Lc A.Lf →
    0 < cr → cr ≤ 1 → cr = 1 → kS.cr = cr → 0 < kS.c₀ →
    Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
  ∀ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
    IsWeakAllocation kW kS Lt →
  ∀ (cP CP cHP Cw Ce : ℝ) (cker : ℕ → ℝ), 0 < cP →
  ∃ k : κ, ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
  ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHt Υt j₀ →
  ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
  ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c), Q c x kc ℓ k

/-- **Join of two steps.** -/
theorem ReconPrefix.and {κ₁ κ₂ : Type}
    {P : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℕ → κ₁ → Prop}
    {Q : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℕ → κ₂ → Prop}
    (hP : ReconPrefix P) (hQ : ReconPrefix Q) :
    ReconPrefix (κ := κ₁ × κ₂) fun c x kc ℓ k => P c x kc ℓ k.1 ∧ Q c x kc ℓ k.2 := by
  intro ℓ X
  obtain ⟨Λ₁, h128, hP⟩ := hP ℓ X
  obtain ⟨Λ₂, -, hQ⟩ := hQ ℓ X
  refine ⟨max Λ₁ Λ₂, le_trans h128 (le_max_left _ _), fun A hΛ hV => ?_⟩
  have hΛ128 : 128 ≤ A.Λ := le_trans h128 (le_trans (le_max_left _ _) hΛ)
  obtain ⟨kc₁, hP⟩ := hP A (le_trans (le_max_left _ _) hΛ) hV
  obtain ⟨kc₂, hQ⟩ := hQ A (le_trans (le_max_right _ _) hΛ) hV
  refine ⟨max kc₁ kc₂, fun kc hkc => ?_⟩
  obtain ⟨SX₁, SZ₁, Kf₁, hP⟩ := hP kc (le_trans (le_max_left _ _) hkc)
  obtain ⟨SX₂, SZ₂, Kf₂, hQ⟩ := hQ kc (le_trans (le_max_right _ _) hkc)
  refine ⟨max SX₁ SX₂, max SZ₁ SZ₂, max Kf₁ Kf₂, fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn₁, hP⟩ := hP sXT sZT (le_trans (le_max_left _ _) hX) (le_trans (le_max_left _ _) hZ)
    Kout (le_trans (le_max_left _ _) hK)
  obtain ⟨Kn₂, hQ⟩ := hQ sXT sZT (le_trans (le_max_right _ _) hX) (le_trans (le_max_right _ _) hZ)
    Kout (le_trans (le_max_right _ _) hK)
  refine ⟨max Kn₁ Kn₂, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0
    hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP => ?_⟩
  have m1 : ∀ {n : ℕ}, max Kn₁ Kn₂ ≤ n → Kn₁ ≤ n := fun h => le_trans (le_max_left _ _) h
  have m2 : ∀ {n : ℕ}, max Kn₁ Kn₂ ≤ n → Kn₂ ≤ n := fun h => le_trans (le_max_right _ _) h
  obtain ⟨k₁, CH₁, Υ₁, hCH₁, hΥ₁, hP⟩ :=
    hP Kw Lt nW hk₀w hLw cr kS (m1 hKn) hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 (m1 hKs)
      (m1 hKan) (m1 hLan) (m1 hJm) cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP
  obtain ⟨k₂, CH₂, Υ₂, hCH₂, hΥ₂, hQ⟩ :=
    hQ Kw Lt nW hk₀w hLw cr kS (m2 hKn) hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 (m2 hKs)
      (m2 hKan) (m2 hLan) (m2 hJm) cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP
  refine ⟨(k₁, k₂), max CH₁ CH₂, max Υ₁ Υ₂, le_trans hCH₁ (le_max_left _ _),
    lt_of_lt_of_le hΥ₁ (le_max_left _ _), fun j₀ hj₀ => ?_⟩
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  have hAnn : ∀ k, 0 ≤ ocA X.α X.q A.Λ k := fun k =>
    Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _
  have hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q A.Λ k := fun k =>
    (Construction.Stream.ocTauPP_pos hΛ1).le
  have hj₁ : IsCarrierStart X.α X.q A.Λ A.bw CH₁ Υ₁ j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCH₁)
      hΥ₁.le hj₀
  have hj₂ : IsCarrierStart X.α X.q A.Λ A.bw CH₂ Υ₂ j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCH₂)
      hΥ₂.le hj₀
  obtain ⟨M₁, hP⟩ := hP j₀ hj₁
  obtain ⟨M₂, hQ⟩ := hQ j₀ hj₂
  exact ⟨max M₁ M₂, fun M hM c x =>
    ⟨hP M (le_trans (le_max_left _ _) hM) c x, hQ M (le_trans (le_max_right _ _) hM) c x⟩⟩

/-- **Monotonicity of the prefix** in the predicate, with a map of the constants. -/
theorem ReconPrefix.mono {κ₁ κ₂ : Type}
    {P : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℕ → κ₁ → Prop}
    {Q : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℕ → κ₂ → Prop}
    (f : κ₁ → κ₂)
    (himp : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ) (k : κ₁), P c x kc ℓ k → Q c x kc ℓ (f k))
    (hP : ReconPrefix P) : ReconPrefix Q := by
  intro ℓ X
  obtain ⟨Λ₀, h128, hP⟩ := hP ℓ X
  refine ⟨Λ₀, h128, fun A hΛ hV => ?_⟩
  obtain ⟨kc₀, hP⟩ := hP A hΛ hV
  refine ⟨kc₀, fun kc hkc => ?_⟩
  obtain ⟨SX, SZ, Kf, hP⟩ := hP kc hkc
  refine ⟨SX, SZ, Kf, fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn, hP⟩ := hP sXT sZT hX hZ Kout hK
  refine ⟨Kn, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 hKs hKan
    hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP => ?_⟩
  obtain ⟨k, CH, Υ, hCH, hΥ, hP⟩ :=
    hP Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 hKs hKan hLan hJm
      cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP
  refine ⟨f k, CH, Υ, hCH, hΥ, fun j₀ hj₀ => ?_⟩
  obtain ⟨M₀, hP⟩ := hP j₀ hj₀
  exact ⟨M₀, fun M hM c x => himp c x kc ℓ k (hP M hM c x)⟩

/-- **The prefix with `ℓ` after the data**: `Λ₀` is uniform in `ℓ`, so a
step can be instantiated at an offset `ℓ` chosen after `k_c` (later steps use the grading of the lift settings at
orders that grow with `k_c`). Otherwise as `ReconPrefix`. The prefix of `entry_terminal_residual` (as in
`TermResPrefix`, without the flux constant and with `ℓ` outermost) around a predicate on the context,
the auxiliary data, the coarse order `k_c`, the offset `ℓ` and the step constants `k : κ`. -/
def ReconPrefixU {κ : Type}
    (Q : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℕ → κ → Prop) : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∀ ℓ : ℕ, ∃ kc₀ : ℕ, ∀ kc : ℕ, kc₀ ≤ kc →
  ∃ (SX SZ Kfloor : ℕ), ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT → ∀ Kout : ℕ, Kfloor ≤ Kout →
  ∃ Kneed : ℕ,
  ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (_ : A.Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
    Kneed ≤ Kw → A.L0w ≤ Lt → A.LpT ≤ Lt → Lt + 1 ≤ 2 * (nW : ℕ) →
    IsTerminalKernelOrders nW A.LoT A.LfT A.LpT A.Lpr A.Lc A.Lf →
    0 < cr → cr ≤ 1 → cr = 1 → kS.cr = cr → 0 < kS.c₀ →
    Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
  ∀ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
    IsWeakAllocation kW kS Lt →
  ∀ (cP CP cHP Cw Ce : ℝ) (cker : ℕ → ℝ), 0 < cP →
  ∃ k : κ, ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
  ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHt Υt j₀ →
  ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
  ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c), Q c x kc ℓ k

/-- **Join of two uniform steps.** -/
theorem ReconPrefixU.and {κ₁ κ₂ : Type}
    {P : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℕ → κ₁ → Prop}
    {Q : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℕ → κ₂ → Prop}
    (hP : ReconPrefixU P) (hQ : ReconPrefixU Q) :
    ReconPrefixU (κ := κ₁ × κ₂) fun c x kc ℓ k => P c x kc ℓ k.1 ∧ Q c x kc ℓ k.2 := by
  intro X
  obtain ⟨Λ₁, h128, hP⟩ := hP X
  obtain ⟨Λ₂, -, hQ⟩ := hQ X
  refine ⟨max Λ₁ Λ₂, le_trans h128 (le_max_left _ _), fun A hΛ hV ℓ => ?_⟩
  have hΛ128 : 128 ≤ A.Λ := le_trans h128 (le_trans (le_max_left _ _) hΛ)
  obtain ⟨kc₁, hP⟩ := hP A (le_trans (le_max_left _ _) hΛ) hV ℓ
  obtain ⟨kc₂, hQ⟩ := hQ A (le_trans (le_max_right _ _) hΛ) hV ℓ
  refine ⟨max kc₁ kc₂, fun kc hkc => ?_⟩
  obtain ⟨SX₁, SZ₁, Kf₁, hP⟩ := hP kc (le_trans (le_max_left _ _) hkc)
  obtain ⟨SX₂, SZ₂, Kf₂, hQ⟩ := hQ kc (le_trans (le_max_right _ _) hkc)
  refine ⟨max SX₁ SX₂, max SZ₁ SZ₂, max Kf₁ Kf₂, fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn₁, hP⟩ := hP sXT sZT (le_trans (le_max_left _ _) hX) (le_trans (le_max_left _ _) hZ)
    Kout (le_trans (le_max_left _ _) hK)
  obtain ⟨Kn₂, hQ⟩ := hQ sXT sZT (le_trans (le_max_right _ _) hX) (le_trans (le_max_right _ _) hZ)
    Kout (le_trans (le_max_right _ _) hK)
  refine ⟨max Kn₁ Kn₂, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0
    hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP => ?_⟩
  have m1 : ∀ {n : ℕ}, max Kn₁ Kn₂ ≤ n → Kn₁ ≤ n := fun h => le_trans (le_max_left _ _) h
  have m2 : ∀ {n : ℕ}, max Kn₁ Kn₂ ≤ n → Kn₂ ≤ n := fun h => le_trans (le_max_right _ _) h
  obtain ⟨k₁, CH₁, Υ₁, hCH₁, hΥ₁, hP⟩ :=
    hP Kw Lt nW hk₀w hLw cr kS (m1 hKn) hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 (m1 hKs)
      (m1 hKan) (m1 hLan) (m1 hJm) cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP
  obtain ⟨k₂, CH₂, Υ₂, hCH₂, hΥ₂, hQ⟩ :=
    hQ Kw Lt nW hk₀w hLw cr kS (m2 hKn) hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 (m2 hKs)
      (m2 hKan) (m2 hLan) (m2 hJm) cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP
  refine ⟨(k₁, k₂), max CH₁ CH₂, max Υ₁ Υ₂, le_trans hCH₁ (le_max_left _ _),
    lt_of_lt_of_le hΥ₁ (le_max_left _ _), fun j₀ hj₀ => ?_⟩
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  have hAnn : ∀ k, 0 ≤ ocA X.α X.q A.Λ k := fun k =>
    Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _
  have hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q A.Λ k := fun k =>
    (Construction.Stream.ocTauPP_pos hΛ1).le
  have hj₁ : IsCarrierStart X.α X.q A.Λ A.bw CH₁ Υ₁ j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCH₁)
      hΥ₁.le hj₀
  have hj₂ : IsCarrierStart X.α X.q A.Λ A.bw CH₂ Υ₂ j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCH₂)
      hΥ₂.le hj₀
  obtain ⟨M₁, hP⟩ := hP j₀ hj₁
  obtain ⟨M₂, hQ⟩ := hQ j₀ hj₂
  exact ⟨max M₁ M₂, fun M hM c x =>
    ⟨hP M (le_trans (le_max_left _ _) hM) c x, hQ M (le_trans (le_max_right _ _) hM) c x⟩⟩

/-- **Monotonicity of the uniform prefix.** -/
theorem ReconPrefixU.mono {κ₁ κ₂ : Type}
    {P : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℕ → κ₁ → Prop}
    {Q : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℕ → κ₂ → Prop}
    (f : κ₁ → κ₂)
    (himp : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ) (k : κ₁), P c x kc ℓ k → Q c x kc ℓ (f k))
    (hP : ReconPrefixU P) : ReconPrefixU Q := by
  intro X
  obtain ⟨Λ₀, h128, hP⟩ := hP X
  refine ⟨Λ₀, h128, fun A hΛ hV ℓ => ?_⟩
  obtain ⟨kc₀, hP⟩ := hP A hΛ hV ℓ
  refine ⟨kc₀, fun kc hkc => ?_⟩
  obtain ⟨SX, SZ, Kf, hP⟩ := hP kc hkc
  refine ⟨SX, SZ, Kf, fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn, hP⟩ := hP sXT sZT hX hZ Kout hK
  refine ⟨Kn, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 hKs hKan
    hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP => ?_⟩
  obtain ⟨k, CH, Υ, hCH, hΥ, hP⟩ :=
    hP Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 hKs hKan hLan hJm
      cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP
  refine ⟨f k, CH, Υ, hCH, hΥ, fun j₀ hj₀ => ?_⟩
  obtain ⟨M₀, hP⟩ := hP j₀ hj₀
  exact ⟨M₀, fun M hM c x => himp c x kc ℓ k (hP M hM c x)⟩

/-- A uniform step is a step of B-recon. -/
theorem ReconPrefixU.toReconPrefix {κ : Type}
    {Q : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℕ → κ → Prop}
    (h : ReconPrefixU Q) : ReconPrefix Q := by
  intro ℓ X
  obtain ⟨Λ₀, h128, h⟩ := h X
  exact ⟨Λ₀, h128, fun A hΛ hV => h A hΛ hV ℓ⟩

/-! ### The steps with the prefix -/

/-- **The lift-sequence step** with the prefix. -/
def TermReconSeqStatement : Prop :=
  ReconPrefixU (κ := Unit) fun c x _ ℓ _ => ReconSeqStep c x ℓ

/-- **The lift-setting step** with the prefix: the lift-setting constants `(C_Gl, C_w, C_a, S_b, C_g)` before the level. -/
def TermReconSettingStatement : Prop :=
  ReconPrefixU (κ := {k : (ℕ → ℝ) × (ℕ → ℝ) × ℝ × ℝ × ℝ // 0 ≤ k.2.2.2.1 ∧ 0 ≤ k.2.2.2.2})
    fun c x _ ℓ k => ReconSettingAt c x ℓ k.1.1 k.1.2.1 k.1.2.2.1 k.1.2.2.2.1 k.1.2.2.2.2

/-- **The family step** with the prefix. -/
def TermReconFamilyStatement : Prop :=
  ReconPrefix (κ := Unit) fun c _ _ ℓ _ => ReconFamilyStep c ℓ

/-- **The coarse step** with the prefix. -/
def TermReconCoarseStatement : Prop :=
  ReconPrefix (κ := Unit) fun c x kc ℓ _ => ∀ hW F1 F2 F3, ReconCoarseAt c x kc ℓ hW F1 F2 F3

/-- **The energy step** with the prefix: the energy constant `C_s`. -/
def TermReconEnergyStatement : Prop :=
  ReconPrefix (κ := {Cs : ℝ // 0 ≤ Cs}) fun c x kc ℓ Cs => ∀ hW, ReconEnergyAt c x kc ℓ hW Cs.1

/-- **The coefficient step** with the prefix. -/
def TermReconCoeffStatement : Prop :=
  ReconPrefix (κ := Unit) fun c _ _ ℓ _ => ReconCoeffAt c ℓ

/-- **The scale of the partition bound** with the prefix: for the constants `(C_gate, c_gate)` of
`partition_window_input` and the grading `S_b` (inserted before the step's own constants: they
come from the lift-setting constants through `partition_window_input`), constants
`(C_px, c_gap, C_g)` with `ReconPartitionScaleAt` for `M` large. -/
def TermReconPartitionStatement : Prop :=
  ∀ _ℓ : ℕ, ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∃ kc₀ : ℕ, ∀ kc : ℕ, kc₀ ≤ kc →
  ∃ (SX SZ Kfloor : ℕ), ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT → ∀ Kout : ℕ, Kfloor ≤ Kout →
  ∃ Kneed : ℕ,
  ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (_ : A.Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
    Kneed ≤ Kw → A.L0w ≤ Lt → A.LpT ≤ Lt → Lt + 1 ≤ 2 * (nW : ℕ) →
    IsTerminalKernelOrders nW A.LoT A.LfT A.LpT A.Lpr A.Lc A.Lf →
    0 < cr → cr ≤ 1 → cr = 1 → kS.cr = cr → 0 < kS.c₀ →
    Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
  ∀ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
    IsWeakAllocation kW kS Lt →
  ∀ (cP CP cHP Cw Ce : ℝ) (cker : ℕ → ℝ), 0 < cP →
  ∀ (Cgate cgate Sb : ℝ), 0 ≤ Cgate → 0 < cgate → 0 ≤ Sb →
  ∃ (Cpx cgap Cg : ℝ), 0 ≤ Cpx ∧ 0 < cgap ∧ 0 ≤ Cg ∧ ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
  ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHt Υt j₀ →
  ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
  ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c), ReconPartitionScaleAt c x Cgate cgate Sb Cpx cgap Cg

/-- **The scale-facts step** with the prefix. -/
def TermReconScaleStatement : Prop :=
  ReconPrefix (κ := Unit) fun c x _ _ _ => ∀ cgap Cg, 0 < cgap → 0 ≤ Cg → ReconScaleAt c x cgap Cg

/-- **The flux-sum step** with the prefix. -/
def TermReconFluxSumStatement : Prop :=
  ReconPrefix (κ := Unit) fun c x kc _ _ => ∀ Cfl hle F1 F2 F3, ReconFluxSumAt c x kc Cfl hle F1 F2 F3

/-- **The conversion step** with the prefix. -/
def TermReconConvStatement : Prop :=
  ReconPrefix (κ := Unit) fun c x _ ℓ _ => ReconConvAt c x ℓ

/-- **The entrance and the deadline at a context**: for `M` large,
`a_M + τ'_M ≤ t_p` (from the preparation's `a_M + c_P τ''_M ≤ t_p`, `τ'_M = τ''_M / L_M`,
`L_M → ∞`; `ocTauP_le_mul_ocTauPP_eventually`) and `t_p < a + T₀` (the deadline). -/
def TermReconTimesStatement : Prop :=
  ReconPrefixU (κ := Unit) fun {_} {A} {_ _ _ _ _} {_} {_} {_} {_} {_ _ _ _ _ _} {_} {_ _ _ _ _} {_}
    {_} {M} c _ _ _ _ => c.aM + ocTauP c.D.α c.D.q c.D.Λ M ≤ c.tp ∧ c.tp < c.a + A.T₀

/-! ### Three groups of steps -/

section Groups

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The lift side at a context: lift sequences, lift settings, family side and conversion. -/
def ReconLiftSideAt
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c) (_kc ℓ : ℕ)
    (k : {k : (ℕ → ℝ) × (ℕ → ℝ) × ℝ × ℝ × ℝ // 0 ≤ k.2.2.2.1 ∧ 0 ≤ k.2.2.2.2}) : Prop :=
  ReconSeqStep c x ℓ ∧ ReconSettingAt c x ℓ k.1.1 k.1.2.1 k.1.2.2.1 k.1.2.2.2.1 k.1.2.2.2.2 ∧
    ReconFamilyStep c ℓ ∧ ReconConvAt c x ℓ

/-- The coarse side at a context: coarse step, energy and flux sum. -/
def ReconCoarseSideAt
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ) (k : {Cs : ℝ // 0 ≤ Cs}) : Prop :=
  (∀ hW F1 F2 F3, ReconCoarseAt c x kc ℓ hW F1 F2 F3) ∧ (∀ hW, ReconEnergyAt c x kc ℓ hW k.1) ∧
    ∀ Cfl hle F1 F2 F3, ReconFluxSumAt c x kc Cfl hle F1 F2 F3

/-- The analytic side at a context: coefficients, scale facts and the times (the scale of the
partition bound is joined separately: its constants depend on those of the lift settings). -/
def ReconAnalyticSideAt
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c) (_kc ℓ : ℕ) (_k : Unit) : Prop :=
  ReconCoeffAt c ℓ ∧ (∀ cgap Cg, 0 < cgap → 0 ≤ Cg → ReconScaleAt c x cgap Cg) ∧
    c.aM + ocTauP c.D.α c.D.q c.D.Λ M ≤ c.tp ∧ c.tp < c.a + A.T₀

end Groups

/-- The lift side from the lift-sequence, lift-setting, family and conversion steps. -/
theorem reconLiftSide_of (h2 : TermReconSeqStatement) (h3 : TermReconSettingStatement)
    (h4 : TermReconFamilyStatement) (hcv : TermReconConvStatement) :
    ReconPrefix ReconLiftSideAt :=
  ReconPrefix.mono (fun k => k.2.1) (fun _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩)
    (h2.toReconPrefix.and (h3.toReconPrefix.and (h4.and hcv)))

/-- The coarse side from the coarse, energy and flux-sum steps. -/
theorem reconCoarseSide_of (h5 : TermReconCoarseStatement) (h6a : TermReconEnergyStatement)
    (h6e : TermReconFluxSumStatement) : ReconPrefix ReconCoarseSideAt :=
  ReconPrefix.mono (fun k => k.2.1) (fun _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2⟩)
    (h5.and (h6a.and h6e))

/-- The analytic side from the coefficient and scale-facts steps and the times. -/
theorem reconAnalyticSide_of (h6b : TermReconCoeffStatement) (h6d : TermReconScaleStatement)
    (ht : TermReconTimesStatement) : ReconPrefix ReconAnalyticSideAt :=
  ReconPrefix.mono (fun _ => ()) (fun _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩)
    (h6b.and (h6d.and ht.toReconPrefix))

/-- **The terminal reconstruction from the three groups of steps, the scale of the partition bound
and monotonicity of lift settings.** The constants of `partition_window_input` are computed from the
lift-setting constants (`recPartC`, `recPartc`) and passed to the scale of the partition bound
before its constants. -/
theorem termRecon_of_sides (hL : ReconPrefix ReconLiftSideAt)
    (hC : ReconPrefix ReconCoarseSideAt) (hN : ReconPrefix ReconAnalyticSideAt)
    (h6c : TermReconPartitionStatement) (hmono : LiftSettingMonoStatement) :
    TermReconStatement := by
  have hall := hL.and (hC.and hN)
  intro ℓ X
  obtain ⟨Λ₀, h128, hall⟩ := hall ℓ X
  obtain ⟨Λ₆, -, h6⟩ := h6c ℓ X
  refine ⟨max Λ₀ Λ₆, le_trans h128 (le_max_left _ _), fun A hΛ hV => ?_⟩
  have hΛ128 : 128 ≤ A.Λ := le_trans h128 (le_trans (le_max_left _ _) hΛ)
  obtain ⟨kc₀, hall⟩ := hall A (le_trans (le_max_left _ _) hΛ) hV
  obtain ⟨kc₆, h6⟩ := h6 A (le_trans (le_max_right _ _) hΛ) hV
  refine ⟨max (max kc₀ kc₆) (max (rm' A ℓ + rkres A ℓ + A.NT + 4) (rpord A ℓ)),
    fun kc hkc => ?_⟩
  have hkc1 : kc₀ ≤ kc := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hkc
  have hkc6 : kc₆ ≤ kc := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hkc
  have hkcm : rm' A ℓ + rkres A ℓ + A.NT + 4 ≤ kc :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hkc
  have hkp : rpord A ℓ ≤ kc + (A.NT + A.Dt) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans hkc (Nat.le_add_right _ _))
  obtain ⟨SX, SZ, Kf, hall⟩ := hall kc hkc1
  obtain ⟨SX₆, SZ₆, Kf₆, h6⟩ := h6 kc hkc6
  refine ⟨max (max SX SX₆) (rKlift A ℓ + A.Dt + 2), max (max SZ SZ₆) (rLlift A ℓ + 2),
    max (max Kf Kf₆) (kc + 1 + (A.NT + A.Dt) + 2 * A.pT), fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn, hall⟩ := hall sXT sZT (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX)
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hZ) Kout
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hK)
  obtain ⟨Kn₆, h6⟩ := h6 sXT sZT (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX)
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hZ) Kout
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hK)
  refine ⟨max Kn Kn₆, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 hKs
    hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP Cfl => ?_⟩
  have m1 : ∀ {n : ℕ}, max Kn Kn₆ ≤ n → Kn ≤ n := fun h => le_trans (le_max_left _ _) h
  have m2 : ∀ {n : ℕ}, max Kn Kn₆ ≤ n → Kn₆ ≤ n := fun h => le_trans (le_max_right _ _) h
  obtain ⟨k, CH, Υ, hCH, hΥ, hall⟩ :=
    hall Kw Lt nW hk₀w hLw cr kS (m1 hKn) hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 (m1 hKs)
      (m1 hKan) (m1 hLan) (m1 hJm) cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP
  obtain ⟨Cpx, cgap, Cg, hCpx, hcgap, hCg, CH₆, Υ₆, hCH₆, hΥ₆, h6⟩ :=
    h6 Kw Lt nW hk₀w hLw cr kS (m2 hKn) hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 (m2 hKs)
      (m2 hKan) (m2 hLan) (m2 hJm) cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP
      (recPartC A ℓ k.1.1.1 k.1.1.2.1 k.1.1.2.2.1) (recPartc A ℓ k.1.1.1 k.1.1.2.1 k.1.1.2.2.1)
      k.1.1.2.2.2.1 (recPartC_nonneg _ _ _ _ _) (recPartc_pos _ _ _ _ _) k.1.2.1
  set C₀ : ℝ := max 1 cK ^ rKmax A ℓ * reconBillConst A.dW A.NT A.Dt (rAcl A) (rKmax A ℓ)
    (rm' A ℓ) (rkres A ℓ) (rNχ A ℓ) (rKlift A ℓ) (rLlift A ℓ) k.1.1.1 k.1.1.2.1 k.1.1.2.2.1
    k.1.1.2.2.2.1 k.1.1.2.2.2.2 k.2.1.1 (max Cfl 0) (Cpx * k.2.1.1) with hC₀
  refine ⟨C₀, cgap, Cg, hcgap, max CH CH₆, max Υ Υ₆, le_trans hCH (le_max_left _ _),
    lt_of_lt_of_le hΥ (le_max_left _ _), fun C hC j₀ hj₀ => ?_⟩
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  have hAnn : ∀ k, 0 ≤ ocA X.α X.q A.Λ k := fun k =>
    Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _
  have hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q A.Λ k := fun k =>
    (Construction.Stream.ocTauPP_pos hΛ1).le
  have hj₁ : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCH)
      hΥ.le hj₀
  have hj₂ : IsCarrierStart X.α X.q A.Λ A.bw CH₆ Υ₆ j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCH₆)
      hΥ₆.le hj₀
  obtain ⟨M₀, hall⟩ := hall j₀ hj₁
  obtain ⟨M₆, h6⟩ := h6 j₀ hj₂
  refine ⟨max M₀ M₆, fun M hM c x => ?_⟩
  obtain ⟨⟨h2c, h3c, h4c, hcvc⟩, ⟨h5c, h6ac, h6ec⟩, ⟨h6bc, h6dc, hent, hdl⟩⟩ :=
    hall M (le_trans (le_max_left _ _) hM) c x
  have hD2 : 2 ≤ A.Dt := le_max_left _ _
  have hN1 : 1 ≤ A.NT := le_trans (by norm_num) (two_le_NT_of_valid A hV)
  have hKo : Kout ≤ A.Khat Kout := le_max_left _ _
  have hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT := by
    have := le_trans (le_max_right _ _) hK
    omega
  exact termReconAt_of_steps c x kc ℓ Cfl C _ _ hD2 hN1 hkcm hkp hW
    (le_trans (le_max_right _ _) hX) (max_le (by have := le_trans (le_max_right _ _) hZ; omega)
      (le_trans (le_max_right _ _) hZ)) hent hdl _ _ _ _ _ _ _ k.1.2.1 k.1.2.2 k.2.1.2
    hCpx h2c h3c h4c (fun F1 F2 F3 => h5c hW F1 F2 F3) (h6ac hW) h6bc hmono
    (h6 M (le_trans (le_max_right _ _) hM) c x) (h6dc _ _ hcgap hCg)
    (fun hle F1 F2 F3 => h6ec Cfl hle F1 F2 F3) hcvc hC

/-- **B-recon from its steps.** -/
theorem termRecon_of_steps (h2 : TermReconSeqStatement) (h3 : TermReconSettingStatement)
    (h4 : TermReconFamilyStatement) (h5 : TermReconCoarseStatement)
    (h6a : TermReconEnergyStatement) (h6b : TermReconCoeffStatement)
    (h6c : TermReconPartitionStatement) (hmono : LiftSettingMonoStatement)
    (h6d : TermReconScaleStatement) (h6e : TermReconFluxSumStatement)
    (hcv : TermReconConvStatement) (ht : TermReconTimesStatement) : TermReconStatement :=
  termRecon_of_sides (reconLiftSide_of h2 h3 h4 hcv) (reconCoarseSide_of h5 h6a h6e)
    (reconAnalyticSide_of h6b h6d ht) h6c hmono

end AVRegularity.EntryTerminal.Ingredients.Recon
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! **The coarse side of the window, split**.

The coarse side (`ReconCoarseAt`) needs three things:
- **Weak equation** (`TermCoarseWeakAt`): the coarse equation of `P_pZ` at the terminal menu. This is the
  content of `Frame.macroWeak` at the terminal frame,
  unfolded at the context: the classical representative `aRep` of `P_pZ` solves
  `(∂_t + 𝐛_{M-1}·∇)a - div(B∇a + F_macro a + F_mean) = 0` weakly on `[t_p, a + T₀]` against smooth
  periodic tests (the convention of `CoupledWeakIdentity`). `frame_transport_of_ingredients`
  gives it from its seven ingredients, a `NativeInput` of the
  terminal frame and the readout equation `Frame.readoutWeak`.
- **Letters** (`ReconLettersAt`): letters `(AD, CE)` presenting the glued means of the window
  (`IsMeanPresentation`), with the coarse setting (`IsCoarseSetting`) at the degree `p_c = 1` and the
  word length `J_c = 0` (so the initial order `N_c = k_c + (d_w + 3)(N_T + D_t + 12)` is fixed before
  the floors).
- **Conversion** (`ReconDefectConvAt`): the conversion. From the weak equation, the letters and the flux realizations,
  `IsCoarseDefect` of the window holds for `W = reconW`, `F_c = reconFc` and `f₀ = P_pZ(t_p)` truncated
  to `N_c`:
  - the macro flux is replaced by the letters' flux (equal divergences, `IsMeanPresentation`, after
  identifying the window's `gluedMean` with the menu's glued mean fluxes);
  - `F_mean = F_cov - F_filter - F_front` (`MenuMeanFluxSplitStatement`) and the realizations;
  - smooth periodic tests are extended to first-order tests by density (the argument of
    `coarseDefect_of_witness`);
  - classical fields become torus jets (`IsClassicalRep` of `P_pZ`).

`reconCoarseAt_of_parts` assembles the coarse side at a context; `termReconCoarse_of_parts` with
the prefix.

Degenerate cases:
- `p_T = 0`: `P_p = I`, `W = 𝖱Z`.
- A weak stage without edges: `CE = 0`, `F_macro` is the diagonal part only.
- `F1 = F2 = F3 = 0` with zero flux pieces: the coarse equation has no source. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

section Parts

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- The initial order of the coarse defect at `p_c = 1`, `J_c = 0`. -/
abbrev rNc (A : TermArgs X) (kc : ℕ) : ℕ := kc + (0 + A.dW + 3) * ((A.NT + A.Dt) + 8 * 1 + 4)

/-- **The weak equation at a context: the coarse equation of `P_pZ`** (the terminal instance of
`Frame.macroWeak`, unfolded): `aRep` solves the coarse equation with the macro flux of the menu and
the mean flux `F_mean`, weakly on `[t_p, a + T₀]` against smooth periodic tests. -/
def TermCoarseWeakAt (x : TermResAux c) : Prop :=
  ∀ w : CompIn c.Gw.comps, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀), ∀ φ : Vec 2 → ScalarH w.1.root,
    ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (c.D.κ (M - 1)) c.tp t
      (streamVel (c.D.Φ (M - 1))) (fun y => c.aRep t y w) (fun y => c.aRep c.tp y w) φ
      (fun k y => gradE φ y k) (fun s k y => gradE (fun y' => c.aRep s y' w) y k)
      (fun s y => toFluxL (menuMacroFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep
        w s y))
      (fun s y => toFluxL (menuMeanFluxF (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ
        (upsilonFlux (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ c.Gw c.Gt'
          (c.Gt'.retained M 1 A.RT) M 1 A.RT (c.D.eps (M - 1)) A.η₀ x.aZ x.aY) w s y))
      (fun _ _ => 0)

/-- The letters of the window at given data: the coarse setting at `p_c = 1`, `J_c = 0` and the
mean presentations of the window's glued means. -/
def ReconLettersBody (kc : ℕ) (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ) : Prop :=
  IsCoarseSetting c.tp (c.tp + rTobs c) (rRho c) (c.D.κ (M - 1)) aC B₀C lamC
    (streamVel (c.D.Φ (M - 1))) (A.NT + A.Dt) A.dW 1 0 kc ((A.NT + A.Dt) + 8 * 1 + 4)
    (kc + (0 + A.dW + 3) * ((A.NT + A.Dt) + 8 * 1 + 4))
    (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) AD CE (c.Gw.mass c.lawW) Aedge Cstar Θc ∧
  ∀ r ∈ Finset.range (A.dW + 1),
    IsMeanPresentation (Set.Icc c.tp (c.tp + rTobs c)) (A.NT + A.Dt) r AD CE
      (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M))
      (gluedMean (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
        (fun k => c.Gw.actualFamily.weight (oddSlotOf k))
        (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c)
        (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) A.NT r
        (fun k => rLiftData c k) c.CcT
        (fun k => ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
        (fun k => ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k)))

/-- **Letters for the window at a context.** -/
def ReconLettersAt (kc : ℕ) : Prop :=
  ∃ (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ),
    ReconLettersBody c kc aC B₀C lamC AD CE Aedge Cstar Θc

/-- **The conversion to the coarse defect at a context.** From the
coarse equation, letters presenting the glued means and the flux realizations, the
coarse defect of the window holds with `f₀ = P_pZ(t_p)` at the order `N_c`. -/
def ReconDefectConvAt (x : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    Prop :=
  TermCoarseWeakAt c x → ReconFluxRealizations c x kc F1 F2 F3 → ReconTimeRegAt c kc hW F1 F2 F3 →
  ReconSeqAt c ℓ → ∀ (CGl Cw : ℕ → ℝ) (Ca Sb Cg : ℝ), ReconSettingAt c x ℓ CGl Cw Ca Sb Cg →
  ∀ (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ),
    ReconLettersBody c kc aC B₀C lamC AD CE Aedge Cstar Θc →
    IsCoarseDefect c.tp (c.tp + rTobs c) (c.D.κ (M - 1)) (streamVel (c.D.Φ (M - 1)))
      (A.NT + A.Dt) A.dW kc (kc + (0 + A.dW + 3) * ((A.NT + A.Dt) + 8 * 1 + 4)) AD CE
      (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M))
      (fun v => truncateTorusHk hf (c.PZ v c.tp)) (reconW c kc hW) (reconFc c F1 F2 F3)

end Parts

/-- **The coarse side at a context from its parts.** -/
theorem reconCoarseAt_of_parts
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (hWk : TermCoarseWeakAt c x) (hL : ReconLettersAt c kc)
    (hD : ReconDefectConvAt c x kc ℓ hW hf F1 F2 F3) :
    ReconCoarseAt c x kc ℓ hW F1 F2 F3 := by
  intro hr hreg hseq CGl Cw' Ca Sb Cg hset
  obtain ⟨aC, B₀C, lamC, AD, CE, Aedge, Cstar, Θc, hlet⟩ := hL
  exact ⟨aC, B₀C, lamC, 1, 0, AD, CE, Aedge, Cstar, Θc, fun v => truncateTorusHk hf (c.PZ v c.tp),
    hlet.1, hD hWk hr hreg hseq CGl Cw' Ca Sb Cg hset aC B₀C lamC AD CE Aedge Cstar Θc hlet, hlet.2⟩

/-! ### With the prefix -/

/-- **The weak equation with the prefix** (`Frame.macroWeak` at the terminal frame). -/
def TermCoarseWeakStatement : Prop :=
  ReconPrefix (κ := Unit) fun c x _ _ _ => TermCoarseWeakAt c x

/-- **The letters with the prefix.** -/
def TermReconLettersStatement : Prop :=
  ReconPrefix (κ := Unit) fun c _ kc _ _ => ReconLettersAt c kc

/-- **The conversion with the prefix.** -/
def TermReconDefectConvStatement : Prop :=
  ReconPrefix (κ := Unit) fun c x kc ℓ _ => ∀ hW hf F1 F2 F3, ReconDefectConvAt c x kc ℓ hW hf F1 F2 F3

/-- The three parts of the coarse side at a context. -/
def ReconCoarsePartsAt
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ) (_k : Unit × Unit × Unit) : Prop :=
  TermCoarseWeakAt c x ∧ ReconLettersAt c kc ∧
    ∀ hW hf F1 F2 F3, ReconDefectConvAt c x kc ℓ hW hf F1 F2 F3

/-- **Monotonicity of the prefix with a raised `K_out` floor** `g A k_c`. -/
theorem ReconPrefix.mono_kout {κ₁ κ₂ : Type}
    {P : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℕ → κ₁ → Prop}
    {Q : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℕ → κ₂ → Prop}
    (g : ∀ {X : TermConstruction}, TermArgs X → ℕ → ℕ) (f : κ₁ → κ₂)
    (himp : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ) (k : κ₁), g A kc ≤ Kout →
        P c x kc ℓ k → Q c x kc ℓ (f k))
    (hP : ReconPrefix P) : ReconPrefix Q := by
  intro ℓ X
  obtain ⟨Λ₀, h128, hP⟩ := hP ℓ X
  refine ⟨Λ₀, h128, fun A hΛ hV => ?_⟩
  obtain ⟨kc₀, hP⟩ := hP A hΛ hV
  refine ⟨kc₀, fun kc hkc => ?_⟩
  obtain ⟨SX, SZ, Kf, hP⟩ := hP kc hkc
  refine ⟨SX, SZ, max Kf (g A kc), fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn, hP⟩ := hP sXT sZT hX hZ Kout (le_trans (le_max_left _ _) hK)
  refine ⟨Kn, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 hKs hKan
    hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP => ?_⟩
  obtain ⟨k, CH, Υ, hCH, hΥ, hP⟩ :=
    hP Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 hKs hKan hLan hJm
      cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP
  refine ⟨f k, CH, Υ, hCH, hΥ, fun j₀ hj₀ => ?_⟩
  obtain ⟨M₀, hP⟩ := hP j₀ hj₀
  exact ⟨M₀, fun M hM c x => himp c x kc ℓ k (le_trans (le_max_right _ _) hK) (hP M hM c x)⟩

/-- **The coarse side with the prefix from its three parts.** -/
theorem termReconCoarse_of_parts (hWk : TermCoarseWeakStatement)
    (hL : TermReconLettersStatement) (hD : TermReconDefectConvStatement) :
    TermReconCoarseStatement :=
  ReconPrefix.mono_kout (P := ReconCoarsePartsAt) (fun A kc => rNc A kc + 2 * A.pT) (fun _ => ())
    (fun {_} {A} {Kout} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} c x kc ℓ _ hg h => by
      intro hW F1 F2 F3
      have hKo : Kout ≤ A.Khat Kout := le_max_left _ _
      have hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT := by omega
      exact reconCoarseAt_of_parts c x kc ℓ hW hf F1 F2 F3 h.1 h.2.1 (h.2.2 hW hf F1 F2 F3))
    (ReconPrefix.mono (Q := ReconCoarsePartsAt) (fun k => k)
      (fun _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2⟩) (hWk.and (hL.and hD)))

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end
