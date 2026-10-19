-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
public import AVRegularity.Proofs.CascadeInvariants.Diag.LedgerCase

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the ledger of each path source from the standing facts of the passage.** For the
tag parameters `succProvParams D C_w c_r σ₀ η₀ N p`, the standing facts `StepFacts`, the constants
`LedgerConsts` and one threshold `ledgerThr ≤ C_w`, the conclusion of the ledger holds for a new
identity whose source is
* a direct transport (`ledger_copyDir`);
* a quadratic conversion of a path of at most `r_H` edges (`ledger_copyQuad`);
* a mean letter of cell degree `3 ≤ n ≤ n_H` along such a path (`ledger_letterMean`): its
  normalization `ε_{m-1}^{-η₀}` and its gain `(d_*/ρ)^{n-2} ≤ C ε_{m-1}^δ` give the tag
  `C_w ε_{m-1}^{δ-η₀}`, the reserve of the lift is the grade step of the birth, and the fresh
  length `c_r ρ` costs `c_r^{-D_m}`;
* a covariance letter with `a + a' ≥ 1` (`ledger_letterCov`): the gain is
  `(‖𝖧‖/ρ²)^{a+a'} ≤ C ε_{m-1}^δ`.
Each is the corresponding case lemma with its hypotheses read off the standing facts. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {kI : InvConsts}
variable {Cw cr σ₀ η₀ : ℝ} {N p : ℕ} {G G' : GenStage D hr Dm b j₀} {Cu : ℝ}
  {κc : MajConsts} {ar Δ K W Cold Wr : ℝ} {S Kg Kd : ℝ≥0}

/-- The slow-flux constant of a lift over the certified old coefficients is at most the largest
one of the menu. (The context is given explicitly: the constants agree by definition.) -/
theorem fluxXc_oldCtx_le_fluxMax (hcert : G.OldCert G.exports (compReserve kI) kI.Lstar 1) (κc : MajConsts) (Δ μ₀ : ℝ)
    (S Kg Kd : ℝ≥0) {rH nH h n : ℕ} (hh : h ≤ rH) (hn : n ≤ nH) :
    UEnv.fluxXc (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm (liftB (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm) h n ≤
      fluxMax κc S Kg Kd Dm rH nH :=
  fluxXc_le_fluxMax (X := oldCtx hcert κc Δ μ₀ S Kg Kd) (κ := κc) (S := S) (Kg := Kg) (Kd := Kd)
    (SameConsts.mk rfl rfl rfl) Dm hh hn

open scoped Classical in
/-- **The ledger of a direct transport.** -/
theorem ledger_copyDir (hF : StepFacts kI G G' (succProvParams D Cw cr σ₀ η₀ N p) Cu)
    (hC : LedgerConsts b Dm kI.Lstar κc ar Δ K W Cold Wr S Kg Kd) (hΔD : (Dm : ℝ) * Δ ≤ 1)
    {v₀ u₀ : CompIn G.comps} (γ₀ : G.fam.Γ v₀ u₀)
    (hval : 3 ≤ (G.fam.identity v₀ u₀ γ₀).maxOrder) (ρ s₀ : ℝ) (t₀ : List WordLetter)
    (Cc : ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin ((SuccSource.copyDir t₀ v₀ u₀ γ₀).pathLen + 1)) (fun _ => ℝ))
    {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u')
    (hprov : G'.prov v' u' γ' = (SuccSource.copyDir t₀ v₀ u₀ γ₀).prov G.level)
    (htgt : (SuccSource.copyDir t₀ v₀ u₀ γ₀).tgtComp G.level = v'.1)
    (hflux : ∀ (q : OddSlot) (c : StageCtx D b j₀ G'.level q) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
      G'.fam.flux q c v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level q.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
        then transferAt D G.level q.1 ((SuccSource.copyDir t₀ v₀ u₀ γ₀).lam G.level η₀)
          (((SuccSource.copyDir t₀ v₀ u₀ γ₀).prov G.level).tags
            (succProvParams D Cw cr σ₀ η₀ N p)).order
          ((SuccSource.copyDir t₀ v₀ u₀ γ₀).fluxOp ρ s₀ Cc) t
          (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0)
    {rH nH : ℕ} (hcr0 : 0 < cr) (hcr1 : cr ≤ 1)
    (hthr : ledgerThr Dm rH nH p K W Cold Wr Δ cr Cu (fluxMax κc S Kg Kd Dm rH nH)
      (covKMax S Kg nH p) ≤ Cw) :
    LedgerConcl kI κc G' v' u' γ' := by
  obtain ⟨hmax', hlen', hsize'⟩ := record_of_dir hF.hGT hF.hGT' γ₀ γ' (m := G.level) hprov
  have hDγ : (((SuccSource.copyDir t₀ v₀ u₀ γ₀).prov G.level).tags
      (succProvParams D Cw cr σ₀ η₀ N p)).order = (G.fam.identity v₀ u₀ γ₀).maxOrder :=
    (Prov.tags_dir_all _ G.level (G.prov v₀ u₀ γ₀)).1.trans (hF.hGT v₀ u₀ γ₀).2.symm
  have hres1 := compReserve_le_one kI v'.1
  have hT := ledgerThr_ge (rH := rH) (nH := nH) (p := p) (cr := cr)
    (FM := fluxMax κc S Kg Kd Dm rH nH) (KM := covKMax S Kg nH p) hC.hK0 hC.hW0 hC.hC0 hC.hWr0
    hC.hΔ hF.hCu (q := 1) (u := 1) (f := 1) (dp := 1) (e := 1) zero_le_one zero_le_one
    zero_le_one zero_le_one zero_le_one (one_le_crInv_pow hcr0 hcr1 Dm)
    (by rw [mul_one]; exact one_le_pow₀ hF.hCu) (one_le_KF _ _)
    (one_le_pow₀ (by have : (0 : ℝ) ≤ Dm := Nat.cast_nonneg _; linarith))
  have hA := dirConst_le_ledgerA (Dm := Dm) hC.hK0 hC.hW0 hC.hC0 hC.hWr0 hC.hΔ
  exact copyDir_ledger_case hF.hζ hF.hΛ1 hF.hb hF.hstart G G' hF.hcert.oldCert hF.hexpU hF.hexp hF.hlev
    γ₀ ρ s₀ t₀ Cc γ' _ hflux hDγ (hmax'.trans hDγ.symm) hlen' (Cw := Cw) hsize'
    ((hF.hℓ v₀ u₀ γ₀ hval).trans hF.heps_le)
    (by rw [← htgt]; exact compReserve_succComp_le kI G.level v₀.1 t₀)
    hF.hεn (hF.hεpos _) (hF.hεle _) (hF.hεpos _) hF.hτ hF.hκ' hF.hsc.hκ0.le hF.hκκ κc hC.ha3
    hC.hΔ (by linarith) hC.hK0 hC.hW0 hC.hC0 hC.hWr0 hC.hK hC.hW hC.hCold hC.hWr
    (by linarith)

open scoped Classical in
/-- **The ledger of a quadratic conversion.** -/
theorem ledger_copyQuad (hF : StepFacts kI G G' (succProvParams D Cw cr σ₀ η₀ N p) Cu)
    (hC : LedgerConsts b Dm kI.Lstar κc ar Δ K W Cold Wr S Kg Kd) (hΔD : (Dm : ℝ) * Δ ≤ 1)
    {h : ℕ} (π : StagePath G h) (ρ s₀ : ℝ) (hρ : ρ = liftLength D G.level)
    (t₀ : List WordLetter)
    (Cc : ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin ((SuccSource.copyQuad t₀ h π).pathLen + 1)) (fun _ => ℝ))
    {sX sZ N₀ R : ℕ}
    (hset : ∀ (k : ℤ) (hk : Odd k), CutoffLiftSetup D b j₀ G.exports G.level k ρ
      (pathEdgesAt G π ⟨k, hk⟩) (Cc k) sX sZ N₀ R)
    (hR : 2 + Dm + 2 ≤ R) {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u')
    (hprov : G'.prov v' u' γ' = (SuccSource.copyQuad t₀ h π).prov G.level)
    (htgt : (SuccSource.copyQuad t₀ h π).tgtComp G.level = v'.1)
    (hflux : ∀ (q : OddSlot) (c : StageCtx D b j₀ G'.level q) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
      G'.fam.flux q c v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level q.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
        then transferAt D G.level q.1 ((SuccSource.copyQuad t₀ h π).lam G.level η₀)
          (((SuccSource.copyQuad t₀ h π).prov G.level).tags
            (succProvParams D Cw cr σ₀ η₀ N p)).order
          ((SuccSource.copyQuad t₀ h π).fluxOp ρ s₀ Cc) t
          (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0)
    {rH nH : ℕ} (hh : h ≤ rH) (hN₀ : N₀ ≤ nH) (h2 : 2 ≤ nH)
    (hLst : UEnv.liftWt Dm rH nH ≤ kI.Lstar) (hcr0 : 0 < cr) (hcr1 : cr ≤ 1)
    (hthr : ledgerThr Dm rH nH p K W Cold Wr Δ cr Cu (fluxMax κc S Kg Kd Dm rH nH)
      (covKMax S Kg nH p) ≤ Cw) :
    LedgerConcl kI κc G' v' u' γ' := by
  subst hρ
  obtain ⟨hmax', hsize'⟩ := record_of_quad hF.hGT hF.hGT' π γ' (m := G.level) hprov
  have ho : (((SuccSource.copyQuad t₀ h π).prov G.level).tags
      (succProvParams D Cw cr σ₀ η₀ N p)).order = 2 := Prov.tags_quad_order _ _ _
  have hflux2 : ∀ (q : OddSlot) (c : StageCtx D b j₀ G'.level q) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
      G'.fam.flux q c v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level q.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
        then transferAt D G.level q.1 1 2
          ((SuccSource.copyQuad t₀ h π).fluxOp (liftLength D G.level) s₀ Cc) t
          (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0 := by
    intro q c d I t X z hd
    have h := hflux q c d I t X z hd
    rw [ho] at h
    exact h
  have hres1 := compReserve_le_one kI v'.1
  have hresT : compReserve kI v'.1 ≤ compReserve kI π.tgt := by
    rw [← htgt]
    exact compReserve_succComp_le kI G.level π.tgt t₀
  have hFle := fluxXc_oldCtx_le_fluxMax hF.hcert.oldCert κc Δ (compReserve kI v'.1) S Kg Kd hh h2
  have hT := ledgerThr_ge (rH := rH) (nH := nH) (p := p) (cr := cr)
    (FM := fluxMax κc S Kg Kd Dm rH nH) (KM := covKMax S Kg nH p) hC.hK0 hC.hW0 hC.hC0 hC.hWr0
    hC.hΔ hF.hCu (q := 1) (u := 1)
    (f := ((UEnv.fluxXc (oldCtx hF.hcert.oldCert κc Δ (compReserve kI v'.1) S Kg Kd) Dm
      (liftB (oldCtx hF.hcert.oldCert κc Δ (compReserve kI v'.1) S Kg Kd) Dm) h 2 : ℝ≥0) : ℝ))
    (dp := (Dm : ℝ) ^ h) (e := 1) zero_le_one zero_le_one (NNReal.coe_nonneg _)
    (pow_nonneg (Nat.cast_nonneg _) _) zero_le_one (one_le_crInv_pow hcr0 hcr1 Dm)
    (by rw [mul_one]; exact one_le_pow₀ hF.hCu) (coe_le_KF (hFle.trans le_self_add))
    (natCast_pow_le_succ_pow Dm hh)
  refine copyQuad_ledger_case hF.hζ hF.hΛ1 hF.hb hF.hκb hF.hstart G G' hF.hcert.oldCert hF.hT hF.hexpU
    hF.hexp hF.hlev π _ s₀ t₀ Cc hset hR γ' hflux2 hmax' (Cw := Cw) hsize'
    (fun j h3 => hF.hℓ _ _ _ h3) (fun j => hresT.trans (hF.hres_path π j))
    hF.hεn (hF.hεpos _) (hF.hεle _) hF.hτ hF.hκ' hF.hη0 hF.hη1 hF.hsc.hρ0 hF.hρE hF.hDst0
    hF.hDst κc hC.ha3 hC.hΔ ((add_le_add hres1 hΔD).trans (by norm_num))
    (oldCtx_ok hF.hcert.oldCert κc hC.hΔ.le (hres1.trans one_le_two) hC.hKg hC.hKd) (hF.hSl hC.hS)
    ((UEnv.liftWt_mono Dm hh hN₀).trans hLst) ((UEnv.liftWt_mono Dm hh h2).trans hLst)
    hC.hK0 hC.hW0 hC.hC0 hC.hWr0 hC.hK hC.hW hC.hCold hC.hWr ?_
  refine le_trans (le_of_eq ?_) (hT.trans (by rw [mul_one]; exact hthr))
  unfold ledgerA
  ring

open scoped Classical in
/-- **The ledger of a mean letter.** -/
theorem ledger_letterMean (hF : StepFacts kI G G' (succProvParams D Cw cr σ₀ η₀ N p) Cu)
    (hC : LedgerConsts b Dm kI.Lstar κc ar Δ K W Cold Wr S Kg Kd)
    (hΔD : (Dm : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1))
    {h : ℕ} (π : StagePath G h) (ρ s₀ : ℝ) (hρ : ρ = liftLength D G.level)
    (t₀ : List WordLetter) (n : ℕ)
    (Cc : ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin ((SuccSource.letterMean t₀ n h π).pathLen + 1)) (fun _ => ℝ))
    {sX sZ N₀ R : ℕ}
    (hset : ∀ (k : ℤ) (hk : Odd k), CutoffLiftSetup D b j₀ G.exports G.level k ρ
      (pathEdgesAt G π ⟨k, hk⟩) (Cc k) sX sZ N₀ R)
    (hn : 3 ≤ n) (hnD : n ≤ Dm) (hR : n + Dm + 2 ≤ R) {v' u' : CompIn G'.comps}
    (γ' : G'.fam.Γ v' u')
    (hprov : G'.prov v' u' γ' = (SuccSource.letterMean t₀ n h π).prov G.level)
    (htgt : (SuccSource.letterMean t₀ n h π).tgtComp G.level = v'.1)
    (hflux : ∀ (q : OddSlot) (c : StageCtx D b j₀ G'.level q) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
      G'.fam.flux q c v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level q.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
        then transferAt D G.level q.1 ((SuccSource.letterMean t₀ n h π).lam G.level η₀)
          (((SuccSource.letterMean t₀ n h π).prov G.level).tags
            (succProvParams D Cw cr σ₀ η₀ N p)).order
          ((SuccSource.letterMean t₀ n h π).fluxOp ρ s₀ Cc) t
          (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0)
    {rH nH : ℕ} (hh : h ≤ rH) (hN₀ : N₀ ≤ nH) (hnH : n ≤ nH)
    (hLst : UEnv.liftWt Dm rH nH ≤ kI.Lstar) (hcr0 : 0 < cr) (hcr1 : cr ≤ 1)
    (hthr : ledgerThr Dm rH nH p K W Cold Wr Δ cr Cu (fluxMax κc S Kg Kd Dm rH nH)
      (covKMax S Kg nH p) ≤ Cw) :
    LedgerConcl kI κc G' v' u' γ' := by
  subst hρ
  obtain ⟨-, hlen', hsize'⟩ :=
    record_of_letter hF.hGT hF.hGT' π γ' (m := G.level) (.mean n h) hprov
  have ho : (((SuccSource.letterMean t₀ n h π).prov G.level).tags
      (succProvParams D Cw cr σ₀ η₀ N p)).order = n :=
    (Prov.tags_letter _ G.level (.mean n h) π.provList).1
  have hlam : (SuccSource.letterMean t₀ n h π).lam G.level η₀ = D.eps (G.level - 1) ^ (-η₀) :=
    rfl
  have hμ : compReserve kI v'.1 + 1 / ((kI.Hprod : ℝ) + 1) = compReserve kI π.tgt := by
    rw [← htgt]
    exact compReserve_succComp_append kI G.level π.tgt t₀ (.mean n h)
  have hμ1 := compReserve_le_one kI π.tgt
  have hlenρ : (G'.fam.identity v' u' γ').record.length = cr * liftLength D G.level := by
    rw [hlen']
    show freshLength D cr (G.level - 1) = _
    unfold freshLength liftLength
    rw [Nat.sub_add_cancel (by have := hF.hlev; omega)]
  have hsz : (G'.fam.identity v' u' γ').record.size =
      Cw * D.eps (G.level - 1) ^ (ocDelta D.α D.q - η₀) *
        ∏ j : Fin h, (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size := by
    rw [hsize']
    show (1 : ℝ) * Cw * D.eps (G.level - 1) ^ (ocDelta D.α D.q - η₀) * _ = _
    rw [one_mul]
  have hFle := fluxXc_oldCtx_le_fluxMax hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd hh hnH
  have hx0 : 0 ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) /
      liftLength D G.level := div_nonneg hF.hDst0 hF.hsc.hρ0.le
  have hgain := mean_gain_le η₀ hx0 hF.hCu (hF.hεpos (G.level - 1)) (hF.hεle _) hF.hδ
    hF.hsc.hDρ p hn hnH
  have hT := ledgerThr_ge (rH := rH) (nH := nH) (p := p) (cr := cr)
    (FM := fluxMax κc S Kg Kd Dm rH nH) (KM := covKMax S Kg nH p) hC.hK0 hC.hW0 hC.hC0 hC.hWr0
    hC.hΔ hF.hCu (q := cr⁻¹ ^ Dm)
    (u := |D.eps (G.level - 1) ^ (-η₀)| *
      (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) /
        liftLength D G.level) ^ (n - 2))
    (f := ((UEnv.fluxXc (oldCtx hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd) Dm
      (liftB (oldCtx hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd) Dm) h n + 1 : ℝ≥0) : ℝ))
    (dp := (Dm : ℝ) ^ h) (e := D.eps (G.level - 1) ^ (ocDelta D.α D.q - η₀))
    (pow_nonneg (inv_nonneg.mpr hcr0.le) _) (mul_nonneg (abs_nonneg _) (pow_nonneg hx0 _))
    (NNReal.coe_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (hF.hεn _) _)
    le_rfl hgain (coe_le_KF (add_le_add hFle le_rfl)) (natCast_pow_le_succ_pow Dm hh)
  refine letterMean_ledger_case hF.hζ hF.hΛ1 hF.hb hF.hκb hF.hstart G G' hF.hcert.oldCert hF.hT hF.hexpU
    hF.hexp hF.hlev π _ s₀ t₀ n Cc hset (by omega) hnD hR γ' _ _ (by rw [ho]; exact hnD) hflux
    (Cw := Cw * D.eps (G.level - 1) ^ (ocDelta D.α D.q - η₀)) hsz
    (fun j h3 => hF.hℓ _ _ _ h3) (μ₀ := compReserve kI π.tgt) (fun j => hF.hres_path π j)
    hF.hεn (hF.hεpos _) (hF.hεle _) hF.hτ hF.hκ' hF.hsc.hκ0.le hF.hκκ hF.hη0 hF.hη1
    hF.hsc.hρ0 hF.hsc.hεd hF.hDst κc hC.ha3 hC.hΔ (by linarith)
    (oldCtx_ok hF.hcert.oldCert κc hC.hΔ.le (by linarith) hC.hKg hC.hKd) (hF.hSl hC.hS)
    ((UEnv.liftWt_mono Dm hh hN₀).trans hLst) ((UEnv.liftWt_mono Dm hh hnH).trans hLst)
    hC.hK0 hC.hW0 hC.hC0 hC.hWr0 hC.hK hC.hW hC.hCold hC.hWr (Q := cr⁻¹ ^ Dm)
    (pow_nonneg (inv_nonneg.mpr hcr0.le) _) (fun d _ hdD i' => ?_) ?_
  · rw [hlenρ]
    exact fresh_Q_le (hF.hεpos _) hF.hsc.hρ0 hF.hρE hcr0 hcr1
      (by have := (G'.fam.identity v' u' γ').le_D; omega) i'
  · rw [hlam]
    refine le_trans (le_of_eq ?_)
      (hT.trans (mul_le_mul_of_nonneg_right hthr (Real.rpow_nonneg (hF.hεn _) _)))
    unfold ledgerA
    ring

open scoped Classical in
/-- **The ledger of a covariance letter.** -/
theorem ledger_letterCov (hF : StepFacts kI G G' (succProvParams D Cw cr σ₀ η₀ N p) Cu)
    (hC : LedgerConsts b Dm kI.Lstar κc ar Δ K W Cold Wr S Kg Kd)
    (hΔD : (Dm : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1))
    {h : ℕ} (π : StagePath G h) (ρ s₀ : ℝ) (hρ : ρ = liftLength D G.level) (hs₀ : s₀ = 0)
    (t₀ : List WordLetter) (n a a' : ℕ)
    (Cc : ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin ((SuccSource.letterCov t₀ n h a a' π).pathLen + 1)) (fun _ => ℝ))
    {sX sZ N₀ R : ℕ}
    (hset : ∀ (k : ℤ) (hk : Odd k), CutoffLiftSetup D b j₀ G.exports G.level k ρ
      (pathEdgesAt G π ⟨k, hk⟩) (Cc k) sX sZ N₀ R)
    (hn : 2 ≤ n) (hR : n + Dm + 2 ≤ R) (haR : 2 * a + Dm + 2 ≤ R) {v' u' : CompIn G'.comps}
    (γ' : G'.fam.Γ v' u')
    (hprov : G'.prov v' u' γ' = (SuccSource.letterCov t₀ n h a a' π).prov G.level)
    (htgt : (SuccSource.letterCov t₀ n h a a' π).tgtComp G.level = v'.1)
    (hflux : ∀ (q : OddSlot) (c : StageCtx D b j₀ G'.level q) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
      G'.fam.flux q c v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level q.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
        then transferAt D G.level q.1 ((SuccSource.letterCov t₀ n h a a' π).lam G.level η₀)
          (((SuccSource.letterCov t₀ n h a a' π).prov G.level).tags
            (succProvParams D Cw cr σ₀ η₀ N p)).order
          ((SuccSource.letterCov t₀ n h a a' π).fluxOp ρ s₀ Cc) t
          (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0)
    {rH nH : ℕ} (hh : h ≤ rH) (hN₀ : N₀ ≤ nH) (hnH : n ≤ nH) (ha : a ≤ p) (ha' : a' ≤ p)
    (haa : 1 ≤ a + a') (hnpD : nH + 4 * p ≤ Dm)
    (hΔR : ((4 * nH + 10 * p : ℕ) : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1))
    (hLst : UEnv.liftWt Dm rH nH ≤ kI.Lstar) (hcr0 : 0 < cr) (hcr1 : cr ≤ 1)
    (hthr : ledgerThr Dm rH nH p K W Cold Wr Δ cr Cu (fluxMax κc S Kg Kd Dm rH nH)
      (covKMax S Kg nH p) ≤ Cw) :
    LedgerConcl kI κc G' v' u' γ' := by
  subst hρ hs₀
  obtain ⟨-, hlen', hsize'⟩ :=
    record_of_letter hF.hGT hF.hGT' π γ' (m := G.level) (.covariance n h a a') hprov
  have ho : (((SuccSource.letterCov t₀ n h a a' π).prov G.level).tags
      (succProvParams D Cw cr σ₀ η₀ N p)).order = n + 2 * (a + a') :=
    (Prov.tags_letter _ G.level (.covariance n h a a') π.provList).1
  have hlam : (SuccSource.letterCov t₀ n h a a' π).lam G.level η₀ =
      D.eps (G.level - 1) ^ (-η₀) := rfl
  have hμ : compReserve kI v'.1 + 1 / ((kI.Hprod : ℝ) + 1) = compReserve kI π.tgt := by
    rw [← htgt]
    exact compReserve_succComp_append kI G.level π.tgt t₀ (.covariance n h a a')
  have hμ1 := compReserve_le_one kI π.tgt
  have hR4 : covLetR n a a' ≤ 4 * nH + 10 * p := by
    unfold covLetR
    omega
  have hgapR : (covLetR n a a' : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1) :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hR4) hC.hΔ.le).trans hΔR
  have hlenρ : (G'.fam.identity v' u' γ').record.length = cr * liftLength D G.level := by
    rw [hlen']
    show freshLength D cr (G.level - 1) = _
    unfold freshLength liftLength
    rw [Nat.sub_add_cancel (by have := hF.hlev; omega)]
  have hsz : (G'.fam.identity v' u' γ').record.size =
      Cw * D.eps (G.level - 1) ^ (ocDelta D.α D.q - η₀) *
        ∏ j : Fin h, (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size := by
    rw [hsize']
    show (1 : ℝ) * Cw * D.eps (G.level - 1) ^ (ocDelta D.α D.q - η₀) * _ = _
    rw [one_mul]
  have hcH0 : 0 ≤ Cu * D.eps (G.level - 1) ^ ocDelta D.α D.q :=
    mul_nonneg (by linarith [hF.hCu]) (Real.rpow_nonneg (hF.hεn _) _)
  have hH : ∀ t i j, |covMat D G.level 0 t i j| ≤
      ((Real.toNNReal (Cu * D.eps (G.level - 1) ^ ocDelta D.α D.q) *
        Real.toNNReal (liftLength D G.level) ^ 2 : ℝ≥0) : ℝ) := by
    intro t i j
    rw [NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal _ hcH0,
      Real.coe_toNNReal _ hF.hsc.hρ0.le]
    exact hF.hsc.hH t i j
  have hFle := fluxXc_oldCtx_le_fluxMax hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd hh hnH
  have hx0 : 0 ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) /
      liftLength D G.level := div_nonneg hF.hDst0 hF.hsc.hρ0.le
  have hgain := cov_gain_le η₀ hx0 hF.hCu (hF.hεpos (G.level - 1)) (hF.hεle _) hF.hδ
    hF.hsc.hDρ hnH ha ha' haa
  have hf : ((covLetK n a a' S Kg : ℝ≥0) : ℝ) *
      ((UEnv.fluxXc (oldCtx hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd) Dm
        (liftB (oldCtx hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd) Dm) h n : ℝ≥0) : ℝ) ≤
      (((covKMax S Kg nH p + 1) * (fluxMax κc S Kg Kd Dm rH nH + 1) : ℝ≥0) : ℝ) := by
    rw [← NNReal.coe_mul]
    exact NNReal.coe_le_coe.mpr (mul_le_mul'
      ((covLetK_le_covKMax S Kg hnH ha ha').trans le_self_add) (hFle.trans le_self_add))
  have hT := ledgerThr_ge (rH := rH) (nH := nH) (p := p) (cr := cr)
    (FM := fluxMax κc S Kg Kd Dm rH nH) (KM := covKMax S Kg nH p) hC.hK0 hC.hW0 hC.hC0 hC.hWr0
    hC.hΔ hF.hCu (q := cr⁻¹ ^ Dm)
    (u := |D.eps (G.level - 1) ^ (-η₀)| *
      (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) /
        liftLength D G.level) ^ (n - 2) *
      (Cu * D.eps (G.level - 1) ^ ocDelta D.α D.q) ^ (a + a'))
    (f := ((covLetK n a a' S Kg : ℝ≥0) : ℝ) *
      ((UEnv.fluxXc (oldCtx hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd) Dm
        (liftB (oldCtx hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd) Dm) h n : ℝ≥0) : ℝ))
    (dp := (Dm : ℝ) ^ h) (e := D.eps (G.level - 1) ^ (ocDelta D.α D.q - η₀))
    (pow_nonneg (inv_nonneg.mpr hcr0.le) _)
    (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hx0 _)) (pow_nonneg hcH0 _))
    (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)) (pow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (hF.hεn _) _) le_rfl hgain hf (natCast_pow_le_succ_pow Dm hh)
  refine letterCov_ledger_case hF.hζ hF.hΛ1 hF.hb hF.hκb hF.hstart G G' hF.hcert.oldCert hF.hT hF.hexpU
    hF.hexp hF.hlev π _ t₀ n a a' Cc hset hn hR haR γ' _ _ (by rw [ho]; omega) hflux
    (Cw := Cw * D.eps (G.level - 1) ^ (ocDelta D.α D.q - η₀)) hsz
    (fun j h3 => hF.hℓ _ _ _ h3) (μ₀ := compReserve kI π.tgt) (fun j => hF.hres_path π j)
    hF.hεn (hF.hεpos _) (hF.hεle _) hF.hτ hF.hκ' hF.hsc.hκm hF.hsc.hκm' hF.hη0 hF.hη1
    hF.hsc.hρ0 hF.hDst0 hF.hDst κc hC.ha3 hC.hΔ (by linarith) (by linarith)
    (oldCtx_ok hF.hcert.oldCert κc hC.hΔ.le (by linarith) hC.hKg hC.hKd) (hF.hSl hC.hS)
    ((UEnv.liftWt_mono Dm hh hN₀).trans hLst) ((UEnv.liftWt_mono Dm hh hnH).trans hLst)
    hC.hK0 hC.hW0 hC.hC0 hC.hWr0 hC.hK hC.hW hC.hCold hC.hWr
    (cH := Real.toNNReal (Cu * D.eps (G.level - 1) ^ ocDelta D.α D.q)) hH
    (Q := cr⁻¹ ^ Dm) (pow_nonneg (inv_nonneg.mpr hcr0.le) _) (fun d _ hdD i' => ?_) ?_
  · rw [hlenρ]
    exact fresh_Q_le (hF.hεpos _) hF.hsc.hρ0 hF.hρE hcr0 hcr1
      (by have := (G'.fam.identity v' u' γ').le_D; omega) i'
  · rw [hlam, NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal _ hcH0]
    refine le_trans (le_of_eq ?_)
      (hT.trans (mul_le_mul_of_nonneg_right hthr (Real.rpow_nonneg (hF.hεn _) _)))
    unfold ledgerA
    ring
end

/-! **Ledger: the ledger of every identity of the next family whose source is not the first
source.** For an actual successor `G'` of `G` at the successor menus, with the lift reserves
`max (N + D_H) (2p) + D_{H+1} + 2 ≤ sX, sZ`, the standing facts of the passage, a
family of the old stage of depth at most `r_H`, the constants of the ledger at a reserve step `Δ`
below the grade step divided by `D_{H+1}` and by `4(N + D_H) + 10p`, the fast weight
`liftWt D_{H+1} r_H (N + D_H) ≤ L_*` and the threshold `ledgerThr ≤ C_w`:
* `ledger_of_source`: the ledger of a new identity with a given non-diagonal source, by cases on
  the source (`ledger_copyDir`, `ledger_copyQuad`, `ledger_letterMean`, `ledger_letterCov`); the
  lift setups are those of the generation statement (`hasSetup_of_liftFamily`), the reserves cover the degrees
  (`reserve_of_valid`), the letters lie in the successor alphabet, and a path of the old stage has
  at most `r_H` edges (`stagePath_length_le`);
* hence the ledger of every new identity whose provenance is not that of the first
  source `𝖣` (`Prov.letter m .diag []`). -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {b : ℝ} {j₀ : ℕ} {kI : InvConsts}

/-- The provenance of the first source. -/
theorem prov_of_isDiag {Dm : ℕ} {G : GenStage D hr Dm b j₀} (s : SuccSource G) (h : s.IsDiag)
    (m : ℕ) : s.prov m = .letter m .diag [] := by
  cases s with
  | letterDiag t u => rfl
  | copyDir t v u γ => exact False.elim h
  | copyQuad t h' π => exact False.elim h
  | letterMean t n h' π => exact False.elim h
  | letterCov t n h' a a' π => exact False.elim h

/-- A reserve step below the grade step divided by the number of steps. -/
theorem step_mul_le {A X y : ℝ} (hA : 0 < A) (hX : 0 < X) (hy : y ≤ X) :
    y * (1 / (A * X)) ≤ 1 / A := by
  rw [mul_one_div, div_le_div_iff₀ (mul_pos hA hX) hA, one_mul]
  calc y * A ≤ X * A := mul_le_mul_of_nonneg_right hy hA.le
    _ = A * X := mul_comm _ _

/-- **The fast weight of the lifts is below the producer's fast weight** `L_*`, by the producer
allocation of the seed constants. -/
theorem liftWt_le_Lstar {kS kI : InvConsts} {r₀ D₀ H J N p Kres Lpr Lc Lf : ℕ}
    (hseed : IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf) (hG0 : kI.G0 = kS.G0)
    (hL : succLstar Kres kI.G0 H J N p ≤ kI.Lstar) :
    UEnv.liftWt (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) (N + succSchedD D₀ N p H) ≤
      kI.Lstar := by
  obtain ⟨-, -, -, -, -, -, hR, hD, -⟩ := hseed
  have hR1 : succSchedR r₀ J H ≤ succSchedR 0 J (kI.G0 + H + 1) := by
    rw [hG0]
    exact (hR H).trans (succSchedR_le_succ 0 J (kS.G0 + H))
  have hD1 : succSchedD D₀ N p (H + 1) ≤ succSchedD 2 N p (kI.G0 + H + 1) := by
    rw [hG0]
    exact hD (H + 1)
  have hDm : succSchedD D₀ N p (H + 1) = succSchedD D₀ N p H + 2 * N + 4 * p + 4 := rfl
  refine le_trans ?_ hL
  unfold UEnv.liftWt succLstar
  generalize succSchedR 0 J (kI.G0 + H + 1) = Rb at hR1 ⊢
  generalize succSchedD 2 N p (kI.G0 + H + 1) = Db at hD1 ⊢
  generalize succSchedR r₀ J H = rH at hR1 ⊢
  generalize succSchedD D₀ N p (H + 1) = Dm at hD1 hDm ⊢
  generalize succSchedD D₀ N p H = DH at hDm ⊢
  have h1 : rH * (Dm + 1) ≤ Rb * (2 * N + 4 + Db + 2) := Nat.mul_le_mul hR1 (by omega)
  have h3 : Rb * (2 * N + 4 + Db + 2) + (2 * N + 4 + Db + 2) =
      (Rb + 1) * (2 * N + 4 + Db + 2) := by ring
  have h4 : (Rb + 1) * (2 * N + 4 + Db + 2) ≤ (Rb + 1) * (2 * N + 4 + Db + 2) * (Db + 2) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

variable {Cw cr σ₀ η₀ : ℝ} {Mnat r₀ D₀ H J N p npad sX sZ : ℕ}
  {G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) b j₀} {Cu : ℝ} {κc : MajConsts}
  {ar Δ K W Cold Wr : ℝ} {S Kg Kd : ℝ≥0}

open scoped Classical in
/-- **The ledger of a new identity with a given non-diagonal source.** -/
theorem ledger_of_source (hN : 2 ≤ N)
    (hsX : max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX)
    (hsZ : max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ)
    (hF : StepFacts kI G G' (succProvParams D Cw cr σ₀ η₀ N p) Cu)
    (hdepth : G.fam.HasDepthAtMost (succSchedR r₀ J H))
    (hC : LedgerConsts b (succSchedD D₀ N p (H + 1)) kI.Lstar κc ar Δ K W Cold Wr S Kg Kd)
    (hΔD : ((succSchedD D₀ N p (H + 1) : ℕ) : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1))
    (hΔR : ((4 * (N + succSchedD D₀ N p H) + 10 * p : ℕ) : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1))
    (hLst : UEnv.liftWt (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H)
      (N + succSchedD D₀ N p H) ≤ kI.Lstar)
    (hcr0 : 0 < cr) (hcr1 : cr ≤ 1)
    (hthr : ledgerThr (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) (N + succSchedD D₀ N p H) p
      K W Cold Wr Δ cr Cu
      (fluxMax κc S Kg Kd (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H)
        (N + succSchedD D₀ N p H))
      (covKMax S Kg (N + succSchedD D₀ N p H) p) ≤ Cw)
    (s : SuccSource G) (hnd : ¬ s.IsDiag)
    (hval : s.Valid (succAlphabetOf r₀ D₀ H J N p npad) J)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hLF : s.IsLiftFamily (succMenu Mnat r₀ D₀ H J N p npad sX sZ η₀) Cc)
    {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u')
    (hprov : G'.prov v' u' γ' = s.prov G.level) (htgt : s.tgtComp G.level = v'.1)
    (hflux : ∀ (q : OddSlot) (c : StageCtx D b j₀ G'.level q) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
      G'.fam.flux q c v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level q.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
        then transferAt D G.level q.1
          (s.lam G.level (succMenu Mnat r₀ D₀ H J N p npad sX sZ η₀).η0)
          ((s.prov G.level).tags (succProvParams D Cw cr σ₀ η₀ N p)).order
          (s.fluxOp ((succMenu Mnat r₀ D₀ H J N p npad sX sZ η₀).lenFactor *
              liftLength D G.level)
            (succMenu Mnat r₀ D₀ H J N p npad sX sZ η₀).anchor Cc) t
          (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0) :
    LedgerConcl kI κc G' v' u' γ' := by
  have hsucc : succSchedD D₀ N p (H + 1) = succSchedD D₀ N p H + 2 * N + 4 * p + 4 := rfl
  have hρ1 : (succMenu Mnat r₀ D₀ H J N p npad sX sZ η₀).lenFactor * liftLength D G.level =
      liftLength D G.level := by
    simp only [succMenu, one_mul]
  have hlamne : (succMenu Mnat r₀ D₀ H J N p npad sX sZ η₀).lenFactor * liftLength D G.level /
      D.eps (G.level - 1) ≠ 0 := by
    rw [hρ1]
    exact div_ne_zero hF.hsc.hρ0.ne' (hF.hεpos _).ne'
  have hNR : (succMenu Mnat r₀ D₀ H J N p npad sX sZ η₀).N + succSchedD D₀ N p (H + 1) + 2 ≤
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 := by
    have : N ≤ max (N + succSchedD D₀ N p H) (2 * p) := le_max_of_le_left (by omega)
    show N + _ + 2 ≤ _
    omega
  have hset := fun (k : ℤ) (hk : Odd k) => hasSetup_of_liftFamily hF.hΛ1 hF.hζ hF.hκb hF.hb G
    hF.hGen hF.hT hF.hcert (succMenu Mnat r₀ D₀ H J N p npad sX sZ η₀) s Cc hLF hlamne hsX hsZ
    hNR k hk
  have hres := reserve_of_valid hN s hval
  have hH0 : (0 : ℝ) < (kI.Hprod : ℝ) + 1 := by positivity
  have hstep1 : 1 / ((kI.Hprod : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hH0]
    have : (0 : ℝ) ≤ kI.Hprod := Nat.cast_nonneg _
    linarith
  have hΔD1 : ((succSchedD D₀ N p (H + 1) : ℕ) : ℝ) * Δ ≤ 1 := hΔD.trans hstep1
  cases s with
  | copyDir t₀ v₀ u₀ γ₀ =>
    exact ledger_copyDir hF hC hΔD1 γ₀ hval.2.2 _ _ t₀ Cc γ' hprov htgt hflux hcr0 hcr1 hthr
  | copyQuad t₀ h π =>
    exact ledger_copyQuad hF hC hΔD1 π _ _ hρ1 t₀ Cc hset hres γ' hprov htgt hflux
      (stagePath_length_le hdepth π) (Nat.le_add_right N _) (by omega) hLst hcr0 hcr1 hthr
  | letterDiag t₀ u₀ => exact absurd trivial hnd
  | letterMean t₀ n h π =>
    obtain ⟨hn3, hnM, -, hhM⟩ := mean_mem_succAlphabet (hval.2.1 _ rfl).2
    exact ledger_letterMean hF hC hΔD π _ _ hρ1 t₀ n Cc hset hn3 (by omega) hres.2 γ' hprov htgt
      hflux hhM (Nat.le_add_right N _) hnM hLst hcr0 hcr1 hthr
  | letterCov t₀ n h a a' π =>
    obtain ⟨hn2, hnM, -, hhM, ha, ha', haa⟩ := cov_mem_succAlphabet (hval.2.1 _ rfl).2
    exact ledger_letterCov hF hC hΔD π _ _ hρ1 rfl t₀ n a a' Cc hset hn2 hres.2.1 hres.2.2 γ'
      hprov htgt hflux hhM (Nat.le_add_right N _) hnM ha ha' haa (by omega) hΔR hLst hcr0 hcr1
      hthr
end

/-! **Ledger: the ledger of every identity of the next family** (conditional helper
`ledger_all`). For an actual successor `G'` of `G` at the successor menus, every new identity has
the conclusion of `successor_ledger`: by cases on its source, the non-diagonal sources
(`ledger_of_source`, with the constants `LedgerConsts` and the threshold `ledgerThr`) and the first
source `𝖣` (`diag_ledger_case`, with the constants `DiagConsts` and the threshold `diagThr`).

Hypotheses beyond those of `ledger_of_source`: for the first source, the chain environment, the lift
reserves `max (N + 1) (2p) + D_{H+1} + 2 ≤ sX, sZ`, the coercivity bound `ownSize m ≤ 1/100`, the
scale facts `a_{m-1} τ''_m ≤ C_a ε_{m-1}^δ`, `ownSize m ≤ C_own ε_{m-1}^δ`,
`ε_m^{1+α} ≤ C_d √(κ_m κ_{m-1})`, the constants `DiagConsts` with `fsR · Δ_D ≤ 1`, the threshold
`diagThr ≤ C_w`, and a nonnegative reserve of the target component. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant AVRegularity.Providers.ComplexContext
  AVRegularity.Providers.ComplexFlow

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {b : ℝ} {j₀ : ℕ} {kI : InvConsts}

/-- The factor of the first source. -/
theorem lam_of_isDiag {Dm : ℕ} {G : GenStage D hr Dm b j₀} (s : SuccSource G) (h : s.IsDiag)
    (m : ℕ) (η₀ : ℝ) : s.lam m η₀ = D.eps (m - 1) ^ (-η₀) := by
  cases s with
  | letterDiag t u => rfl
  | copyDir t v u γ => exact False.elim h
  | copyQuad t h' π => exact False.elim h
  | letterMean t n h' π => exact False.elim h
  | letterCov t n h' a a' π => exact False.elim h

variable {Cw cr σ₀ η₀ : ℝ} {Mnat r₀ D₀ H J N p npad sX sZ : ℕ}
  {G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) b j₀} {Cu : ℝ} {κc : MajConsts}
  {ar Δ K W Cold Wr : ℝ} {S Kg Kd : ℝ≥0}

open scoped Classical in
/-- **The ledger of every new identity.** -/
theorem ledger_all (hN : 2 ≤ N)
    (hsX : max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX)
    (hsZ : max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ)
    (hF : StepFacts kI G G' (succProvParams D Cw cr σ₀ η₀ N p) Cu)
    (hdepth : G.fam.HasDepthAtMost (succSchedR r₀ J H))
    (hC : LedgerConsts b (succSchedD D₀ N p (H + 1)) kI.Lstar κc ar Δ K W Cold Wr S Kg Kd)
    (hΔD : ((succSchedD D₀ N p (H + 1) : ℕ) : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1))
    (hΔR : ((4 * (N + succSchedD D₀ N p H) + 10 * p : ℕ) : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1))
    (hLst : UEnv.liftWt (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H)
      (N + succSchedD D₀ N p H) ≤ kI.Lstar)
    (hcr0 : 0 < cr) (hcr1 : cr ≤ 1)
    (hthr : ledgerThr (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) (N + succSchedD D₀ N p H) p
      K W Cold Wr Δ cr Cu
      (fluxMax κc S Kg Kd (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H)
        (N + succSchedD D₀ N p H))
      (covKMax S Kg (N + succSchedD D₀ N p H) p) ≤ Cw)
    -- the first source
    {CH Υ : ℝ} (env : ChainEnv D b CH Υ j₀) (hij : j₀ ≤ G'.level)
    (hsXd : max (N + 1) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX)
    (hsZd : max (N + 1) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ)
    (hm : ownSize D G.level ≤ 1 / 100) {Ca Cown Cd : ℝ} (hCa : 0 ≤ Ca) (hCown : 0 ≤ Cown)
    (haτ : ocA D.α D.q D.Λ G'.level * ocTauPP D.α D.q D.Λ G.level ≤
      Ca * D.eps G'.level ^ ocDelta D.α D.q)
    (hown : ownSize D G.level ≤ Cown * D.eps G'.level ^ ocDelta D.α D.q)
    (hCd : D.eps G.level ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap G.level * D.kap G'.level))
    {ΔD aD a₀D : ℝ} {L₀ : ℕ} {sD Wg Wc Wl KgD KdD SD : ℝ≥0} {WrD ColdD CslowD : ℝ}
    (hCD : DiagConsts b kI.Lstar κc N p ΔD aD a₀D L₀ sD Wg Wc Wl KgD KdD SD WrD ColdD CslowD)
    (hΔfs : ((fsR N p (2 * N + 1) : ℕ) : ℝ) * ΔD ≤ 1)
    (hthrD : diagThr (constCtx κc SD KgD KdD) (succSchedD D₀ N p (H + 1)) N p sD Wg Wl Wc Cu Ca Cd
      Cown WrD cr ≤ Cw)
    (hSucc : IsActualSuccessor D (succProvParams D Cw cr σ₀ η₀ N p)
      (succMenu Mnat r₀ D₀ H J N p npad sX sZ η₀) G G')
    {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u') (hres0 : 0 ≤ compReserve kI v'.1) :
    LedgerConcl kI κc G' v' u' γ' := by
  obtain ⟨-, -, -, -, -, -, e, Cc, Cc0, hLF, hDLs, hfl⟩ := hSucc
  obtain ⟨hprov, -, hndf, hdf⟩ := hfl v' u' γ'
  by_cases hd : (e v' u' γ').1.IsDiag
  · have hprov' : G'.prov v' u' γ' = .letter G.level .diag [] :=
      hprov.trans (prov_of_isDiag _ hd G.level)
    refine diag_ledger_case hF env hij γ' hprov' (by omega) hsXd hsZd Cc0
      (fun k A hk hA => ?_) (fun q ctx d I t X z h2 => ?_) hm hCa hCown haτ hown hCd κc hCD hres0
      (by linarith [compReserve_le_one kI v'.1]) hcr0 hcr1 hthrD
    · have h := hDLs k A hk hA
      simp only [succMenu, one_mul] at h
      exact h
    · have h := hdf hd q ctx d I t X z h2
      rw [lam_of_isDiag _ hd] at h
      simp only [succMenu, one_mul] at h
      exact h
  · exact ledger_of_source hN hsX hsZ hF hdepth hC hΔD hΔR hLst hcr0 hcr1 hthr (e v' u' γ').1 hd
      (e v' u' γ').2.1 (Cc _) (hLF _) γ' hprov (e v' u' γ').2.2.2 (hndf hd)
end

end AVRegularity.Providers.CascadeInvariants
end
