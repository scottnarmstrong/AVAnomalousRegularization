-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.CascadeInvariants.Menu.FirstSource
import AVRegularity.Proofs.CascadeInvariants.LedgerAll
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants.Menu

/-! Four one-step source ledgers at the actual menu radius and covariance anchor. -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {kI : InvConsts}
variable {cr : ℝ} {P : ProvParams} {Mn : SuccMenu} {nMax hMax npad : ℕ} {G G' : GenStage D hr Dm b j₀} {Cu : ℝ}
  {κc : MajConsts} {ar Δ K W Cold Wr : ℝ} {S Kg Kd : ℝ≥0}

/-- The menu lift radius is positive. -/
theorem MenuFacts.radius_positive (hM : MenuFacts kI G G' P Mn Cu cr nMax hMax npad) :
    0 < Mn.lenFactor * liftLength D G.level :=
  mul_pos hM.radius_pos hM.stage.hsc.hρ0

/-- The menu lift radius fits inside the coarser wavelength. -/
theorem MenuFacts.radius_le_epsilon (hM : MenuFacts kI G G' P Mn Cu cr nMax hMax npad) :
    Mn.lenFactor * liftLength D G.level ≤ D.eps G'.level :=
  (mul_le_of_le_one_left hM.stage.hsc.hρ0.le hM.radius_le).trans hM.stage.hρE

/-- Slow differentiation at the menu radius is covered by the ledger constants. -/
theorem MenuFacts.slow (hM : MenuFacts kI G G' P Mn Cu cr nMax hMax npad)
    {κc : MajConsts} {Δ : ℝ} {S : ℝ≥0} (hS : κc.Cslow / ENNReal.ofReal Δ ≤ S) :
    ENNReal.ofReal |Mn.lenFactor * liftLength D G.level| *
      (κc.Cslow / ENNReal.ofReal (D.eps (G.level - 1) * Δ)) ≤ S :=
  (slow_le hM.radius_positive.le
    (by rw [hM.stage.e1]; exact hM.radius_le_epsilon) (hM.stage.hεpos _)).trans hS

open scoped Classical in
/-- **The ledger of a direct transport.** -/
theorem ledger_copyDir_menu_case (hM : MenuFacts kI G G' P Mn Cu cr nMax hMax npad)
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
        then transferAt D G.level q.1 ((SuccSource.copyDir t₀ v₀ u₀ γ₀).lam G.level Mn.η0)
          (((SuccSource.copyDir t₀ v₀ u₀ γ₀).prov G.level).tags
            P).order
          ((SuccSource.copyDir t₀ v₀ u₀ γ₀).fluxOp ρ s₀ Cc) t
          (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0)
    {rH nH : ℕ} (hcr0 : 0 < cr) (hcr1 : cr ≤ 1)
    (hthr : ledgerThr Dm rH nH Mn.p K W Cold Wr Δ cr Cu (fluxMax κc S Kg Kd Dm rH nH)
      (covKMax S Kg nH Mn.p) ≤ P.C) :
    LedgerConcl kI κc G' v' u' γ' := by
  have hF := hM.stage
  obtain ⟨hmax', hlen', hsize'⟩ := record_of_dir hF.hGT hF.hGT' γ₀ γ' (m := G.level) hprov
  have hDγ : (((SuccSource.copyDir t₀ v₀ u₀ γ₀).prov G.level).tags
      P).order = (G.fam.identity v₀ u₀ γ₀).maxOrder :=
    (Prov.tags_dir_all _ G.level (G.prov v₀ u₀ γ₀)).1.trans (hF.hGT v₀ u₀ γ₀).2.symm
  have hres1 := compReserve_le_one kI v'.1
  have hT := ledgerThr_ge (rH := rH) (nH := nH) (p := Mn.p) (cr := cr)
    (FM := fluxMax κc S Kg Kd Dm rH nH) (KM := covKMax S Kg nH Mn.p) hC.hK0 hC.hW0 hC.hC0 hC.hWr0
    hC.hΔ hF.hCu (q := 1) (u := 1) (f := 1) (dp := 1) (e := 1) zero_le_one zero_le_one
    zero_le_one zero_le_one zero_le_one (one_le_crInv_pow hcr0 hcr1 Dm)
    (by rw [mul_one]; exact one_le_pow₀ hF.hCu) (one_le_KF _ _)
    (one_le_pow₀ (by have : (0 : ℝ) ≤ Dm := Nat.cast_nonneg _; linarith))
  have hA := dirConst_le_ledgerA (Dm := Dm) hC.hK0 hC.hW0 hC.hC0 hC.hWr0 hC.hΔ
  exact copyDir_ledger_case hF.hζ hF.hΛ1 hF.hb hF.hstart G G' hF.hcert.oldCert hF.hexpU hF.hexp hF.hlev
    γ₀ ρ s₀ t₀ Cc γ' _ hflux hDγ (hmax'.trans hDγ.symm) hlen' (Cw := P.C) hsize'
    ((hF.hℓ v₀ u₀ γ₀ hval).trans hF.heps_le)
    (by rw [← htgt]; exact compReserve_succComp_le kI G.level v₀.1 t₀)
    hF.hεn (hF.hεpos _) (hF.hεle _) (hF.hεpos _) hF.hτ hF.hκ' hF.hsc.hκ0.le hF.hκκ κc hC.ha3
    hC.hΔ (by linarith) hC.hK0 hC.hW0 hC.hC0 hC.hWr0 hC.hK hC.hW hC.hCold hC.hWr
    (by linarith)

open scoped Classical in
/-- **The ledger of a quadratic conversion.** -/
theorem ledger_copyQuad_menu_case (hM : MenuFacts kI G G' P Mn Cu cr nMax hMax npad)
    (hC : LedgerConsts b Dm kI.Lstar κc ar Δ K W Cold Wr S Kg Kd) (hΔD : (Dm : ℝ) * Δ ≤ 1)
    {h : ℕ} (π : StagePath G h) (ρ s₀ : ℝ) (hρ : ρ = Mn.lenFactor * liftLength D G.level)
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
        then transferAt D G.level q.1 ((SuccSource.copyQuad t₀ h π).lam G.level Mn.η0)
          (((SuccSource.copyQuad t₀ h π).prov G.level).tags
            P).order
          ((SuccSource.copyQuad t₀ h π).fluxOp ρ s₀ Cc) t
          (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0)
    {rH nH : ℕ} (hh : h ≤ rH) (hN₀ : N₀ ≤ nH) (h2 : 2 ≤ nH)
    (hLst : UEnv.liftWt Dm rH nH ≤ kI.Lstar) (hcr0 : 0 < cr) (hcr1 : cr ≤ 1)
    (hthr : ledgerThr Dm rH nH Mn.p K W Cold Wr Δ cr Cu (fluxMax κc S Kg Kd Dm rH nH)
      (covKMax S Kg nH Mn.p) ≤ P.C) :
    LedgerConcl kI κc G' v' u' γ' := by
  have hF := hM.stage
  subst hρ
  obtain ⟨hmax', hsize'⟩ := record_of_quad hF.hGT hF.hGT' π γ' (m := G.level) hprov
  have ho : (((SuccSource.copyQuad t₀ h π).prov G.level).tags
      P).order = 2 := Prov.tags_quad_order _ _ _
  have hflux2 : ∀ (q : OddSlot) (c : StageCtx D b j₀ G'.level q) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
      G'.fam.flux q c v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level q.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
        then transferAt D G.level q.1 1 2
          ((SuccSource.copyQuad t₀ h π).fluxOp ((Mn.lenFactor * liftLength D G.level)) s₀ Cc) t
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
  have hT := ledgerThr_ge (rH := rH) (nH := nH) (p := Mn.p) (cr := cr)
    (FM := fluxMax κc S Kg Kd Dm rH nH) (KM := covKMax S Kg nH Mn.p) hC.hK0 hC.hW0 hC.hC0 hC.hWr0
    hC.hΔ hF.hCu (q := 1) (u := 1)
    (f := ((UEnv.fluxXc (oldCtx hF.hcert.oldCert κc Δ (compReserve kI v'.1) S Kg Kd) Dm
      (liftB (oldCtx hF.hcert.oldCert κc Δ (compReserve kI v'.1) S Kg Kd) Dm) h 2 : ℝ≥0) : ℝ))
    (dp := (Dm : ℝ) ^ h) (e := 1) zero_le_one zero_le_one (NNReal.coe_nonneg _)
    (pow_nonneg (Nat.cast_nonneg _) _) zero_le_one (one_le_crInv_pow hcr0 hcr1 Dm)
    (by rw [mul_one]; exact one_le_pow₀ hF.hCu) (coe_le_KF (hFle.trans le_self_add))
    (natCast_pow_le_succ_pow Dm hh)
  refine copyQuad_ledger_case hF.hζ hF.hΛ1 hF.hb hF.hκb hF.hstart G G' hF.hcert.oldCert hF.hT hF.hexpU
    hF.hexp hF.hlev π _ s₀ t₀ Cc hset hR γ' hflux2 hmax' (Cw := P.C) hsize'
    (fun j h3 => hF.hℓ _ _ _ h3) (fun j => hresT.trans (hF.hres_path π j))
    hF.hεn (hF.hεpos _) (hF.hεle _) hF.hτ hF.hκ' hF.hη0 hF.hη1 hM.radius_positive hM.radius_le_epsilon hF.hDst0
    hF.hDst κc hC.ha3 hC.hΔ ((add_le_add hres1 hΔD).trans (by norm_num))
    (oldCtx_ok hF.hcert.oldCert κc hC.hΔ.le (hres1.trans one_le_two) hC.hKg hC.hKd) (hM.slow hC.hS)
    ((UEnv.liftWt_mono Dm hh hN₀).trans hLst) ((UEnv.liftWt_mono Dm hh h2).trans hLst)
    hC.hK0 hC.hW0 hC.hC0 hC.hWr0 hC.hK hC.hW hC.hCold hC.hWr ?_
  refine le_trans (le_of_eq ?_) (hT.trans (by rw [mul_one]; exact hthr))
  unfold ledgerA
  ring

open scoped Classical in
/-- **The ledger of a mean letter.** -/
theorem ledger_letterMean_menu_case (hM : MenuFacts kI G G' P Mn Cu cr nMax hMax npad)
    (hC : LedgerConsts b Dm kI.Lstar κc ar Δ K W Cold Wr S Kg Kd)
    (hΔD : (Dm : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1))
    {h : ℕ} (π : StagePath G h) (ρ s₀ : ℝ) (hρ : ρ = Mn.lenFactor * liftLength D G.level)
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
        then transferAt D G.level q.1 ((SuccSource.letterMean t₀ n h π).lam G.level Mn.η0)
          (((SuccSource.letterMean t₀ n h π).prov G.level).tags
            P).order
          ((SuccSource.letterMean t₀ n h π).fluxOp ρ s₀ Cc) t
          (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0)
    {rH nH : ℕ} (hh : h ≤ rH) (hN₀ : N₀ ≤ nH) (hnH : n ≤ nH)
    (hLst : UEnv.liftWt Dm rH nH ≤ kI.Lstar) (hcr0 : 0 < cr) (hcr1 : cr ≤ 1)
    (hthr : ledgerThr Dm rH nH Mn.p K W Cold Wr Δ cr Cu (fluxMax κc S Kg Kd Dm rH nH)
      (covKMax S Kg nH Mn.p) ≤ P.C) :
    LedgerConcl kI κc G' v' u' γ' := by
  have hF := hM.stage
  subst hρ
  obtain ⟨-, hlen', hsize'⟩ :=
    record_of_letter hF.hGT hF.hGT' π γ' (m := G.level) (.mean n h) hprov
  have ho : (((SuccSource.letterMean t₀ n h π).prov G.level).tags
      P).order = n :=
    (Prov.tags_letter _ G.level (.mean n h) π.provList).1
  have hlam : (SuccSource.letterMean t₀ n h π).lam G.level Mn.η0 = D.eps (G.level - 1) ^ (-Mn.η0) :=
    rfl
  have hμ : compReserve kI v'.1 + 1 / ((kI.Hprod : ℝ) + 1) = compReserve kI π.tgt := by
    rw [← htgt]
    exact compReserve_succComp_append kI G.level π.tgt t₀ (.mean n h)
  have hμ1 := compReserve_le_one kI π.tgt
  have hlenρ : (G'.fam.identity v' u' γ').record.length = cr * (Mn.lenFactor * liftLength D G.level) := by
    rw [hlen']
    exact hM.tag_length
  have hsz : (G'.fam.identity v' u' γ').record.size =
      P.C * D.eps (G.level - 1) ^ (ocDelta D.α D.q - Mn.η0) *
        ∏ j : Fin h, (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size := by
    rw [hsize', hM.tag_inflation, hM.tag_epsilon, hM.tag_delta, hM.tag_eta]
    show (1 : ℝ) * P.C * D.eps (G.level - 1) ^ (ocDelta D.α D.q - Mn.η0) * _ = _
    rw [one_mul]
  have hFle := fluxXc_oldCtx_le_fluxMax hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd hh hnH
  have hx0 : 0 ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) /
      (Mn.lenFactor * liftLength D G.level) := div_nonneg hF.hDst0 hM.radius_positive.le
  have hgain := mean_gain_le Mn.η0 hx0 hF.hCu (hF.hεpos (G.level - 1)) (hF.hεle _) hF.hδ
    hM.displacement Mn.p hn hnH
  have hT := ledgerThr_ge (rH := rH) (nH := nH) (p := Mn.p) (cr := cr)
    (FM := fluxMax κc S Kg Kd Dm rH nH) (KM := covKMax S Kg nH Mn.p) hC.hK0 hC.hW0 hC.hC0 hC.hWr0
    hC.hΔ hF.hCu (q := cr⁻¹ ^ Dm)
    (u := |D.eps (G.level - 1) ^ (-Mn.η0)| *
      (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) /
        (Mn.lenFactor * liftLength D G.level)) ^ (n - 2))
    (f := ((UEnv.fluxXc (oldCtx hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd) Dm
      (liftB (oldCtx hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd) Dm) h n + 1 : ℝ≥0) : ℝ))
    (dp := (Dm : ℝ) ^ h) (e := D.eps (G.level - 1) ^ (ocDelta D.α D.q - Mn.η0))
    (pow_nonneg (inv_nonneg.mpr hcr0.le) _) (mul_nonneg (abs_nonneg _) (pow_nonneg hx0 _))
    (NNReal.coe_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (hF.hεn _) _)
    le_rfl hgain (coe_le_KF (add_le_add hFle le_rfl)) (natCast_pow_le_succ_pow Dm hh)
  refine letterMean_ledger_case hF.hζ hF.hΛ1 hF.hb hF.hκb hF.hstart G G' hF.hcert.oldCert hF.hT hF.hexpU
    hF.hexp hF.hlev π _ s₀ t₀ n Cc hset (by omega) hnD hR γ' _ _ (by rw [ho]; exact hnD) hflux
    (Cw := P.C * D.eps (G.level - 1) ^ (ocDelta D.α D.q - Mn.η0)) hsz
    (fun j h3 => hF.hℓ _ _ _ h3) (μ₀ := compReserve kI π.tgt) (fun j => hF.hres_path π j)
    hF.hεn (hF.hεpos _) (hF.hεle _) hF.hτ hF.hκ' hF.hsc.hκ0.le hF.hκκ hF.hη0 hF.hη1
    hM.radius_positive hF.hsc.hεd hF.hDst κc hC.ha3 hC.hΔ (by linarith)
    (oldCtx_ok hF.hcert.oldCert κc hC.hΔ.le (by linarith) hC.hKg hC.hKd) (hM.slow hC.hS)
    ((UEnv.liftWt_mono Dm hh hN₀).trans hLst) ((UEnv.liftWt_mono Dm hh hnH).trans hLst)
    hC.hK0 hC.hW0 hC.hC0 hC.hWr0 hC.hK hC.hW hC.hCold hC.hWr (Q := cr⁻¹ ^ Dm)
    (pow_nonneg (inv_nonneg.mpr hcr0.le) _) (fun d _ hdD i' => ?_) ?_
  · rw [hlenρ]
    exact fresh_Q_le (hF.hεpos _) hM.radius_positive hM.radius_le_epsilon hcr0 hcr1
      (by have := (G'.fam.identity v' u' γ').le_D; omega) i'
  · rw [hlam]
    refine le_trans (le_of_eq ?_)
      (hT.trans (mul_le_mul_of_nonneg_right hthr (Real.rpow_nonneg (hF.hεn _) _)))
    unfold ledgerA
    ring

open scoped Classical in
/-- **The ledger of a covariance letter.** -/
theorem ledger_letterCov_menu_case (hM : MenuFacts kI G G' P Mn Cu cr nMax hMax npad)
    (hC : LedgerConsts b Dm kI.Lstar κc ar Δ K W Cold Wr S Kg Kd)
    (hΔD : (Dm : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1))
    {h : ℕ} (π : StagePath G h) (ρ s₀ : ℝ) (hρ : ρ = Mn.lenFactor * liftLength D G.level) (hs₀ : s₀ = Mn.anchor)
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
        then transferAt D G.level q.1 ((SuccSource.letterCov t₀ n h a a' π).lam G.level Mn.η0)
          (((SuccSource.letterCov t₀ n h a a' π).prov G.level).tags
            P).order
          ((SuccSource.letterCov t₀ n h a a' π).fluxOp ρ s₀ Cc) t
          (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0)
    {rH nH : ℕ} (hh : h ≤ rH) (hN₀ : N₀ ≤ nH) (hnH : n ≤ nH) (ha : a ≤ Mn.p) (ha' : a' ≤ Mn.p)
    (haa : 1 ≤ a + a') (horder : n + 2 * (a + a') ≤ Dm)
    (hΔR : ((4 * nH + 10 * Mn.p : ℕ) : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1))
    (hLst : UEnv.liftWt Dm rH nH ≤ kI.Lstar) (hcr0 : 0 < cr) (hcr1 : cr ≤ 1)
    (hthr : ledgerThr Dm rH nH Mn.p K W Cold Wr Δ cr Cu (fluxMax κc S Kg Kd Dm rH nH)
      (covKMax S Kg nH Mn.p) ≤ P.C) :
    LedgerConcl kI κc G' v' u' γ' := by
  have hF := hM.stage
  subst hρ hs₀
  obtain ⟨-, hlen', hsize'⟩ :=
    record_of_letter hF.hGT hF.hGT' π γ' (m := G.level) (.covariance n h a a') hprov
  have ho : (((SuccSource.letterCov t₀ n h a a' π).prov G.level).tags
      P).order = n + 2 * (a + a') :=
    (Prov.tags_letter _ G.level (.covariance n h a a') π.provList).1
  have hlam : (SuccSource.letterCov t₀ n h a a' π).lam G.level Mn.η0 =
      D.eps (G.level - 1) ^ (-Mn.η0) := rfl
  have hμ : compReserve kI v'.1 + 1 / ((kI.Hprod : ℝ) + 1) = compReserve kI π.tgt := by
    rw [← htgt]
    exact compReserve_succComp_append kI G.level π.tgt t₀ (.covariance n h a a')
  have hμ1 := compReserve_le_one kI π.tgt
  have hR4 : covLetR n a a' ≤ 4 * nH + 10 * Mn.p := by
    unfold covLetR
    omega
  have hgapR : (covLetR n a a' : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1) :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hR4) hC.hΔ.le).trans hΔR
  have hlenρ : (G'.fam.identity v' u' γ').record.length = cr * (Mn.lenFactor * liftLength D G.level) := by
    rw [hlen']
    exact hM.tag_length
  have hsz : (G'.fam.identity v' u' γ').record.size =
      P.C * D.eps (G.level - 1) ^ (ocDelta D.α D.q - Mn.η0) *
        ∏ j : Fin h, (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size := by
    rw [hsize', hM.tag_inflation, hM.tag_epsilon, hM.tag_delta, hM.tag_eta]
    show (1 : ℝ) * P.C * D.eps (G.level - 1) ^ (ocDelta D.α D.q - Mn.η0) * _ = _
    rw [one_mul]
  have hcH0 : 0 ≤ Cu * D.eps (G.level - 1) ^ ocDelta D.α D.q :=
    mul_nonneg (by linarith [hF.hCu]) (Real.rpow_nonneg (hF.hεn _) _)
  have hH : ∀ t i j, |covMat D G.level 0 t i j| + |covMat D G.level 0 Mn.anchor i j| ≤
      ((Real.toNNReal (Cu * D.eps (G.level - 1) ^ ocDelta D.α D.q) *
        Real.toNNReal ((Mn.lenFactor * liftLength D G.level)) ^ 2 : ℝ≥0) : ℝ) := by
    intro t i j
    rw [NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal _ hcH0,
      Real.coe_toNNReal _ hM.radius_positive.le]
    exact hM.covariance_cost t i j
  have hFle := fluxXc_oldCtx_le_fluxMax hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd hh hnH
  have hx0 : 0 ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) /
      (Mn.lenFactor * liftLength D G.level) := div_nonneg hF.hDst0 hM.radius_positive.le
  have hgain := cov_gain_le Mn.η0 hx0 hF.hCu (hF.hεpos (G.level - 1)) (hF.hεle _) hF.hδ
    hM.displacement hnH ha ha' haa
  have hf : ((covLetK n a a' S Kg : ℝ≥0) : ℝ) *
      ((UEnv.fluxXc (oldCtx hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd) Dm
        (liftB (oldCtx hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd) Dm) h n : ℝ≥0) : ℝ) ≤
      (((covKMax S Kg nH Mn.p + 1) * (fluxMax κc S Kg Kd Dm rH nH + 1) : ℝ≥0) : ℝ) := by
    rw [← NNReal.coe_mul]
    exact NNReal.coe_le_coe.mpr (mul_le_mul'
      ((covLetK_le_covKMax S Kg hnH ha ha').trans le_self_add) (hFle.trans le_self_add))
  have hT := ledgerThr_ge (rH := rH) (nH := nH) (p := Mn.p) (cr := cr)
    (FM := fluxMax κc S Kg Kd Dm rH nH) (KM := covKMax S Kg nH Mn.p) hC.hK0 hC.hW0 hC.hC0 hC.hWr0
    hC.hΔ hF.hCu (q := cr⁻¹ ^ Dm)
    (u := |D.eps (G.level - 1) ^ (-Mn.η0)| *
      (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) /
        (Mn.lenFactor * liftLength D G.level)) ^ (n - 2) *
      (Cu * D.eps (G.level - 1) ^ ocDelta D.α D.q) ^ (a + a'))
    (f := ((covLetK n a a' S Kg : ℝ≥0) : ℝ) *
      ((UEnv.fluxXc (oldCtx hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd) Dm
        (liftB (oldCtx hF.hcert.oldCert κc Δ (compReserve kI π.tgt) S Kg Kd) Dm) h n : ℝ≥0) : ℝ))
    (dp := (Dm : ℝ) ^ h) (e := D.eps (G.level - 1) ^ (ocDelta D.α D.q - Mn.η0))
    (pow_nonneg (inv_nonneg.mpr hcr0.le) _)
    (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hx0 _)) (pow_nonneg hcH0 _))
    (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)) (pow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (hF.hεn _) _) le_rfl hgain hf (natCast_pow_le_succ_pow Dm hh)
  refine letterCov_ledger_case_anchor hF.hζ hF.hΛ1 hF.hb hF.hκb hF.hstart G G' hF.hcert.oldCert hF.hT hF.hexpU
    hF.hexp hF.hlev π _ Mn.anchor t₀ n a a' Cc hset hn hR haR γ' _ _ (by rw [ho]; exact horder) hflux
    (Cw := P.C * D.eps (G.level - 1) ^ (ocDelta D.α D.q - Mn.η0)) hsz
    (fun j h3 => hF.hℓ _ _ _ h3) (μ₀ := compReserve kI π.tgt) (fun j => hF.hres_path π j)
    hF.hεn (hF.hεpos _) (hF.hεle _) hF.hτ hF.hκ' hF.hsc.hκm hF.hsc.hκm' hF.hη0 hF.hη1
    hM.radius_positive hF.hDst0 hF.hDst κc hC.ha3 hC.hΔ (by linarith) (by linarith)
    (oldCtx_ok hF.hcert.oldCert κc hC.hΔ.le (by linarith) hC.hKg hC.hKd) (hM.slow hC.hS)
    ((UEnv.liftWt_mono Dm hh hN₀).trans hLst) ((UEnv.liftWt_mono Dm hh hnH).trans hLst)
    hC.hK0 hC.hW0 hC.hC0 hC.hWr0 hC.hK hC.hW hC.hCold hC.hWr
    (cH := Real.toNNReal (Cu * D.eps (G.level - 1) ^ ocDelta D.α D.q)) hH
    (Q := cr⁻¹ ^ Dm) (pow_nonneg (inv_nonneg.mpr hcr0.le) _) (fun d _ hdD i' => ?_) ?_
  · rw [hlenρ]
    exact fresh_Q_le (hF.hεpos _) hM.radius_positive hM.radius_le_epsilon hcr0 hcr1
      (by have := (G'.fam.identity v' u' γ').le_D; omega) i'
  · rw [hlam, NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal _ hcH0]
    refine le_trans (le_of_eq ?_)
      (hT.trans (mul_le_mul_of_nonneg_right hthr (Real.rpow_nonneg (hF.hεn _) _)))
    unfold ledgerA
    ring

end AVRegularity.Providers.CascadeInvariants.Menu
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal Classical
namespace AVRegularity.Providers.CascadeInvariants.Menu

/-! The four generic source cases, with setups supplied by the actual menu lift family. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {kI : InvConsts} {κc : MajConsts}
variable {G G' : GenStage D hr Dm b j₀} {P : ProvParams} {Mn : SuccMenu}
  {Cu cr : ℝ} {nMax hMax npad : ℕ}

/-- Every specified non-diagonal source satisfies the generic ledger. -/
theorem ledger_of_source_menu (hM : MenuFacts kI G G' P Mn Cu cr nMax hMax npad)
    (B : MenuLedgerBudget kI P Mn Cu cr nMax hMax κc b Dm)
    (s : SuccSource G) (hnd : ¬ s.IsDiag) : SourceLedgerStatement kI κc G G' P Mn s := by
  intro hval Cc hLF v' u' γ' hprov htgt hflux
  have hF := hM.stage
  have hlamne : Mn.lenFactor * liftLength D G.level / D.eps (G.level - 1) ≠ 0 :=
    div_ne_zero hM.radius_positive.ne' (hF.hεpos _).ne'
  have hNR : Mn.N + Dm + 2 ≤ max nMax (2 * Mn.p) + Dm + 2 := by
    have : Mn.N ≤ max nMax (2 * Mn.p) := le_max_of_le_left (by have := hM.degree_cap; omega)
    omega
  have hset := fun (k : ℤ) (hk : Odd k) => hasSetup_of_liftFamily hF.hΛ1 hF.hζ hF.hκb hF.hb G
    hF.hGen hF.hT hF.hcert Mn s Cc hLF hlamne hM.reserveX hM.reserveZ hNR k hk
  have hN := hM.degree
  have hNn := hM.degree_cap
  have hres := reserve_of_valid_alphabet hM.alphabet (by omega) s hval
  have hH0 : (0 : ℝ) < (kI.Hprod : ℝ) + 1 := by positivity
  have hstep1 : 1 / ((kI.Hprod : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hH0]
    have : (0 : ℝ) ≤ kI.Hprod := Nat.cast_nonneg _
    linarith only [this]
  have hΔD1 : (Dm : ℝ) * B.Δ ≤ 1 := B.order_step.trans hstep1
  cases s with
  | copyDir t₀ v₀ u₀ γ₀ =>
    exact ledger_copyDir_menu_case hM B.constants hΔD1 γ₀ hval.2.2 _ _ t₀ Cc γ' hprov htgt
      hflux hM.record_pos hM.record_le B.threshold
  | copyQuad t₀ h π =>
    exact ledger_copyQuad_menu_case hM B.constants hΔD1 π _ _ rfl t₀ Cc hset hres γ' hprov htgt
      hflux (stagePath_length_le hM.depth π) (by omega) (by omega) hM.weight
      hM.record_pos hM.record_le B.threshold
  | letterDiag t₀ u₀ => exact absurd trivial hnd
  | letterMean t₀ n h π =>
    have hnD : n ≤ Dm := hM.order_cap (.mean n h) (hval.2.1 _ rfl).2
    have hm := (hval.2.1 _ rfl).2
    rw [hM.alphabet] at hm
    obtain ⟨hn3, hnM, -, hhM⟩ := mean_mem_succAlphabet hm
    exact ledger_letterMean_menu_case hM B.constants B.order_step π _ _ rfl t₀ n Cc hset hn3
      hnD hres.2 γ' hprov htgt hflux hhM (by omega) hnM hM.weight
      hM.record_pos hM.record_le B.threshold
  | letterCov t₀ n h a a' π =>
    have horder : n + 2 * (a + a') ≤ Dm :=
      hM.order_cap (.covariance n h a a') (hval.2.1 _ rfl).2
    have hm := (hval.2.1 _ rfl).2
    rw [hM.alphabet] at hm
    obtain ⟨hn2, hnM, -, hhM, ha, ha', haa⟩ := cov_mem_succAlphabet hm
    exact ledger_letterCov_menu_case hM B.constants B.order_step π _ _ rfl rfl t₀ n a a' Cc hset
      hn2 hres.2.1 hres.2.2 γ' hprov htgt hflux hhM (by omega) hnM ha ha' haa horder B.letter_step
      hM.weight hM.record_pos hM.record_le B.threshold

/-- Generic direct-transport source ledger. -/
theorem ledger_copyDir_menu (hM : MenuFacts kI G G' P Mn Cu cr nMax hMax npad)
    (B : MenuLedgerBudget kI P Mn Cu cr nMax hMax κc b Dm) :
    CopyDirLedgerStatement kI κc G G' P Mn :=
  fun t₀ v₀ u₀ γ₀ => ledger_of_source_menu hM B (.copyDir t₀ v₀ u₀ γ₀) id

/-- Generic quadratic-path source ledger. -/
theorem ledger_copyQuad_menu (hM : MenuFacts kI G G' P Mn Cu cr nMax hMax npad)
    (B : MenuLedgerBudget kI P Mn Cu cr nMax hMax κc b Dm) :
    CopyQuadLedgerStatement kI κc G G' P Mn :=
  fun t₀ h π => ledger_of_source_menu hM B (.copyQuad t₀ h π) id

/-- Generic mean-letter source ledger. -/
theorem ledger_letterMean_menu (hM : MenuFacts kI G G' P Mn Cu cr nMax hMax npad)
    (B : MenuLedgerBudget kI P Mn Cu cr nMax hMax κc b Dm) :
    LetterMeanLedgerStatement kI κc G G' P Mn :=
  fun t₀ n h π => ledger_of_source_menu hM B (.letterMean t₀ n h π) id

/-- Generic covariance-letter source ledger. -/
theorem ledger_letterCov_menu (hM : MenuFacts kI G G' P Mn Cu cr nMax hMax npad)
    (B : MenuLedgerBudget kI P Mn Cu cr nMax hMax κc b Dm) :
    LetterCovLedgerStatement kI κc G G' P Mn :=
  fun t₀ n h a a' π => ledger_of_source_menu hM B (.letterCov t₀ n h a a' π) id
end

/-! First-source ledger at the actual menu radius and covariance anchor. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant
  AVRegularity.Providers.ComplexContext AVRegularity.Providers.ComplexFlow
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {kI : InvConsts} {κc : MajConsts}
variable {G G' : GenStage D hr Dm b j₀} {P : ProvParams} {Mn : SuccMenu}
  {Cu cr : ℝ} {nMax hMax npad : ℕ}

/-- Generic first-source ledger. -/
theorem diag_ledger_case_menu (hM : MenuFacts kI G G' P Mn Cu cr nMax hMax npad)
    (B : MenuDiagBudget kI G P Mn Cu cr κc)
    {CH Υ : ℝ} (env : ChainEnv D b CH Υ j₀) (hij : j₀ ≤ G'.level) :
    DiagLedgerStatement kI κc G G' Mn := by
  intro Cc0 hDL v' u' γ' hprov hflux hres0
  have hF := hM.stage
  have hC := B.constants
  have hm := B.own_small
  have hCa := B.Ca_nonneg
  have hCown := B.Cown_nonneg
  have haτ := B.amplitude_time
  have hown := B.own
  have hCd := B.drift
  have hthr := B.threshold
  have hresΔ : compReserve kI v'.1 + ((fsR Mn.N Mn.p (2 * Mn.N + 1) : ℕ) : ℝ) * B.Δ ≤ 2 :=
    (add_le_add (compReserve_le_one kI v'.1) B.reserve_step).trans (by norm_num)
  have hN : 1 ≤ Mn.N := by have := hM.degree; omega
  have hsX : max (Mn.N + 1) (2 * Mn.p) + Dm + 2 ≤ Mn.sX :=
    hM.diagonal_reserveX
  have hsZ : max (Mn.N + 1) (2 * Mn.p) + Dm + 2 ≤ Mn.sZ :=
    hM.diagonal_reserveZ
  have hlev : G.level = G'.level + 1 := hF.hlev
  rw [hlev] at hprov hDL hflux hm haτ hown hCd
  simp only [Nat.add_sub_cancel] at haτ hown hCd
  have hsc : PassScales D (G'.level + 1) Cu := hlev ▸ hF.hsc
  set i := G'.level with hi
  have hΛ := hF.hΛ1
  have hε : 0 < D.eps i := hF.hεpos i
  have hε1 : D.eps i ≤ 1 := hF.hεle i
  have hδ : 0 < ocDelta D.α D.q := hF.hδ
  have hκm : D.kap (i + 1) = D.κ (i + 1) := hsc.hκm
  have hκi : D.kap i = D.κ i := by simpa only [Nat.add_sub_cancel] using hsc.hκm'
  have hκ0 : 0 < D.kap i := by simpa only [Nat.add_sub_cancel] using hsc.hκ1
  have hκle : D.kap (i + 1) ≤ D.kap i := by simpa only [Nat.add_sub_cancel] using hsc.hκle
  set ρ := Mn.lenFactor * liftLength D (i + 1) with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef, ← hlev]; exact hM.radius_positive
  have hρε : ρ ≤ D.eps i := by
    rw [hρdef, ← hlev]; exact hM.radius_le_epsilon
  have hc : 0 < D.cellScaleSq (i + 1) :=
    EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hF.hζ hF.hκb _
  have hw : Real.toNNReal ρ ≠ 0 := (Real.toNNReal_pos.mpr hρ).ne'
  -- the cost of one label derivative
  obtain ⟨hσc, hσf, hσl, hσw, hSl⟩ := diag_sigma hC hF.hb hε hρ hρε
  set σ := B.s * (Real.toNNReal (D.eps i))⁻¹ with hσdef
  -- the constants
  set KB := bleafK D i Mn.p B.Cd with hKB
  set cB := B.Wl * KB * (Real.toNNReal ρ)⁻¹ with hcBdef
  have hcB : B.Wl * KB ≤ cB * Real.toNNReal ρ :=
    le_of_eq (by rw [hcBdef, mul_assoc (B.Wl * KB), inv_mul_cancel₀ hw, mul_one])
  have hCu0 : 0 ≤ Cu := le_trans zero_le_one hF.hCu
  have hcov : ∀ t a1 b, |covMat D (i + 1) 0 t a1 b| + |covMat D (i + 1) 0 Mn.anchor a1 b| ≤
      ((Real.toNNReal Cu * Real.toNNReal ρ ^ 2 : ℝ≥0) : ℝ) := by
    intro t a1 b
    have h := hM.covariance_cost t a1 b
    rw [hlev] at h
    simp only [Nat.add_sub_cancel] at h
    push_cast
    rw [Real.coe_toNNReal _ hCu0, Real.coe_toNNReal _ hρ.le]
    have hE : D.eps i ^ ocDelta D.α D.q ≤ 1 := Real.rpow_le_one hε.le hε1 hδ.le
    calc |covMat D (i + 1) 0 t a1 b| + |covMat D (i + 1) 0 Mn.anchor a1 b| ≤ Cu * D.eps i ^ ocDelta D.α D.q * ρ ^ 2 := h
      _ ≤ Cu * 1 * ρ ^ 2 := by gcongr
      _ = Cu * ρ ^ 2 := by ring
  -- the reserves
  have hR1 : Mn.N + 1 + Dm + 2 ≤ min Mn.sX Mn.sZ := by
    have := le_max_left (Mn.N + 1) (2 * Mn.p)
    exact le_min (by omega) (by omega)
  have hR2 : 2 * Mn.p + Dm + 2 ≤ min Mn.sX Mn.sZ := by
    have := le_max_right (Mn.N + 1) (2 * Mn.p)
    exact le_min (by omega) (by omega)
  -- the slot expressions
  have hslot := fun (pc : OddSlot) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) =>
    slot_firstSource_ctxAlgQ_anchor (s₀ := Mn.anchor) (𝒮 := G.exports) env hF.hκb hρ hN (min_le_left Mn.sX Mn.sZ)
      (min_le_right Mn.sX Mn.sZ) hR1 hR2 hsc.hDst hκm hκi hκle Cc0 hDL κc hC.hΔ hC.hLN hσc hσf hσw
      hC.hWg hC.hWc hC.hWl hC.hKg hC.hKd hSl hcov hcB pc d I c
  set X := diagX D b j₀ G.exports i (2 * Mn.p) κc B.Δ B.a B.a₀ B.L₀ σ KB with hXdef
  have hX : X.Ok := diagX_ok hC.hΔ.le
  set F := fsK Mn.N Mn.p B.s B.Wg (Real.toNNReal Cu)
    (jhK (4 * Mn.p) B.Wg (Real.toNNReal (ocA D.α D.q D.Λ i)) (Real.toNNReal Cu) (Real.toNNReal ρ))
    (dfK D (X.toG B.S B.Kg B.Kd) Dm i ρ Mn.N Mn.p B.s cB B.Wc) with hFdef
  set lamd : ℕ → ℝ := fun d => D.eps i ^ (-Mn.η0) * (D.κ i * D.eps i ^ (d - 2))⁻¹ with hlamd
  -- the leaf map is certified
  have hstart := hF.hstart
  have hNR : Mn.N + Dm + 2 ≤ min Mn.sX Mn.sZ := by omega
  have hLC : LeavesCertified D b j₀ X.leaf := by
    have hB := fun pc : OddSlot => bridgeCtx_of hΛ hF.hζ hF.hκb hF.hb hstart G.exports hρ.ne' hN
      (min_le_left Mn.sX Mn.sZ) (min_le_right Mn.sX Mn.sZ) hNR hsc.hDst Cc0 hDL pc.1
    exact leavesCertified_bleaf env hij hF.hexpU hm hCd hc hκm hκle hC.hΔ le_rfl hσl
      (by omega) (by omega) _ _ _ hB fun x => exists_leafRep hΛ hF.hζ hF.hκb hF.hb hstart
        G.exports hρ.ne' hN (min_le_left Mn.sX Mn.sZ) (min_le_right Mn.sX Mn.sZ) hNR hsc.hDst Cc0 hDL hκm x.1.1
        x.2.1 x.2.2.1 (by have := Nat.lt_succ_iff.mp x.2.2.2.1.2; omega) (by omega) x.2.2.2.2
  have ha0 : 0 ≤ B.a := by have := mul_pos Real.pi_pos hF.hb; linarith [hC.ha3]
  refine ⟨fun d _ _ => B.Wr * (|lamd d| * ((F * Real.toNNReal ρ ^ (d - 1) : ℝ≥0) : ℝ)),
    fun d _ _ => mul_nonneg hC.hWr0 (mul_nonneg (abs_nonneg _) (NNReal.coe_nonneg _)),
    fun d hd hdD => ?_, fun d I c => ?_⟩
  · -- the record bound
    obtain ⟨hm', ho'⟩ := hF.hGT' v' u' γ'
    rw [hprov] at hm' ho'
    obtain ⟨h1, h2, h3⟩ := Prov.tags_letter P (i + 1) .diag []
    rw [ho', h1, hM.tag_degree, hM.tag_covariance] at hdD
    rw [hm'.1, hm'.2.2.2.1, h2, h3]
    have hwtag : P.w i = 1 := by simpa only [hlev, Nat.add_sub_cancel] using hM.tag_inflation
    have hltag : P.Rb i = cr * ρ := by simpa only [hlev, Nat.add_sub_cancel] using hM.tag_length
    simp only [Nat.add_sub_cancel]
    rw [hwtag, hM.tag_epsilon, hM.tag_delta, hM.tag_eta, hltag]
    simp only [Prov.pathTags, List.map_nil, List.prod_nil, mul_one, one_mul,
      letterOrder] at hdD ⊢
    have hFb := fsK_diag_le D i (X' := X.toG B.S B.Kg B.Kd) (κc := κc) ⟨rfl, rfl, rfl⟩ Dm Mn.N Mn.p B.s B.Wg B.Wl B.Wc
      (Cd := B.Cd) hρ
      (by rw [hρdef, mul_pow, liftLength, Nat.add_sub_cancel, Real.sq_sqrt
        (mul_nonneg (hκi ▸ hκ0.le) (Construction.Stream.ocTauPP_pos hΛ).le), hκi]; ring)
      hκ0.le hCa hCown hε hε1 hδ.le haτ hown hc hsc.hDst
      (mul_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le (Real.sqrt_nonneg _))
      (by simpa only [hlev, Nat.add_sub_cancel] using hM.displacement) hF.hCu hΛ
    rw [← NNReal.coe_le_coe] at hFb
    simp only [NNReal.coe_mul, Real.coe_toNNReal _ hρ.le,
      Real.coe_toNNReal _ (mul_nonneg hκ0.le (Real.rpow_nonneg hε.le _))] at hFb
    have hκ' : 0 < D.κ i := hκi ▸ hκ0
    rw [hκi] at hFb
    unfold diagThr at hthr
    refine Eq.trans_le ?_ (diag_record_le (η := Mn.η0) hd hdD hε hM.record_pos hM.record_le hρ hκ' hC.hWr0
      (NNReal.coe_nonneg _) hFb hthr)
    congr 1
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun c _ => ?_
    simp only [hlamd, NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal _ hρ.le]
    rfl
  · -- the expressions
    by_cases hd : 2 ≤ d
    · choose φ E hφ hrep hsf hnm hbound using fun pc : OddSlot => hslot pc d I c
      refine ⟨fun pc => Gen.mul (Gen.time (.const (lamd d))) (E pc), B.Δ, X.leaf, fun q => ?_,
        hC.hΔ, hLC, fun pc => Or.inr ⟨trivial, hsf pc⟩, ?_⟩
      · obtain ⟨hs, hf, f, hd', hv⟩ := hrep q
        refine ⟨.mul (.timeConst _) hs, .mul (.time _) (fromSeed_mono hF.hexp hf), _,
          .mul (.time _) hd', fun ctx t ht X z => ?_⟩
        rw [hflux q ctx d I t X z hd]
        split_ifs with hadm
        · have hPz : slotCtx D b j₀ i q.1 t (ctx.1.recenter D (D.eps (i - 1) • X)) z :=
            And.intro hadm ht
          have h1 := hv t _ z hPz
          have h2 := hφ q ⟨(t, ctx.1.recenter D (D.eps (i - 1) • X), z), hPz⟩
          simp only [Pi.smul_apply, smul_eq_mul, GenSort.mul, GenSort.ofTime, TimeLetter.eval]
          rw [h1, ← h2]
          simp only [hlamd, Nat.add_sub_cancel]
          rfl
        · rfl
      · refine (ledgerSum_le D κc B.Δ B.a₀ X.leaf hC.ha₀
          (fun pc => Gen.mul (Gen.time (.const (lamd d))) (E pc)) ha0 (3 * Real.pi * b) kI.Lstar
          (compReserve kI v'.1) (ENNReal.ofReal |lamd d| *
            ((F * Real.toNNReal ρ ^ (d - 1) : ℝ≥0) : ℝ≥0∞)) fun pc t ht => ?_).trans ?_
        · rw [genNorm_mul_eq _ _ _ _ _ (hX.hshape _ (not_isMarkShape_mul _ _)),
            genNorm_const_eq _ _ _ _ _ _ (hX.hshape _ (not_isMarkShape_time _))]
          exact mul_le_mul' le_rfl (hbound pc t ht (compReserve kI v'.1) 0 hres0 hresΔ
            (by rw [zero_add]; exact hC.hLf))
        · calc wsum (3 * Real.pi * b) kI.Lstar (expProfile 1 B.a) * (ENNReal.ofReal |lamd d| *
                ((F * Real.toNNReal ρ ^ (d - 1) : ℝ≥0) : ℝ≥0∞))
              ≤ ENNReal.ofReal B.Wr * (ENNReal.ofReal |lamd d| *
                ((F * Real.toNNReal ρ ^ (d - 1) : ℝ≥0) : ℝ≥0∞)) := mul_le_mul' hC.hWr le_rfl
            _ = ENNReal.ofReal (B.Wr * (|lamd d| * ((F * Real.toNNReal ρ ^ (d - 1) : ℝ≥0) : ℝ))) := by
                rw [ENNReal.ofReal_mul hC.hWr0, ENNReal.ofReal_mul (abs_nonneg _),
                  ENNReal.ofReal_coe_nnreal]
    · refine ⟨fun pc => Gen.time (.const 0), B.Δ, X.leaf, fun q => ⟨.timeConst 0, .time _,
        GenSort.ofTime .ctx (TimeLetter.eval D (.const 0)), .time _, fun ctx t _ X z => ?_⟩,
        hC.hΔ, hLC, fun _ => trivial, ?_⟩
      · rw [G'.fam.flux_zero q ctx v' u' γ' d I (fun h => hd h.1)]
        split_ifs <;> simp [GenSort.ofTime, TimeLetter.eval]
      · refine (ledgerSum_le D κc B.Δ B.a₀ X.leaf hC.ha₀ (fun pc => Gen.time (.const 0)) ha0
          (3 * Real.pi * b) kI.Lstar (compReserve kI v'.1) 0 fun pc t _ => ?_).trans ?_
        · rw [genNorm_const_eq _ _ _ _ _ _ (hX.hshape _ (not_isMarkShape_time _))]
          simp
        · rw [mul_zero]
          exact zero_le
end

end AVRegularity.Providers.CascadeInvariants.Menu
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.CascadeInvariants.Menu

/-! The complete one-step ledger at an arbitrary successor menu. -/

open AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Every identity of an actual successor has the ledger bound, at its menu radius and anchor. -/
theorem ledger_all_menu (kI : InvConsts) (κc : MajConsts)
    (G G' : GenStage D hr Dm b j₀) (P : ProvParams) (Mn : SuccMenu) :
    LedgerAllMenuStatement kI κc G G' P Mn := by
  intro Cu cr nMax hMax npad hM B BD CH Υ env hij hSucc v' u' γ' hres
  exact ledger_all_menu_of_cases (ledger_copyDir_menu hM B) (ledger_copyQuad_menu hM B)
    (ledger_letterMean_menu hM B) (ledger_letterCov_menu hM B)
    (diag_ledger_case_menu hM BD env hij) hSucc γ' hres

end AVRegularity.Providers.CascadeInvariants.Menu
end
