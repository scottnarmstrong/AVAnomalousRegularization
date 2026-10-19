-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Assembly.SuccessorResidualIdentitiesOfIngredients
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Definitions.Finite.FiniteLiftBridge

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.Seed

/-! Shrinking envelope domains and derivative reserves, and enlarging their constants. -/

section
theorem jetSupFam_domain_mono {ι : Type*} (dom dom' : ι → Set (ℝ × Vec 2))
    (hdom : ∀ i, dom i ⊆ dom' i) (r q : ℕ)
    (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2) :
    jetSupFam dom r q f ≤ jetSupFam dom' r q f := by
  apply iSup_mono
  intro i
  unfold jetSupOn
  refine essSup_mono_ae (ae_of_all volume ?_)
  intro t
  exact iSup_le fun Y => iSup_le fun hY =>
    le_iSup_of_le Y (le_iSup_of_le (hdom i hY) le_rfl)

private theorem rectangle_sum_mono {a b c d : ℕ} (ha : a ≤ c) (hb : b ≤ d)
    (f g : ℕ → ℕ → ℝ≥0∞) (hfg : ∀ r q, f r q ≤ g r q) :
    (∑ r ∈ Finset.range a, ∑ q ∈ Finset.range b, f r q) ≤
      ∑ r ∈ Finset.range c, ∑ q ∈ Finset.range d, g r q := by
  apply le_trans _ (Finset.sum_le_sum_of_subset (Finset.range_mono ha))
  exact Finset.sum_le_sum fun r _ =>
    (Finset.sum_le_sum fun q _ => hfg r q).trans
      (Finset.sum_le_sum_of_subset (Finset.range_mono hb))

private theorem analyticJet_domain_order_mono {ι : Type*} (dom dom' : ι → Set (ℝ × Vec 2))
    (hdom : ∀ i, dom i ⊆ dom' i) (E : ℝ) {K L K' L' : ℕ} (hK : K ≤ K') (hL : L ≤ L')
    (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2) :
    (∑ r ∈ Finset.range (K+1), ∑ q ∈ Finset.range (L+1),
      ENNReal.ofReal (E^r) * jetSupFam dom r q f) ≤
    ∑ r ∈ Finset.range (K'+1), ∑ q ∈ Finset.range (L'+1),
      ENNReal.ofReal (E^r) * jetSupFam dom' r q f :=
  rectangle_sum_mono (Nat.succ_le_succ hK) (Nat.succ_le_succ hL) _ _
    (fun r q => mul_le_mul_right (jetSupFam_domain_mono dom dom' hdom r q f) _)

private theorem molecularJet_domain_mono {ι : Type*} (dom dom' : ι → Set (ℝ × Vec 2))
    (hdom : ∀ i, dom i ⊆ dom' i) (ρ e : ℝ) (k j : ℕ)
    (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2) :
    molecularJet ρ e k j dom f ≤ molecularJet ρ e k j dom' f := by
  exact Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun q _ =>
    mul_le_mul_right (jetSupFam_domain_mono dom dom' hdom (r+j) q f) _

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem smoothOn_domain_order_mono (F : ChartedFamily ι h D P Ctx)
    {dom dom' : F.Domain} (hdom : ∀ p c, dom p c ⊆ dom' p c)
    {E : ℝ} {n n' : ι → ℕ} (hn : ∀ v, n v ≤ n' v)
    (hs : F.IsSmoothOn dom' E n') : F.IsSmoothOn dom E n := by
  intro p c v u γ d I tY htY z
  exact (hs p c v u γ d I tY (hdom p c htY) z).of_le (by exact_mod_cast hn v)

theorem analyticEnvelope_mono (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) {dom dom' : F.Domain} (hdom : ∀ p c, dom p c ⊆ dom' p c)
    (E C C' : ℝ) {Ks Ls Ks' Ls' : ℕ} (hK : Ks ≤ Ks') (hL : Ls ≤ Ls')
    (b : ι → ι → ℝ) (hb : ∀ v u, 0 ≤ b v u) (hC : C ≤ C')
    (he : IsAnalyticEnvelope F π dom' E C Ks' Ls' b) :
    IsAnalyticEnvelope F π dom E C' Ks Ls b := by
  refine ⟨smoothOn_domain_order_mono F hdom (fun _ => Nat.add_le_add hK hL) he.1, ?_⟩
  intro v u
  apply le_trans ?_ ((he.2 v u).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hC (hb v u))))
  have hjet (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) :
      (∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (Ls + 1),
        ENNReal.ofReal (E ^ r) * jetSupFam (fun x : F.Index => dom x.1 x.2) r q
          (fun x => F.slowFlux E x.1 x.2 v u γ d I)) ≤
      ∑ r ∈ Finset.range (Ks' + 1), ∑ q ∈ Finset.range (Ls' + 1),
        ENNReal.ofReal (E ^ r) * jetSupFam (fun x : F.Index => dom' x.1 x.2) r q
          (fun x => F.slowFlux E x.1 x.2 v u γ d I) :=
    analyticJet_domain_order_mono (fun x : Σ p, Ctx p => dom x.1 x.2)
      (fun x : Σ p, Ctx p => dom' x.1 x.2) (fun x => hdom x.1 x.2) E hK hL
      (fun x => F.slowFlux E x.1 x.2 v u γ d I)
  exact mul_le_mul_right (Finset.sum_le_sum fun γ _ =>
    mul_le_mul_right (Finset.sum_le_sum fun d _ =>
      Finset.sum_le_sum fun I _ => hjet γ d I) _) _

theorem molecularEnvelope_mono (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) {dom dom' : F.Domain}
    (hdom : ∀ p c, dom p c ⊆ dom' p c) (ν e E ρ : ℝ) (hE : 0 ≤ E)
    (C C' : ℕ → ℝ) {J J' : ℕ} (hJ : J ≤ J') (hC : ∀ j, C j ≤ C' j)
    (b : ι → ι → ℝ) (hb : ∀ v u, 0 ≤ b v u)
    (he : IsMolecularEnvelope F π K dom' ν e E ρ C J' b) :
    IsMolecularEnvelope F π K dom ν e E ρ C' J b := by
  refine ⟨smoothOn_domain_order_mono F hdom (fun _ => Nat.add_le_add_left hJ _) he.1, ?_⟩
  intro v u j hj
  apply le_trans ?_ ((he.2 v u j (hj.trans hJ)).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC j)
      (inv_nonneg.mpr (pow_nonneg hE _))) (hb v u))))
  have hjet (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) :
      molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) ≤
      molecularJet ρ e (K v) j (fun x : F.Index => dom' x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) :=
    molecularJet_domain_mono (fun x : Σ p, Ctx p => dom x.1 x.2)
      (fun x : Σ p, Ctx p => dom' x.1 x.2) (fun x => hdom x.1 x.2) ρ e (K v) j
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)
  exact mul_le_mul_right (Finset.sum_le_sum fun γ _ =>
    mul_le_mul_right (Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun I _ =>
      mul_le_mul_left (mul_le_mul_left (hjet γ d I) _) _) _) _
end

/-! Admissible changes of seed constants preserve every invariant clause except repricing,
which is supplied explicitly by the separate seed estimate. -/

private theorem ctxSize_weight_mono (D : OCData) (b : ℝ) (j₀ i : ℕ)
    (F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ) (μ : ℝ)
    {L L' : ℕ} (hL : L ≤ L') : ctxSize D b j₀ i F μ L ≤ ctxSize D b j₀ i F μ L' := by
  unfold ctxSize
  apply ENNReal.tsum_le_tsum
  intro h
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by have := abs_nonneg (h : ℝ); linarith) hL)
    (Real.exp_pos _).le

theorem stage_invariant_constants_mono : Assembly.StageInvariantConstantsMonoStatement := by
  intro hr _ _ _ _ _ _ D Dm bw j₀ hbw hε law P seedK freshK φ₀ hφ₀ M kS thr kI
    H J N p nk Kres Lpr Lc Lf σ₀ δ q c hadm hc₀ hcr G tS tf S θ S' θ' he hE hI hS hprice
  rcases hadm with ⟨hc, hcrEq, hΓ, _hΓthr, hCwid, _hCwthr, hσ,
    _hσlam, hlam, _hlammax, hCa, _hCathr, hCm, hcker, _hLlo, hL, _hLnk,
    _hKslo, hKs, _hKanlo, hKan, _hLanlo, hLan, _hJlo, hJ, _hLstarlo, hLstar,
    hG0, hHprod, _hprod, _hm0, hmm, _hmb⟩
  rcases hI with ⟨hnat, htags, hgen, hshift, htrans, hcert, henv, hled, hkern, _hschur,
    hquiet⟩
  have hres (v : CompIn G.comps) : compReserve kI v.1 = compReserve kS v.1 := by
    simp only [compReserve, hG0, hHprod]
  have hdom : ∀ p c, G.innerDomain (Set.Icc tS tf) kI.mEnv p c ⊆
      G.innerDomain (Set.Icc tS tf) kS.mEnv p c := by
    intro p c tY htY
    refine ⟨htY.1, ?_⟩
    rcases htY.2 with ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
    intro k hk
    exact (h7 k hk).trans_le (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (add_le_add (le_refl 1) hmm) hbw.le) (by norm_num)) (hε _).le)
  have hρ : 0 ≤ rhoStar D kS.c₀ G.level :=
    mul_nonneg hc₀ (le_min (hε _).le (Real.sqrt_nonneg _))
  have hρe : 0 ≤ rhoEnh D kS.cr G.level := mul_nonneg hcr (Real.sqrt_nonneg _)
  refine ⟨hnat, htags, hgen, hshift, htrans, ?_, ?_, hled.trans hS, ?_, hprice, hquiet⟩
  · intro v u γ
    obtain ⟨θ, hθ, hrecord, hex⟩ := hcert v u γ
    refine ⟨θ, hθ, hrecord, ?_⟩
    intro d I c
    obtain ⟨f, F, hF, hsize⟩ := hex d I c
    refine ⟨f, F, hF, ?_⟩
    rw [hres v]
    exact (ctxSize_weight_mono D bw j₀ G.level _ _ hLstar).trans hsize
  · intro K hK
    obtain ⟨ha, hm⟩ := henv K (fun v => (hK v).trans hKs)
    have henvMono (F : ChartedFamily (CompIn G.comps) (fun v => hr v.1.root) Dm OddSlot
        (StageCtx D bw j₀ G.level)) (b : CompIn G.comps → CompIn G.comps → ℝ)
        (hh : IsEnvelope F (G.mass law) K (G.innerDomain (Set.Icc tS tf) kS.mEnv)
          (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) (rhoStar D kS.c₀ G.level)
          b S kS.Ca kS.Kan kS.Lan kS.Cm kS.Jm) :
        IsEnvelope F (G.mass law) K (G.innerDomain (Set.Icc tS tf) kI.mEnv)
          (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) (rhoStar D kI.c₀ G.level)
          b S' kI.Ca kI.Kan kI.Lan kI.Cm kI.Jm := by
      rw [hc]
      exact ⟨hh.nonneg, fun v => (hh.row_sum v).trans hS,
        fun u => (hh.col_sum u).trans hS,
        analyticEnvelope_mono F (G.mass law) hdom _ _ _ hKan hLan b hh.nonneg hCa hh.analytic,
        molecularEnvelope_mono F (G.mass law) K hdom _ _ _ _ (hε _).le _ _ hJ
          (fun j => (hCm j).1) b hh.nonneg hh.molecular⟩
    exact ⟨henvMono G.fam _ ha, henvMono (markerConj (G.marker law) G.fam) _ hm⟩
  · intro v u γ
    obtain ⟨hadmK, hw, hfine, hcoarse, hreg⟩ := hkern v u γ
    have hσle : kI.σf ≤ kS.σf := by rw [hσ]; exact min_le_left _ _
    have hfp : 0 ≤ kS.Cwid * rhoStar D kS.c₀ G.level := by
      exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos (hε _) kS.σf)).mp
        ((G.fam.identity v u γ).record.width_pos.le.trans hfine)
    have hcp : 0 ≤ kS.Cwid * rhoEnh D kS.cr G.level := by
      exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos (hε _) kS.lamC)).mp
        ((G.fam.identity v u γ).record.width_pos.le.trans hcoarse)
    refine ⟨?_, hw, ?_, ?_, ?_⟩
    · exact ⟨hadmK.1, hadmK.2.1, fun t => ⟨(hadmK.2.2.1 t).1.trans hΓ,
        (hadmK.2.2.1 t).2.1.trans hΓ, (hadmK.2.2.1 t).2.2.1,
        (hadmK.2.2.1 t).2.2.2.trans hΓ⟩, (Nat.add_le_add_right hL 1).trans hadmK.2.2.2⟩
    · rw [hc]
      exact hfine.trans ((mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge (hε _) he hσle) hfp).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCwid hρ)
          (Real.rpow_nonneg (hε _).le _)))
    · rw [hcrEq]
      exact hcoarse.trans ((mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge (hε _) hE hlam) hcp).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCwid hρe)
          (Real.rpow_nonneg (hε _).le _)))
    · intro ρ hρ kk hkk
      exact FullLift.spatial_regularizer_constants_mono (hreg ρ hρ kk (hkk.trans hKs))
        (by rw [hw]; exact (G.fam.identity v u γ).record.width_pos.le)
        (fun j _ => (hcker j).1)

end AVRegularity.Construction.Preservation.Seed
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Seed

/-! Reprice the supplied seed using the proved native identity estimates, then convert its
wavelength decay to the parent wavelength. All choices precede the birth law. -/

private theorem decay_to_parent {e E q τ τe : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hE : 0 < E) (hτ : 0 ≤ τ) (hτe : τ ≤ τe)
    (hstep : e ≤ 2 * E ^ q) : e ^ τe ≤ (2 : ℝ) ^ τ * E ^ (q * τ) := by
  apply (Real.rpow_le_rpow_of_exponent_ge he he1 hτe).trans
  have hh := Real.rpow_le_rpow he.le hstep hτ
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hE.le _),
    ← Real.rpow_mul hE.le] at hh
  exact hh

private theorem schur_constants_mono
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (G : GenStage D hr Dm bw j₀) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (ν ρ a b : ℝ) (π : CompIn G.comps → ℝ) (k : ℕ) (c C : ℕ → ℝ)
    (hc : ∀ j, c j ≤ C j) (hν : 0 < ν)
    (hrpos : ∀ v u γ, 0 < (G.kernelOf P seedK freshK v u γ).width)
    (v u : CompIn G.comps) :
    kernelSchurMatrix ν ρ π k Dm a b c
      (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
      (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
      (fun v u γ d => G.physCoeff v u γ d.1) v u ≤
    kernelSchurMatrix ν ρ π k Dm a b C
      (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
      (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
      (fun v u γ d => G.physCoeff v u γ d.1) v u := by
  unfold kernelSchurMatrix
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Finset.sum_le_sum
  intro γ _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro d _
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hc _) ENNReal.toReal_nonneg)
    (mul_nonneg hν.le (pow_nonneg (hrpos v u γ).le _))

theorem seed_ledger_decay_conversion :
    ∀ (α s q : ℝ) (ζ : ℝ → ℝ), Assembly.SeedLedgerDecayConversionStatement α s q ζ := by
  classical
  intro α s q ζ hα0 hα1 hs0 hs1 hq hζ
  refine ⟨128, le_rfl, ?_⟩
  intro Λ hΛ
  refine ⟨1, zero_lt_one, ?_⟩
  intro φ₀ hφ₀ _hφsmooth _hφnonneg _hφmass _hφsupport bw hbw _hbwmax Q T₀ _hQ _hT
    Ce τe kS r₀ D₀ hCe hτ hcS hcSmax _hcr _hcrmax _hσf _hlam H J N p nk Lc Lf Lpr Acl Naux Nout
    Kres npad sX sZ σ₀ a σ _hsched _haux _hres halloc
  refine ⟨kS, 1, 1, le_rfl, zero_lt_one, ?_⟩
  intro kI hadm
  let c : ℕ → ℝ := fun j => max (kI.cker j) 0
  have hc (j : ℕ) : 0 ≤ c j := le_max_right _ _
  have hh (kk : Fin (kI.Ks + 1)) := FullLift.uniform_native_kernel_schur_of_certificates
    α s q hα0 hα1 hs0 hs1 hq Λ hΛ ζ hζ bw hbw kk.1
    (kk.1 + succSchedD D₀ N p (H+1)) (succSchedD D₀ N p (H+1)) le_rfl c (fun j _ => hc j)
  choose A hA m₀ hm₀ hb using hh
  let Atot : ℝ := ∑ kk, A kk
  have hAtot : 0 ≤ Atot := Finset.sum_nonneg fun kk _ => hA kk
  have hAle (kk : Fin (kI.Ks+1)) : A kk ≤ Atot :=
    Finset.single_le_sum (fun kk _ => hA kk) (Finset.mem_univ kk)
  let τ := min (ocDelta α q / 4) τe
  have hτpos : 0 < τ := lt_min (div_pos (ocDelta_pos_of_admissible hα0 hq) (by norm_num)) hτ
  let CIthr := Atot * Ce * (2 : ℝ) ^ τ
  refine ⟨CIthr, 0, ?_⟩
  intro CI Cw j₀ hled _hstart
  let mStar := max j₀ (Finset.univ.sup m₀ + 2)
  refine ⟨mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat _hMnat law _hlaw hr _ _ _ _ _ _
    seedK freshK _hfresh seed n tS tf hseed hn hnM
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hqD : 1 < D.q := hDq.symm ▸ hq.1
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have he (i : ℕ) := Scales.epsilon_basic (m := i) hqD hΛD
  have hnterm : seed.level ≤ D.term := by rw [hseed.1, hterm]; exact hnM.le
  have hκ : 0 < D.κ seed.level := CycleReference.bandChain_pos (by omega) hζD hbandD hnterm
  have hν : 0 < D.kap seed.level := by simpa only [OCData.kap, min_eq_left hnterm] using hκ
  have hρ := Buffer.molecular_radius_bounds (a := ocA D.α D.q D.Λ seed.level) hcS (he seed.level).1 hκ
    (Real.rpow_pos_of_pos (he seed.level).1 _)
  have hcEq := hadm.1
  have hρpos : 0 < rhoStar D kI.c₀ seed.level := by simpa only [hcEq, rhoStar, OCData.eps] using hρ.1
  have hρle : rhoStar D kI.c₀ seed.level ≤ D.eps seed.level := by
    rw [hcEq]
    exact hρ.2.1.trans (mul_le_of_le_one_left (he _).1.le hcSmax)
  have hεmono : D.eps seed.level ≤ D.eps (seed.level-1) :=
    EntryScales.epsilon_antitone hqD hΛD (Nat.sub_le _ _)
  have hI := hseed.2.2.2.2.2.2.2.1
  rcases hI with ⟨hnat, _htags, _hgen, _hshift, htrans, hcert, _henv, hledger, hkern, _hschur,
    _hquiet⟩
  have hprod : kS.Hprod = kS.G0 + H + 1 := halloc.2.2.2.2.2.2.2.2.1
  have hreserve (v : CompIn seed.comps) : 0 ≤ compReserve kS v.1 := by
    have hg : compGrade v.1 = 0 := by simp only [compGrade, hseed.2.1 v, List.length_nil]
    exact (by positivity : (0 : ℝ) ≤ 1 / ((kS.Hprod : ℝ) + 1)).trans
      (Buffer.compReserve_ge_allocated_gap kS H hprod v.1 (by rw [hg]; omega))
  have hreserve2 (v : CompIn seed.comps) : compReserve kS v.1 ≤ 2 :=
    (Buffer.compReserve_le_one kS v.1).trans (by norm_num)
  have hwidth (v u : CompIn seed.comps) (γ : seed.fam.Γ v u) :
      (seed.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK v u γ).width =
        (seed.fam.identity v u γ).record.width := (hkern v u γ).2.1
  have hlen (v u : CompIn seed.comps) (γ : seed.fam.Γ v u)
      (hd : 3 ≤ (seed.fam.identity v u γ).maxOrder) :
      (seed.fam.identity v u γ).record.length ≤ D.eps (seed.level-1) := by
    have hbirth : 1 ≤ (seed.fam.identity v u γ).record.birthExcess := by
      have := (seed.fam.identity v u γ).le_birth
      omega
    have hh := (hseed.2.2.2.2.2.1 v u γ).2.2 hbirth
    rw [← hseed.1] at hh
    exact hh.trans hεmono
  have hCe0 : 0 ≤ Ce := zero_le_one.trans hCe
  have hscalar : Ce * D.eps n ^ τe ≤ CI * D.eps n ^ τ :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (he n).1 (he n).2.1 (min_le_right _ _)) hCe0).trans
      (mul_le_mul_of_nonneg_right hled.1 (Real.rpow_nonneg (he n).1.le _))
  refine ⟨(he n).2.1, (he (n-1)).2.1, hscalar, ?_⟩
  intro kk hkk w hw
  let ki : Fin (kI.Ks+1) := ⟨kk, by omega⟩
  have hmki : m₀ ki + 1 ≤ seed.level := by
    have hi := Finset.le_sup (f := m₀) (Finset.mem_univ ki)
    dsimp [mStar] at hn
    rw [hseed.1]
    omega
  have hj : j₀ ≤ seed.level := by rw [hseed.1]; exact (le_max_left _ _).trans hn
  have hi : 1 ≤ seed.level := by have := hm₀ ki; omega
  have hp := hb ki hr D hDα hDq hDΛ hDζ hseq j₀ Mnat seed kS hcert hnat hmki hi hj
    (he _).1 (he _).1 hν htrans hreserve hreserve2
    (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK hwidth tS tf
    (rhoStar D kI.c₀ seed.level) (Ce * D.eps n ^ τe) (seed.mass law) (seed.marker law)
    hρpos (hρle.trans hεmono) hρle hlen
    (fun v => Buffer.birth_compMass_pos hqD hΛD law v.1)
    (fun v => Buffer.birth_compMarker_pos hqD hΛD law v.1) hledger w hw
  have hq16D : D.q < 17 / 16 := hDq.symm ▸ hq.2.1
  have hn1 : 1 ≤ n := by rw [hseed.1] at hi; exact hi
  have hstep : D.eps n ≤ 2 * D.eps (n-1) ^ q := by
    simpa only [OCData.eps, hDq] using (Scales.epsilon_q_step hqD hq16D hΛD hn1)
  have hdecay := decay_to_parent (he n).1 (he n).2.1 (he (n-1)).1 hτpos.le (min_le_right _ _) hstep
  have hbudget : A ki * (Ce * D.eps n ^ τe) ≤ CI * D.eps (n-1) ^ (q*τ) := calc
    _ ≤ Atot * (Ce * D.eps n ^ τe) := mul_le_mul_of_nonneg_right (hAle ki)
      (mul_nonneg hCe0 (Real.rpow_nonneg (he n).1.le _))
    _ = (Atot * Ce) * D.eps n ^ τe := (mul_assoc _ _ _).symm
    _ ≤ (Atot * Ce) * ((2 : ℝ)^τ * D.eps (n-1)^(q*τ)) :=
      mul_le_mul_of_nonneg_left hdecay (mul_nonneg hAtot hCe0)
    _ = CIthr * D.eps (n-1)^(q*τ) := (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hled.2.1 (Real.rpow_nonneg (he (n-1)).1.le _)
  have hentry := schur_constants_mono seed
    (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
    (D.kap seed.level) (rhoStar D kI.c₀ seed.level) tS tf
    (fun v => seed.mass law v / w v ^ 2) kk kI.cker c (fun j => le_max_left _ _) hν
    (fun v u γ => by rw [hwidth v u γ]; exact (seed.fam.identity v u γ).record.width_pos)
  exact ⟨fun v => (Finset.sum_le_sum fun u _ => hentry v u).trans ((hp.1 v).trans hbudget),
    fun u => (Finset.sum_le_sum fun v _ => hentry v u).trans ((hp.2 u).trans hbudget)⟩

end AVRegularity.Construction.Preservation.Seed
end
