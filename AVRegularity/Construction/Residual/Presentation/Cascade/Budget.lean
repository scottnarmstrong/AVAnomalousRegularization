-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Cascade.ReconCoarseParts
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleLiftIdentity
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Applications.Global.CompactRangeMain
public import AVRegularity.CycleComparison.Assembly.CoarseLetters
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.CycleComparison.Assembly.OfPhysicalLift
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleReference.TorusStreamFluxEquation
import AVRegularity.Families.ActualFamily.MeasurableOfCertified

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Residual.Presentation.Cascade
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation AVRegularity.EntryWeakProofs
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The lift settings and the grading of the observed pulses at a cascade frame**
(cascade side of the bill residual).

`frameReconSettingBody`: for a frame whose incoming stage carries the stage invariant, at a level
`m₀ ≤ F.m < D.term`, the body `FrameReconSettingBody` holds at the stored orders `q_s = wQs`,
`q_f = wQf` (they are not free: `qs_eq`, `qf_eq` of `IsLiftSetting`), the parallel index
`pulseParallel`, the shear profile `pulseShearProfile` and the price majorant `recordMajorant`, for
every price bound `S_b ≥ S` (`S` the Schur constant of the invariant), every offset `ℓ` and every
cleanup order `A_cl`. The constants `C_G, C_w, C_a, C_g, m₀` are chosen before the frame, from
`(α, s, q, ζ, Λ, b_w, D_m, H, N, A_cl, ℓ)`; the grading uses the lift sequences of the window
(`FrameReconSeqAt`).

For a stage without identities `C_j` is arbitrary and the setting is that of the trivial lift
data. -/

/-- The stored jet order `q_s = K_lift + 4(H+1)(N+D_m)^2` of the setting at the window. -/
def wQs (Dm depth N Acl ℓ : ℕ) : ℕ := wKlift Dm depth N Acl ℓ + 4 * (depth + 1) * (N + Dm) ^ 2

/-- The stored fast order `q_f = max L (L+2) + H D_m + 2N + 2D_m` of the setting at the window. -/
def wQf (Dm depth N ℓ : ℕ) : ℕ :=
  max (wLlift Dm depth N ℓ) (wLlift Dm depth N ℓ + 2) + depth * Dm + 2 * N + 2 * Dm

/-- **The lift settings and the grading of the observed pulses at a cascade frame.** -/
theorem frameReconSettingBody {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ bw : ℝ, 0 < bw →
    ∀ Dm H N Acl ℓ : ℕ, 2 ≤ Dm → 1 ≤ N →
    ∃ (CGl Cw : ℕ → ℝ) (Ca Cg : ℝ) (m₀ : ℕ), 2 ≤ m₀ ∧ 0 ≤ Cg ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (j₀ : ℕ) (F : Frame D hr Dm bw j₀) (law : BirthLaw) (hφ₀ : Integrable F.φ₀)
      (Mnat : ℕ) (kI : InvConsts) (tA tB S θK : ℝ),
    IsStageInvariant law F.P F.seedK F.freshK F.φ₀ hφ₀ Mnat kI tA tB S θK F.G →
    F.depth = H → F.N = N → F.G.level = F.m → m₀ ≤ F.m → F.m < D.term → j₀ ≤ F.m →
    F.G.fam.HasDepthAtMost H →
    (∀ v : CompIn F.G.comps, 0 ≤ compReserve kI v.1) →
    (∀ v : CompIn F.G.comps, compReserve kI v.1 ≤ 2) →
    (∀ v u γ, 1 ≤ (F.G.fam.identity v u γ).record.birthExcess →
      (F.G.fam.identity v u γ).record.length ≤ D.eps F.G.level) →
    FrameReconSeqAt F Acl ℓ →
    ∀ Sb : ℝ, S ≤ Sb →
      FrameReconSettingBody F law Acl ℓ CGl Cw Ca Sb Cg (wQs Dm F.depth F.N Acl ℓ)
        (wQf Dm F.depth F.N ℓ) (fun k => pulseParallel k)
        (fun k => pulseShearProfile D.α D.q D.Λ F.m D.ζ (D.κ F.m) k)
        (recordMajorant (F.G.mass law) F.G.fam) := by
  obtain ⟨Λ₀, hΛ₀, hnat⟩ := native_stage_setting hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ bw hbw Dm H N Acl ℓ hDm hN => ?_⟩
  obtain ⟨CG, Cw, Cj, m₀, hm₀, hCj, hmain⟩ :=
    hnat Λ hΛ bw hbw Dm H N (wKlift Dm H N Acl ℓ) (wLlift Dm H N ℓ) (wLlift Dm H N ℓ) hDm hN
  set Ca : ℝ := ∑ r ∈ Finset.range (wQs Dm H N Acl ℓ + 1),
    ∑ q ∈ Finset.range (wQf Dm H N ℓ + 1), Cj r q with hCa
  have hCa0 : ∀ r, r ≤ wQs Dm H N Acl ℓ → ∀ q, q ≤ wQf Dm H N ℓ → Cj r q ≤ Ca := by
    intro r hr q hq
    refine le_trans ?_ (Finset.single_le_sum (f := fun r => ∑ q ∈ Finset.range (wQf Dm H N ℓ + 1),
      Cj r q) (fun r _ => Finset.sum_nonneg fun q _ => hCj r q)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hr)))
    exact Finset.single_le_sum (f := fun q => Cj r q) (fun q _ => hCj r q)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hq))
  obtain ⟨Cg, hCg0, hgrad⟩ := Providers.cycle_lift_grading.{0, 0} N (wKlift Dm H N Acl ℓ)
    (wLlift Dm H N ℓ) (wLlift Dm H N ℓ) Dm H CG Cw (fun _ _ => Ca)
  refine ⟨CG, Cw, Ca, Cg, m₀, hm₀, hCg0, ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hΦ hband j₀ F law hφ₀ Mnat kI tA tB S θK hinv hH hNN
    hlev hm hmt hj hdepth hres hres2 hlen hseq Sb hSb
  have hΛ1 : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hm1 : 1 ≤ F.m := by omega
  subst hH hNN
  have hinv0 := hinv
  obtain ⟨hnatF, -, -, -, -, hcert, -, -⟩ := hinv
  have hset : ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
      IsLiftSetting (fLiftData F k) (F.G.mass law) (fSeqStart F k) (fSeqEnd F k)
        (ocEpsilon D.q D.Λ F.m) (D.κ F.m) (D.κ (F.m - 1)) (fRho F)
        (ocEpsilon D.q D.Λ (F.m - 1)) (ocEll D.q D.Λ F.m (D.κ F.m))
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)))
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F)
        (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) (pulseParallel k)
        (pulseShearProfile D.α D.q D.Λ F.m D.ζ (D.κ F.m) k) F.depth F.N
        (wKlift Dm F.depth F.N Acl ℓ) (wLlift Dm F.depth F.N ℓ) (wLlift Dm F.depth F.N ℓ)
        (wQs Dm F.depth F.N Acl ℓ) (wQf Dm F.depth F.N ℓ) CG Cw (fun _ _ => Ca)
        (recordMajorant (F.G.mass law) F.G.fam) Sb := by
    intro k hk
    have hodd : Odd k := CycleComparison.LiftSetting.obsPulse_odd hk
    have h1 := hmain hr D hDα hDq hDΛ hDζ hΦ hband j₀ F.G law F.P F.seedK F.freshK F.φ₀ hφ₀
      Mnat kI tA tB S θK hinv0 (by rw [hlev]; exact hm) (by rw [hlev]; exact hmt)
      (by rw [hlev]; exact hj) hdepth hres hres2 hlen ⟨k, hodd⟩ F.m hlev
    exact setting_of_native' F law hnatF hcert hlev hΛ1 hm1 hmt.le hζD hband hCa0 hSb hk h1
  refine ⟨hset, ?_⟩
  intro k hk hh hhH n hn1 hnN m'' hm1' hmn j hj
  have hj' : j ≤ wKlift Dm F.depth F.N Acl ℓ := by
    simp only [wKlift, wKmax] at hj ⊢; omega
  exact (hgrad (fLiftData F k) (F.G.mass law) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hset k hk)
    (F.CcT k) (hseq k hk) hh hhH n hn1 hnN m'' hm1' hmn j hj').1

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The scales at a cascade frame and the five dominations** (cascade side of the bill
residual).

`frameReconScaleBody`: the body `FrameReconScaleBody F s A_cl ρ_⋆ 𝔱 (C₁·𝔅)` at the radius
`ρ_⋆ = rhoStar D c₀ m`, the price sum `𝔱 = fTT F c_r σ₀ L_c θ₁ θ₂` and the bill `C₁·𝔅`,
`𝔅 = succReconBill …`. The constants `Λ₀`, `C₁`, `m₀` are chosen before the frame, from
`(α, s, q, ζ)`, the cleanup order `A_cl` and the length bound `T₀`; the frame enters only through a
level `m₀ ≤ F.m < D.term` of the band chain and a window length `0 < T_obs ≤ T₀`.

**Why the factor `C₁`.** The bill carries the factor `E^{-qγ}` against the price sum, and the
contrast is only `√(κ_{m-1}/κ_m) ≤ C₁E^{-qγ}` (`bandChain_uniform_ledger`), with `C₁ ≥ 1` the
constant of the band chain, not `1`. The five dominations hold against `C₁·𝔅`, which is what the
window theorem asks (the bill `bill` of `frameReconBound_of_window` is a free real, and the
conclusion carries `bill` linearly).

The schedule asks `(qγ + 3δ)A_cl ≥ 2 - β + 8δ`. For `𝔱 = 0` only the second term of the bill
remains and the contrast domination reads `0 ≤ C₁𝔅`. -/

/-- The price sum of the cascade bill is nonnegative. -/
theorem fTT_nonneg {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (F : Frame D hr Dm b j₀) (cr σ₀ : ℝ) (Lc : ℕ)
    (θ₁ θ₂ : ℝ) (hDE : 0 ≤ D.eps (F.m - 1)) : 0 ≤ fTT F cr σ₀ Lc θ₁ θ₂ := by
  have h1 : 0 ≤ succCovPrice D F.m cr F.p F.tp F.tf := by
    unfold succCovPrice
    have hS : 0 ≤ (⨆ t : Set.Icc F.tp F.tf, ∑ a : Fin 2, ∑ a' : Fin 2,
        |covPrimitive D F.m t a a'|) :=
      Real.iSup_nonneg fun t => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        abs_nonneg _
    have hb : 0 ≤ (⨆ t : Set.Icc F.tp F.tf, ∑ a : Fin 2, ∑ a' : Fin 2,
        |covPrimitive D F.m t a a'|) / rhoEnh D cr F.m ^ 2 := div_nonneg hS (sq_nonneg _)
    exact add_nonneg (pow_nonneg hb _) (pow_nonneg hb _)
  have h2 : 0 ≤ succFilterPrice D F.G F.m cr σ₀ Lc := by
    unfold succFilterPrice
    exact pow_nonneg (le_max_of_le_left (Real.rpow_nonneg hDE _)) _
  have h3 : 0 ≤ succFrontPrice D F.m F.η₀ F.J F.H θ₁ θ₂ := by
    unfold succFrontPrice
    exact add_nonneg (Real.rpow_nonneg hDE _) (Real.rpow_nonneg hDE _)
  exact add_nonneg (add_nonneg h1 h2) h3

/-- The gluing term of the cascade bill is at most the bill. -/
theorem gluing_le_bill {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (F : Frame D hr Dm b j₀) (cr c σ₀ : ℝ) (Lc Acl : ℕ)
    (θ₁ θ₂ : ℝ) (hcr : 0 ≤ cr) (hDE : 0 ≤ D.eps (F.m - 1)) (hDe : 0 ≤ D.eps F.m) :
    Real.sqrt (D.cellScaleSq F.m) *
      Real.sqrt ((1 + (F.tf - F.tp) / ocTau D.α D.q D.Λ F.m) / ocTau D.α D.q D.Λ F.m) *
      Real.exp (-(c * ocTau D.α D.q D.Λ F.m / Real.sqrt (D.cellScaleSq F.m) ^ 2)) ≤
    succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂ := by
  have hP := fTT_nonneg F cr σ₀ Lc θ₁ θ₂ hDE
  have hρ : 0 ≤ rhoEnh D cr F.m := mul_nonneg hcr (Real.sqrt_nonneg _)
  have hEq : 0 ≤ D.eps (F.m - 1) ^ (-(D.q * ocGamma D.α D.q)) := Real.rpow_nonneg hDE _
  have hd : 0 ≤ ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / rhoEnh D cr F.m :=
    div_nonneg (mul_nonneg hDe (Real.sqrt_nonneg _)) hρ
  have hR : 0 ≤ Real.sqrt (F.tf - F.tp) / Real.sqrt (D.cellScaleSq F.m) *
      (D.eps F.m / rhoEnh D cr F.m) ^ Acl :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (pow_nonneg (div_nonneg hDe hρ) _)
  have h1 : 0 ≤ D.eps (F.m - 1) ^ (-(D.q * ocGamma D.α D.q)) * fTT F cr σ₀ Lc θ₁ θ₂ :=
    mul_nonneg hEq hP
  have h2 : 0 ≤ (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / rhoEnh D cr F.m) ^ F.N *
      (1 + Real.sqrt (F.tf - F.tp) / Real.sqrt (D.cellScaleSq F.m) *
        (D.eps F.m / rhoEnh D cr F.m) ^ Acl) :=
    mul_nonneg (pow_nonneg hd _) (by linarith)
  unfold succReconBill
  linarith

/-- **The scales of the window and the five dominations at a cascade frame.** -/
theorem frameReconScaleBody {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ (Acl : ℕ) (T₀ : ℝ),
      2 - (1 + α) + 8 * ocDelta α q ≤ (q * ocGamma α q + 3 * ocDelta α q) * Acl →
      ∃ (C₁ : ℝ) (m₀ : ℕ), 1 ≤ C₁ ∧ 2 ≤ m₀ ∧
      ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
        [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
        [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
        (F : Frame D hr Dm b j₀),
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ D.term D.κ → m₀ ≤ F.m → F.m < D.term →
      0 < fTobs F → fTobs F ≤ T₀ →
      ∀ (c₀ cr c σ₀ : ℝ) (Lc : ℕ) (θ₁ θ₂ : ℝ), 0 < c₀ → c₀ ≤ 1 → 0 < cr → cr ≤ 1 →
        FrameReconScaleBody F s Acl (rhoStar D c₀ F.m) (fTT F cr σ₀ Lc θ₁ θ₂)
          (C₁ * succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂) := by
  obtain ⟨Λ₀, hΛ₀, hlev⟩ := levels hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ Acl T₀ hAcl => ?_⟩
  obtain ⟨C₁, m₀, hC₁, hm₀, hmain⟩ := hlev Λ hΛ Acl T₀ hAcl
  refine ⟨C₁, m₀, hC₁, hm₀, ?_⟩
  intro hr _ _ _ _ _ _ D Dm b j₀ F hDα hDq hDΛ hDζ hΦ hband hm hmt hTobs hT c₀ cr c σ₀ Lc θ₁ θ₂
    hc₀ hc₀1 hcr hcr1
  subst hDα hDq hDΛ hDζ
  obtain ⟨hκm, hκB, hlo, hhi, hcon, hεc, hZ⟩ :=
    hmain D.term D.κ hband F.m hm hmt
  have hm2 : 2 ≤ F.m := le_trans hm₀ hm
  have hq1 : 1 < D.q := hq.1
  have h128 : 128 ≤ D.Λ := by
    have := le_trans hΛ₀ hΛ
    exact this
  have hexp := AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  have hγ : 0 < ocGamma D.α D.q := hexp.1
  have hq0 : 0 < D.q := lt_trans zero_lt_one hq1
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hE0 : 0 < ocEpsilon D.q D.Λ (F.m - 1) := Applications.eps_pos hq1 h128
  have hE1 : ocEpsilon D.q D.Λ (F.m - 1) ≤ 1 := Applications.eps_le_one hq1 h128
  have he : 0 < ocEpsilon D.q D.Λ F.m := Applications.eps_pos hq1 h128
  have hτ : 0 < ocTauPP D.α D.q D.Λ F.m := Construction.Stream.ocTauPP_pos hΛ1
  have hRpos : 0 < fRho F := Real.sqrt_pos.2 (mul_pos hκB hτ)
  have hρ : rhoEnh D cr F.m = cr * fRho F := rfl
  have hρpos : 0 < rhoEnh D cr F.m := by rw [hρ]; exact mul_pos hcr hRpos
  have hkap : D.kap F.m = D.κ F.m := by simp [OCData.kap, min_eq_left hmt.le]
  have hcell : Real.sqrt (D.cellScaleSq F.m) = ocEll D.q D.Λ F.m (D.κ F.m) := by
    simp only [OCData.cellScaleSq, hkap, ocEll, OCData.eps]
    rw [Real.sqrt_div' _ hκm.le, Real.sqrt_sq he.le]
  have hell0 : 0 < ocEll D.q D.Λ F.m (D.κ F.m) := div_pos he (Real.sqrt_pos.2 hκm)
  -- the radius ρ_⋆
  have hA : 0 < ocA D.α D.q D.Λ F.m := Real.rpow_pos_of_pos he _
  have hmin : 0 < min (D.eps F.m) (Real.sqrt (D.κ F.m / ocA D.α D.q D.Λ F.m)) :=
    lt_min he (Real.sqrt_pos.2 (div_pos hκm hA))
  have hrs0 : 0 < rhoStar D c₀ F.m := mul_pos hc₀ hmin
  have hrse : rhoStar D c₀ F.m ≤ ocEpsilon D.q D.Λ F.m :=
    calc rhoStar D c₀ F.m = c₀ * min (D.eps F.m) (Real.sqrt (D.κ F.m / ocA D.α D.q D.Λ F.m)) :=
          rfl
      _ ≤ 1 * min (D.eps F.m) (Real.sqrt (D.κ F.m / ocA D.α D.q D.Λ F.m)) :=
          mul_le_mul_of_nonneg_right hc₀1 hmin.le
      _ ≤ D.eps F.m := by rw [one_mul]; exact min_le_left _ _
  -- the terms of the bill
  have hdst : 0 ≤ ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) :=
    mul_nonneg he.le (Real.sqrt_nonneg _)
  have hEq : 1 ≤ D.eps (F.m - 1) ^ (-(D.q * ocGamma D.α D.q)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hE0 hE1 (by
      have : 0 ≤ D.q * ocGamma D.α D.q := by positivity
      linarith)
  have hP : 0 ≤ fTT F cr σ₀ Lc θ₁ θ₂ := fTT_nonneg F cr σ₀ Lc θ₁ θ₂ hE0.le
  have hG : 0 ≤ Real.sqrt (D.cellScaleSq F.m) *
      Real.sqrt ((1 + (F.tf - F.tp) / ocTau D.α D.q D.Λ F.m) / ocTau D.α D.q D.Λ F.m) *
      Real.exp (-(c * ocTau D.α D.q D.Λ F.m / Real.sqrt (D.cellScaleSq F.m) ^ 2)) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.exp_pos _).le
  have he₀e : ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F ≤
      ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / rhoEnh D cr F.m :=
    div_le_div_of_nonneg_left hdst hρpos (by rw [hρ]; exact mul_le_of_le_one_left hRpos.le hcr1)
  have hrat : ocEpsilon D.q D.Λ F.m / fRho F ≤ D.eps F.m / rhoEnh D cr F.m :=
    div_le_div_of_nonneg_left he.le hρpos (by rw [hρ]; exact mul_le_of_le_one_left hRpos.le hcr1)
  have hRf : Real.sqrt (fTobs F) / ocEll D.q D.Λ F.m (D.κ F.m) *
        (ocEpsilon D.q D.Λ F.m / fRho F) ^ Acl ≤
      Real.sqrt (F.tf - F.tp) / Real.sqrt (D.cellScaleSq F.m) *
        (D.eps F.m / rhoEnh D cr F.m) ^ Acl := by
    rw [hcell]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg he.le hRpos.le) hrat Acl)
      (div_nonneg (Real.sqrt_nonneg _) hell0.le)
  have hRf0 : 0 ≤ Real.sqrt (fTobs F) / ocEll D.q D.Λ F.m (D.κ F.m) *
        (ocEpsilon D.q D.Λ F.m / fRho F) ^ Acl :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hell0.le)
      (pow_nonneg (div_nonneg he.le hRpos.le) _)
  have hR0 : 0 ≤ Real.sqrt (F.tf - F.tp) / Real.sqrt (D.cellScaleSq F.m) *
        (D.eps F.m / rhoEnh D cr F.m) ^ Acl :=
    hRf0.trans hRf
  have key := dominations (D.eps (F.m - 1) ^ (-(D.q * ocGamma D.α D.q)))
    (fTT F cr σ₀ Lc θ₁ θ₂) (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / rhoEnh D cr F.m)
    (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) _ _
    (Real.sqrt (D.κ (F.m - 1) / D.κ F.m)) _ C₁ F.N hEq hP (div_nonneg hdst hRpos.le) he₀e hR0
    hRf0 hRf hG hC₁ hcon hεc (hZ (fTobs F) hTobs.le hT)
  have hbill : ∀ x : ℝ, x ≤ C₁ * (D.eps (F.m - 1) ^ (-(D.q * ocGamma D.α D.q)) *
      fTT F cr σ₀ Lc θ₁ θ₂ + (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) /
      rhoEnh D cr F.m) ^ F.N * (1 + Real.sqrt (F.tf - F.tp) / Real.sqrt (D.cellScaleSq F.m) *
      (D.eps F.m / rhoEnh D cr F.m) ^ Acl) + Real.sqrt (D.cellScaleSq F.m) *
      Real.sqrt ((1 + (F.tf - F.tp) / ocTau D.α D.q D.Λ F.m) / ocTau D.α D.q D.Λ F.m) *
      Real.exp (-(c * ocTau D.α D.q D.Λ F.m / Real.sqrt (D.cellScaleSq F.m) ^ 2))) →
      x ≤ C₁ * succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂ :=
    fun x hx => hx
  refine ⟨hα0, hα1, hs0, hs1, hq, hζ, h128, hΦ, hm2, hκm, hκB, hrs0, hrse, hrse.trans hlo,
    hhi, hP, ?_, ?_, ?_, ?_, ?_⟩
  · exact hbill _ key.1
  · exact hbill _ key.2.1
  · exact hbill _ key.2.2.1
  · exact hbill _ key.2.2.2.1
  · exact hbill _ key.2.2.2.2

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Residual.Presentation.Cascade
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation AVRegularity.EntryWeakProofs
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The lift sequences at a cascade frame, with the constants chosen before the frame** (cascade side of the
bill residual).

`frameReconSeqAt`: for a frame whose incoming stage carries the stage invariant on
`[t_A, t_B]`, at a level `m₁ ≤ F.m < D.term`, under the quiet margin of `t_p`
(`t_A + τ' ≤ t_p ≤ t_B`), at the menu length factor `1`, the lift sequences of the observed pulses
on the clipped windows hold at the orders of the window, for every offset `ℓ` and every cleanup
order `A_cl`: `FrameReconSeqAt F Acl ℓ` (`ℓ = 0` included). The constants
`Λ₀`, `m₁` are chosen before the frame, from `(α, s, q, ζ, Λ, b_w, D_m, H, N, A_cl, ℓ)`; the
lift settings are those of `setting_of_native'`, the ellipticity is the uniform native
ellipticity above its level threshold.

If no pulse window passes through `t_p`, or the family of observed pulses is empty, the
corresponding clauses are empty. -/

/-- **The lift sequences of the observed pulses at a cascade frame.** -/
theorem frameReconSeqAt {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ bw : ℝ, 0 < bw →
    ∀ Dm H N Acl ℓ : ℕ, 2 ≤ Dm → 1 ≤ N → ∃ m₁ : ℕ, 2 ≤ m₁ ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (j₀ : ℕ) (F : Frame D hr Dm bw j₀) (law : BirthLaw) (hφ₀ : Integrable F.φ₀)
      (Mnat : ℕ) (kI : InvConsts) (tA tB S θK : ℝ),
    IsStageInvariant law F.P F.seedK F.freshK F.φ₀ hφ₀ Mnat kI tA tB S θK F.G →
    F.depth = H → F.N = N → F.G.level = F.m → m₁ ≤ F.m → F.m < D.term → j₀ ≤ F.m →
    F.G.fam.HasDepthAtMost H →
    (∀ v : CompIn F.G.comps, 0 ≤ compReserve kI v.1) →
    (∀ v : CompIn F.G.comps, compReserve kI v.1 ≤ 2) →
    (∀ v u γ, 1 ≤ (F.G.fam.identity v u γ).record.birthExcess →
      (F.G.fam.identity v u γ).record.length ≤ D.eps F.G.level) →
    F.Mn.lenFactor = 1 →
    tA + 3 * ocTau D.α D.q D.Λ F.m ≤ F.tp → F.tp ≤ tB →
    Set.Icc (F.tp - ocTauP D.α D.q D.Λ F.m) (F.tp + ocTauP D.α D.q D.Λ F.m) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ F.m →
    FrameReconSeqAt F Acl ℓ := by
  obtain ⟨Λ₀, hΛ₀, hnat⟩ := native_stage_setting hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ bw hbw Dm H N Acl ℓ hDm hN => ?_⟩
  obtain ⟨CG, Cw, Cj, m₀, hm₀, hCj, hmain⟩ :=
    hnat Λ hΛ bw hbw Dm H N (wKlift Dm H N Acl ℓ) (wLlift Dm H N ℓ) (wLlift Dm H N ℓ) hDm hN
  obtain ⟨M₁, hM₁, hell⟩ := FullLift.uniform_native_lift_ellipticity_all_carriers
    α s q hα0 hα1 hs0 hs1 hq Λ (by omega) ζ hζ
  set Ca : ℝ := ∑ r ∈ Finset.range (wQs Dm H N Acl ℓ + 1),
    ∑ q ∈ Finset.range (wQf Dm H N ℓ + 1), Cj r q with hCa
  have hCa0 : ∀ r, r ≤ wQs Dm H N Acl ℓ → ∀ q, q ≤ wQf Dm H N ℓ → Cj r q ≤ Ca := by
    intro r hr q hq
    refine le_trans ?_ (Finset.single_le_sum (f := fun r => ∑ q ∈ Finset.range (wQf Dm H N ℓ + 1),
      Cj r q) (fun r _ => Finset.sum_nonneg fun q _ => hCj r q)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hr)))
    exact Finset.single_le_sum (f := fun q => Cj r q) (fun q _ => hCj r q)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hq))
  refine ⟨max m₀ (M₁ + 1), by omega, ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hΦ hband j₀ F law hφ₀ Mnat kI tA tB S θK hinv hH hNN
    hlev hm hmt hj hdepth hres hres2 hlen hone hentry htp hquietMargin
  have hm0 : m₀ ≤ F.m := (le_max_left _ _).trans hm
  have hm1 : M₁ + 1 ≤ F.m := (le_max_right _ _).trans hm
  have hΛ1 : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hFm1 : 1 ≤ F.m := by omega
  subst hH hNN
  have hinv0 := hinv
  obtain ⟨hnatF, -, -, -, -, hcert, -, -⟩ := hinv
  have hset : FrameLiftSettingsAt F law Acl ℓ CG Cw Ca S (wQs Dm F.depth F.N Acl ℓ)
      (wQf Dm F.depth F.N ℓ) (fun k => pulseParallel k)
      (fun k => pulseShearProfile D.α D.q D.Λ F.m D.ζ (D.κ F.m) k)
      (recordMajorant (F.G.mass law) F.G.fam) := by
    intro k hk
    have hodd : Odd k := CycleComparison.LiftSetting.obsPulse_odd hk
    have h1 := hmain hr D hDα hDq hDΛ hDζ hΦ hband j₀ F.G law F.P F.seedK F.freshK F.φ₀ hφ₀
      Mnat kI tA tB S θK hinv0 (by rw [hlev]; exact hm0) (by rw [hlev]; exact hmt)
      (by rw [hlev]; exact hj) hdepth hres hres2 hlen ⟨k, hodd⟩ F.m hlev
    exact setting_of_native' F law hnatF hcert hlev hΛ1 hFm1 hmt.le hζD hband hCa0 le_rfl hk h1
  have hellF : FrameSeqEll F := by
    intro k hk t ht X' ξ
    exact hell (CompIn F.G.comps) (fun v => hr v.1.root) Dm D hDα hDq hDΛ hDζ hΦ hband
      F.m hm1 k hk _ _ t ht X' ξ
  exact frameReconSeqAt_of_settings F law hinv0 hlev hone hΛ1 hζD hband hmt.le hFm1
    hentry htp hquietMargin hellF hset

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The size form of the covariance primitive at every context** (cascade side of the
bill residual, the discharge of the `covSizeForm_at_frame`).

`succPrefix_covSize`: in the common prefix form, at every context of level `≥ m_*` and at the
frame of every lifted field of the context with classical representatives,
`CovSizeForm F.Mn D m t_p t_f (rhoEnh D c_r m) (frameOmega F c_r)` at a radius factor `c_r > 0`
chosen from the invariant constants: `c_r = k_I.c_r` (the flux radius of the bill, positive by
admissibility: `k_I.c_r = k_S.c_r`) and `c_r = 1` (the slow length of the window, for the energy
step). The frame has the cascade menu, whose anchor is `0` by definition, and
`m ≤ n < M`.

The case `t_p = t_f` is allowed, and an empty component family is harmless (the form does not
mention the family). -/

/-- **The covariance size form at every context of level `≥ m_*`**, at the radius factor `cr`. -/
def CovSizeCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (cr : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
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
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      CovSizeForm (c.frame CcT PZ aRep û hlift aZ aY hZ hY).Mn c.D c.m c.tp c.tf
        (rhoEnh c.D cr c.m) (frameOmega (c.frame CcT PZ aRep û hlift aZ aY hZ hY) cr)

/-- **The covariance size form in the common prefix form** at a radius factor `crf k_S k_I` that is positive
whenever `k_S.c_r` is and `k_I.c_r = k_S.c_r`; the constant is the level `m_*`. -/
theorem succPrefix_covSize (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (crf : InvConsts → InvConsts → ℝ)
    (hcrf : ∀ kS kI : InvConsts, 0 < kS.cr → kI.cr = kS.cr → 0 < crf kS kI) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        CovSizeCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ (crf kS kI) x) := by
  refine SuccPrefix.of_scale (covSizeForm_at_frame hα₀ hα₁ hs₀ hs₁ hq hζ) ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ hfacts htail CQ Cpr
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  have hcr : 0 < crf kS kI := hcrf kS kI hfacts.hcr
    (Construction.Preservation.Buffer.invariantAdmissible_molecular_parameters hkI).2.1
  obtain ⟨mStar, -, h⟩ := htail (crf kS kI) hcr
  refine ⟨mStar, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift aZ aY hZ hY
  exact h c.D c.M c.hα c.hq c.hΛ c.hζ c.hband (c.frame CcT PZ aRep û hlift aZ aY hZ hY) rfl hm
    (le_trans c.hmn c.hnM.le)

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! The two source ingredients of the reconstruction letters at a cascade frame. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The geometry and reference flux of the coarse window, independent of its mean letters. -/
structure WindowGeometry
    (F : Frame D hr Dm b j₀) (law : BirthLaw) (kc : ℕ) where
  a : ℝ
  B₀ : ℝ
  lam : ℝ
  window : F.tp ≤ F.tp + fTobs F
  rho_pos : 0 < fRho F
  B_pos : 0 < D.κ (F.m - 1)
  D_ge : 2 ≤ F.N + Dm
  mass_pos : ∀ v, 0 < F.G.mass law v
  drift_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), ∀ x,
    ‖streamVel (D.Φ (F.m - 1)) t x‖ ≤ C
  drift_meas : Measurable fun q : Set.Icc F.tp (F.tp + fTobs F) × Vec 2 =>
    streamVel (D.Φ (F.m - 1)) q.1 q.2
  drift_smooth : ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F),
    ContDiff ℝ (⊤ : ℕ∞) (streamVel (D.Φ (F.m - 1)) t)
  drift_div : ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), ∀ x,
    ∑ k : Fin 2, fderiv ℝ (streamVel (D.Φ (F.m - 1)) t) x (basisVec k) k = 0
  drift_per : ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), IsZ2Periodic (streamVel (D.Φ (F.m - 1)) t)
  a_nonneg : 0 ≤ a
  B₀_ge : 1 ≤ B₀
  lam_pos : 0 < lam
  drift_jets : ∀ l : ℕ, 1 ≤ l → l ≤ fNc F kc → ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (streamVel (D.Φ (F.m - 1)) t)) l x‖ ≤
      a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)
  drift_scale : B₀ * fRho F / lam ≤ 1 / 2
  drift_small : a * B₀ * fRho F ^ 2 ≤ D.κ (F.m - 1) / 8
  J_symm : ∀ t i j,
    ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t i j =
      ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t j i
  J_meas : ∀ i j, Measurable fun t => ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t i j
  J_bdd : matrixSupNorm (fun t =>
    ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t -
      D.κ (F.m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) F.tp (F.tp + fTobs F) ≠ ⊤
  cov_small : matrixSupNorm
    (covarianceMatrix (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) (D.κ (F.m - 1)) F.tp)
      F.tp (F.tp + fTobs F) ≤ ENNReal.ofReal (fRho F ^ 2)

/-- Eulerian letters presenting the actual glued means, including all coefficient and graph
clauses of `IsCoarseSetting`; produced through the entrywise and actual-mean bounds. -/
structure MeanLetters
    (F : Frame D hr Dm b j₀) (law : BirthLaw) (kc : ℕ) where
  AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)
  CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => hr v.1.root))
  Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ
  Cstar : ℝ
  Θ : ℝ
  AD_meas : ∀ d, Measurable fun q : Set.Icc F.tp (F.tp + fTobs F) × Vec 2 => AD d q.1 q.2
  AD_smooth : ∀ d, ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), ContDiff ℝ ((fNc F kc) : ℕ) (AD d t)
  AD_per : ∀ d, ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), AVenhance.IsZ2Periodic (AD d t)
  AD_fin : ∀ d, coefficientSeminorm (fRho F) (fNc F kc) F.tp (F.tp + fTobs F) (AD d) ≠ ⊤
  CE_meas : ∀ r ∈ Finset.Icc 1 F.depth, ∀ v u d, Measurable fun q : Set.Icc F.tp (F.tp + fTobs F) × Vec 2 => CE r v u d q.1 q.2
  CE_smooth : ∀ r ∈ Finset.Icc 1 F.depth, ∀ v u d, ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), ContDiff ℝ ((fNc F kc) : ℕ) (CE r v u d t)
  CE_per : ∀ r ∈ Finset.Icc 1 F.depth, ∀ v u d, ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), AVenhance.IsZ2Periodic (CE r v u d t)
  CE_fin : ∀ r ∈ Finset.Icc 1 F.depth, ∀ v u d, coefficientSeminorm (fRho F) (fNc F kc) F.tp (F.tp + fTobs F) (CE r v u d) ≠ ⊤
  edge_nonneg : ∀ v u, 0 ≤ Aedge v u
  edge_row : ∀ v, ∑ u, Aedge v u ≤ Θ
  edge_col : ∀ u, ∑ v, Aedge v u ≤ Θ
  edge_acyclic : Aedge ^ (F.depth + 1) = 0
  edge_mean : ∀ r ∈ Finset.Icc 1 F.depth, ∀ v u,
    ENNReal.ofReal (Real.sqrt ((F.G.mass law) u / (F.G.mass law) v)) *
      ∑ d : Finset.Icc 2 (F.N + Dm), coefficientSeminorm (fRho F) (fNc F kc) F.tp (F.tp + fTobs F) (CE r v u d) *
        (ENNReal.ofReal ((D.κ (F.m - 1)) * (fRho F) ^ (d.1 - 2)))⁻¹
      ≤ ENNReal.ofReal (Cstar ^ r * (Aedge ^ r) v u)

  presentation :
  ∀ r ∈ Finset.range (F.depth + 1),
    IsMeanPresentation (Set.Icc F.tp (F.tp + fTobs F)) (F.N + Dm) r AD CE
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m))
      (gluedMean (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
        (fun k => F.G.actualFamily.weight (oddSlotOf k))
        (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F)
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) F.N r
        (fun k => fLiftData F k) F.CcT
        (fun k => ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
          (ocPulseChartIndex D.α D.q D.Λ F.m k))
        (fun k => ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
          (ocPulseChartIndex D.α D.q D.Λ F.m k)))

/-- The geometry and letters give every field of the coarse setting, and exactly the actual
mean presentations requested by the reconstruction letters. -/
theorem lettersAt_of_inputs
    (F : Frame D hr Dm b j₀) (law : BirthLaw) (kc : ℕ) (g : WindowGeometry F law kc) (m : MeanLetters F law kc) :
    FrameReconLettersAt F law kc := by
  refine ⟨g.a, g.B₀, g.lam, m.AD, m.CE, m.Aedge, m.Cstar, m.Θ, ?_, m.presentation⟩
  exact {
    window := g.window
    rho_pos := g.rho_pos
    B_pos := g.B_pos
    D_ge := g.D_ge
    p_pos := le_rfl
    L_eq := rfl
    N_eq := rfl
    mass_pos := g.mass_pos
    drift_bdd := g.drift_bdd
    drift_meas := g.drift_meas
    drift_smooth := g.drift_smooth
    drift_div := g.drift_div
    drift_per := g.drift_per
    a_nonneg := g.a_nonneg
    B₀_ge := g.B₀_ge
    lam_pos := g.lam_pos
    drift_jets := g.drift_jets
    drift_scale := g.drift_scale
    drift_small := g.drift_small
    J_symm := g.J_symm
    J_meas := g.J_meas
    J_bdd := g.J_bdd
    cov_small := g.cov_small
    AD_meas := m.AD_meas
    AD_smooth := m.AD_smooth
    AD_per := m.AD_per
    AD_fin := m.AD_fin
    CE_meas := m.CE_meas
    CE_smooth := m.CE_smooth
    CE_per := m.CE_per
    CE_fin := m.CE_fin
    edge_nonneg := m.edge_nonneg
    edge_row := m.edge_row
    edge_col := m.edge_col
    edge_acyclic := m.edge_acyclic
    edge_mean := m.edge_mean }

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Reconstruction
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! The two source ingredients of the reconstruction letters at a cascade frame. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem reference_bounds' (D : OCData) (M : ℕ) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hν : 0 < D.κ M) (B tp tf : ℝ) (hB : 0 ≤ B) :
    (∀ t i j, ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) t i j =
      ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) t j i) ∧
    (∀ i j, Measurable fun t => ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) t i j) ∧
    matrixSupNorm (fun t => ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) t -
      B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) tp tf ≠ ⊤ := by
  refine ⟨fun t i j => Construction.Preservation.FullLift.refFlux_entry_symm hΛ hζ (D.κ M) t i j,
    fun i j => CycleReference.refFlux_entry_measurable hΛ hζ hν i j, ?_⟩
  have hId : ∀ i j : Fin 2, |B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ B := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [abs_of_nonneg hB, hB]
  have hb : matrixSupNorm (fun t => ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) t -
      B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) tp tf ≤
      ENNReal.ofReal (D.κ M + ocHStar D.α D.q D.Λ M (D.κ M) + B) := by
    refine iSup₂_le fun t _ => iSup_le fun i => iSup_le fun j => ?_
    apply ENNReal.ofReal_le_ofReal
    change |ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) t i j -
      B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ _
    exact (abs_sub _ _).trans (add_le_add
      (by simpa only [Real.norm_eq_abs] using CycleReference.refFlux_entry_norm_le hΛ hζ hν i j)
      (hId i j))
  exact ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top)

/-- The geometry at every sufficiently high cascade level, with an all-anchor band chain.
The threshold is chosen before the frame and its carrier data. -/
theorem windowGeometry {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain α q Λ ζ D.term D.κ →
    ∀ {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (F : Frame D hr Dm b j₀) (law : BirthLaw) (kc : ℕ),
      m₀ ≤ F.m → F.m ≤ D.term → 2 ≤ F.N + Dm → F.tp ≤ F.tf →
      Nonempty (WindowGeometry F law kc) := by
  obtain ⟨ΛD, B₀, C₁, hΛD, hB₀, _, hdr⟩ := CycleComparison.Assembly.coarse_drift_small
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨C, hC, ΛH, hΛH, hcov⟩ := CycleReference.bandChain_covariance_estimates
    hα₀ hα₁ hs₀ hs₁ hq hζ
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  obtain ⟨η, hη, hsmall⟩ := Applications.exists_small_pow (K := C) (zero_le_one.trans hC)
    hδ (zero_lt_one : (0 : ℝ) < 1)
  refine ⟨max ΛD ΛH, hΛD.trans (le_max_left _ _), fun Λ hΛ => ?_⟩
  have h128 : 128 ≤ Λ := hΛD.trans ((le_max_left _ _).trans hΛ)
  obtain ⟨n₀, hn₀⟩ := Applications.eps_eventually_le hq.1 h128 hη
  refine ⟨n₀ + 3, by omega, ?_⟩
  intro hr _ _ _ _ _ _ D hα hqD hΛD' hζD hseq hband Dm b j₀ F law kc hm hmt hDm htp
  have hM2 : 2 ≤ F.m := by omega
  have hΛ1 : 1 ≤ Λ := by omega
  have hΛc : 1 ≤ D.Λ := hΛD' ▸ hΛ1
  have hζc : IsFastProfile D.ζ := hζD ▸ hζ
  have hν : 0 < D.κ F.m := CycleReference.bandChain_pos hΛ1 hζ hband hmt
  have hB : 0 < D.κ (F.m - 1) := CycleReference.bandChain_pos hΛ1 hζ hband
    ((Nat.sub_le F.m 1).trans hmt)
  have hrho : fRho F = Real.sqrt (D.κ (F.m - 1) * ocTauPP α q Λ F.m) := by
    simp only [fRho, hα, hqD, hΛD']
  have hrpos : 0 < fRho F := by
    rw [hrho]
    exact Real.sqrt_pos.mpr (mul_pos hB (Construction.Stream.ocTauPP_pos hΛ1))
  obtain ⟨a, lam, ha, hlam, hscale, hstrain, _, hjets, hsmooth, hdiv, hper, hbdd, hmeas⟩ :=
    hdr Λ ((le_max_left _ _).trans hΛ) D.Φ hseq D.term D.κ hband F.m hM2 hmt
      (D.κ F.m) (D.κ (F.m - 1)) rfl rfl
  obtain ⟨hJs, hJm, hJb⟩ := reference_bounds' D F.m hΛc hζc hν (D.κ (F.m - 1))
    F.tp (F.tp + fTobs F) hB.le
  have hCsmall : C * ocEpsilon q Λ (F.m - 1) ^ ocDelta α q ≤ 1 :=
    hsmall _ (Applications.eps_pos hq.1 h128).le (hn₀ (F.m - 1) (by omega))
  have hCov : matrixSupNorm
      (covarianceMatrix (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) (D.κ (F.m - 1)) F.tp)
        F.tp (F.tp + fTobs F) ≤ ENNReal.ofReal (fRho F ^ 2) := by
    refine iSup₂_le fun t _ => iSup_le fun i => iSup_le fun j => ?_
    apply ENNReal.ofReal_le_ofReal
    change |ocCovariance D.α D.q D.Λ D.ζ F.m (D.κ F.m) (D.κ (F.m - 1)) F.tp t i j| ≤ _
    have hh := (hcov Λ ((le_max_right _ _).trans hΛ) D.term (by omega) D.κ hband F.m hM2 hmt
      F.tp t i j).2.2.2
    have hR : ocRh α q Λ F.m (D.κ (F.m - 1)) = fRho F := hrho.symm
    rw [hR] at hh
    rw [hα, hqD, hΛD', hζD]
    exact (div_le_one (sq_pos_of_pos hrpos)).mp (hh.trans hCsmall)
  exact ⟨{
    a := a, B₀ := B₀, lam := lam
    window := by change F.tp ≤ F.tp + (F.tf - F.tp); linarith only [htp]
    rho_pos := hrpos, B_pos := hB, D_ge := hDm
    mass_pos := fun v => Construction.Preservation.Buffer.birth_compMass_pos
      (hqD ▸ hq.1) (hΛD' ▸ h128) law v.1
    drift_bdd := hbdd F.tp (F.tp + fTobs F)
    drift_meas := hmeas F.tp (F.tp + fTobs F)
    drift_smooth := fun t _ => hsmooth t
    drift_div := fun t _ x => hdiv t x
    drift_per := fun t _ => hper t
    a_nonneg := ha, B₀_ge := hB₀, lam_pos := hlam
    drift_jets := fun l hl _ t _ x => hjets l hl t x
    drift_scale := by rw [hrho]; exact hscale
    drift_small := by rw [hrho]; exact hstrain
    J_symm := hJs, J_meas := hJm, J_bdd := hJb, cov_small := hCov }⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Assembly
open AVRegularity.CycleComparison.ActualMeans
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! The two source ingredients of the reconstruction letters at a cascade frame. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Actual Eulerian mean letters and their normalized budgets. The edge budget is expressed
in the physical masked majorant, as in the existing cycle-comparison means stage. -/
structure MeanBudget
    (F : Frame D hr Dm b j₀) (law : BirthLaw) (kc : ℕ) where
  AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)
  CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => hr v.1.root))
  Lb : ℤ → ℕ → ℕ → MeanCoeff (CompIn F.G.comps) (fun v => hr v.1.root)
  transferCost : ℝ
  physicalEdge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ
  physical_nonneg : ∀ v u, 0 ≤ physicalEdge v u
  diagonalCost : ℝ
  edgeCost : ℝ
  actual : IsActualMeans F.N Dm F.depth (fNc F kc) transferCost
    (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (fun k => F.G.actualFamily.weight (oddSlotOf k)) F.tp (F.tp + fTobs F)
    (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F)
    (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F)
    (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) (ocEpsilon D.q D.Λ (F.m - 1))
    (fLiftData F) F.CcT
    (fun k => ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k))
    (fun k => ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k))
    (fSeqStart F) (fSeqEnd F) Lb
    (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) AD CE
  diagonal_bound :
    ∑ d : Finset.Icc 2 (F.N + Dm),
      coefficientSeminorm (fRho F) (fNc F kc) F.tp (F.tp + fTobs F) (AD d) *
        (ENNReal.ofReal (D.κ (F.m - 1) * fRho F ^ (d.1 - 2)))⁻¹ ≤
      ENNReal.ofReal diagonalCost
  edge_bound : ∀ r ∈ Finset.Icc 1 F.depth, ∀ v u,
    ENNReal.ofReal (Real.sqrt ((F.G.mass law) u / (F.G.mass law) v)) *
      ((∑ d : Finset.Icc 2 (F.N + Dm),
        coefficientSeminorm (ocEpsilon D.q D.Λ (F.m - 1)) (fNc F kc)
          F.tp (F.tp + fTobs F) (CE r v u d) *
          (ENNReal.ofReal (D.κ (F.m - 1) * ocEpsilon D.q D.Λ (F.m - 1) ^ (d.1 - 2)))⁻¹) +
      ∑ d : Finset.Icc 2 (F.N + Dm),
        coefficientSeminorm (fRho F) (fNc F kc) F.tp (F.tp + fTobs F) (CE r v u d) *
          (ENNReal.ofReal (D.κ (F.m - 1) * fRho F ^ (d.1 - 2)))⁻¹) ≤
      ENNReal.ofReal (edgeCost *
        (Real.sqrt ((F.G.mass law) u / (F.G.mass law) v) *
          (CycleComparison.Coarse.maskedEdgeMatrix (familyAdj F.G.actualFamily) physicalEdge ^ r) v u))

/-- The budgets and regularity of `MeanBudget` give all the coarse letter fields. -/
theorem meanLetters_of_budget
    (F : Frame D hr Dm b j₀) (law : BirthLaw) (kc : ℕ) (hdepth : F.G.fam.HasDepthAtMost F.depth) (hπ : ∀ v, 0 < F.G.mass law v) (b : MeanBudget F law kc) :
    Nonempty (MeanLetters F law kc) := by
  classical
  let π := F.G.mass law
  let Ae : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ :=
    Matrix.of (familyMask F.G.actualFamily (fun v u => Real.sqrt (π u / π v) * b.physicalEdge v u))
  have hAe : ∀ v u, 0 ≤ Ae v u :=
    familyMask_nonneg _ (fun v u => mul_nonneg (Real.sqrt_nonneg _) (b.physical_nonneg v u))
  have hrow : ∀ v, ∑ u, Ae v u ≤ ∑ v, ∑ u, Ae v u := fun v =>
    Finset.single_le_sum (fun w _ => Finset.sum_nonneg fun u _ => hAe w u) (Finset.mem_univ v)
  have hcol : ∀ u, ∑ v, Ae v u ≤ ∑ v, ∑ u, Ae v u := by
    intro u
    exact Finset.sum_le_sum fun v _ =>
      Finset.single_le_sum (fun w _ => hAe v w) (Finset.mem_univ u)
  have hconj : (Matrix.of fun v u => Real.sqrt (π u / π v) *
      CycleComparison.Coarse.maskedEdgeMatrix (familyAdj F.G.actualFamily) b.physicalEdge v u) = Ae := by
    ext v u
    exact (familyMask_eq_conj F.G.actualFamily π b.physicalEdge v u).symm
  refine ⟨{
    AD := b.AD, CE := b.CE, Aedge := Ae, Cstar := max 1 b.edgeCost, Θ := ∑ v, ∑ u, Ae v u
    AD_meas := b.actual.2.2.2.1
    AD_smooth := b.actual.2.2.1
    AD_per := b.actual.2.2.2.2.1
    AD_fin := fun d => ne_top_of_sum_inv_le _ _ b.diagonal_bound d
    CE_meas := b.actual.2.2.2.2.2.2.1
    CE_smooth := b.actual.2.2.2.2.2.1
    CE_per := b.actual.2.2.2.2.2.2.2.1
    CE_fin := ?_
    edge_nonneg := hAe, edge_row := hrow, edge_col := hcol
    edge_acyclic := familyMask_pow_eq_zero _ (F.G.hasDepthAtMost_actualFamily hdepth) _
    edge_mean := ?_
    presentation := fun r hr => b.actual.1 r (by have := Finset.mem_range.mp hr; omega) }⟩
  · intro r hr v u d
    have h := b.edge_bound r hr v u
    exact ne_top_of_sum_inv_ne_top _ _ (ne_top_of_mul_add_le
      (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (div_pos (hπ u) (hπ v)))).ne' h) d
  · intro r hr v u
    have h := edge_mean_of_bound hπ
      (CycleComparison.Coarse.maskedEdgeMatrix_nonneg _ _ b.physical_nonneg)
      (le_rfl : max 1 b.edgeCost ≤ max 1 b.edgeCost) (Finset.mem_Icc.mp hr).1
      (b.edge_bound r hr v u)
    rw [hconj] at h
    exact h

/-- Frame statement from the window geometry and normalized actual-mean budgets.
This is an assembly from the two budgets; it does not prove the reconstruction letters by itself. -/
theorem lettersAt_of_budget (F : Frame D hr Dm b j₀) (law : BirthLaw) (kc : ℕ)
    (hdepth : F.G.fam.HasDepthAtMost F.depth)
    (g : WindowGeometry F law kc) (b : MeanBudget F law kc) :
    FrameReconLettersAt F law kc := by
  obtain ⟨m⟩ := meanLetters_of_budget F law kc hdepth g.mass_pos b
  exact lettersAt_of_inputs F law kc g m

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
