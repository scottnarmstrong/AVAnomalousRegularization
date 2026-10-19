-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct
import AVRegularity.EntryWeakAssembly.PositiveCutoffMetricEllipticity
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.CovarianceTimeMeasurable
public import AVRegularity.EntryTerminal.Assembly.Seed.RetainedGeneric
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup

/-! **The kernels of the seed** (`SeedKernelPart`).
The re-rooting gives every seed identity the kernel of its retained identity
(`IsSeedEncoding`). That kernel is either the weak paired kernel `S_{r_w}` of order `n_W` (on
copies of weak identities and the quadratic conversions of their paths) or the fresh terminal
kernel `S_{r_new}` of order `n_T` (on letters and empty conversions).
- Admissibility at `Γ_k ≥ 2` and `L_ker`: `isoPairedKernel_isAdmissible`, with
  `L_ker ≤ max{L_pr, L_c, L_f}` (the plan) and the kernel orders `IsTerminalKernelOrders`,
  `IsFreshKernelOrder`.
- Widths: the retained family matches widths (`actual_successor_kernel_width_matching`, from the
  weak widths `r_w` and `R_b = r_new`).
- The fine and coarse width budgets at `σ_f = δ` and `λ_c = λ_entry`:
  `band_interior_width_ratios`. The ratios decay like `ε_{M-1}^{qγ+3δ+qσ_w}`,
  `ε_{M-1}^{t_T}`, `ε_{M-2}^{λ_w-λ_entry}` and `ε_{M-2}^{λ_new-λ_entry}` beyond the needed powers,
  so `C_wid ≥ 1` suffices at late levels.
- Regularizers: `exists_isoPairedKernel_regularizer_constants` at the orders `n_W` and `n_T`. The
  floors are `c_ker ≥` both families of constants, monotone (`spatial_regularizer_constants_mono`).

Degenerate cases:
- No identities: vacuous.
- Only weak copies: the paired kernel `S_{r_w}`.
- Only letters: the fresh kernel `S_{r_new}`.
- `L_ker = max{L_pr, L_c, L_f}`: the plan's choice. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Preservation.FullLift

/-- `w ≤ C_wid R E^δ` from `w/R ≤ C E^{δ+p}`, `C E^p ≤ 1`, `C_wid ≥ 1`. -/
theorem seedKernel_width_le {w R E C e p δ Cw : ℝ} (hR : 0 < R) (hE : 0 < E)
    (h : w / R ≤ C * E ^ e) (he : e = δ + p) (hs : C * E ^ p ≤ 1) (hCw : 1 ≤ Cw) :
    w ≤ Cw * R * E ^ δ := by
  rw [div_le_iff₀ hR, he, Real.rpow_add hE] at h
  have hRE : 0 ≤ R * E ^ δ := mul_nonneg hR.le (Real.rpow_nonneg hE.le _)
  calc w ≤ C * (E ^ δ * E ^ p) * R := h
    _ = (C * E ^ p) * (R * E ^ δ) := by ring
    _ ≤ 1 * (R * E ^ δ) := mul_le_mul_of_nonneg_right hs hRE
    _ ≤ Cw * (R * E ^ δ) := mul_le_mul_of_nonneg_right hCw hRE
    _ = Cw * R * E ^ δ := by ring

/-- Admissibility at a larger bound. -/
theorem kernelSpec_admissible_mono {S : KernelSpec} {Γ Γ' : ℝ} {L : ℕ}
    (h : S.IsAdmissible Γ L) (hΓ : Γ ≤ Γ') : S.IsAdmissible Γ' L :=
  ⟨h.1, h.2.1, fun t => ⟨(h.2.2.1 t).1.trans hΓ, (h.2.2.1 t).2.1.trans hΓ, (h.2.2.1 t).2.2.1,
    (h.2.2.1 t).2.2.2.trans hΓ⟩, h.2.2.2⟩

/-- **The kernels of the seed.** -/
theorem seedKernel : SeedKernelPart := by
  intro X
  obtain ⟨Λw, hΛw, hw⟩ := band_interior_width_ratios X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨Λw, hΛw, fun A hΛ hA Kout => ⟨0, 0, fun sXT sZT _ _ => ?_⟩⟩
  obtain ⟨-, ⟨hφs, -, -, hφsupp⟩, -, ⟨-, -, -, -, hσw, -, -, -, -⟩, -, hsched, hexp, hfresh, -⟩ :=
    hA
  have hreg (n : ℕ+) := WeakEntryProofs.exists_isoPairedKernel_regularizer_constants A.φ₀
    (Providers.hasCompactSupport_of_unitBall hφsupp) hφs A.hφ₀ n
  choose cR hcR0 hcR using hreg
  let F : SeedFloors :=
    { cker := fun n j => max (cR n j) (cR A.nT j)
      Γk := fun _ => 2
      Cwid := fun _ => 1
      Ca := fun _ => 0
      Cm := fun _ _ => 0 }
  refine ⟨0, F, fun Lt nW cr kS hplan cK CL Cχ kW _ _ _ cP CP _ => ?_⟩
  show SeedKernelBlock A sXT sZT nW cr kS CL Cχ kW cP CP
  unfold SeedKernelBlock
  obtain ⟨-, -, -, hko, hcr, -, hkcr, hc0, -, -, -, hσf, hlam, -, hLker, hF⟩ := hplan
  obtain ⟨hFc, hFΓ, hFw, -, -⟩ := hF
  obtain ⟨-, -, -, -, -, -, -, -, htT, -⟩ := hsched
  obtain ⟨-, -, -, -, hlw, hln⟩ := hexp
  intro cH Cw _ _ j₀
  have h128 : 128 ≤ A.Λ := hΛw.trans hΛ
  have hq1 : 1 < X.q := X.hq.1
  obtain ⟨C, hC, hrat⟩ := hw A.Λ hΛ A.σw A.tT kS.c₀ cr hσw htT hc0 hcr
  have hγ := (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).1
  have hδ := (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).2.1
  have hp1 : 0 < X.q * ocGamma X.α X.q + 3 * ocDelta X.α X.q + X.q * A.σw := by
    have : 0 < X.q := by linarith
    positivity
  have hp3 : 0 < X.q ^ 2 * (1 + A.σw) - 1 - ocC X.α X.q - A.lamE := by linarith
  have hp4 : 0 < X.q * (1 + ocC X.α X.q + A.tT) - 1 - ocC X.α X.q - A.lamE := by linarith
  obtain ⟨Ma, hMa⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 h128 hp1
    (inv_pos.mpr hC)
  obtain ⟨Mb, hMb⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 h128 htT
    (inv_pos.mpr hC)
  obtain ⟨Mc, hMc⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 h128 hp3
    (inv_pos.mpr hC)
  obtain ⟨Md, hMd⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 h128 hp4
    (inv_pos.mpr hC)
  refine ⟨max 3 (max (max (Ma + 1) (Mb + 1)) (max (Mc + 2) (Md + 2))), fun M hM => ?_⟩
  have hM3 : 3 ≤ M := le_trans (le_max_left _ _) hM
  have hMs := le_trans (le_max_right _ _) hM
  have hMa' : Ma ≤ M - 1 := by have := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMs; omega
  have hMb' : Mb ≤ M - 1 := by have := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMs; omega
  have hMc' : Mc ≤ M - 1 - 1 := by have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMs; omega
  have hMd' : Md ≤ M - 1 - 1 := by have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hMs; omega
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx P freshK v u γ
  obtain ⟨hD, hW, -, -, -, -, hsucc, henc, -, -, -⟩ := hctx
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := hD
  obtain ⟨-, -, hlevW, -, -, ⟨hseedW, -, -⟩, hrecW, -, -, hinv⟩ := hW
  have hslev : seed.level = M - 1 := by
    rw [henc.1]
    show Gt'.level = M - 1
    rw [hsucc.2.1, hlevW]
  obtain ⟨-, -, -, -, -, -, e, idx, -, hdata⟩ := henc
  -- the two kernels
  set rW : ℝ := D.termRW A.σw M with hrW
  set rN : ℝ := D.termRNew cr A.tT M with hrN
  -- widths of the retained family
  have hGw : ∀ v u (γ : Gw.fam.Γ v u),
      (Gw.kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr) v u γ).width =
        (Gw.fam.identity v u γ).record.width := by
    intro v u γ
    obtain ⟨k, tag, hp⟩ := hseedW v u γ
    unfold GenStage.kernelOf
    rw [hp]
    exact ((hrecW v u γ).2.1).symm
  have hGt' := actual_successor_kernel_width_matching ScalarH D A.Dt A.bw j₀ (A.Pt D Cw cr M)
    (A.Mt M sXT sZT tp cr) (A.Kw_ D M nW) (A.Kn_ D M cr) Gw Gt'
    (hasTags_of_seed hinv.2.1 hseedW) hGw rfl hsucc
  have hcls : ∀ v u (γ : Gt'.fam.Γ v u),
      Gt'.kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr) v u γ = isoPairedKernel rW nW ∨
        Gt'.kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr) v u γ =
          isoPairedKernel rN A.nT := by
    intro v u γ
    unfold GenStage.kernelOf
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- reduce to a retained identity
  obtain ⟨v₀, rfl⟩ := ι.surjective v
  obtain ⟨u₀, rfl⟩ := ι.surjective u
  obtain ⟨γ₀, rfl⟩ := (e v₀ u₀).surjective γ
  obtain ⟨hprov, hker, -, hrecd, -, -⟩ := hdata v₀ u₀ γ₀
  have hK : seed.kernelOf P seedKc freshK (ι v₀) (ι u₀) (e v₀ u₀ γ₀) =
      Gt'.kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr)
        ⟨v₀.1, Finset.filter_subset _ _ v₀.2⟩ ⟨u₀.1, Finset.filter_subset _ _ u₀.2⟩ γ₀ := by
    unfold GenStage.kernelOf
    rw [hprov]
    exact hker
  have hsys : seed.sysS P seedKc freshK A.φ₀ A.hφ₀ (ι v₀) (ι u₀) (e v₀ u₀ γ₀) =
      (Gt'.kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr)
        ⟨v₀.1, Finset.filter_subset _ _ v₀.2⟩ ⟨u₀.1, Finset.filter_subset _ _ u₀.2⟩ γ₀).op
          A.φ₀ A.hφ₀ := by
    unfold GenStage.sysS
    rw [hK]
  have hwid := hGt' ⟨v₀.1, Finset.filter_subset _ _ v₀.2⟩ ⟨u₀.1, Finset.filter_subset _ _ u₀.2⟩ γ₀
  rw [hsys, hK, hrecd, hslev]
  change _ ∧ _ = (Gt'.fam.identity _ _ γ₀).record.width ∧
    (Gt'.fam.identity _ _ γ₀).record.width ≤ _ ∧ (Gt'.fam.identity _ _ γ₀).record.width ≤ _ ∧ _
  rw [← hwid]
  -- scales
  have hΛD : D.Λ = A.Λ := hDΛ
  obtain ⟨hE, -, -⟩ := Scales.epsilon_basic (m := M - 1) hq1 h128
  obtain ⟨hE2, -, -⟩ := Scales.epsilon_basic (m := M - 1 - 1) hq1 h128
  have hκ1 : 0 < D.κ (M - 1) := CycleReference.bandChain_pos (by omega) X.hζ hband (by omega)
  have hκ2 : 0 < D.κ (M - 1 - 1) := CycleReference.bandChain_pos (by omega) X.hζ hband (by omega)
  have hτ1 : 0 < ocTauPP X.α X.q A.Λ (M - 1) := Construction.Stream.ocTauPP_pos (by omega)
  have hτ0 : 0 < ocTauPP X.α X.q A.Λ M := Construction.Stream.ocTauPP_pos (by omega)
  have hA1 : 0 < ocA X.α X.q A.Λ (M - 1) := by
    unfold ocA
    exact Real.rpow_pos_of_pos hE _
  have hstar : 0 < kS.c₀ * min (ocEpsilon X.q A.Λ (M - 1))
      (Real.sqrt (D.κ (M - 1) / ocA X.α X.q A.Λ (M - 1))) :=
    mul_pos hc0 (lt_min hE (Real.sqrt_pos.mpr (div_pos hκ1 hA1)))
  have henh : 0 < cr * Real.sqrt (D.κ (M - 1 - 1) * ocTauPP X.α X.q A.Λ (M - 1)) :=
    mul_pos hcr (Real.sqrt_pos.mpr (mul_pos hκ2 hτ1))
  obtain ⟨r1, r2, r3, r4⟩ := hrat M D.κ hband M hM3 le_rfl
  have hCw : 1 ≤ kS.Cwid := hFw
  have hΓ : (2 : ℝ) ≤ kS.Γk := hFΓ
  have hs1 := seedStruct_mul_le_one hC (hMa (M - 1) hMa')
  have hs2 := seedStruct_mul_le_one hC (hMb (M - 1) hMb')
  have hs3 := seedStruct_mul_le_one hC (hMc (M - 1 - 1) hMc')
  have hs4 := seedStruct_mul_le_one hC (hMd (M - 1 - 1) hMd')
  have hrW0 : 0 < rW := by
    rw [hrW]
    exact Real.rpow_pos_of_pos (by simpa only [OCData.eps, hDq, hDΛ] using
      (Scales.epsilon_basic (m := M) hq1 h128).1) _
  have hrN0 : 0 < rN := by
    rw [hrN]
    simp only [OCData.termRNew, OCData.termRho, OCData.termB, OCData.termH, OCData.eps, hDα, hDq,
      hDΛ]
    exact mul_pos (mul_pos hcr (Real.sqrt_pos.mpr (mul_pos hκ1 hτ0))) (Real.rpow_pos_of_pos hE _)
  rcases hcls ⟨v₀.1, Finset.filter_subset _ _ v₀.2⟩ ⟨u₀.1, Finset.filter_subset _ _ u₀.2⟩ γ₀
    with hk | hk <;> rw [hk]
  · -- the weak paired kernel
    refine ⟨kernelSpec_admissible_mono (WeakEntryProofs.isoPairedKernel_isAdmissible rW nW kS.Lker
      (by have := hko.2; omega)) hΓ, rfl, ?_, ?_, fun ϱ _ kk _ => ?_⟩
    · show rW ≤ kS.Cwid * rhoStar D kS.c₀ (M - 1) * D.eps (M - 1) ^ kS.σf
      simp only [rhoStar, OCData.eps, hrW, OCData.termRW, hDα, hDq, hDΛ, hσf]
      exact seedKernel_width_le hstar hE r1 (by ring) hs1 hCw
    · show rW ≤ kS.Cwid * rhoEnh D kS.cr (M - 1) * D.eps (M - 1 - 1) ^ kS.lamC
      simp only [rhoEnh, OCData.eps, hrW, OCData.termRW, hDα, hDq, hDΛ, hkcr, hlam]
      exact seedKernel_width_le henh hE2 r3 (by ring) hs3 hCw
    · exact spatial_regularizer_constants_mono (hcR nW rW hrW0 ϱ (tp + D.termH M) (a + A.T₀) kk A.Ds)
        hrW0.le fun j _ => (le_max_left _ _).trans (hFc j)
  · -- the fresh terminal kernel
    refine ⟨kernelSpec_admissible_mono (WeakEntryProofs.isoPairedKernel_isAdmissible rN A.nT
      kS.Lker (by have := hfresh.2; omega)) hΓ, rfl, ?_, ?_, fun ϱ _ kk _ => ?_⟩
    · show rN ≤ kS.Cwid * rhoStar D kS.c₀ (M - 1) * D.eps (M - 1) ^ kS.σf
      simp only [rhoStar, OCData.eps, hrN, OCData.termRNew, OCData.termRho, OCData.termB,
        OCData.termH, hDα, hDq, hDΛ, hσf]
      exact seedKernel_width_le hstar hE r2 rfl hs2 hCw
    · show rN ≤ kS.Cwid * rhoEnh D kS.cr (M - 1) * D.eps (M - 1 - 1) ^ kS.lamC
      simp only [rhoEnh, OCData.eps, hrN, OCData.termRNew, OCData.termRho, OCData.termB,
        OCData.termH, hDα, hDq, hDΛ, hkcr, hlam]
      exact seedKernel_width_le henh hE2 r4 (by ring) hs4 hCw
    · exact spatial_regularizer_constants_mono
        (hcR A.nT rN hrN0 ϱ (tp + D.termH M) (a + A.T₀) kk A.Ds)
        hrN0.le fun j _ => (le_max_right _ _).trans (hFc j)

end AVRegularity.EntryTerminal.Ingredients
