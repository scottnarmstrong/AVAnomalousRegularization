-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Ledger.TaggedRecurrence
public import AVRegularity.Construction.Preservation.Assembly.StageInvariantPropagationOfIngredients
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Construction.Preservation.Assembly.FullLiftFromInputs
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.StageKernelPrice

/-! Common finite-incidence step of weak, terminal and retained-stage kernel pricing.
Encoding, provenance and uniform choices belong to the callers, not to this estimate. -/

/-- Constituent prices and their positive mass-conjugated matrix control the kernel matrix.
The widths may differ from constituent to constituent. No component-count factor occurs. -/
theorem kernel_schur_of_identity_prices {ι : Type*} [Fintype ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j γ, NormedAddCommGroup (G i j γ)]
    [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
    (ν ρ : ℝ) (π : ι → ℝ) (k D : ℕ) (a b : ℝ) (c : ℕ → ℝ)
    (r : ∀ i j, Γ i j → ℝ)
    (C : ∀ i j (γ : Γ i j), h j →L[ℝ] G i j γ)
    (B : ∀ i j (γ : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j γ)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (p : ∀ i j, Γ i j → ℝ) (A S : ℝ)
    (hν : 0 < ν) (hr : ∀ i j γ, 0 < r i j γ)
    (hc : ∀ d, d + 2 ≤ D → 0 ≤ c d) (hC : ∀ i j γ, ‖C i j γ‖ ≤ 1)
    (hA : 0 ≤ A)
    (hprice : ∀ i j γ,
      (∑ d : ↥(Finset.Icc 2 D),
        (coefficientSeminorm ρ k a b (B i j γ d)).toReal * c (d.1 - 2) /
          (ν * r i j γ ^ (d.1 - 2))) ≤ A * p i j γ)
    (hbudget : SchurBound S (fun i j => Real.sqrt (π j / π i) * ∑ γ, p i j γ)) :
    SchurBound (A * S) (kernelSchurMatrix ν ρ π k D a b c r C B) := by
  classical
  have he (i j) : kernelSchurMatrix ν ρ π k D a b c r C B i j ≤
      A * (Real.sqrt (π j / π i) * ∑ γ, p i j γ) := by
    unfold kernelSchurMatrix
    calc
      _ ≤ Real.sqrt (π j / π i) * ∑ γ, A * p i j γ := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply Finset.sum_le_sum
        intro γ _
        have hn : 0 ≤ ∑ d : ↥(Finset.Icc 2 D),
            (coefficientSeminorm ρ k a b (B i j γ d)).toReal * c (d.1 - 2) /
              (ν * r i j γ ^ (d.1 - 2)) := by
          apply Finset.sum_nonneg
          intro d _
          exact div_nonneg (mul_nonneg ENNReal.toReal_nonneg
            (hc _ (by have hd := Finset.mem_Icc.mp d.property; omega)))
            (mul_nonneg hν.le (pow_nonneg (hr i j γ).le _))
        exact (mul_le_mul_of_nonneg_right (hC i j γ) hn).trans
          (by simpa only [one_mul] using hprice i j γ)
      _ = _ := by rw [← Finset.mul_sum, mul_left_comm]
  constructor
  · intro i
    exact (Finset.sum_le_sum (fun j _ => he i j)).trans
      (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hbudget.1 i) hA)
  · intro j
    exact (Finset.sum_le_sum (fun i _ => he i j)).trans
      (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hbudget.2 j) hA)

end AVRegularity.Construction.StageKernelPrice
end
end

section
section
/-! Pay a fixed physical kernel price from the strictly decaying one-step ledger recurrence.
The starting level is chosen after the price constant, before the stage and its data. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.StageKernelPrice

/-- The original-order kernel constant is absorbed with the exact parent-wavelength price. -/
theorem successor_kernel_price_absorption (q : ℝ) (Λ : ℕ)
    (hq : 1 < q) (hq16 : q < 17 / 16) (hΛ : 128 ≤ Λ)
    (τ θ A B C CI : ℝ) (hτ : 0 < τ) (hθ : τ < θ)
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hC : 1 ≤ C) (hCI : 0 < CI) :
    ∃ mStar : ℕ, 3 ≤ mStar ∧ ∀ m : ℕ, mStar ≤ m →
      A * (CI * ocEpsilon q Λ m ^ τ) ≤ 1 / 2 ∧
      C * (B * ocEpsilon q Λ (m - 1) ^ θ + 2 * A * (CI * ocEpsilon q Λ m ^ τ)) ≤
        CI * ocEpsilon q Λ (m - 1 - 1) ^ (q * τ) := by
  let K : ℝ := (2 : ℝ) ^ τ
  have hK : 0 < K := Real.rpow_pos_of_pos (by norm_num) _
  have hK1 : 1 ≤ K := Real.one_le_rpow (by norm_num) hτ.le
  have hCA : 1 ≤ C * A := by
    simpa only [one_mul] using mul_le_mul hC hA zero_le_one (zero_le_one.trans hC)
  have hA' : 1 ≤ C * A * K := by
    simpa only [one_mul] using mul_le_mul hCA hK1 zero_le_one (zero_le_one.trans hCA)
  obtain ⟨m₀, _, hs⟩ := Preservation.Ledger.ledger_scale_absorption q Λ hq hq16 hΛ
    τ θ (C * A * K) (C * B) (CI / K) hτ hθ hA'
    (mul_nonneg (zero_le_one.trans hC) hB) (div_pos hCI hK)
  refine ⟨max 3 m₀, le_max_left _ _, ?_⟩
  intro m hm
  have hsmall := hs m ((le_max_right _ _).trans hm)
  have hcancel : (C * A * K) * (CI / K * ocEpsilon q Λ m ^ τ) =
      C * (A * (CI * ocEpsilon q Λ m ^ τ)) := by field_simp
  rw [hcancel] at hsmall
  have hnonneg : 0 ≤ A * (CI * ocEpsilon q Λ m ^ τ) :=
    mul_nonneg (zero_le_one.trans hA) (mul_nonneg hCI.le
      (Real.rpow_nonneg (Scales.epsilon_basic hq hΛ).1.le _))
  refine ⟨(le_mul_of_one_le_left hnonneg hC).trans hsmall.1, ?_⟩
  have hstep := Real.rpow_le_rpow (Scales.epsilon_basic (m := m - 1) hq hΛ).1.le
    (Scales.epsilon_q_step hq hq16 hΛ (by omega : 1 ≤ m - 1)) hτ.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
    (Real.rpow_nonneg (Scales.epsilon_basic hq hΛ).1.le _),
    ← Real.rpow_mul (Scales.epsilon_basic hq hΛ).1.le] at hstep
  calc
    _ = C * B * ocEpsilon q Λ (m - 1) ^ θ +
        2 * (C * A * K) * (CI / K * ocEpsilon q Λ m ^ τ) := by
      field_simp
    _ ≤ (CI / K) * ocEpsilon q Λ (m - 1) ^ τ := hsmall.2
    _ ≤ (CI / K) * (K * ocEpsilon q Λ (m - 1 - 1) ^ (q * τ)) :=
      mul_le_mul_of_nonneg_left hstep (div_nonneg hCI.le hK.le)
    _ = _ := by field_simp

end AVRegularity.Construction.StageKernelPrice
end
end

section
/-! Instantiate the shared stage kernel-price estimate on the actual retained successor.
The K3 birth/transport recurrence pays the original physical-price constant before data. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.StageKernelPrice
open Preservation Preservation.Assembly Preservation.FullLift

private theorem transport_constant_ge_one (Cw : ℝ) (Tw : ℕ) (hCw : 0 < Cw) :
    1 ≤ ledgerTransportConstant Cw Tw := by
  unfold ledgerTransportConstant
  have ht : 0 ≤ (Tw : ℝ) := Nat.cast_nonneg _
  nlinarith only [ht, hCw]

private theorem birth_constant_nonneg (α q s Cw : ℝ) (Tw L : ℕ) (hCw : 0 < Cw) :
    0 ≤ ledgerBirthConstant α q s Cw Tw L :=
  mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num) (add_nonneg (Nat.cast_nonneg _) zero_le_one))
    (add_nonneg (Nat.cast_nonneg _) zero_le_one)) (add_nonneg hCw.le zero_le_one))
    (Real.sqrt_nonneg _)

/-- Both weights and all reserved kernel orders satisfy the exact propagation price. -/
theorem successor_kernel_prices (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : SuccessorKernelPriceStatement α s q ζ := by
  classical
  obtain ⟨Λc, hΛc, hc⟩ := retained_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λl, hΛl, hlength⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λc Λl, by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ (by omega)
  refine ⟨min cmax 1, lt_min hcmax zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr₀, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  let thr : InvConsts := { thr₀ with cker := fun j => max 0 (thr₀.cker j) }
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  have hkI₀ := invariant_admissible_of_threshold_bounds (a := thr₀) (b := thr)
    le_rfl le_rfl le_rfl (fun _ => le_rfl) (fun _ => le_max_right _ _) hkI
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkI₀
  have hcker : ∀ j, 0 ≤ kI.cker j := fun j =>
    (le_max_left _ _).trans (invariant_admissible_kernel_bounds hkI j).2
  obtain ⟨hc0I, hcrI, hprod⟩ := Buffer.invariantAdmissible_molecular_parameters hkI
  have hc0pos : 0 < kI.c₀ := hc0I.symm ▸ hc₀
  have hc0le : kI.c₀ ≤ 1 := hc0I.symm ▸ hc₀upper.trans (min_le_right _ _)
  have hcrle : kI.cr ≤ 1 := hcrI.symm ▸ hcrupper
  let Dm := succSchedD D₀ N p (H + 1)
  have hprices (i : Fin (kI.Ks + 1)) := uniform_native_identity_kernel_price α s q
    hα₀ hα₁ hs₀ hs₁ hq Λ h128 ζ hζ bw hbw i.1 (i.1 + Dm) Dm (le_refl _)
    kI.cker (fun j _ => hcker j)
  choose A hA mo hmo hidentity using hprices
  let C : ℝ := 1 + ∑ i : Fin (kI.Ks + 1), A i
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hA i)
  have hAC (i : Fin (kI.Ks + 1)) : A i ≤ C :=
    (Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
  let mp := ∑ i : Fin (kI.Ks + 1), mo i
  have hmp (i : Fin (kI.Ks + 1)) : mo i ≤ mp :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨max CIthr 1, max Cwthr 1, ?_⟩
  intro CI Cw j₀ hledger hstart
  have hLc : IsLedgerAdmissible Ce CI Cw CIthr Cwthr :=
    ⟨hledger.1, (le_max_left _ _).trans hledger.2.1,
      (le_max_left _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  obtain ⟨mc, hc⟩ := hc CI Cw j₀ hLc hstart
  have hCI : 0 < CI := (zero_lt_one.trans_le hCe).trans_le hledger.1
  have hCw : 0 < Cw := hledger.2.2.2
  obtain ⟨_, _, _, _, _, hσeq, ha, haσ, _, hσD, _⟩ := hsched
  have hσ₀ : 0 ≤ σ₀ := by linarith only [hσeq, ha, haσ]
  let Tw := (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card
  let At := ledgerTransportConstant Cw Tw
  let Bt := ledgerBirthConstant α q s Cw Tw (succAlphabetOf r₀ D₀ H J N p npad).card
  let τ := min (ocDelta α q / 4) τe
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ : 0 < τ := lt_min (div_pos hδ (by norm_num)) hτe
  have hθ : τ < succTheta1 α q s σ₀ (succDstar D₀ N p H) := by
    have hηle : succEta0 α q s ≤ ocDelta α q / 8 := min_le_left _ _
    have hτle : τ ≤ ocDelta α q / 4 := min_le_left _ _
    dsimp only [succTheta1]
    linarith only [hδ, hηle, hτle, hσD]
  have hAt : 1 ≤ At := transport_constant_ge_one Cw Tw hCw
  have hBt : 0 ≤ Bt := birth_constant_nonneg α q s Cw Tw _ hCw
  obtain ⟨ma, hma, habs⟩ := successor_kernel_price_absorption q Λ hq.1 hq.2.1 h128
    τ (succTheta1 α q s σ₀ (succDstar D₀ N p H)) At Bt C CI hτ hθ hAt hBt hC hCI
  refine ⟨max mc (max ma (max (mp + 3) (j₀ + 3))), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  have hm2 : 2 ≤ m := by omega
  have hqD : 1 < D.q := hDq.symm ▸ hq.1
  have hΛD : 128 ≤ D.Λ := hDΛ.symm ▸ h128
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  let P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p
  let Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)
  let Gr := G'.retained m H J
  have hGrlevel : Gr.level = m - 1 := by change G'.level = _; rw [hactual.2.1, hlevel]
  have hcert := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM tA htA G G' hcascade hlevel hG hactual
  obtain ⟨hnat, _hshift, hslot, hctx, _hled, hker⟩ := hcert
  have hcGr : IsCascadeStage D P Mn seed Gr := by
    simpa only [hlevel, succMenu, P, Mn, Gr] using IsCascadeStage.step hcascade hactual
  have hprod' : kI.Hprod = kI.G0 + Mn.H + 1 := hprod
  have hmGr v : 0 ≤ compReserve kI (v : CompIn Gr.comps).1 :=
    (Buffer.cascade_component_reserve_pos hseed.2.1 hcGr kI hprod' v).le
  have hm2Gr v : compReserve kI (v : CompIn Gr.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hseedI := hseed.2.2.2.2.2.2.2.1
  have hlens : ∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level := by
    intro v u γ hb
    simpa only [hseed.1] using (hseed.2.2.2.2.2.1 v u γ).2.2 hb
  have hlenGr := hlength hr D hDα hDq hDζ (by rw [hDΛ]; omega) hbandD
    _ bw j₀ Mn Cw kI.cr σ₀ (succEta0 α q s) N p hcrle seed Gr hseedI.2.1 hlens
    (by rw [hseed.1, hterm]; exact hnM.le) hcGr (by rw [hGrlevel]; omega)
  have he (i : ℕ) : 0 < D.eps i := Construction.Stream.ocEpsilon_pos (by omega)
  have hν : 0 < D.kap Gr.level := by
    unfold OCData.kap
    rw [Nat.min_eq_left (by rw [hGrlevel, hterm]; omega)]
    exact CycleReference.bandChain_pos (by omega) (hDζ.symm ▸ hζ) hbandD
      (by rw [hGrlevel, hterm]; omega)
  have hκ : 0 < D.κ Gr.level := by
    have hkap : D.kap Gr.level = D.κ Gr.level := by
      unfold OCData.kap
      rw [Nat.min_eq_left (by rw [hGrlevel, hterm]; omega)]
    exact hkap ▸ hν
  have hrho : 0 < rhoStar D kI.c₀ Gr.level := mul_pos hc0pos
    (lt_min (he _) (Real.sqrt_pos.2 (div_pos hκ (Real.rpow_pos_of_pos (he _) _))))
  have hrhoe : rhoStar D kI.c₀ Gr.level ≤ D.eps Gr.level :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hc0pos.le).trans
      (mul_le_of_le_one_left (he _).le hc0le)
  have hrhoE : rhoStar D kI.c₀ Gr.level ≤ D.eps (Gr.level - 1) :=
    hrhoe.trans (EntryScales.epsilon_antitone hqD hΛD (Nat.sub_le _ _))
  have hlengthop v u (γ : Gr.fam.Γ v u) (hj : 3 ≤ (Gr.fam.identity v u γ).maxOrder) :
      (Gr.fam.identity v u γ).record.length ≤ D.eps (Gr.level - 1) := by
    have hb : 1 ≤ (Gr.fam.identity v u γ).record.birthExcess := by
      have hh := (Gr.fam.identity v u γ).le_birth
      omega
    exact (hlenGr v u γ hb).trans (EntryScales.epsilon_antitone hqD hΛD (Nat.sub_le _ _))
  have hletter : ∀ l ∈ (succAlphabetOf r₀ D₀ H J N p npad),
      letterOrder N p l - 2 ≤ succDstar D₀ N p H := by
    intro l hl
    have hnext : succSchedD D₀ N p (H + 1) = succSchedD D₀ N p H + 2 * N + 4 * p + 4 := rfl
    cases l with
    | diag => simp only [letterOrder, succDstar]; omega
    | mean n h =>
      have hn := (Providers.CascadeInvariants.mean_mem_succAlphabet hl).2.1
      simp only [letterOrder, succDstar]
      omega
    | covariance n h a a' =>
      have hf := Providers.CascadeInvariants.cov_mem_succAlphabet hl
      simp only [letterOrder, succDstar]
      omega
    | eddy n => simp [succAlphabetOf, succAlphabet] at hl
    | padding n => simp only [letterOrder]; omega
  have hold := InitialValue.cascade_invariant hseed.2.1 hcascade
  have hbounds := habs m (by omega)
  have hε : D.eps m = ocEpsilon q Λ m := by simp only [OCData.eps, hDq, hDΛ]
  have hE : D.eps (m - 1) = ocEpsilon q Λ (m - 1) := by simp only [OCData.eps, hDq, hDΛ]
  let S := Bt * D.eps (m - 1) ^ succTheta1 α q s σ₀ (succDstar D₀ N p H) +
    2 * At * (CI * D.eps m ^ τ)
  have hledgerGr : markedLedger (Gr.mass law) (Gr.marker law) Gr.fam ≤ S := by
    have hh := Ledger.tagged_ledger_recurrence hr D _ bw j₀ α s q hDα hDq hq.1 hΛD
      (successor_eta0_pos hα₀ hα₁ hs₀ hs₁ hq) Cw kI.cr σ₀ N p (succDstar D₀ N p H) Mn
      hCw hσ₀ hletter law hlaw G G' hG.2.1 (fun v hv => (hold v hv).1) hactual (hlevel.symm ▸ hm2)
      (CI * D.eps m ^ τ) (mul_nonneg hCI.le (Real.rpow_nonneg (he m).le _))
      hG.2.2.2.2.2.2.2.1 (by simpa only [At, Tw, hε, Mn, succMenu] using hbounds.1) H J
    rw [hlevel] at hh
    simpa only [S, At, Bt, Tw, Mn, succMenu, Gr] using hh
  have hpriced := priced_record_ledger_schur Gr.fam (Gr.mass law) (Gr.marker law)
    (fun v => Buffer.birth_compMass_pos hqD hΛD law v.1)
    (fun v => Buffer.birth_compMarker_pos hqD hΛD law v.1) S hledgerGr
  intro kk hkk w hw
  let i : Fin (kI.Ks + 1) := ⟨kk, by omega⟩
  have hid (v u : CompIn Gr.comps) (γ : Gr.fam.Γ v u) :=
    hidentity i hr D hDα hDq hDΛ hDζ hseq j₀ Mnat Gr kI hctx hnat
      (by rw [hGrlevel]; have hi := hmp i; omega)
      (by rw [hGrlevel]; omega) (by rw [hGrlevel]; omega) (he _) (he _) hν hslot
      (tA + 3 * ocTau α q Λ m) tf v u γ (hmGr v) (hm2Gr v)
      (rhoStar D kI.c₀ Gr.level) hrho hrhoE hrhoe (hlengthop v u γ)
  have hbudget : SchurBound S (pricedRecordMajorant (fun v => Gr.mass law v / w v ^ 2)
      (fun _ => 1) Gr.fam) := by
    rcases hw with rfl | rfl
    · simpa only [one_pow, div_one] using hpriced.1
    · exact hpriced.2
  have hidentityPrice (v u : CompIn Gr.comps) (γ : Gr.fam.Γ v u) :
      (∑ d : ↥(Finset.Icc 2 Dm),
        (coefficientSeminorm (rhoStar D kI.c₀ Gr.level) kk
          (tA + 3 * ocTau α q Λ m) tf (Gr.physCoeff v u γ d.1)).toReal * kI.cker (d.1 - 2) /
          (D.kap Gr.level * (Gr.kernelOf P seedK freshK v u γ).width ^ (d.1 - 2))) ≤
        C * (‖(Gr.fam.identity v u γ).map‖ * (Gr.fam.identity v u γ).record.size *
          constituentPrice (Gr.fam.identity v u γ).record) := by
    rw [(hker v u γ).1]
    exact (hid v u γ).trans (mul_le_mul_of_nonneg_right (hAC i)
      (mul_nonneg (mul_nonneg (norm_nonneg _) (Gr.fam.identity v u γ).record.size_nonneg)
        (constituentPrice_nonneg _)))
  have hbudget' : SchurBound S (fun v u =>
      Real.sqrt ((Gr.mass law u / w u ^ 2) / (Gr.mass law v / w v ^ 2)) *
        ∑ γ, ‖(Gr.fam.identity v u γ).map‖ * (Gr.fam.identity v u γ).record.size *
          constituentPrice (Gr.fam.identity v u γ).record) := by
    change SchurBound S (fun v u => (1 : ℝ) / 1 *
      Real.sqrt ((Gr.mass law u / w u ^ 2) / (Gr.mass law v / w v ^ 2)) *
        ∑ γ, ‖(Gr.fam.identity v u γ).map‖ * (Gr.fam.identity v u γ).record.size *
          constituentPrice (Gr.fam.identity v u γ).record) at hbudget
    simpa only [div_self (by norm_num : (1 : ℝ) ≠ 0), one_mul] using hbudget
  have hkernel := kernel_schur_of_identity_prices (D.kap Gr.level) (rhoStar D kI.c₀ Gr.level)
    (fun v => Gr.mass law v / w v ^ 2) kk Dm (tA + 3 * ocTau α q Λ m) tf kI.cker
    (fun v u γ => (Gr.kernelOf P seedK freshK v u γ).width)
    (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
    (fun v u γ d => Gr.physCoeff v u γ d.1)
    (fun v u γ => ‖(Gr.fam.identity v u γ).map‖ * (Gr.fam.identity v u γ).record.size *
      constituentPrice (Gr.fam.identity v u γ).record) C S hν
    (fun v u γ => by rw [(hker v u γ).1]; exact (Gr.fam.identity v u γ).record.width_pos)
    (fun j _ => hcker j) (fun _ _ _ => ContinuousLinearMap.norm_id_le) (zero_le_one.trans hC)
    hidentityPrice hbudget'
  have hfinal : C * S ≤ CI * D.eps (m - 1 - 1) ^ (q * τ) := by
    simpa only [S, hε, hE, OCData.eps, hDq, hDΛ, hGrlevel] using hbounds.2
  exact ⟨fun v => (hkernel.1 v).trans hfinal, fun u => (hkernel.2 u).trans hfinal⟩

end AVRegularity.Construction.StageKernelPrice
end
end
end
