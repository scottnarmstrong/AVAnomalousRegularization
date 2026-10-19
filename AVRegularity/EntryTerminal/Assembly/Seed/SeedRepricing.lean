-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
import AVRegularity.EntryTerminal.Assembly.Seed.OfParts
import AVRegularity.EntryTerminal.Ingredients.SeedKernel.SeedKernel
import AVRegularity.EntryTerminal.Ingredients.SeedEnvelope.Assembly
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
public import AVRegularity.EntryTerminal.Assembly.Seed.SeedLedgerAssembly
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct

/-! E4 follows by repricing the seed ledger at a smaller constant. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.StageEnvelopes
namespace AVRegularity.EntryTerminal.Route
open AVRegularity.EntryTerminal.Ingredients

/-- The rounded scales cost a fixed factor when converting to the parent. -/
theorem schur_decay {e E q τ A : ℝ} (he : 0 ≤ e) (hE : 0 ≤ E)
    (hτ : 0 ≤ τ) (hstep : e ≤ 2 * E ^ q) (hA : 0 ≤ A) :
    A * e ^ τ ≤ (A * (2 : ℝ) ^ τ) * E ^ (q * τ) := by
  have hp := Real.rpow_le_rpow he hstep hτ
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hE _),
    ← Real.rpow_mul hE] at hp
  exact (mul_le_mul_of_nonneg_left hp hA).trans_eq (mul_assoc _ _ _).symm

/-- E4: all kernel Schur bounds of the encoded seed. -/
theorem seedSchurPart : SeedSchurPart := by
  intro X
  obtain ⟨Λl, hΛl, hl⟩ := (seedLedgerPart.and seedKernel) X
  obtain ⟨Λs, hΛs, hsc⟩ := seedEnv_scales X
  refine ⟨max Λl Λs, hΛl.trans (le_max_left _ _), fun A hΛ hA Kout => ?_⟩
  have hΛl' := (le_max_left Λl Λs).trans hΛ
  have hΛs' := (le_max_right Λl Λs).trans hΛ
  have h128 := hΛl.trans hΛl'
  obtain ⟨SX, SZ, hl⟩ := hl A hΛl' hA Kout
  let R := max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2
  refine ⟨max SX R, max SZ R, fun sXT sZT hX hZ => ?_⟩
  have hXR : R ≤ sXT := (le_max_right _ _).trans hX
  have hZR : R ≤ sZT := (le_max_right _ _).trans hZ
  obtain ⟨KS, F, hl⟩ := hl sXT sZT ((le_max_left _ _).trans hX) ((le_max_left _ _).trans hZ)
  refine ⟨KS, F.sup seedStructFloors, fun Lt nW cr kS hplan cK CL Cχ kW hcK hkW hwa cP CP hcP => ?_⟩
  obtain ⟨hledger, hkernel⟩ := hl Lt nW cr kS (hplan.weaken le_rfl fun h => h.left)
    cK CL Cχ kW hcK hkW hwa cP CP hcP
  have hcker : ∀ j, 0 ≤ kS.cker j := hplan.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.right.1
  have hb : 0 < A.bw := hA.2.2.1.1
  obtain ⟨-, -, -, -, hcr, -, -, hc0, hc0m, -, -, -, -, halloc, -, -⟩ := hplan
  have hc01 : kS.c₀ ≤ 1 := hc0m.trans (min_le_left _ _)
  obtain ⟨-, -, -, -, -, -, -, -, hHprod, -, -⟩ := halloc
  have hτ : 0 < A.τe := hA.2.2.2.2.2.2.1.1
  have hh (kk : Fin (kS.Ks + 1)) :=
    Construction.Preservation.FullLift.uniform_native_kernel_schur_of_certificates
      X.α X.s X.q X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq A.Λ h128 X.ζ X.hζ A.bw hb
      kk.1 (kk.1 + A.Ds) A.Ds le_rfl kS.cker (fun j _ => hcker j)
  choose C hC m₀ hm₀ hprice using hh
  let CT : ℝ := 1 + ∑ kk, C kk
  have hCT : 0 < CT := by
    have hn : 0 ≤ ∑ kk, C kk := Finset.sum_nonneg fun kk _ => hC kk
    dsimp only [CT]; linarith only [hn]
  have hCle (kk) : C kk ≤ CT :=
    (Finset.single_le_sum (fun kk _ => hC kk) (Finset.mem_univ kk)).trans (by dsimp [CT]; linarith)
  let B : ℝ := CT * (2 : ℝ) ^ A.τe
  have hB : 0 < B := mul_pos hCT (Real.rpow_pos_of_pos (by norm_num) _)
  obtain ⟨Ms, -, hMs⟩ := hsc A.Λ hΛs' kS.c₀ cr CL hc0 hcr
  intro cH Cw hcH hCw
  obtain ⟨Ce₀, CH, Y, hCH, hY, hl⟩ := hledger cH Cw hcH hCw
  refine ⟨B * max Ce₀ 1, max CH 1, max Y 1, hCH.trans (le_max_left _ _),
    lt_of_lt_of_le one_pos (le_max_right _ _), fun Ce hCe j₀ hj₀ => ?_⟩
  have hCe' : max Ce₀ 1 ≤ Ce / B := (le_div_iff₀ hB).2 (by simpa only [mul_comm] using hCe)
  have hCe0 : 0 < Ce / B := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hCe')
  have hcar1 : IsCarrierStart X.α X.q A.Λ A.bw 1 1 j₀ :=
    IsCarrierStart.mono (fun _ => Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos (by omega)).le _)
      (fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le)
      (le_max_right _ _) (le_max_right _ _) zero_le_one zero_le_one hj₀
  have hcarL : IsCarrierStart X.α X.q A.Λ A.bw CH Y j₀ :=
    IsCarrierStart.mono (fun _ => Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos (by omega)).le _)
      (fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le)
      (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCH) hY.le hj₀
  obtain ⟨Ml, hl⟩ := hl (Ce / B) ((le_max_left _ _).trans hCe') j₀ hcarL
  obtain ⟨Mk, hk⟩ := hkernel cH Cw hcH hCw j₀
  refine ⟨Ms + Ml + Mk + j₀ + 4 + ∑ kk, m₀ kk, fun M hM => ?_⟩
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hnat hcert law hm hr
    P freshK kk hkk w hw
  have hctx' := hctx
  obtain ⟨hD, -, -, -, -, -, -, henc, -, -, -⟩ := hctx
  obtain ⟨hDα, hDq, hDΛ, hDζ, hstream, hband, hterm⟩ := hD
  have hslot := seedE1_slotTransverse hA h128 hcar1 hXR hZR hcr hctx'
  obtain ⟨hρ, hCL⟩ := hMs M (by omega) D hDα hDq hDΛ hDζ hband hterm
  obtain ⟨hlev, hlength⟩ := seedEnv_higherLength hctx' hρ hCL
  obtain ⟨-, hbirths, -, -, -, -⟩ := seedEncoding_struct henc
  have hqD : 1 < D.q := hDq ▸ X.hq.1
  have hΛD : 128 ≤ D.Λ := hDΛ ▸ h128
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hζD : IsFastProfile D.ζ := hDζ ▸ X.hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]; exact hband
  have he (i : ℕ) : 0 < D.eps i := Construction.Stream.ocEpsilon_pos hΛ1
  have hν : 0 < D.kap seed.level := by
    unfold OCData.kap
    exact CycleReference.bandChain_pos hΛ1 hζD hbandD (Nat.min_le_right _ _)
  have hνκ : 0 < D.κ seed.level :=
    CycleReference.bandChain_pos hΛ1 hζD hbandD (by rw [hlev, hterm]; omega)
  have hρ0 : 0 < rhoStar D kS.c₀ seed.level := by
    unfold rhoStar
    exact mul_pos hc0 (lt_min (he _) (Real.sqrt_pos.2 (div_pos hνκ
      (Real.rpow_pos_of_pos (he _) _))))
  have hρe : rhoStar D kS.c₀ seed.level ≤ D.eps seed.level :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hc0.le).trans
      (mul_le_of_le_one_left (he _).le hc01)
  have hEE : D.eps seed.level ≤ D.eps (seed.level - 1) :=
    Providers.CascadeInvariants.eps_le_of_le hqD hΛD (Nat.sub_le _ _)
  have hres (v : CompIn seed.comps) : 0 ≤ compReserve kS v.1 :=
    (by positivity : (0 : ℝ) ≤ 2 / ((kS.Hprod : ℝ) + 1)).trans
      (retained_compReserve_ge hHprod (by simp [compGrade, hbirths v]))
  have hres2 (v : CompIn seed.comps) : compReserve kS v.1 ≤ 2 :=
    (Construction.Preservation.Buffer.compReserve_le_one kS v.1).trans (by norm_num)
  let ki : Fin (kS.Ks + 1) := ⟨kk, by omega⟩
  have hmki : m₀ ki ≤ ∑ kk, m₀ kk :=
    Finset.single_le_sum (fun kk _ => Nat.zero_le (m₀ kk)) (Finset.mem_univ ki)
  have hled := hl M (by omega) D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι
    hctx' hnat hcert law hm hr
  have hwid := hk M (by omega) D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx'
  have hp := hprice ki ScalarH D hDα hDq hDΛ hDζ hstream j₀ (M + A.Jw) seed kS hcert hnat
    (by rw [hlev]; omega) (by rw [hlev]; omega) (by rw [hlev]; omega) (he _) (he _) hν hslot
    hres hres2 P seedKc freshK (fun v u γ => (hwid P freshK v u γ).2.1)
    (tp + D.termH M) (a + A.T₀) (rhoStar D kS.c₀ seed.level)
    (Ce / B * D.eps (M - 1) ^ A.τe) (seed.mass law) (seed.marker law) hρ0 (hρe.trans hEE) hρe
    (fun v u γ h3 => ((hlength v u γ h3).trans hρe).trans hEE)
    (fun v => Construction.Preservation.Buffer.birth_compMass_pos hqD hΛD law v.1)
    (fun v => Construction.Preservation.Buffer.birth_compMarker_pos hqD hΛD law v.1) hled w hw
  have hstep : D.eps (M - 1) ≤ 2 * D.eps (M - 1 - 1) ^ D.q :=
    Scales.epsilon_q_step hqD (hDq ▸ X.hq.2.1) hΛD (by omega)
  have hdec := schur_decay (he (M - 1)).le (he (M - 1 - 1)).le hτ.le hstep
    (mul_nonneg (hC ki) hCe0.le)
  have hconst : (C ki * (Ce / B)) * (2 : ℝ) ^ A.τe ≤ Ce := by
    have hh : C ki * (Ce / B) ≤ CT * (Ce / B) :=
      mul_le_mul_of_nonneg_right (hCle ki) hCe0.le
    calc _ ≤ (CT * (Ce / B)) * (2 : ℝ) ^ A.τe :=
          mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (by norm_num) _)
      _ = Ce := by dsimp [B]; field_simp
  have hbudget : C ki * (Ce / B * D.eps (M - 1) ^ A.τe) ≤
      Ce * D.eps (M - 1 - 1) ^ (D.q * A.τe) := by
    rw [← mul_assoc]
    exact hdec.trans (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (he _).le _))
  exact ⟨fun v => (hp.1 v).trans hbudget, fun u => (hp.2 u).trans hbudget⟩

end AVRegularity.EntryTerminal.Route
