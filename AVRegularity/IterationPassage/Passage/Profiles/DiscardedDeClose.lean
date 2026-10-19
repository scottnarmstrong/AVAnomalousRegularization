-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.IterationPassage.Passage.Profiles.RetainedCovFresh
import AVRegularity.IterationPassage.Passage.Profiles.RetainedCov
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.FullLift.NativeLiftedFieldCovarianceEnergy
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Finite.WeakPositive.PositiveInputJets
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import Mathlib.Algebra.Order.Star.Real

section
section
/-! **The discarded profiles: assembly**.

`passageDiscardedProfiles_of`: `PassageDiscardedProfilesStatement` from the four named steps
`DiscMomentStatement`, `DiscDEStatement`, `DiscScalesStatement` and `DiscDeStep`. For the data of a
passage: the marked bound gives the unmarked one (`ordinary_input_from_marked`); the defect
`Y - S_r Y` (`S_r` the fresh kernel, width `r = ρ E^{σ₀}`) has realizations at orders `K+2+2p` and
`K+N+2+2p` of norm `≤ C E^{σ₀L} B` (`DiscMomentStatement`); `D_E` by `DiscDEStatement` with
`μ = fbCovConst = O(E^δ)`, the scale sum `O(E^{-Z_K})`; `D_e` by `DiscDeStep`; exponents by
`DiscScalesStatement`. Level threshold `m_* = max(m₀, m_S, m₁)`.

Special cases: `p = 0`, `B = 0`, `Cn < 0` (the readout hypothesis is false). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation AVRegularity.Finite
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- The profile `D_E`, in the form of the definition. -/
theorem disc_profile_two {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (law : BirthLaw)
    (G Gr : GenStage D ScalarH Dm b j₀) (m p N depth : ℕ) (η₀ : ℝ) (φ₀ : Vec 2 → ℝ)
    (Sr : KernelSpec)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ) :
    ((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map fun q => q.1 t).getD 2 0 =
      compField (G.mass law) (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀
        (fieldCov D m p (aY - fieldKernel φ₀ Sr aY) - (aY - fieldKernel φ₀ Sr aY)) t) := rfl

/-- The covariance correction at a time, pointwise. -/
theorem disc_field_sub {S : Finset Comp} (D : OCData) (m p : ℕ) (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (aY : ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) (t : ℝ) :
    (fieldCov D m p (aY - fieldKernel φ₀ Sr aY) - (aY - fieldKernel φ₀ Sr aY)) t =
      fun x => covPolyP (covPrimitive D m t) p (fun y => aY t y - fieldKernel φ₀ Sr aY t y) x -
          (aY t x - fieldKernel φ₀ Sr aY t x) := by
  funext x
  rfl

/-- `fieldReadout` at a time depends on the field at that time only. -/
theorem disc_readout_congr {S S' : Finset Comp} (m : ℕ) (E η₀ : ℝ)
    (a a' : ℝ → Vec 2 → ∀ v : CompIn S', ScalarH v.1.root) (t : ℝ) (h : a t = a' t) :
    fieldReadout (S := S) m E η₀ a t = fieldReadout (S := S) m E η₀ a' t := by
  unfold fieldReadout
  funext x v
  simp only [h]

theorem disc_nat_facts {m₀ mS m₁ m n M : ℕ} (hm₀ : 2 ≤ m₀) (hm : max (max m₀ mS) m₁ ≤ m)
    (hn : m ≤ n) (hnM : n < M) :
    2 ≤ m ∧ m₀ ≤ m ∧ mS ≤ m ∧ m₁ ≤ m ∧ 1 ≤ m - 1 ∧ m - 1 < M ∧ m ≤ M := by
  simp only [max_le_iff] at hm
  omega

theorem disc_lam_facts {Λ Λa Λs Λc Λd : ℕ} (h : max (max Λa Λs) (max Λc Λd) ≤ Λ)
    (ha : 128 ≤ Λa) : Λa ≤ Λ ∧ Λs ≤ Λ ∧ Λc ≤ Λ ∧ Λd ≤ Λ ∧ 128 ≤ Λ ∧ 1 ≤ Λ := by
  simp only [max_le_iff] at h
  omega

theorem disc_ord_facts {K N p L Naux : ℕ} (h : 2 * (K + 2) + N + 2 * p + L ≤ Naux) :
    K + 2 + 2 * p + L + 2 ≤ Naux ∧ K + N + 2 + 2 * p + L + 2 ≤ Naux ∧ 0 < K + 2 + 2 * p := by
  omega

theorem disc_sched_facts {α q s Q σ₀ a σ σf lamC : ℝ} {D₀ H J N p nk Lc Lf Lpr Acl Naux Nout : ℕ}
    (hsched : IsSuccessorSchedule α q s Q σ₀ a σ σf lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout) :
    0 < σ₀ ∧ 2 * σ₀ ≤ ocDelta α q := by
  obtain ⟨_, _, _, _, _, hσa, ha, haσ, _, hDs, _, _, _, _, _, _, _, hN2, hp1, hnk1⟩ := hsched
  have hDst : 1 ≤ succDstar D₀ N p H := by
    unfold succDstar
    have : succSchedD D₀ N p (H + 1) = succSchedD D₀ N p H + 2 * N + 4 * p + 4 := rfl
    omega
  have hσ₀pos : 0 < σ₀ := by linarith
  refine ⟨hσ₀pos, ?_⟩
  have h1 : σ₀ * 1 ≤ σ₀ * (succDstar D₀ N p H : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hDst) hσ₀pos.le
  linarith


/-- **The discarded profiles** from the four named steps. -/
theorem passageDiscardedProfiles_of (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hM : DiscMomentStatement) (hE : DiscDEStatement) (hS : DiscScalesStatement α q ζ)
    (hDe : DiscDeStep α s q ζ) : PassageDiscardedProfilesStatement α s q ζ := by
  classical
  obtain ⟨Λa, hΛa, hadm⟩ := retCov_fresh_admissible α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  obtain ⟨C, hC, Λs, hΛs, hsc⟩ := retCov_cov_scales α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  obtain ⟨Λc, hΛc, hscale⟩ := hS
  obtain ⟨Λd, hΛd, hdd⟩ := hDe
  refine discPrefix_main ⟨max (max Λa Λs) (max Λc Λd), le_trans hΛa ((le_max_left _ _).trans (le_max_left _ _)), fun Λ hΛ => ?_⟩
  obtain ⟨hΛa', hΛs', hΛc', hΛd', hΛ128, hΛ1⟩ := disc_lam_facts hΛ hΛa
  obtain ⟨c₀max, hc₀, hdeP⟩ := hdd Λ hΛd'
  refine ⟨c₀max, hc₀, fun P => ?_⟩
  obtain ⟨Cd, mS, hCd0, hDeD⟩ := hdeP P
  rcases P with ⟨φ₀, hφ₀, hφs, hφpos, hφint, hφsupp, bw, hbw, hbw', K, Pacc, hK, hPacc, Q, T₀, hQ,
    hT₀, hQb, r₀, D₀, τe, lamE, σE, hτe, hlamE, hσE, H, J, N, p, nk, Lc, Lf, Lpr, Acl, Naux, Nout,
    Kres, npad, σ₀, a, σ, hsched, hNaux, hNout, L, hL, hwid, sX, sZ, Ce, kS, hCe, hc₀', hc₀max, hcr,
    hcr1, hσf, hlamC, halloc, kI, hkI, CI, Cw, j₀, hledger, hstart, Cn⟩
  obtain ⟨hcC, hepsth, hscale'⟩ := hscale Λ hΛc'
  obtain ⟨Γ, hΓ, m₀, hm₀, hadm'⟩ := hadm Λ hΛa'
  obtain ⟨hσ₀pos, hσδ⟩ := disc_sched_facts hsched
  have hδ : 0 < ocDelta α q := ocDelta_pos_of_admissible hα₀ hq
  have hcrk : kI.cr = kS.cr := (Buffer.invariantAdmissible_molecular_parameters hkI).2.1
  have hcr0 : 0 < kI.cr := hcrk ▸ hcr
  have hcr1' : kI.cr ≤ 1 := hcrk ▸ hcr1
  obtain ⟨hk1, hk2, hRK⟩ := disc_ord_facts hL.1
  have hnk0 : 0 < nk := by have := hL.2.2; omega
  have hnkc : ((nk.toPNat' : ℕ+) : ℕ) = nk := by simp [Nat.toPNat'_coe, hnk0]
  have hη := FullLift.successor_eta0_pos hα₀ hα₁ hs₀ hs₁ hq
  obtain ⟨Cs, hCs, hscD⟩ := hscale' kI.cr hcr0 hcr1'
  obtain ⟨Cm1, hCm1, hmom1⟩ := hM φ₀ hφ₀ hφs hφpos hφint hφsupp (K + 2 + 2 * p) L nk.toPNat' Γ
  obtain ⟨Cm2, hCm2, hmom2⟩ := hM φ₀ hφ₀ hφs hφpos hφint hφsupp (K + N + 2 + 2 * p) L nk.toPNat' Γ
  obtain ⟨CE, hCE, hDEs⟩ := hE K p (max Cn 0)
  set R : ℝ := ((K + 2 + 2 * p : ℕ) : ℝ) with hR
  have hRpos : 0 < R := by rw [hR]; exact_mod_cast hRK
  set Cμ : ℝ := 4 * (C / kI.cr ^ 2) * R ^ 2 with hCμ
  have hCμpos : 0 < Cμ := by
    have : 0 < C := by linarith
    positivity
  have hCs0' : 0 < Cs := by linarith
  obtain ⟨m₁, hm₁⟩ := hepsth (min ((1 / Cμ) ^ (1 / ocDelta α q)) Cs⁻¹) (lt_min (by positivity) (by positivity))
  set CS : ℝ := ((K : ℝ) + 1) * Cs ^ ((K : ℝ) + 1) with hCS
  have hCS0 : 0 ≤ CS := by have : 0 < Cs := by linarith
                           positivity
  refine ⟨CE * Cμ * CS * Cm1 + Cd * Cs ^ (s + 1) * Cm2, max (max m₀ mS) m₁, ?_⟩
  intro Cf hCf D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n
    tS tf hseed hmol m hm hn hnM tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual hRn CcT
    hCcT aU aY t hts htf haY haYp Yn B hYn hB
  obtain ⟨hm2, hmm₀, hmmS, hmm₁, hm1a, hm1b, hmM⟩ := disc_nat_facts hm₀ hm hn hnM
  have hΛD128 : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ128
  have hΛD1 : 1 ≤ D.Λ := by rw [hDΛ]; exact hΛ1
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hspec := hfresh (m - 1) hm1a hm1b
  obtain ⟨hSadm, hSw⟩ := hadm' D hDα hDq hDΛ hDζ hseq hbandD kI.cr σ₀ hcr0 nk.toPNat' L
    (by rw [hnkc]; exact hL.2.2) m hmm₀ (by rw [hterm]; exact hmM) (freshK (m - 1)) hspec
  obtain ⟨hρeq, hρ1', hρc, hρq, heq⟩ := hscD D hDα hDq hDΛ hDζ M hband hterm m hm2 hmM
  obtain ⟨_, _, hcovb⟩ := hsc Λ hΛs' D hDα hDq hDΛ hDζ M hband hterm kI.cr σ₀ hcr0 hcr1'
    hσ₀pos.le hσδ m hm2 hmM
  have hCs0 : 0 < Cs := by linarith
  have hEpos : 0 < D.eps (m - 1) := Construction.Stream.ocEpsilon_pos hΛD1
  have hE1 : D.eps (m - 1) ≤ 1 := ocEpsilon_le_one hΛD1 _
  have hρ0 : 0 < rhoEnh D kI.cr m := discScale_pos hCs0 hEpos hρc
  have hrw : (freshK (m - 1)).width = rhoEnh D kI.cr m * D.eps (m - 1) ^ σ₀ := by
    rw [hspec.1, hρeq]; rfl
  have hEσ : D.eps (m - 1) ^ σ₀ ≤ 1 := Real.rpow_le_one hEpos.le hE1 hσ₀pos.le
  have hrρ : (freshK (m - 1)).width ≤ rhoEnh D kI.cr m := by
    rw [hrw]; exact mul_le_of_le_one_right hρ0.le hEσ
  have hπ' : ∀ v, 0 < (G'.retained m H J).mass law v := fun v =>
    Buffer.birth_compMass_pos hqD hΛD128 law v.1
  have hπ : ∀ v, 0 < G.mass law v := fun v => Buffer.birth_compMass_pos hqD hΛD128 law v.1
  have hiota : 0 ≤ law.iota := by rw [hlaw.2.2.1]; exact div_nonneg hη.le (by norm_num)
  have hY0 : weightedNorm (rhoEnh D kI.cr m) ((G'.retained m H J).mass law) (fun _ => 1) Yn ≤ B :=
    FullLift.ordinary_input_from_marked (G'.retained m H J) hqD hΛD128 law hiota _ Yn hB
  have hB0 : 0 ≤ B := le_trans (by unfold weightedNorm; exact Real.sqrt_nonneg _) hY0
  have hcont : Continuous (aY t) := haY.continuous
  obtain ⟨W1, hW1rep, hW1n⟩ := hmom1 _ hπ' (freshK (m - 1)) t _ hspec.2.1 hSadm hSw hrρ Naux hk1 Yn
    (aY t) hcont haYp hYn
  obtain ⟨W2, hW2rep, hW2n⟩ := hmom2 _ hπ' (freshK (m - 1)) t _ hspec.2.1 hSadm hSw hrρ Naux hk2 Yn
    (aY t) hcont haYp hYn
  rw [discScale_ratio L hρ0 hEpos hrw] at hW1n hW2n
  have hEL : 0 ≤ D.eps (m - 1) ^ (σ₀ * L) := (Real.rpow_pos_of_pos hEpos _).le
  have hw1 : weightedNorm (rhoEnh D kI.cr m) ((G'.retained m H J).mass law) (fun _ => 1) W1 ≤
      Cm1 * D.eps (m - 1) ^ (σ₀ * L) * B :=
    hW1n.trans (mul_le_mul_of_nonneg_left hY0 (mul_nonneg hCm1 hEL))
  have hw2 : weightedNorm (rhoEnh D kI.cr m) ((G'.retained m H J).mass law) (fun _ => 1) W2 ≤
      Cm2 * D.eps (m - 1) ^ (σ₀ * L) * B :=
    hW2n.trans (mul_le_mul_of_nonneg_left hY0 (mul_nonneg hCm2 hEL))
  have hcb := discScale_covBound_le (covPrimitive D m t) (x := (C / kI.cr ^ 2 * D.eps (m - 1) ^
      (ocDelta α q - 2 * σ₀)) * (freshK (m - 1)).width ^ 2)
    (by rw [hspec.1]; exact hcovb t)
  have hμle := discScale_mu (R := R) (δ := ocDelta α q) (σ₀ := σ₀) (C' := C / kI.cr ^ 2)
    (r := (freshK (m - 1)).width) (ε := C / kI.cr ^ 2 * D.eps (m - 1) ^ (ocDelta α q - 2 * σ₀))
    hρ0 hEpos hrw rfl hcb
  have hEm := hm₁ D hDα hDq hDΛ hDζ m hmm₁
  have hρ1 := hρ1' (hEm.trans (min_le_right _ _))
  have hμ1 := discScale_mu_one hCμpos hμle
    (discScale_pow_thresh hδ (by positivity) hEpos (hEm.trans (min_le_left _ _)))
  have hRn' : ‖readoutCLM m (D.eps (m - 1)) (succEta0 α q s) (G.mass law)
      ((G'.retained m H J).mass law)‖ ≤ max Cn 0 := hRn.trans (le_max_left _ _)
  have hprof2 := hDEs D m (G.mass law) ((G'.retained m H J).mass law) hπ hπ' (D.eps (m - 1))
    (succEta0 α q s) s (rhoEnh D kI.cr m) _ t hρ0 hρ1 hEpos hRn'
    (fun i j => FullLift.native_covPrimitive_entry_symm D hΛD1 (hDζ ▸ hζ) m t i j) le_rfl hμ1 W1
    (fun x => aY t x - fieldKernel φ₀ (freshK (m - 1)) aY t x) hW1rep
  have hprof3 := hDeD D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh
    seed n tS tf hseed hmol m hmmS hn hnM tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG
    hactual hRn CcT hCcT aU aY t hts htf haY haYp W2 hW2rep
  have hSb : ∑ j ∈ Finset.range (K + 1), D.eps (m - 1) ^ ((j : ℝ) - s) *
      rhoEnh D kI.cr m ^ (-(j : ℝ) - 1) ≤ CS * D.eps (m - 1) ^ (-iterZ α q s K) := by
    unfold iterZ; exact discScale_sum K hEpos hE1 hCs hcC hρc
  have hS0 : 0 ≤ ∑ j ∈ Finset.range (K + 1), D.eps (m - 1) ^ ((j : ℝ) - s) *
      rhoEnh D kI.cr m ^ (-(j : ℝ) - 1) :=
    Finset.sum_nonneg fun j _ => by positivity
  have hwn : ∀ {k : ℕ} (X : ∀ v : CompIn (G'.retained m H J).comps, TorusHk k (ScalarH v.1.root)),
      0 ≤ weightedNorm (rhoEnh D kI.cr m) ((G'.retained m H J).mass law) (fun _ => 1) X :=
    fun X => by unfold weightedNorm; exact Real.sqrt_nonneg _
  have hLmax := hL.2.1
  have hZ := le_max_left (iterZ α q s K) (q * (1 + s))
  have hQ2 := le_max_right (iterZ α q s K) (q * (1 + s))
  rw [disc_profile_two, disc_readout_congr m (D.eps (m - 1)) (succEta0 α q s) _
    (fun _ x => covPolyP (covPrimitive D m t) p (fun y => aY t y - fieldKernel φ₀ (freshK (m - 1)) aY t y) x -
      (aY t x - fieldKernel φ₀ (freshK (m - 1)) aY t x)) t (disc_field_sub D m p φ₀ (freshK (m - 1)) aY t)]
  exact discScale_combine hEpos hE1 hs₀ hCs hCE (CycleComparison.Coarse.fbCovConst_nonneg hρ0 _ _)
    hμle hCS0 hCm1 hCm2 hCd0 hB0 hS0 hSb (hwn W1) (hwn W2) hw1 hw2 heq hρq (by linarith)
    (by linarith) hCf hprof2 hprof3

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The input of the discarded lift at the lift radius** (step `DiscDeStep`).

The positive bound of the lift (`passageLift_positive_partial_bound`) sees its input
`P_p𝖱(Y - S_rY)` through the positive jets at the lift radius `ρ_L = ρ/c_r`. Here they are bounded
by the weighted Sobolev norm at the radius `ρ` of a realization of the defect `Y - S_rY`:

`∑_{1≤|γ|≤K+N} ρ_L^{|γ|} |∂^γ P_p(R ∘ G)(x)| ≤ C ρ^{-1} W`,

when `[G]_{ρ,K';0} ≤ C_s ρ^{-1} W` (`K' ≥ K + N + 2p`) and `|𝖧_{ij}| ≤ C_b ρ²`.

* `discDe_term_alg`: `ρ_L^j (4C_bρ²)^n ρ^{-(j+2n)} ≤ c_r^{-(K+N)} (4C_b)^p`.
* `discDe_jet_le`: the jet of order `1 ≤ i ≤ K'` from the profile seminorm at the scale `ρ` with the
  exponent `0` (`retCov_jet_le`, `retCov_block_le`).
* `discDe_seminorm_le`: that seminorm from the scaled Sobolev norm (`sobolevProfile`).
* `discDe_input_bound`: the input bound (word bound `liftInput_word_le` of the full `P_p(R ∘ G)`).

Special cases: `p = 0` (`P_0 = I`); `N = 0`; `W = 0` (the field vanishes); `c_r = 1`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Finite.TerminalLift AVRegularity.Finite.WeakLift
  AVRegularity.Construction.Preservation.FullLift
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- The radius powers of one term of the input bound. -/
theorem discDe_term_alg {ρ ρL cr Cb : ℝ} {j n K N p : ℕ} (hρ : 0 < ρ) (hcr : 0 < cr)
    (hcr1 : cr ≤ 1) (hρL : ρ = cr * ρL) (hCb : 1 ≤ Cb) (hj : j ≤ K + N) (hn : n ≤ p) :
    ρL ^ j * (4 * (Cb * ρ ^ 2)) ^ n * (ρ ^ (j + 2 * n))⁻¹ ≤ cr⁻¹ ^ (K + N) * (4 * Cb) ^ p := by
  have hρLe : ρL = ρ * cr⁻¹ := by
    rw [hρL]
    field_simp
  have hcr' : 1 ≤ cr⁻¹ := (one_le_inv₀ hcr).mpr hcr1
  have h4 : 1 ≤ 4 * Cb := by linarith
  have hρj : 0 < ρ ^ (j + 2 * n) := pow_pos hρ _
  have heq : ρL ^ j * (4 * (Cb * ρ ^ 2)) ^ n * (ρ ^ (j + 2 * n))⁻¹ = cr⁻¹ ^ j * (4 * Cb) ^ n := by
    rw [hρLe, mul_pow, show (4 * (Cb * ρ ^ 2)) = (4 * Cb) * ρ ^ 2 by ring, mul_pow, ← pow_mul]
    have hsplit : ρ ^ (j + 2 * n) = ρ ^ j * ρ ^ (2 * n) := pow_add ρ j (2 * n)
    rw [hsplit]
    field_simp
  rw [heq]
  exact mul_le_mul (pow_le_pow_right₀ hcr' hj) (pow_le_pow_right₀ h4 hn) (by positivity)
    (by positivity)

/-- The constant of the input bound of the discarded lift. -/
def discDeInputConst (cr Cb Cn Cs : ℝ) (K N p K' : ℕ) : ℝ :=
  ((multiIndicesBetween 1 (K + N)).card : ℝ) * ((p + 1 : ℕ) : ℝ) *
    (cr⁻¹ ^ (K + N) * (4 * Cb) ^ p * Cn * 2 ^ K' * (K'.factorial : ℝ) * Cs)

section Abstract

variable {V₀ W₀ : Type*} [NormedAddCommGroup V₀] [NormedSpace ℝ V₀]
  [NormedAddCommGroup W₀] [NormedSpace ℝ W₀]

/-- The jet of order `1 ≤ i ≤ K'` from the profile seminorm at the scale `ρ`, exponent `0`. -/
theorem discDe_jet_le {ρ : ℝ} (hρ : 0 < ρ) {K' i : ℕ} (hi1 : 1 ≤ i) (hiK : i ≤ K')
    {G : Vec 2 → V₀} (hG : ContDiff ℝ ((i : ℕ) : ℕ∞) G) (x : Vec 2) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ i G x‖ ≤
      ENNReal.ofReal ((2 : ℝ) ^ i * (K'.factorial : ℝ) * (ρ ^ i)⁻¹) * profileSeminorm ρ K' 0 G := by
  have hjet := retCov_jet_le hG x
  have hblock := retCov_block_le (s := 0) hρ hi1 hiK G
  rw [sub_zero, Real.rpow_natCast] at hblock
  have hρi : 0 < ρ ^ i := pow_pos hρ i
  set SW := ∑ α ∈ multiIndicesBetween i i, supNorm (partialDerivative α G) with hSW
  have hone : ENNReal.ofReal ((ρ ^ i)⁻¹) * ENNReal.ofReal (ρ ^ i) = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hρi.le), inv_mul_cancel₀ hρi.ne',
      ENNReal.ofReal_one]
  calc ENNReal.ofReal ‖iteratedFDeriv ℝ i G x‖ ≤ ENNReal.ofReal ((2 : ℝ) ^ i) * SW := hjet
    _ = ENNReal.ofReal ((2 : ℝ) ^ i) * (ENNReal.ofReal ((ρ ^ i)⁻¹) *
          (ENNReal.ofReal (ρ ^ i) * SW)) := by
        rw [← mul_assoc (ENNReal.ofReal ((ρ ^ i)⁻¹)), hone, one_mul]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ i) * (ENNReal.ofReal ((ρ ^ i)⁻¹) *
          (ENNReal.ofReal (K'.factorial : ℝ) * profileSeminorm ρ K' 0 G)) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

/-- **The input bound of the discarded lift**, abstract form. -/
theorem discDe_input_bound {ρ ρL cr Cb Cn Cs Wn : ℝ} {K N p K' : ℕ}
    (hρ : 0 < ρ) (hcr : 0 < cr) (hcr1 : cr ≤ 1) (hρL : ρ = cr * ρL) (hCb : 1 ≤ Cb)
    (hCn : 0 ≤ Cn) (hCs : 0 ≤ Cs) (hWn : 0 ≤ Wn) (hK' : K + N + 2 * p ≤ K')
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, |A i j| ≤ Cb * ρ ^ 2)
    (R : V₀ →L[ℝ] W₀) (hR : ‖R‖ ≤ Cn) (G : Vec 2 → V₀)
    (hG : ContDiff ℝ ((K' : ℕ) : ℕ∞) G)
    (hsemi : profileSeminorm ρ K' 0 G ≤ ENNReal.ofReal (Cs * ρ⁻¹ * Wn)) (x : Vec 2) :
    ∑ γ ∈ multiIndicesBetween 1 (K + N), ρL ^ (γ 0 + γ 1) *
        ‖partialDerivative γ (covPolyP A p (fun y => R (G y))) x‖ ≤
      discDeInputConst cr Cb Cn Cs K N p K' * (ρ⁻¹ * Wn) := by
  have hρL0 : 0 < ρL := by
    have h1 : ρL = ρ / cr := by
      rw [hρL]
      field_simp
    rw [h1]
    positivity
  have hCb0 : 0 ≤ Cb := zero_le_one.trans hCb
  have hB : 0 ≤ Cb * ρ ^ 2 := by positivity
  have hρi : 0 ≤ ρ⁻¹ := inv_nonneg.mpr hρ.le
  have hbound0 : 0 ≤ Cs * ρ⁻¹ * Wn := by positivity
  -- the jets of `G`, in real form
  have hjet : ∀ i, 1 ≤ i → i ≤ K' →
      ‖iteratedFDeriv ℝ i G x‖ ≤ (2 : ℝ) ^ i * (K'.factorial : ℝ) * (ρ ^ i)⁻¹ * (Cs * ρ⁻¹ * Wn) := by
    intro i hi1 hiK
    have h1 := discDe_jet_le hρ hi1 hiK (hG.of_le (by exact_mod_cast hiK)) x
    have h2 := h1.trans (mul_le_mul' le_rfl hsemi)
    rw [← ENNReal.ofReal_mul (by positivity)] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
  -- one multi-index
  have hterm : ∀ γ ∈ multiIndicesBetween 1 (K + N), ρL ^ (γ 0 + γ 1) *
      ‖partialDerivative γ (covPolyP A p (fun y => R (G y))) x‖ ≤
      ((p + 1 : ℕ) : ℝ) * (cr⁻¹ ^ (K + N) * (4 * Cb) ^ p * Cn * 2 ^ K' * (K'.factorial : ℝ) *
        Cs) * (ρ⁻¹ * Wn) := by
    intro γ hγ
    have hj := (Finset.mem_filter.mp hγ).2
    have heq : ![γ 0, γ 1] = γ := by ext i; fin_cases i <;> rfl
    have hgj : ContDiff ℝ ((γ 0 + γ 1 + 2 * p : ℕ) : ℕ∞) G :=
      hG.of_le (by exact_mod_cast (by omega : γ 0 + γ 1 + 2 * p ≤ K'))
    have hw := liftInput_word_le A (Cb * ρ ^ 2) Cn hB hA R hR p (γ 0 + γ 1) hgj
      (Fin.append (fun _ : Fin (γ 0) => (0 : Fin 2)) (fun _ : Fin (γ 1) => (1 : Fin 2))) x
    rw [weakPositive_sorted_word_eq_partial, heq] at hw
    have hn : ∀ n ∈ Finset.range (p + 1), ρL ^ (γ 0 + γ 1) * ((4 * (Cb * ρ ^ 2)) ^ n *
        (Cn * ‖iteratedFDeriv ℝ (γ 0 + γ 1 + 2 * n) G x‖)) ≤
        cr⁻¹ ^ (K + N) * (4 * Cb) ^ p * Cn * 2 ^ K' * (K'.factorial : ℝ) * Cs * (ρ⁻¹ * Wn) := by
      intro n hn
      have hnp : n ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hi := hjet (γ 0 + γ 1 + 2 * n) (by omega) (by omega)
      have halg := discDe_term_alg (K := K) (N := N) hρ hcr hcr1 hρL hCb hj.2 hnp
      have h2 : (2 : ℝ) ^ (γ 0 + γ 1 + 2 * n) ≤ 2 ^ K' :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hpos1 : 0 ≤ ρL ^ (γ 0 + γ 1) * (4 * (Cb * ρ ^ 2)) ^ n * Cn := by positivity
      calc ρL ^ (γ 0 + γ 1) * ((4 * (Cb * ρ ^ 2)) ^ n *
            (Cn * ‖iteratedFDeriv ℝ (γ 0 + γ 1 + 2 * n) G x‖))
          = ρL ^ (γ 0 + γ 1) * (4 * (Cb * ρ ^ 2)) ^ n * Cn *
            ‖iteratedFDeriv ℝ (γ 0 + γ 1 + 2 * n) G x‖ := by ring
        _ ≤ ρL ^ (γ 0 + γ 1) * (4 * (Cb * ρ ^ 2)) ^ n * Cn *
            ((2 : ℝ) ^ (γ 0 + γ 1 + 2 * n) * (K'.factorial : ℝ) *
              (ρ ^ (γ 0 + γ 1 + 2 * n))⁻¹ * (Cs * ρ⁻¹ * Wn)) :=
          mul_le_mul_of_nonneg_left hi hpos1
        _ = (ρL ^ (γ 0 + γ 1) * (4 * (Cb * ρ ^ 2)) ^ n * (ρ ^ (γ 0 + γ 1 + 2 * n))⁻¹) *
            (2 : ℝ) ^ (γ 0 + γ 1 + 2 * n) * (Cn * (K'.factorial : ℝ) * Cs * (ρ⁻¹ * Wn)) := by
          ring
        _ ≤ (cr⁻¹ ^ (K + N) * (4 * Cb) ^ p) * 2 ^ K' *
            (Cn * (K'.factorial : ℝ) * Cs * (ρ⁻¹ * Wn)) := by
          gcongr
        _ = _ := by ring
    calc ρL ^ (γ 0 + γ 1) * ‖partialDerivative γ (covPolyP A p (fun y => R (G y))) x‖
        ≤ ρL ^ (γ 0 + γ 1) * ∑ n ∈ Finset.range (p + 1), (4 * (Cb * ρ ^ 2)) ^ n *
            (Cn * ‖iteratedFDeriv ℝ (γ 0 + γ 1 + 2 * n) G x‖) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ = ∑ n ∈ Finset.range (p + 1), ρL ^ (γ 0 + γ 1) * ((4 * (Cb * ρ ^ 2)) ^ n *
            (Cn * ‖iteratedFDeriv ℝ (γ 0 + γ 1 + 2 * n) G x‖)) := Finset.mul_sum _ _ _
      _ ≤ ∑ _n ∈ Finset.range (p + 1), cr⁻¹ ^ (K + N) * (4 * Cb) ^ p * Cn * 2 ^ K' *
            (K'.factorial : ℝ) * Cs * (ρ⁻¹ * Wn) := Finset.sum_le_sum hn
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  calc ∑ γ ∈ multiIndicesBetween 1 (K + N), ρL ^ (γ 0 + γ 1) *
        ‖partialDerivative γ (covPolyP A p (fun y => R (G y))) x‖
      ≤ ∑ _γ ∈ multiIndicesBetween 1 (K + N), ((p + 1 : ℕ) : ℝ) * (cr⁻¹ ^ (K + N) *
          (4 * Cb) ^ p * Cn * 2 ^ K' * (K'.factorial : ℝ) * Cs) * (ρ⁻¹ * Wn) :=
        Finset.sum_le_sum hterm
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        unfold discDeInputConst
        ring

end Abstract

/-- The profile seminorm at the scale `ρ`, exponent `0`, of a normalized field with a weighted
Sobolev realization of order `K' + 2`. -/
theorem discDe_seminorm_le (K' : ℕ) : ∃ Cs : ℝ, 0 ≤ Cs ∧
    ∀ {S : Finset Comp} (π : CompIn S → ℝ), (∀ v, 0 < π v) → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
    ∀ (M : ℕ), K' + 2 = M → ∀ (w : ∀ v : CompIn S, TorusHk M (ScalarH v.1.root))
      (g : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root),
      (∀ v, IsClassicalRep (w v) (fun x => g x v) M) →
      profileSeminorm ρ K' 0 (compField π g) ≤
        ENNReal.ofReal (Cs * ρ⁻¹ * weightedNorm ρ π (fun _ => 1) w) := by
  obtain ⟨CK, hCK, hsob⟩ := sobolevProfile K'
  refine ⟨CK * ((K' + 1 : ℕ) : ℝ), by positivity, ?_⟩
  intro S π hπ ρ hρ hρ1 M hM w g hw
  have hKM : K' ≤ M := by omega
  have hgc : ContDiff ℝ ((K' : ℕ) : ℕ∞) g := contDiff_pi.mpr fun v =>
    (hw v).2.1.of_le (by exact_mod_cast hKM)
  subst hM
  have hgp : IsZ2Periodic g := fun n x => funext fun v => (hw v).2.2.1 n x
  have hval : ∀ v, (w v).toFunction.jet (valueIndex2 (K' + 2)) =ᵐ[volume.restrict
      AVenhance.unitCube] fun x => g x v := by
    intro v
    have h0 := (hw v).2.2.2 0 (Nat.zero_le _) Fin.elim0
    have h1 : torusJetOrder (w v) 0 Fin.elim0 = (w v).toFunction.jet (valueIndex2 (K' + 2)) := by
      funext y
      simp [torusJetOrder, valueIndex2, valueIndex]
    rw [h1] at h0
    exact h0
  have hmain := hsob π hπ ρ ρ 0 hρ hρ1 hρ w g (regularCompField_contDiff π hgc)
    (regularCompField_periodic π hgp) hval
  have hT : (∑ j ∈ Finset.range (K' + 1), ρ ^ ((j : ℝ) - 0) * ρ ^ (-(j : ℝ) - 1)) =
      ((K' + 1 : ℕ) : ℝ) * ρ⁻¹ := by
    have hterm : ∀ j ∈ Finset.range (K' + 1), ρ ^ ((j : ℝ) - 0) * ρ ^ (-(j : ℝ) - 1) = ρ⁻¹ := by
      intro j _
      rw [← Real.rpow_add hρ, show ((j : ℝ) - 0) + (-(j : ℝ) - 1) = -1 by ring,
        Real.rpow_neg_one]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hT] at hmain
  refine le_trans ?_ (hmain.trans_eq (by congr 1; ring))
  unfold profileNorm
  exact le_add_self

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The retained lift profile** `𝓘_{e,K;s}(H_e) ≤ C E^{μ_s} [Y]_{E,K;s}`,
`H_e = (T - I)P_p𝖱S_rY`.

`passageRetainedLift`: the prefix of `iteration_passage` through the carrier start, then, after
the readout bound `C_n`, the constant `C₀` and the level threshold `m_*`. The proof at a time `t`:

* the slot lifts of the incoming stage (`uniform_native_weighted_slot_lifts`, weight
  `1`, masses of the stage; the stage geometry as in `passageProfilesRegular`) and the chart jets
  at the lift radius (`uniform_native_physical_flow_jets`);
* `retainedLift_at_stage`: the positive bound of the lift
  (`passageLift_positive_partial_bound`), the packing and the scale `passageLift_scale`;
* `passageLiftInput_bound`: the input `P_p𝖱S_rY` at the lift radius, with the exponent
  conditions `2σ₀ ≤ δ`, `σ₀N ≤ c(K-1)` from the schedule (`liftSchedule_exponents`).

Constants: `C₀ = #jets · C_P · C_in · C_sc` with `C_P` the price of the positive words times the
path cost at the Schur budget `C_I` (the stage budget `C_I e^{min(δ/4,τ_e)}` is at most `C_I`);
`m_* = max{m₀, j₀, m_in, M_f + 1}`. The thresholds `c₀max = 1`, `SX = SZ = Kneed = 0`,
`thr = kS`, `CH = Υ = 1`, `CIthr = Cwthr = 0` are trivial.

Special cases: `aY t` constant (the profile vanishes, `[Y] = 0`); `p = 0`; an empty family. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.FullLift AVRegularity.Construction.Preservation
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- The second profile of the passage at a time is the retained lift profile. -/
theorem passageProfiles_getD_one {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (law : BirthLaw)
    (G Gr : GenStage D ScalarH Dm b j₀) (m p N depth : ℕ) (η₀ : ℝ) (φ₀ : Vec 2 → ℝ)
    (Sr : KernelSpec)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ) :
    ((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map fun q => q.1 t).getD 1 0 =
      compField (G.mass law) (fun y => passageLift D m N depth CcT
        (fieldCov D m p (fieldReadout m (D.eps (m - 1)) η₀ (fieldKernel φ₀ Sr aY))) t y -
        fieldCov D m p (fieldReadout m (D.eps (m - 1)) η₀ (fieldKernel φ₀ Sr aY)) t y) :=
  rfl

/-- **The retained lift profile** `H_e`. -/
theorem passageRetainedLift (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : PassageRetainedLiftStatement α s q ζ := by
  classical
  obtain ⟨Λa, hΛa, hlift⟩ := uniform_native_weighted_slot_lifts hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λl, _hΛl, hlength⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λi, _hΛi, hinput⟩ := passageLiftInput_bound α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  obtain ⟨Csc, _hCsc, Λs, _hΛs, hscale⟩ := passageLift_scale α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  refine ⟨max (max Λa Λl) (max Λi Λs),
    hΛa.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro Λ hΛ
  have hΛa' : Λa ≤ Λ := (le_max_left _ _).trans ((le_max_left _ _).trans hΛ)
  have hΛl' : Λl ≤ Λ := (le_max_right _ _).trans ((le_max_left _ _).trans hΛ)
  have hΛi' : Λi ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans hΛ)
  have hΛs' : Λs ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans hΛ)
  have hΛ128 : 128 ≤ Λ := hΛa.trans hΛa'
  refine ⟨1, one_pos, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK hPacc Q T₀ hQ hT₀ hQb
    r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched
    hNaux hNout L hL hwid
  refine ⟨0, 0, 0, ?_⟩
  intro sX sZ _ _ Ce kS hCe hc₀ hc₀upper hcr hcrupper hσf hlamC halloc _ _ _ _
  refine ⟨kS, 1, 1, le_rfl, one_pos, ?_⟩
  intro kI hkI
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ hledger hstart Cn
  obtain ⟨_, _, _, _, _, hσeq, ha0, haσ, _, hσD, _, _, _, _, _, _, _, hN2, _, _⟩ := hsched
  have hDm : 2 ≤ succSchedD D₀ N p (H + 1) := Buffer.preparation_schedule_order_ge_two D₀ N p H
  have hσ0 : 0 ≤ σ₀ := by rw [hσeq]; linarith
  have hDstar : N ≤ succDstar D₀ N p H ∧ 2 ≤ succDstar D₀ N p H := by
    simp only [succDstar, succSchedD]
    omega
  have hexp := liftSchedule_exponents (γ := ocGamma α q) (K := K) hσ0
    (ocDelta_pos_of_admissible hα₀ hq) (ocGamma_pos_of_admissible hα₀ hq).le hK hDstar.1
    hDstar.2 hσD
  have hcrI : kI.cr = kS.cr := (Buffer.invariantAdmissible_molecular_parameters hkI).2.1
  have hcrI0 : 0 < kI.cr := by rw [hcrI]; exact hcr
  have hcr1 : kI.cr ≤ 1 := by rw [hcrI]; exact hcrupper
  have hCI0 : 0 ≤ CI := (zero_le_one.trans hCe).trans hledger.1
  obtain ⟨CG, Cw', Cj, m₀, hm₀, hpk⟩ := hlift Λ hΛa' bw hbw (succSchedD D₀ N p (H + 1))
    (succSchedR r₀ J H) N ((K + 2) + N + succSchedD D₀ N p (H + 1)) K 0 hDm (by omega)
  obtain ⟨Mf, _hMf, hflow⟩ := uniform_native_physical_flow_jets α s q hα₀ hα₁ hs₀ hs₁ hq Λ
    hΛ128 ζ hζ (K + N)
  obtain ⟨Cin, mi, hCin, _hmi, hinput'⟩ := hinput Λ hΛi' φ₀ hφ₀ hφsmooth hφsupport K N p
    nk.toPNat' kI.cr σ₀ Cn (by omega) hcrI0 hcr1 hσ0 hexp.1 hexp.2
  refine ⟨liftProfileConst (EntryWeakProofs.weakChartJetBudget (K + N) 0) K (max K (0 + 2))
    (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N CG Cw' Cj CI Cin Csc,
    max (max m₀ j₀) (max mi (Mf + 1)), ?_⟩
  intro C hC
  unfold PassageRetainedLiftData
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
    hseed hmol m hm hn hnM tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual hRn CcT
    hCcT aU aY t hts htf haY haYp
  subst hlevel
  have hm₀' : m₀ ≤ G.level := (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hj₀ : j₀ ≤ G.level := (le_max_right _ _).trans ((le_max_left _ _).trans hm)
  have hmi' : mi ≤ G.level := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hMf' : Mf + 1 ≤ G.level := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hi : 1 ≤ G.level := by omega
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hΛD128 : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ128
  have hΛD : 1 ≤ D.Λ := by omega
  have hζD : IsFastProfile D.ζ := hDζ ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hprod : kI.Hprod = kI.G0 + H + 1 :=
    (Buffer.invariantAdmissible_molecular_parameters hkI).2.2
  have hprod' : kI.Hprod =
      kI.G0 + (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)).H + 1 := hprod
  have hmG v : 0 ≤ compReserve kI (v : CompIn G.comps).1 :=
    (Buffer.cascade_component_reserve_pos hseed.2.1 hcascade kI hprod' v).le
  have hm2G v : compReserve kI (v : CompIn G.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hseedI := hseed.2.2.2.2.2.2.2.1
  have hlens : ∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level := by
    intro v u γ hb
    simpa only [hseed.1] using (hseed.2.2.2.2.2.1 v u γ).2.2 hb
  have hlenG := hlength ScalarH D hDα hDq hDζ (by rw [hDΛ]; exact hΛl') hbandD
    _ bw j₀ (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) Cw kI.cr σ₀
    (succEta0 α q s) N p hcr1 seed G hseedI.2.1 hlens
    (by rw [hseed.1, hterm]; exact hnM.le) hcascade hi
  have hdepth := Providers.CascadeInvariants.cascade_depth_of_generatedSeed hseed hcascade
  have hlt : G.level < D.term := by rw [hterm]; omega
  have hpk' := hpk ScalarH D hDα hDq hDΛ hDζ hseq hbandD j₀ G law _ seedK freshK φ₀ hφ₀ Mnat kI
    tA tf _ _ hG hm₀' hlt hj₀ hdepth hmG hm2G hlenG (fun _ => 1) (Or.inl rfl)
  have hpk'' : ∀ slot : OddSlot, Nonempty (NativeSlotLift G slot (G.mass law)
      (succSchedR r₀ J H) N ((K + 2) + N + succSchedD D₀ N p (H + 1)) K 0 CG Cw' Cj
      (CI * D.eps G.level ^ min (ocDelta α q / 4) τe)) := by
    simpa only [one_pow, div_one] using hpk'
  have slotLifts := fun slot => Classical.choice (hpk'' slot)
  have htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)) := hG.isTorusCompatible
  have hπ' : ∀ v, 0 < (G'.retained G.level H J).mass law v := fun v =>
    Buffer.birth_compMass_pos hqD hΛD128 law v.1
  have heps : 0 < D.eps G.level := Construction.Stream.ocEpsilon_pos hΛD
  have heps1 : D.eps G.level ≤ 1 := ocEpsilon_le_one hΛD _
  have hmin : 0 ≤ min (ocDelta α q / 4) τe :=
    le_min (by have := ocDelta_pos_of_admissible hα₀ hq; linarith) hτe.le
  have hS0 : 0 ≤ CI * D.eps G.level ^ min (ocDelta α q / 4) τe :=
    mul_nonneg hCI0 (Real.rpow_nonneg heps.le _)
  have hSle : CI * D.eps G.level ^ min (ocDelta α q / 4) τe ≤ CI :=
    mul_le_of_le_one_right hCI0 (Real.rpow_le_one heps.le heps1 hmin)
  have hρ : 0 < liftLength D G.level := (slotLifts ⟨1, by decide⟩).setting.ρ_pos
  have hρE : liftLength D G.level ≤ D.eps (G.level - 1) :=
    (div_le_one (slotLifts ⟨1, by decide⟩).setting.E_pos).mp (slotLifts ⟨1, by decide⟩).setting.lam_le
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛD
  have haY0 : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) (aY t) := haY
  have hSreg := regularKernel_contDiff_periodic hφsmooth hφsupport (freshK (G.level - 1)) t
    haY0 haYp
  obtain ⟨hgreg, hgper⟩ := regularFields_PRX D G.level p K N (D.eps (G.level - 1))
    (succEta0 α q s) (S := G.comps) (fieldKernel φ₀ (freshK (G.level - 1)) aY) t hSreg.1 hSreg.2
  have hfreshK : IsFreshKernel D kI.cr σ₀ nk.toPNat' (G.level - 1) (freshK (G.level - 1)) :=
    hfresh (G.level - 1) (by omega) (by omega)
  have hreserve : ∀ slot : OddSlot, K + (N + (slotLifts slot).cap) ≤
      (K + 2) + N + succSchedD D₀ N p (H + 1) +
        4 * (succSchedR r₀ J H + 1) * (N + (slotLifts slot).cap) ^ 2 := by
    intro slot
    have hcap := (slotLifts slot).cap_le
    exact le_trans (by omega : K + (N + (slotLifts slot).cap) ≤
      K + 2 + N + succSchedD D₀ N p (H + 1)) (Nat.le_add_right _ _)
  rw [passageProfiles_getD_one]
  exact retainedLift_at_stage slotLifts hS0 hSle hi hΛD hζD hbandD hlt.le htorus K hreserve
    (le_max_left _ _) (EntryWeakProofs.weakChartJetBudget_ge_one _ _) t
    (fun j hj hcut => hflow D hDα hDq hDΛ hDζ hseq G.level hMf' j hj (liftLength D G.level)
      hρ hρE t (Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut))
    sX sZ CcT hCcT
    (fieldCov D G.level p (fieldReadout G.level (D.eps (G.level - 1)) (succEta0 α q s)
      (fieldKernel φ₀ (freshK (G.level - 1)) aY)))
    (hgreg.of_le (by exact_mod_cast (by omega : K + N ≤ K + 2 + N))) hgper hCin _
    (fun x => hinput' D hDα hDq hDΛ hDζ hseq M hband hterm G.level hmi' (by omega)
      (freshK (G.level - 1)) hfreshK (G.mass law) ((G'.retained G.level H J).mass law) hπ'
      (succEta0 α q s) hRn aY t
      (haY0.of_le (by exact_mod_cast (by omega : K + N + 2 * p ≤ K + N + 2 * p + 2))) haYp x)
    (hscale Λ hΛs' D hDα hDq hDΛ hDζ M hband hterm G.level (by omega) (by omega)) hC

end AVRegularity.IterationPassage.Passage
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.FullLift AVRegularity.Construction.Preservation
open scoped ENNReal
namespace AVRegularity.IterationPassage.Passage

/-! **The discarded lift profile** `𝓘_{e,K;s}(D_e) ≤ C e^{-s} ρ^{-1} ‖w‖_{ρ,K+N+2+2p;π'}`,
`D_e = (T - I)P_p𝖱(Y - S_rY)` (step `DiscDeStep`).

`discDeStep : DiscDeStep α s q ζ`. The proof at a time `t`, for a realization `w` of the defect
`Y - S_rY` of order `K + N + 2 + 2p`:

* the slot lifts of the incoming stage and the chart jets at the lift radius, as in
  `passageRetainedLift`;
* `discardedLift_at_stage`: the positive bound of the lift and the packing;
* `discDe_input_bound`: the positive jets of the input `P_p𝖱(Y - S_rY)` at the lift radius
  `ρ_L = ρ/c_r` are at most `C ρ^{-1}‖w‖`: the profile seminorm of the normalized defect at the
  scale `ρ` by `discDe_seminorm_le` (`sobolevProfile`), the covariance `|𝖧_{ij}| ≤ (C/c_r²)ρ²`
  by `retCov_cov_scales` (`r = ρ E^{σ₀} ≤ ρ`), the readout by its norm bound `C_n`.

Here `ρ = rhoEnh D c_r m = c_r · liftLength D m` and `ρ ≤ ρ_L ≤ E ≤ 1` from the slot lifts. No
comparison of `e` with `ρ` is needed.

Special cases: `aY t = S_r aY t` (`w = 0` realizes it; the profile vanishes); `p = 0`; an empty
family. -/

/-- The fourth profile of the passage at a time is the discarded lift profile. -/
theorem passageProfiles_getD_three {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (law : BirthLaw)
    (G Gr : GenStage D ScalarH Dm b j₀) (m p N depth : ℕ) (η₀ : ℝ) (φ₀ : Vec 2 → ℝ)
    (Sr : KernelSpec)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ) :
    ((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map fun q => q.1 t).getD 3 0 =
      compField (G.mass law) (fun y => passageLift D m N depth CcT
        (fieldCov D m p (fieldReadout m (D.eps (m - 1)) η₀ (aY - fieldKernel φ₀ Sr aY))) t y -
        fieldCov D m p (fieldReadout m (D.eps (m - 1)) η₀ (aY - fieldKernel φ₀ Sr aY)) t y) :=
  rfl

/-- The covariance of the passage at the radius `ρ`: `|𝖧_{ij}| ≤ (C/c_r²) ρ²`. -/
theorem discDe_cov_le {c x f ρ' Hc : ℝ} (hc : 0 ≤ c) (hx1 : x ≤ 1) (hf0 : 0 ≤ f)
    (hfle : f ≤ ρ') (h : Hc ≤ (c * x) * f ^ 2) : Hc ≤ c * ρ' ^ 2 := by
  have h1 : (c * x) * f ^ 2 ≤ (c * 1) * ρ' ^ 2 := by
    have hx' : c * x ≤ c * 1 := mul_le_mul_of_nonneg_left hx1 hc
    have hf' : f ^ 2 ≤ ρ' ^ 2 := pow_le_pow_left₀ hf0 hfle 2
    calc (c * x) * f ^ 2 ≤ (c * 1) * f ^ 2 := mul_le_mul_of_nonneg_right hx' (sq_nonneg f)
      _ ≤ (c * 1) * ρ' ^ 2 := mul_le_mul_of_nonneg_left hf' (by positivity)
  exact h.trans (h1.trans_eq (by ring))

/-- **The discarded lift profile** (`DiscDeStep`). -/
theorem discDeStep (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : DiscDeStep α s q ζ := by
  classical
  obtain ⟨Λa, hΛa, hlift⟩ := uniform_native_weighted_slot_lifts hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λl, _hΛl, hlength⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Cs', hCs', Λs, _hΛs, hscale⟩ := retCov_cov_scales α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  refine ⟨max (max Λa Λl) Λs, hΛa.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro Λ hΛ
  have hΛa' : Λa ≤ Λ := (le_max_left _ _).trans ((le_max_left _ _).trans hΛ)
  have hΛl' : Λl ≤ Λ := (le_max_right _ _).trans ((le_max_left _ _).trans hΛ)
  have hΛs' : Λs ≤ Λ := (le_max_right _ _).trans hΛ
  have hΛ128 : 128 ≤ Λ := hΛa.trans hΛa'
  refine ⟨1, one_pos, ?_⟩
  rintro ⟨φ₀, hφ₀, hφsmooth, hφpos, hφint, hφsupport, bw, hbw, hbwupper, K, Pacc, hK, hPacc, Q,
    T₀, hQ, hT₀, hQb, r₀, D₀, τe, lamE, σE, hτe, hlamE, hσE, H, J, N, p, nk, Lc, Lf, Lpr, Acl, Naux,
    Nout, Kres, npad, σ₀, a, σ, hsched, hNaux, hNout, L, hL, hwid, sX, sZ, Ce, kS, hCe, hc₀,
    hc₀upper, hcr, hcrupper, hσf, hlamC, halloc, kI, hkI, CI, Cw, j₀, hledger, hstart, Cn⟩
  dsimp only
  obtain ⟨_, _, _, _, _, hσeq, ha0, haσ, _, hσD, _, _, _, _, _, _, _, hN2, _, _⟩ := hsched
  have hDm : 2 ≤ succSchedD D₀ N p (H + 1) := Buffer.preparation_schedule_order_ge_two D₀ N p H
  have hσ0 : 0 ≤ σ₀ := by rw [hσeq]; linarith
  have hDstar : N ≤ succDstar D₀ N p H ∧ 2 ≤ succDstar D₀ N p H := by
    simp only [succDstar, succSchedD]
    omega
  have hexp := liftSchedule_exponents (γ := ocGamma α q) (K := K) hσ0
    (ocDelta_pos_of_admissible hα₀ hq) (ocGamma_pos_of_admissible hα₀ hq).le hK hDstar.1
    hDstar.2 hσD
  have hcrI : kI.cr = kS.cr := (Buffer.invariantAdmissible_molecular_parameters hkI).2.1
  have hcrI0 : 0 < kI.cr := by rw [hcrI]; exact hcr
  have hcr1 : kI.cr ≤ 1 := by rw [hcrI]; exact hcrupper
  have hCI0 : 0 ≤ CI := (zero_le_one.trans hCe).trans hledger.1
  have hcr2 : kI.cr ^ 2 ≤ 1 := pow_le_one₀ hcrI0.le hcr1
  have hCb : 1 ≤ Cs' / kI.cr ^ 2 := (one_le_div (pow_pos hcrI0 2)).mpr (hcr2.trans hCs')
  obtain ⟨CG, Cw', Cj, m₀, hm₀, hpk⟩ := hlift Λ hΛa' bw hbw (succSchedD D₀ N p (H + 1))
    (succSchedR r₀ J H) N ((K + 2) + N + succSchedD D₀ N p (H + 1)) K 0 hDm (by omega)
  obtain ⟨Mf, _hMf, hflow⟩ := uniform_native_physical_flow_jets α s q hα₀ hα₁ hs₀ hs₁ hq Λ
    hΛ128 ζ hζ (K + N)
  obtain ⟨Csem, hCsem, hsem⟩ := discDe_seminorm_le (K + N + 2 * p)
  have hCχ := EntryWeakProofs.weakChartJetBudget_ge_one (K + N) 0
  refine ⟨discDeProfileConst (EntryWeakProofs.weakChartJetBudget (K + N) 0) K (max K (0 + 2))
      (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N CG Cw' Cj CI *
      discDeInputConst kI.cr (Cs' / kI.cr ^ 2) (max Cn 0) Csem K N p (K + N + 2 * p),
    max (max m₀ j₀) (Mf + 1), ?_, ?_⟩
  · refine mul_nonneg (discDeProfileConst_nonneg hCχ _ _ _ _ _ _ _ _ hCI0) ?_
    have h0 : 0 ≤ max Cn 0 := le_max_right _ _
    have hCb0 : 0 ≤ Cs' / kI.cr ^ 2 := zero_le_one.trans hCb
    unfold discDeInputConst
    positivity
  unfold DiscDeData
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
    hseed hmol m hm hn hnM tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual hRn CcT
    hCcT aU aY t hts htf haY haYp w hw
  subst hlevel
  have hm₀' : m₀ ≤ G.level := (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hj₀ : j₀ ≤ G.level := (le_max_right _ _).trans ((le_max_left _ _).trans hm)
  have hMf' : Mf + 1 ≤ G.level := (le_max_right _ _).trans hm
  have hi : 1 ≤ G.level := by omega
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hΛD128 : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ128
  have hΛD : 1 ≤ D.Λ := by omega
  have hζD : IsFastProfile D.ζ := hDζ ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hprod : kI.Hprod = kI.G0 + H + 1 :=
    (Buffer.invariantAdmissible_molecular_parameters hkI).2.2
  have hprod' : kI.Hprod =
      kI.G0 + (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)).H + 1 := hprod
  have hmG v : 0 ≤ compReserve kI (v : CompIn G.comps).1 :=
    (Buffer.cascade_component_reserve_pos hseed.2.1 hcascade kI hprod' v).le
  have hm2G v : compReserve kI (v : CompIn G.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hseedI := hseed.2.2.2.2.2.2.2.1
  have hlens : ∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level := by
    intro v u γ hb
    simpa only [hseed.1] using (hseed.2.2.2.2.2.1 v u γ).2.2 hb
  have hlenG := hlength ScalarH D hDα hDq hDζ (by rw [hDΛ]; exact hΛl') hbandD
    _ bw j₀ (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) Cw kI.cr σ₀
    (succEta0 α q s) N p hcr1 seed G hseedI.2.1 hlens
    (by rw [hseed.1, hterm]; exact hnM.le) hcascade hi
  have hdepth := Providers.CascadeInvariants.cascade_depth_of_generatedSeed hseed hcascade
  have hlt : G.level < D.term := by rw [hterm]; omega
  have hpk' := hpk ScalarH D hDα hDq hDΛ hDζ hseq hbandD j₀ G law _ seedK freshK φ₀ hφ₀ Mnat kI
    tA tf _ _ hG hm₀' hlt hj₀ hdepth hmG hm2G hlenG (fun _ => 1) (Or.inl rfl)
  have hpk'' : ∀ slot : OddSlot, Nonempty (NativeSlotLift G slot (G.mass law)
      (succSchedR r₀ J H) N ((K + 2) + N + succSchedD D₀ N p (H + 1)) K 0 CG Cw' Cj
      (CI * D.eps G.level ^ min (ocDelta α q / 4) τe)) := by
    simpa only [one_pow, div_one] using hpk'
  have slotLifts := fun slot => Classical.choice (hpk'' slot)
  have htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)) := hG.isTorusCompatible
  have hπ' : ∀ v, 0 < (G'.retained G.level H J).mass law v := fun v =>
    Buffer.birth_compMass_pos hqD hΛD128 law v.1
  have heps : 0 < D.eps G.level := Construction.Stream.ocEpsilon_pos hΛD
  have heps1 : D.eps G.level ≤ 1 := ocEpsilon_le_one hΛD _
  have hE0 : 0 < D.eps (G.level - 1) := Construction.Stream.ocEpsilon_pos hΛD
  have hE1 : D.eps (G.level - 1) ≤ 1 := ocEpsilon_le_one hΛD _
  have hmin : 0 ≤ min (ocDelta α q / 4) τe :=
    le_min (by have := ocDelta_pos_of_admissible hα₀ hq; linarith) hτe.le
  have hS0 : 0 ≤ CI * D.eps G.level ^ min (ocDelta α q / 4) τe :=
    mul_nonneg hCI0 (Real.rpow_nonneg heps.le _)
  have hSle : CI * D.eps G.level ^ min (ocDelta α q / 4) τe ≤ CI :=
    mul_le_of_le_one_right hCI0 (Real.rpow_le_one heps.le heps1 hmin)
  have hρ : 0 < liftLength D G.level := (slotLifts ⟨1, by decide⟩).setting.ρ_pos
  have hρE : liftLength D G.level ≤ D.eps (G.level - 1) :=
    (div_le_one (slotLifts ⟨1, by decide⟩).setting.E_pos).mp (slotLifts ⟨1, by decide⟩).setting.lam_le
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛD
  -- the radius `ρ = c_r ρ_L`
  have hρe : rhoEnh D kI.cr G.level = kI.cr * liftLength D G.level := rfl
  have hρe0 : 0 < rhoEnh D kI.cr G.level := by rw [hρe]; exact mul_pos hcrI0 hρ
  have hρe1 : rhoEnh D kI.cr G.level ≤ 1 := by
    rw [hρe]
    calc kI.cr * liftLength D G.level ≤ 1 * D.eps (G.level - 1) :=
          mul_le_mul hcr1 hρE hρ.le zero_le_one
      _ ≤ 1 := by rw [one_mul]; exact hE1
  -- the covariance at the radius `ρ`
  obtain ⟨hεle, _hrE, hcov⟩ := hscale Λ hΛs' D hDα hDq hDΛ hDζ M hband hterm kI.cr σ₀ hcrI0 hcr1
    hσ0 hexp.1 G.level (by omega) (by omega)
  have hfw : freshWidth D kI.cr σ₀ (G.level - 1) =
      rhoEnh D kI.cr G.level * D.eps (G.level - 1) ^ σ₀ := by
    rw [freshWidth_eq_liftLength D kI.cr σ₀ hi]
    rfl
  have hfw0 : 0 ≤ freshWidth D kI.cr σ₀ (G.level - 1) := by
    rw [hfw]
    exact mul_nonneg hρe0.le (Real.rpow_nonneg hE0.le _)
  have hfwle : freshWidth D kI.cr σ₀ (G.level - 1) ≤ rhoEnh D kI.cr G.level := by
    rw [hfw]
    exact mul_le_of_le_one_right hρe0.le (Real.rpow_le_one hE0.le hE1 hσ0)
  have hA : ∀ i j, |covPrimitive D G.level t i j| ≤
      Cs' / kI.cr ^ 2 * rhoEnh D kI.cr G.level ^ 2 := fun i j =>
    discDe_cov_le (zero_le_one.trans hCb) hεle hfw0 hfwle (hcov t i j)
  -- the fields
  have haY0 : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) (aY t) := haY
  have hSreg := regularKernel_contDiff_periodic hφsmooth hφsupport (freshK (G.level - 1)) t
    haY0 haYp
  have hδ : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞)
      ((aY - fieldKernel φ₀ (freshK (G.level - 1)) aY) t) := haY0.sub hSreg.1
  have hδp : IsZ2Periodic ((aY - fieldKernel φ₀ (freshK (G.level - 1)) aY) t) :=
    regular_periodic_sub haYp hSreg.2
  obtain ⟨hgreg, hgper⟩ := regularFields_PRX D G.level p K N (D.eps (G.level - 1))
    (succEta0 α q s) (S := G.comps) (aY - fieldKernel φ₀ (freshK (G.level - 1)) aY) t hδ hδp
  have hRreg : ContDiff ℝ ((2 * p : ℕ) : ℕ∞)
      (fieldReadout (S := G.comps) G.level (D.eps (G.level - 1)) (succEta0 α q s)
        (aY - fieldKernel φ₀ (freshK (G.level - 1)) aY) t) :=
    regularReadout_contDiff G.level (D.eps (G.level - 1)) (succEta0 α q s)
      (aY - fieldKernel φ₀ (freshK (G.level - 1)) aY) t
      (hδ.of_le (by exact_mod_cast (by omega : 2 * p ≤ K + N + 2 * p + 2)))
  have hmodel : compField (G.mass law) (fieldCov D G.level p
      (fieldReadout G.level (D.eps (G.level - 1)) (succEta0 α q s)
        (aY - fieldKernel φ₀ (freshK (G.level - 1)) aY)) t) =
      covPolyP (covPrimitive D G.level t) p (fun y =>
        readoutCLM G.level (D.eps (G.level - 1)) (succEta0 α q s) (G.mass law)
          ((G'.retained G.level H J).mass law)
          (compField ((G'.retained G.level H J).mass law)
            (fun x => aY t x - fieldKernel φ₀ (freshK (G.level - 1)) aY t x) y)) := by
    rw [retCov_compField_cov D G.level p (G.mass law) _ t hRreg]
    congr 1
    funext y
    exact retCov_compField_readout G.level (D.eps (G.level - 1)) (succEta0 α q s) (G.mass law)
      ((G'.retained G.level H J).mass law) hπ'
      (aY - fieldKernel φ₀ (freshK (G.level - 1)) aY) t y
  have hGreg : ContDiff ℝ ((K + N + 2 * p : ℕ) : ℕ∞)
      (compField ((G'.retained G.level H J).mass law)
        (fun x => aY t x - fieldKernel φ₀ (freshK (G.level - 1)) aY t x)) :=
    regularCompField_contDiff _
      (hδ.of_le (by exact_mod_cast (by omega : K + N + 2 * p ≤ K + N + 2 * p + 2)))
  have hsemi := hsem ((G'.retained G.level H J).mass law) hπ' (rhoEnh D kI.cr G.level) hρe0
    hρe1 (K + N + 2 + 2 * p) (by omega) w
    (fun x => aY t x - fieldKernel φ₀ (freshK (G.level - 1)) aY t x) hw
  have hWn : 0 ≤ weightedNorm (rhoEnh D kI.cr G.level) ((G'.retained G.level H J).mass law)
      (fun _ => 1) w := Real.sqrt_nonneg _
  have hreserve : ∀ slot : OddSlot, K + (N + (slotLifts slot).cap) ≤
      (K + 2) + N + succSchedD D₀ N p (H + 1) +
        4 * (succSchedR r₀ J H + 1) * (N + (slotLifts slot).cap) ^ 2 := by
    intro slot
    have hcap := (slotLifts slot).cap_le
    exact le_trans (by omega : K + (N + (slotLifts slot).cap) ≤
      K + 2 + N + succSchedD D₀ N p (H + 1)) (Nat.le_add_right _ _)
  have hB : 0 ≤ discDeInputConst kI.cr (Cs' / kI.cr ^ 2) (max Cn 0) Csem K N p
      (K + N + 2 * p) * ((rhoEnh D kI.cr G.level)⁻¹ *
        weightedNorm (rhoEnh D kI.cr G.level) ((G'.retained G.level H J).mass law)
          (fun _ => 1) w) := by
    have h0 : 0 ≤ max Cn 0 := le_max_right _ _
    have hCb0 : 0 ≤ Cs' / kI.cr ^ 2 := zero_le_one.trans hCb
    have hρi : 0 ≤ (rhoEnh D kI.cr G.level)⁻¹ := inv_nonneg.mpr hρe0.le
    unfold discDeInputConst
    positivity
  rw [passageProfiles_getD_three]
  refine (discardedLift_at_stage slotLifts hS0 hSle hi hΛD hζD hbandD hlt.le htorus K hreserve
    (le_max_left _ _) hCχ t
    (fun j hj hcut => hflow D hDα hDq hDΛ hDζ hseq G.level hMf' j hj (liftLength D G.level)
      hρ hρE t (Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut))
    sX sZ CcT hCcT
    (fieldCov D G.level p (fieldReadout G.level (D.eps (G.level - 1)) (succEta0 α q s)
      (aY - fieldKernel φ₀ (freshK (G.level - 1)) aY)))
    (hgreg.of_le (by exact_mod_cast (by omega : K + N ≤ K + 2 + N))) hgper hB
    (fun x => by
      rw [hmodel]
      exact discDe_input_bound hρe0 hcrI0 hcr1 hρe hCb (le_max_right Cn 0) hCsem hWn le_rfl
        (covPrimitive D G.level t) hA _ (hRn.trans (le_max_left Cn 0)) _ hGreg hsemi x)).trans_eq
    ?_
  congr 1
  ring

end AVRegularity.IterationPassage.Passage
end
end

section
section
/-! **The discarded profiles**.

`passageDiscardedProfiles_of_open`: `PassageDiscardedProfilesStatement` from the two steps
`DiscDEStatement` (the covariance correction of the defect in the profile norm) and
`DiscDeStep` (the lift profile `D_e`); moment cancellation (`discMoment`) and the scales
(`discScales`) are proved. -/

@[expose] public noncomputable section

namespace AVRegularity.IterationPassage.Passage

theorem passageDiscardedProfiles_of_open (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hE : DiscDEStatement) (hDe : DiscDeStep α s q ζ) :
    PassageDiscardedProfilesStatement α s q ζ :=
  passageDiscardedProfiles_of α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ discMoment hE
    (discScales α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ) hDe

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The discarded profiles** `D_E`, `D_e` (Step 5 of the proof of Proposition 4.4 of the
paper).

`passageDiscardedProfiles : PassageDiscardedProfilesStatement α s q ζ`, from the assembly, the
moment cancellation and the scales (`passageDiscardedProfiles_of_open`, `discMoment`,
`discScales`), the lift profile `D_e` (`discDeStep`) and the covariance step (`discDE`).
`passageDiscardedProfiles_of_DE` is the same with the covariance step as a hypothesis. -/

@[expose] public noncomputable section

namespace AVRegularity.IterationPassage.Passage

theorem passageDiscardedProfiles_of_DE (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hE : DiscDEStatement) :
    PassageDiscardedProfilesStatement α s q ζ :=
  passageDiscardedProfiles_of_open α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ hE
    (discDeStep α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ)

/-- **The discarded profiles.** -/
theorem passageDiscardedProfiles (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : PassageDiscardedProfilesStatement α s q ζ :=
  passageDiscardedProfiles_of_DE α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ discDE

end AVRegularity.IterationPassage.Passage
end
end
end
