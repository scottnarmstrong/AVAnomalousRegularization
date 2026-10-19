-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
public import AVRegularity.CycleJoint.TransitionJetTermDerivative
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees
import AVRegularity.Construction.Preservation.FullLift.NativeContextKernelOperator
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
public import AVRegularity.Construction.Preservation.FullLift.CovarianceTimeMeasurable
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
public import AVRegularity.EntryWeak.NativeMixedChartBudget
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
import AVRegularity.EntryWeak.IndependentFreshCoarseAppendedSourceReserve

@[expose] public noncomputable section

section
open Homogenization
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.Construction.Preservation.FullLift

/-! Arbitrary native base labels turn the produced local chart bound into global slow metric jets. -/

section
open AVRegularity.EntryWeakProofs

theorem uniform_native_lift_metric_jets (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (K : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ m, M + 1 ≤ m → ∀ slot : ℤ, Odd slot → ∀ lam : ℝ, 0 ≤ lam →
      ∀ u ∈ ocPulseWindow D.α D.q D.Λ m slot, ∀ n ≤ K, ∀ X : Vec 2,
      ‖iteratedFDeriv ℝ n (fun Y : Vec 2 =>
        ((nativeChain m slot).recenter D ((D.eps (m - 1) * lam) • Y)).famMetric D u) X‖ ≤
        planarGramJetBudget n (nativeMixedChartBudget (K + 1) 0 1) * lam ^ n := by
  obtain ⟨M, hM, hC⟩ := uniform_fresh_metric_jet_production α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ 0
  refine ⟨M, hM, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq m hm slot hslot lam hlam u hu n hn X
  let ρ := D.eps (m - 1) * lam
  let A : RealChain := ⟨m - 1, [slot], ρ • X, []⟩
  have hA : A.WellSlotted := rfl
  have hctx : A.ctxLevel = m := by dsimp [A, RealChain.ctxLevel, RealChain.lastLevel]; omega
  have hslotA : A.slot = slot := by simp [A, RealChain.slot]
  have hΛ' : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hclock : u ∈ nativeWeakChartWindow D A.baseLevel 0 (realChainSlotSeq A) A.children.length := by
    apply actual_family_pulse_in_native_chart_window D hΛ' A hA 0 u
    simpa only [hctx, hslotA] using hu
  have hp : ∀ j ≤ 0, Odd (realChainSlotSeq A j) := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa [A, realChainSlotSeq] using hslot
  have hzero := hC D hDα hDq hDΛ hDζ hseq A (by dsimp [A]; omega) hA rfl
    (realChainSlotSeq A) (by simp [A, realChainSlotSeq]) hp
    (fun j hj => False.elim (Nat.not_lt_zero j hj)) 0 le_rfl K 1 u hclock
    (0 : Vec (4 * 0) × Vec 2) (fun j => Fin.elim0 j) (by simp) n hn
  have hb : ‖iteratedFDeriv ℝ n (fun Z : Vec (4 * 0) × Vec 2 =>
      ((independentFreshChain A (fun j : Fin 0 => Fin.elim0 j)
        (fun j : Fin 0 => Fin.elim0 j) Z.1).recenter D
        (D.eps (m - 1) • Z.2)).famMetric D u) 0‖ ≤
      planarGramJetBudget n (nativeMixedChartBudget (K + 1) 0 1) := by
    simpa only [A, Nat.add_zero, independentFreshChain, List.ofFn_zero, List.append_nil] using hzero
  have hscaled := zeroFresh_metric_scaled_slice_jet_le D A hA (D.eps (m - 1)) lam u
    (planarGramJetBudget n (nativeMixedChartBudget (K + 1) 0 1)) hlam n hb
  have he : (fun Z : Vec 2 => (A.recenter D (ρ • Z)).famMetric D u) =
      fun Z : Vec 2 => ((nativeChain m slot).recenter D (ρ • (X + Z))).famMetric D u := by
    funext Z
    rw [Providers.GenSem.recenter_nil D A rfl,
      Providers.GenSem.recenter_nil D (nativeChain m slot) rfl]
    simp only [A, nativeChain, zero_add, smul_add]
  change ‖iteratedFDeriv ℝ n (fun Z : Vec 2 => (A.recenter D (ρ • Z)).famMetric D u) 0‖ ≤ _
    at hscaled
  rw [he] at hscaled
  rw [iteratedFDeriv_comp_add_left (f := fun Y : Vec 2 =>
    ((nativeChain m slot).recenter D (ρ • Y)).famMetric D u) n X 0, add_zero] at hscaled
  exact hscaled
end

/-! The global native metric bound supplies the literal lift-setting uniform time and label supremum. -/

section
open AVRegularity.EntryWeakProofs
theorem uniform_native_lift_metric_sup_all_carriers (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (K : ℕ) :
    ∃ CG : ℕ → ℝ, (∀ n, 0 ≤ CG n) ∧ ∃ M : ℕ, 2 ≤ M ∧ ∀ (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
      [∀ i, NormedSpace ℝ (h i)] (Dm : ℕ), ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ m, M + 1 ≤ m → ∀ slot : ℤ, Odd slot → ∀ lam : ℝ, 0 ≤ lam →
      ∀ edge : ConstituentEdges Dm h, ∀ n ≤ K,
      (⨆ t ∈ Set.Icc (D.slotStart m slot / D.cellScaleSq m)
        ((((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m),
        ⨆ X : Vec 2, ‖iteratedFDeriv ℝ n (fun Y =>
          (familyLiftData D m slot (nativeChain m slot) (D.eps (m - 1) * lam) edge).G t Y) X‖ₑ) ≤
        ENNReal.ofReal (CG n * lam ^ n) := by
  obtain ⟨M, hM, hC⟩ := uniform_native_lift_metric_jets α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ K
  refine ⟨fun n => planarGramJetBudget n (nativeMixedChartBudget (K + 1) 0 1),
    fun n => planarGramJetBudget_nonneg n _ (zero_le_one.trans (nativeMixedChartBudget_ge_one _ _ _)),
    M, hM, ?_⟩
  intro ι h _ _ Dm D hDα hDq hDΛ hDζ hseq hband m hm slot hslot lam hlam edge n hn
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  apply iSup_le
  intro X
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  have hΛ₁ : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  exact hC D hDα hDq hDΛ hDζ hseq m hm slot hslot lam hlam
    (D.cellScaleSq m * t) (weak_lift_clock_in_pulse_window D hΛ₁ hζD hband m slot t ht) n hn X
end

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Literal certified native fluxes have transported kernel prices controlled by their own record. -/

open CycleJointProofs

theorem context_certified_transport_record_price (bw : ℝ) (hb : 0 < bw) (nmax : ℕ)
    (Cchart : ℝ) (hchart : 1 ≤ Cchart) :
    ∃ Csample : ℝ, 0 ≤ Csample ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ (D : OCData) (Dm j₀ : ℕ) (G : GenStage D hr Dm bw j₀) (k : InvConsts),
      G.IsContextCertified k → ∀ (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
      0 < D.eps (G.level - 1) → G.IsSlotTransverse →
      ∀ (v u : CompIn G.comps) (γ : G.fam.Γ v u),
      0 ≤ compReserve k v.1 → compReserve k v.1 ≤ 2 →
      ∀ (p : OddSlot), (G.actual p).1 = nativeChain G.level p.1 →
      ∀ (N Dmax Kmax n dout : ℕ), n ≤ nmax → (G.fam.identity v u γ).maxOrder ≤ Dmax → n ≤ Kmax →
      2 ≤ dout → dout ≤ Dmax → n + (G.fam.identity v u γ).maxOrder ≤ N →
      ∀ (C ν e ρ R r : ℝ), e = D.eps G.level →
      R = (G.fam.identity v u γ).record.length → 1 ≤ C → 0 < ν → 0 < e → 0 < ρ →
      ρ ≤ D.eps (G.level - 1) → ρ ≤ e → 0 < R → 0 < r →
      (3 ≤ (G.fam.identity v u γ).maxOrder → R ≤ D.eps (G.level - 1)) →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)
        nmax Cchart (D.eps (G.level - 1)) →
      (∀ a b j, j ≤ N → ∀ x, D.eps (G.level - 1) ^ j * ‖iteratedFDeriv ℝ j
        (fun y => naturalPreparationJacobian (D.hΦ (G.level - 1))
          (D.slotAnchor G.level p.1) t y a b) x‖ ≤ C) →
      ∀ x : Vec 2,
      (ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => nativeArrayAssembly (dout - 1)
        (G.fam.identity v u γ).map
        (fun a A => transportedCoeff
          (naturalPreparationJacobian (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) t)
          (G.fam.identity v u γ).maxOrder
          (fun d I => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
            (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)
            (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t))
          (dout - 1) A y a)) x‖) / (ν * r ^ (dout - 2)) ≤
        4 * (2 : ℝ) ^ Dmax * ‖(G.fam.identity v u γ).map‖ *
          (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * C *
            (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ Dmax) * Csample *
              max 1 ((R / r) ^ ((G.fam.identity v u γ).maxOrder - 2)) * ((G.fam.identity v u γ).maxOrder : ℝ) *
                (G.fam.identity v u γ).record.size := by
  obtain ⟨Cs, hCs, hprices⟩ := uniform_context_certified_sampled_flux_price bw hb nmax Cchart hchart
  refine ⟨Cs, hCs, ?_⟩
  intro hr _ _ D Dm j₀ G k hG hi hj hE hpar v u γ hm hm2 p ha
    N Dmax Kmax n dout hnn hD hkn hdout hout hn C ν e ρ R r heActual hRActual hC hν he hρ hρE hρe hR hrpos hRE
    t ht hflow hKC x
  obtain ⟨θ, hθ, hledger, hprice⟩ := hprices hr D Dm j₀ G k hG hi hj hE hpar v u γ hm hm2
  let B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2 := fun d I y =>
    G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
      (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)
      (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)
  have hs d I c := hprice p d I c ha ν e he ρ hρ hρE hρe t ht
    (D.eps (G.level - 1)) hρE hflow
  have hBj d (_hd : d ∈ Finset.Icc dout (G.fam.identity v u γ).maxOrder) I i j
      (hj : j ≤ n) y :
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => B d I x i) y‖ ≤
        Cs * (ν * e ^ (d - 2)) * ∑ c, θ d I c := by
    have hp := (hs d I i).2 j (hj.trans hnn) y
    have habs : ‖ν * e ^ (d - 2)‖ = ν * e ^ (d - 2) :=
      Real.norm_of_nonneg (mul_nonneg hν.le (pow_nonneg he.le _))
    rw [habs] at hp
    apply hp.trans
    apply mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun c _ => hθ d I c) (Finset.mem_univ i))
      (mul_nonneg hCs (mul_nonneg hν.le (pow_nonneg he.le _)))
  have hK a b : ContDiff ℝ (⊤ : ℕ∞) (fun y =>
      naturalPreparationJacobian (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) t y a b) :=
    (naturalPreparationJacobian_entry_smooth (D.hΦ (G.level - 1))
      (D.slotAnchor G.level p.1) a b).comp (contDiff_const.prodMk contDiff_id)
  exact native_transport_record_price _ hK N (G.fam.identity v u γ).maxOrder Dmax Kmax n dout
    hD hkn hdout hout C (D.eps (G.level - 1)) ρ ν e R r Cs hC hE hρ.le hρE
    hν he.le hR hrpos hRE hCs hn hKC B (fun d I c => (hs d I c).1.of_le (by exact_mod_cast hnn))
    (fun d I => ∑ c, θ d I c) (fun d I => Finset.sum_nonneg fun c _ => hθ d I c)
    hBj (G.fam.identity v u γ).record.size (G.fam.identity v u γ).record.size_nonneg
    (by simpa only [heActual, hRActual] using hledger) (G.fam.identity v u γ).map x

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.Construction.Preservation.FullLift

/-! Express the global metric jet budget at the literal physical preparation radius. -/

theorem uniform_native_lift_metric_radius_sup_all_carriers (α s q : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (K : ℕ) :
    ∃ CG : ℕ → ℝ, (∀ n, 0 ≤ CG n) ∧ ∃ M : ℕ, 2 ≤ M ∧ ∀ (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
      [∀ i, NormedSpace ℝ (h i)] (Dm : ℕ), ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ m, M + 1 ≤ m → ∀ slot : ℤ, Odd slot → ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ edge : ConstituentEdges Dm h, ∀ n ≤ K,
      (⨆ t ∈ Set.Icc (D.slotStart m slot / D.cellScaleSq m)
        ((((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m),
        ⨆ X : Vec 2, ‖iteratedFDeriv ℝ n (fun Y =>
          (familyLiftData D m slot (nativeChain m slot) ρ edge).G t Y) X‖ₑ) ≤
        ENNReal.ofReal (CG n * (ρ / D.eps (m - 1)) ^ n) := by
  obtain ⟨CG, hCG, M, hM, hb⟩ :=
    uniform_native_lift_metric_sup_all_carriers α s q hα0 hα1 hs0 hs1 hq Λ hΛ ζ hζ K
  refine ⟨CG, hCG, M, hM, ?_⟩
  intro ι h _ _ Dm D hDα hDq hDΛ hDζ hseq hband m hm slot hslot ρ hρ edge n hn
  have hE : 0 < D.eps (m - 1) := by
    unfold OCData.eps
    exact Construction.Stream.ocEpsilon_pos (by rw [hDΛ]; omega)
  have hscale : D.eps (m - 1) * (ρ / D.eps (m - 1)) = ρ := by
    field_simp
  simpa only [hscale] using hb ι h Dm D hDα hDq hDΛ hDζ hseq hband m hm slot hslot
    (ρ / D.eps (m - 1)) (div_nonneg hρ hE.le) edge n hn

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.Construction.Preservation.FullLift

/-! The actual restricted setting discharges the smooth-input premises of ambient-cap promotion. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D Ksrc H N K k L qs qf : ℕ} {hKD : Ksrc ≤ D} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {price : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting (EntryWeakProofs.restrictLiftData Ksrc hKD Q) π a b e ν B ρ E ℓ dstar εc lam
    par V H N K k L qs qf CG Cw Cj price Θ)

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, MeasurableSpace (h i)] in
include P in
theorem effective_setting_source_good
    (hz : ∀ v u d, Ksrc < d.1 → Q.edge v u d = []) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ I,
      GoodField 1 (fun X z => γ.coeff I t X z) := by
  intro v u d γ hγ I
  have hd : d.1 ≤ Ksrc := by
    by_contra hh
    have he := hz v u d (by omega)
    rw [he] at hγ
    exact List.not_mem_nil hγ
  let dk : Finset.Icc 2 Ksrc := ⟨d.1, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp d.2).1, hd⟩⟩
  have hmem : γ ∈ (EntryWeakProofs.restrictLiftData Ksrc hKD Q).edge v u dk := by
    change γ ∈ Q.edge v u ⟨dk.1, _⟩
    exact hγ
  have hs := P.coeff_smooth v u dk γ hmem I t ht
  have hbox := hs.mono (setting_source_slow_reserve P)
    ((show 1 ≤ Ksrc by have hh := P.D_ge; omega).trans (setting_source_fast_reserve P))
  exact ⟨hbox.contDiff_uncurry le_rfl le_rfl, γ.periodic I t⟩

include P in
theorem effective_setting_predecessor_good (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence (EntryWeakProofs.restrictLiftData Ksrc hKD Q) sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∀ p ≤ hh, ∀ m ≤ n, ∀ j ∈ Finset.range (min D m + 1),
      GoodField Ksrc (liftApply (m - j) (Cc (p - 1) (m - j)) (fun _ => f) t) := by
  intro p hp m hm j _
  exact setting_liftApply_goodField_D P sX sZ hsZ Cc hseq (p - 1) (by omega)
    (m - j) (by omega) f hf t ht
end

/-! A lift on its true source degree is the original ambient-cap lift at every allocated cell order. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {D Ksrc H N K k L qs qf : ℕ} {hKD : Ksrc ≤ D} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {price : ι → ι → ℝ} {Θ : ℝ}

theorem effective_liftSequence_promote
    (P : IsLiftSetting (EntryWeakProofs.restrictLiftData Ksrc hKD Q) π a b e ν B ρ E ℓ dstar εc lam
      par V H N K k L qs qf CG Cw Cj price Θ)
    (hz : ∀ v u d, Ksrc < d.1 → Q.edge v u d = []) (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence (EntryWeakProofs.restrictLiftData Ksrc hKD Q) sX sZ a b N H Cc) :
    IsLiftSequence Q sX sZ a b N H Cc := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1,
    hc.2.2.2.2.2.1, ?_⟩
  intro hh hhh n hn hnN f hf X
  have hi := hc.2.2.2.2.2.2 hh hhh n hn hnN f hf X
  apply cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _ hi
  intro t ht
  funext z
  have he := liftCellSource_restrict_all_degrees Ksrc
    (show 1 ≤ Ksrc by have hd := P.D_ge; omega) hKD Q hz Cc (fun _ => f) hh n t
    (effective_setting_predecessor_good P sX sZ hsZ Cc hc hh n hhh hnN f hf t ht)
    (effective_setting_source_good P hz t ht)
  exact (congrFun (congrFun he X) z).symm
end

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! The literal physical coefficient keeps its original context-certified record kernel price. -/

open CycleJointProofs

theorem context_certified_physical_kernel_price (bw : ℝ) (hb : 0 < bw) (n : ℕ)
    (Cchart : ℝ) (hchart : 1 ≤ Cchart) :
    ∃ Csample : ℝ, 0 ≤ Csample ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ (D : OCData) (Dm j₀ M : ℕ) (G : GenStage D hr Dm bw j₀) (k : InvConsts),
      G.IsContextCertified k → G.IsNatural M → ∀ (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
      0 < D.eps (G.level - 1) → 0 < D.eps G.level → 0 < D.kap G.level →
      G.IsSlotTransverse → ∀ (a b : ℝ) (v u : CompIn G.comps) (γ : G.fam.Γ v u),
      0 ≤ compReserve k v.1 → compReserve k v.1 ≤ 2 →
      ∀ (N Dmax dout : ℕ), (G.fam.identity v u γ).maxOrder ≤ Dmax →
      2 ≤ dout → dout ≤ Dmax → n + (G.fam.identity v u γ).maxOrder ≤ N →
      ∀ (C ρ r : ℝ), 1 ≤ C → 0 < ρ → 0 < r →
      ρ ≤ D.eps (G.level - 1) → ρ ≤ D.eps G.level →
      (3 ≤ (G.fam.identity v u γ).maxOrder →
        (G.fam.identity v u γ).record.length ≤ D.eps (G.level - 1)) →
      (∀ t ∈ Set.Icc a b, ∀ p : OddSlot, t ∈ (G.fam.piece p).output →
        ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)
          n Cchart (D.eps (G.level - 1))) →
      (∀ t ∈ Set.Icc a b, ∀ p : OddSlot, t ∈ (G.fam.piece p).output →
        ∀ a b j, j ≤ N → ∀ x, D.eps (G.level - 1) ^ j * ‖iteratedFDeriv ℝ j
          (fun y => naturalPreparationJacobian (D.hΦ (G.level - 1))
            (D.slotAnchor G.level p.1) t y a b) x‖ ≤ C) →
      (coefficientSeminorm ρ n a b (G.physCoeff v u γ dout)).toReal /
        (D.kap G.level * r ^ (dout - 2)) ≤
          (4 * (2 : ℝ) ^ Dmax * ‖(G.fam.identity v u γ).map‖ *
            (((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C *
              (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ Dmax) * Csample *
                max 1 (((G.fam.identity v u γ).record.length / r) ^ ((G.fam.identity v u γ).maxOrder - 2)) *
                  ((G.fam.identity v u γ).maxOrder : ℝ) * (G.fam.identity v u γ).record.size) *
                    (∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j / (j.factorial : ℝ)) := by
  obtain ⟨Cs, hCs, htransport⟩ := context_certified_transport_record_price bw hb n Cchart hchart
  refine ⟨Cs, hCs, ?_⟩
  intro hr _ _ D Dm j₀ M G k hG hnat hi hj hE he hν hpar a b v u γ hm hm2
    N Dmax dout hD hdout hout hn C ρ r hC hρ hrpos hρE hρe hRE hflow hKC
  let P := 4 * (2 : ℝ) ^ Dmax * ‖(G.fam.identity v u γ).map‖ *
    (((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C *
      (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ Dmax) * Cs *
        max 1 (((G.fam.identity v u γ).record.length / r) ^ ((G.fam.identity v u γ).maxOrder - 2)) *
          ((G.fam.identity v u γ).maxOrder : ℝ) * (G.fam.identity v u γ).record.size
  have hP : 0 ≤ P := by
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    have hsize := (G.fam.identity v u γ).record.size_nonneg
    have hR := (G.fam.identity v u γ).record.length_pos
    dsimp only [P]
    positivity
  apply native_physical_kernel_price_of_raw_prices hG hpar hnat hi hj hb hE hν a b
    v u γ hm hm2 n dout ρ r P hρ hrpos hP
  intro t ht p hp j hjn y
  have hwindow : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 := by
    rwa [← (hnat.1 p).2.1]
  exact htransport hr D Dm j₀ G k hG hi hj hE hpar v u γ hm hm2 p (hnat.2.2.1 p)
    N Dmax n j dout hjn hD hjn hdout hout (by omega)
    C (D.kap G.level) (D.eps G.level) ρ (G.fam.identity v u γ).record.length r rfl rfl
    hC hν he hρ hρE hρe (G.fam.identity v u γ).record.length_pos hrpos hRE
    t hwindow (hflow t ht p hp) (hKC t ht p hp) y

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization
open scoped ENNReal Matrix Matrix.Norms.Elementwise
namespace AVRegularity.Construction.Preservation.FullLift

/-! Choose native analytic constants and one level threshold before the carrier, data and slot. -/

theorem uniform_native_lift_analytic_certificates {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ qs : ℕ,
      ∃ CG Cw : ℕ → ℝ, (∀ r, 0 ≤ CG r) ∧ (∀ r, 0 ≤ Cw r) ∧
      ∃ m₀ : ℕ, 2 ≤ m₀ ∧
      ∀ (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
        [∀ i, NormedSpace ℝ (h i)] (Dm : ℕ) (D : OCData),
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ m, m₀ ≤ m → m < D.term → ∀ slot : ℤ, Odd slot →
      ∀ ρ, 0 ≤ ρ → ∀ edge : ConstituentEdges Dm h,
      let Q := familyLiftData D m slot (nativeChain m slot) ρ edge
      let a := D.slotStart m slot / D.cellScaleSq m
      let b := (((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m
      (∀ r ≤ qs, (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => Q.G t Y) X‖ₑ) ≤
          ENNReal.ofReal (CG r * (ρ / D.eps (m - 1)) ^ r)) ∧
      (∀ t ∈ Set.Icc a b, ∀ X ξ : Vec 2,
        (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ∧
        ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2) ∧
      (∀ r : ℕ, (⨆ t ∈ Set.Icc a b, ⨆ z : Vec 2,
        ‖iteratedFDeriv ℝ r (fun y => Real.sqrt Q.η • Q.v t y) z‖ₑ) ≤
          ENNReal.ofReal (Cw r)) := by
  obtain ⟨Cw, hCw, Λ₀, hΛ₀, hw⟩ :=
    uniform_native_lift_balanced_drift_sup_all_carriers hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ qs
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛ
  obtain ⟨CG, hCG, MG, hMG, hG⟩ := uniform_native_lift_metric_radius_sup_all_carriers
    α s q hα0 hα1 hs0 hs1 hq Λ hΛ128 ζ hζ qs
  obtain ⟨ME, hME, hEllip⟩ := uniform_native_lift_ellipticity_all_carriers
    α s q hα0 hα1 hs0 hs1 hq Λ hΛ128 ζ hζ
  refine ⟨CG, Cw, hCG, hCw, max MG ME + 1, by omega, ?_⟩
  intro ι h _ _ Dm D hDα hDq hDΛ hDζ hseq hband m hm hmM slot hslot ρ hρ edge Q a b
  have hΛD : Λ₀ ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hband' : IsOCBandChain α q D.Λ ζ D.term D.κ := by
    simpa only [hDα, hDq, hDζ] using hband
  refine ⟨?_, ?_, ?_⟩
  · exact hG ι h Dm D hDα hDq hDΛ hDζ hseq hband m (by omega) slot hslot ρ hρ edge
  · exact hEllip ι h Dm D hDα hDq hDΛ hDζ hseq hband m (by omega) slot hslot ρ edge
  · exact hw ι h Dm D hDα hDq hΛD hDζ hband' m (by omega) hmM slot hslot
      (nativeChain m slot) ρ edge a b

end AVRegularity.Construction.Preservation.FullLift
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift

/-! Higher native existence from strict order-zero absorption and finite smooth coefficient prices. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_exists_higher_of_context (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ} {k : ℕ}
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν 0 Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    (hθ : R.θ < 1 / 8)
    {kI : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified kI) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (hρε : ρ ≤ D.eps (G.level - 1))
    (hm : ∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1)
    (hm2 : ∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root)) :
    ∃ (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
      (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
      (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)),
      G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
        (fun _ _ => 0) (fun _ _ => 0) U W Y := by
  have hfin : ∀ i j γ d, coefficientSeminorm ρ k a b (R.B i j γ d) ≠ ⊤ := by
    intro i j γ d
    rw [hB]
    exact native_physCoeff_all_order_seminorm_finite hG hpar hnat hi hj hb hε a b
      i j γ (hm i) (hm2 i) ρ R.radius_pos hρε k d.1
  have hsmooth : ∀ i j γ d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (k : ℕ) (R.B i j γ d t) := by
    intro i j γ d t ht
    rw [hB]
    exact native_physCoeff_all_order_smooth hG hpar hnat hi hj hb hε a b
      i j γ (hm i) (hm2 i) k d.1 t ht
  exact native_reg_solution_exists_higher P seedK freshK φ₀ hφ₀ G R hB hC hS hθ
    hfin hsmooth hφ α B lam hα hBdrift hlam hsmall hstrain hjets f
end

/-! Higher native existence from strict order-zero absorption and finite smooth coefficient prices. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_higher_extension_of_context (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ} {k l : ℕ} (hkl : k ≤ l)
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν 0 Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    (hθ : R.θ < 1 / 8)
    {kI : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified kI) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (hρε : ρ ≤ D.eps (G.level - 1))
    (hm : ∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1)
    (hm2 : ∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ j, 1 ≤ j → j ≤ l → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) j x‖ ≤
        α * B ^ j * (j.factorial : ℝ) * lam ^ ((1 : ℤ) - j))
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y)
    (fhi : ∀ v : CompIn G.comps, TorusHk l (hr v.1.root))
    (hinit : ∀ v, truncateTorusHk hkl (fhi v) = f v) :
    ∃ (Uhi : ∀ v : CompIn G.comps, ℝ → TorusHk l (hr v.1.root)),
      ∀ v, ∀ t ∈ Set.Icc a b, U v t = truncateTorusHk hkl (Uhi v t) := by
  obtain ⟨Uhi, Whi, Yhi, hhi⟩ := native_reg_solution_exists_higher_of_context P seedK freshK
    φ₀ hφ₀ G R hB hC hS hθ hG hpar hnat hi hj hb hε hρε hm hm2 hφ
    α B lam hα hBdrift hlam hsmall hstrain hjets fhi
  refine ⟨Uhi, ?_⟩
  exact native_reg_solution_eq_higher_truncate_from_zero P seedK freshK φ₀ hφ₀ G R
    hB hC hS hφ α B lam hα hBdrift hlam hsmall hstrain
    f U W Y hsol hkl fhi Uhi Whi Yhi hhi hinit
end

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal Matrix Matrix.Norms.Elementwise
namespace AVRegularity.Construction.Preservation.FullLift

/-! Assemble the literal native setting from its separately proved scale and analytic certificates.
The source is extended measurably and restricted to its actual finite degree; the metric and
drift remain the original native ones. -/

open EntryWeakProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Assemble the native setting from actual fibre facts. The edge degree and certificates
need not come from a strictly interior generated stage. This also permits an empty family
at the minimal effective degree when its original ambient degree is smaller. -/
theorem native_lift_setting_of_fiber_facts
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ v, NormedAddCommGroup (h v)] [∀ v, InnerProductSpace ℝ (h v)] {Dc : ℕ}
    (D : OCData) (m : ℕ) (hi : 1 ≤ m)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (slot : OddSlot) (ρ : ℝ) (hρ : 0 < ρ)
    (hcell : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ ≤ 1)
    (hlam : ρ / D.eps (m - 1) ≤ 1)
    (Q : LiftOperatorData ι h Dc)
    (hη : Q.η = D.kap m / D.kap (m - 1))
    (hG : Q.G = (familyLiftData D m slot.1 (nativeChain m slot.1) ρ Q.edge).G)
    (hv : Q.v = (familyLiftData D m slot.1 (nativeChain m slot.1) ρ Q.edge).v)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (H N K k L : ℕ) (hN : 1 ≤ N) (hDc : 2 ≤ Dc)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (price : ι → ι → ℝ) (Θ : ℝ) :
    let a := D.slotStart m slot.1 / D.cellScaleSq m
    let b := (((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m
    let qs := K + 4 * (H + 1) * (N + Dc) ^ 2
    let qf := max k (L + 2) + H * Dc + 2 * N + 2 * Dc
    (∀ t ∈ Set.Icc a b, ∀ X ξ : Vec 2,
      (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ∧
      ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2) →
    (∀ r ≤ qs, (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
      ‖iteratedFDeriv ℝ r (fun Y => Q.G t Y) X‖ₑ) ≤
        ENNReal.ofReal (CG r * (ρ / D.eps (m - 1)) ^ r)) →
    (∀ q ≤ qf, (⨆ t ∈ Set.Icc a b, ⨆ z : Vec 2,
      ‖iteratedFDeriv ℝ q (fun y => Real.sqrt Q.η • Q.v t y) z‖ₑ) ≤
        ENNReal.ofReal (Cw q)) →
    HasDepthAtMost Q.edge H →
    (∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsTransverseOn (pulseParallel slot.1) (Set.Icc a b) (γ.coeff α)) →
    (∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z, Measurable fun t => γ.coeff α t X z) →
    (∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α, ∀ t ∈ Set.Icc a b,
      IsBoxSmooth qs qf (γ.coeff α t)) →
    IsScaledJetEnvelope π Q.edge (Set.Icc a b) (ρ / D.eps (m - 1)) Cj qs qf price Θ →
    IsLiftSetting Q π a b (D.eps m) (D.kap m) (D.kap (m - 1)) ρ
      (D.eps (m - 1)) (D.eps m / Real.sqrt (D.kap m))
      (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)))
      (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ)
      (ρ / D.eps (m - 1)) (pulseParallel slot.1)
      (pulseShearProfile D.α D.q D.Λ m D.ζ (D.kap m) slot.1)
      H N K k L qs qf CG Cw Cj price Θ := by
  intro a b qs qf hellip hGjets hwjets hdepth htrans hcoeff hbox hsource
  have hν := weakData_kap_pos D hΛ hζ hband m
  have hB := weakData_kap_pos D hΛ hζ hband (m - 1)
  have hc := weakData_cellScaleSq_pos D hΛ hζ hband m
  have hτ := Construction.Stream.ocTau_pos (α := D.α) (q := D.q) hΛ (m := m)
  have hab : a ≤ b := by
    apply (div_le_div_iff_of_pos_right hc).mpr
    dsimp only [OCData.slotStart]
    exact mul_le_mul_of_nonneg_right (by linarith) hτ.le
  obtain ⟨hsym, hmeas, hsmooth⟩ := native_lift_metric_qualitative D hζ m slot.1 ρ Q.edge
  obtain ⟨hshear, hVsmooth, hVper, hVmean, hvmeas⟩ :=
    native_lift_shear_qualitative D hΛ hζ hband m slot.1 slot.2
      (nativeChain m slot.1) ρ Q.edge
  refine {
    window := hab
    e_pos := Construction.Stream.ocEpsilon_pos hΛ
    ν_pos := hν
    B_pos := hB
    ρ_pos := hρ
    E_pos := Construction.Stream.ocEpsilon_pos hΛ
    ℓ_eq := rfl
    η_eq := hη
    η_le := ?_
    dstar_eq := native_dstar_eq D m hB.le
    εc_eq := rfl
    εc_le := hcell
    lam_eq := rfl
    lam_le := hlam
    N_ge := hN
    D_ge := hDc
    qs_eq := rfl
    qf_eq := rfl
    mass_pos := hπ
    G_symm := hG.symm ▸ hsym
    G_meas := hG.symm ▸ hmeas
    G_smooth := hG.symm ▸ (fun t _ i j => (hsmooth t i j).of_le (by simp))
    G_ellip := hellip
    G_jets := hGjets
    v_shear := hv.symm ▸ hshear
    V_smooth := fun t _ => (hVsmooth t).of_le (by simp)
    V_per := fun t _ => hVper t
    V_mean := fun t _ => hVmean t
    v_meas := hv.symm ▸ hvmeas
    w_jets := hwjets
    depth := hdepth
    transverse := htrans
    coeff_meas := hcoeff
    coeff_smooth := hbox
    envelope := hsource }
  rw [hη]
  exact (div_le_one hB).mpr (native_kap_step_le D hΛ hζ hband m hi)

theorem native_lift_setting_of_certificates
    (G : GenStage D hr Dm bw j₀) (kI : InvConsts) (M : ℕ)
    (hcert : G.IsContextCertified kI) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hm : ∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1)
    (hm2 : ∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2)
    (slot : OddSlot) (ρ : ℝ) (hρ : 0 < ρ)
    (hcell : ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ ≤ 1)
    (hlam : ρ / D.eps (G.level - 1) ≤ 1)
    (π : CompIn G.comps → ℝ) (hπ : ∀ v, 0 < π v)
    (H N K k L Ksrc : ℕ) (hN : 1 ≤ N) (hKsrc : 2 ≤ Ksrc) (hKD : Ksrc ≤ Dm)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (price : CompIn G.comps → CompIn G.comps → ℝ)
    (Θ : ℝ) :
    let a := D.slotStart G.level slot.1 / D.cellScaleSq G.level
    let b := (((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let Q := familyLiftData D G.level slot.1 (nativeChain G.level slot.1) ρ
      (G.fam.fiber slot (G.actual slot))
    let qs := K + 4 * (H + 1) * (N + Ksrc) ^ 2
    let qf := max k (L + 2) + H * Ksrc + 2 * N + 2 * Ksrc
    G.fam.HasDepthAtMost H →
    (∀ v u d, Ksrc < d.1 → Q.edge v u d = []) →
    (∀ t ∈ Set.Icc a b, ∀ X ξ : Vec 2,
      (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ∧
      ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2) →
    (∀ r ≤ qs, (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
      ‖iteratedFDeriv ℝ r (fun Y => Q.G t Y) X‖ₑ) ≤
        ENNReal.ofReal (CG r * (ρ / D.eps (G.level - 1)) ^ r)) →
    (∀ q ≤ qf, (⨆ t ∈ Set.Icc a b, ⨆ z : Vec 2,
      ‖iteratedFDeriv ℝ q (fun y => Real.sqrt Q.η • Q.v t y) z‖ₑ) ≤
        ENNReal.ofReal (Cw q)) →
    IsScaledJetEnvelope π Q.edge (Set.Icc a b) (ρ / D.eps (G.level - 1)) Cj qs qf price Θ →
    IsLiftSetting (restrictLiftData Ksrc hKD {Q with edge := windowEdges a b Q.edge})
      π a b (D.eps G.level) (D.kap G.level) (D.kap (G.level - 1)) ρ
      (D.eps (G.level - 1)) (D.eps G.level / Real.sqrt (D.kap G.level))
      (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)))
      (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ)
      (ρ / D.eps (G.level - 1)) (pulseParallel slot.1)
      (pulseShearProfile D.α D.q D.Λ G.level D.ζ (D.kap G.level) slot.1)
      H N K k L qs qf CG Cw Cj price Θ := by
  intro a b Q qs qf hdepth hz hellip hGjets hwjets hsource
  have hE : 0 < D.eps (G.level - 1) := Construction.Stream.ocEpsilon_pos hΛ
  have hc := weakData_cellScaleSq_pos D hΛ hζ hband G.level
  have hτ := Construction.Stream.ocTau_pos (α := D.α) (q := D.q) hΛ (m := G.level)
  have hab : a ≤ b := by
    apply (div_le_div_iff_of_pos_right hc).mpr
    dsimp only [OCData.slotStart]
    exact mul_le_mul_of_nonneg_right (by linarith) hτ.le
  have htrans := windowEdges_transverse a b Q.edge (slotParallel slot.1)
    (native_lift_fiber_transverse G hpar hΛ hζ hband slot ρ)
  have hcoeff := windowEdges_coefficient_measurable a b hab Q.edge
    (native_lift_fiber_measurable G kI hcert slot ρ hΛ hζ hband)
  have hbox := windowEdges_boxSmooth a b Q.edge qs qf
    (native_lift_fiber_boxSmooth hcert hpar hnat hi hj hb hE hΛ hζ hband hm hm2 slot ρ qs qf)
  apply native_lift_setting_of_fiber_facts D G.level hi hΛ hζ hband slot ρ hρ hcell hlam
    (restrictLiftData Ksrc hKD {Q with edge := windowEdges a b Q.edge}) rfl rfl rfl
    π hπ H N K k L hN hKsrc CG Cw Cj price Θ
    hellip hGjets hwjets
  · exact restrictSource_depth Ksrc hKD (windowEdges a b Q.edge)
      (windowEdges_depth a b Q.edge
        (liftEdges_depth _ _ _ (chartedFiber_depth G.fam slot (G.actual slot) hdepth)))
  · intro v u d γ hγ α
    have heq : slotParallel slot.1 = pulseParallel slot.1 := by
      have hodd := slot.2
      have hmod : slot.1 % 4 = 1 ∨ slot.1 % 4 = 3 := by
        obtain ⟨r, hr⟩ := hodd
        omega
      rcases hmod with h1 | h3
      · simp only [slotParallel, pulseParallel, h1]
        norm_num
      · simp only [slotParallel, pulseParallel, h3]
        norm_num
    rw [← heq]
    exact htrans v u (degreeRangeInclusion Ksrc Dm hKD d) γ hγ α
  · intro v u d γ hγ α X z
    exact hcoeff v u (degreeRangeInclusion Ksrc Dm hKD d) γ hγ α X z
  · intro v u d γ hγ α t ht
    exact hbox v u (degreeRangeInclusion Ksrc Dm hKD d) γ hγ α t ht
  · exact restrictSource_scaled_envelope Ksrc hKD _
      (fun v u d hd => (windowEdges_empty_iff a b Q.edge v u d).mpr (hz v u d hd))
      π _ _ Cj qs qf price Θ (windowEdges_scaled_envelope a b _ π Q.edge Cj qs qf price Θ hsource)

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Uniform stream estimates supply the literal physical coefficient record kernel price. -/

open CycleJointProofs

theorem uniform_native_physical_kernel_price (α s q : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (bw : ℝ) (hb : 0 < bw) (n N : ℕ) :
    ∃ C Csample : ℝ, 1 ≤ C ∧ 0 ≤ Csample ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → ∀ (Dm j₀ M : ℕ) (G : GenStage D hr Dm bw j₀) (k : InvConsts),
      G.IsContextCertified k → G.IsNatural M → m₀ + 1 ≤ G.level →
      ∀ (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
      0 < D.eps (G.level - 1) → 0 < D.eps G.level → 0 < D.kap G.level →
      G.IsSlotTransverse → ∀ (a b : ℝ) (v u : CompIn G.comps) (γ : G.fam.Γ v u),
      0 ≤ compReserve k v.1 → compReserve k v.1 ≤ 2 →
      ∀ (Dmax dout : ℕ), (G.fam.identity v u γ).maxOrder ≤ Dmax →
      2 ≤ dout → dout ≤ Dmax → n + (G.fam.identity v u γ).maxOrder ≤ N →
      ∀ (ρ r : ℝ), 0 < ρ → 0 < r →
      ρ ≤ D.eps (G.level - 1) → ρ ≤ D.eps G.level →
      (3 ≤ (G.fam.identity v u γ).maxOrder →
        (G.fam.identity v u γ).record.length ≤ D.eps (G.level - 1)) →
      (coefficientSeminorm ρ n a b (G.physCoeff v u γ dout)).toReal /
        (D.kap G.level * r ^ (dout - 2)) ≤
          (4 * (2 : ℝ) ^ Dmax * ‖(G.fam.identity v u γ).map‖ *
            (((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C *
              (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ Dmax) * Csample *
                max 1 (((G.fam.identity v u γ).record.length / r) ^ ((G.fam.identity v u γ).maxOrder - 2)) *
                  ((G.fam.identity v u γ).maxOrder : ℝ) * (G.fam.identity v u γ).record.size) *
                    (∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j / (j.factorial : ℝ)) := by
  let Cchart := EntryWeakProofs.weakChartJetBudget n 0
  have hchart : 1 ≤ Cchart := EntryWeakProofs.weakChartJetBudget_ge_one _ _
  obtain ⟨C, hC, Mp, hMp, hmatrix⟩ := uniform_native_piola_matrix_jets α s q
    hα0 hα1 hs0 hs1 hq Λ hΛ ζ hζ N
  obtain ⟨Mf, hMf, hflow⟩ := uniform_native_physical_flow_jets α s q
    hα0 hα1 hs0 hs1 hq Λ hΛ ζ hζ n
  obtain ⟨Cs, hCs, hphysical⟩ := context_certified_physical_kernel_price bw hb n Cchart hchart
  refine ⟨C, Cs, hC, hCs, max Mp Mf, hMp.trans (le_max_left _ _), ?_⟩
  intro hr _ _ D hDα hDq hDΛ hDζ hseq Dm j₀ M G k hG hnat hlevel hi hj hE he hν hpar
    a b v u γ hm hm2 Dmax dout hD hdout hout hn ρ r hρ hrpos hρE hρe hRE
  apply hphysical hr D Dm j₀ M G k hG hnat hi hj hE he hν hpar a b v u γ hm hm2
    N Dmax dout hD hdout hout hn C ρ r hC hρ hrpos hρE hρe hRE
  · intro t _ht p hp
    have hwindow : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 := by
      rwa [← (hnat.1 p).2.1]
    exact (hflow D hDα hDq hDΛ hDζ hseq G.level (by omega) p.1 p.2
      (D.eps (G.level - 1)) hE (le_refl _) t hwindow).2
  · intro t _ht p hp
    have hwindow : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 := by
      rwa [← (hnat.1 p).2.1]
    exact hmatrix D hDα hDq hDΛ hDζ hseq G.level (by omega) hE p.1 p.2 t hwindow

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Construction.Preservation.FullLift

/-! Uniform literal identity prices are paid once by the original inflated birth record. -/

theorem uniform_native_identity_kernel_price (α s q : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (bw : ℝ) (hb : 0 < bw) (n N Dm : ℕ)
    (hN : n + Dm ≤ N) (c : ℕ → ℝ) (hc : ∀ j, j + 2 ≤ Dm → 0 ≤ c j) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → ∀ (j₀ M : ℕ) (G : GenStage D hr Dm bw j₀) (k : InvConsts),
      G.IsContextCertified k → G.IsNatural M → m₀ + 1 ≤ G.level →
      ∀ (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
      0 < D.eps (G.level - 1) → 0 < D.eps G.level → 0 < D.kap G.level →
      G.IsSlotTransverse → ∀ (a b : ℝ) (v u : CompIn G.comps) (γ : G.fam.Γ v u),
      0 ≤ compReserve k v.1 → compReserve k v.1 ≤ 2 →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ D.eps (G.level - 1) → ρ ≤ D.eps G.level →
      (3 ≤ (G.fam.identity v u γ).maxOrder →
        (G.fam.identity v u γ).record.length ≤ D.eps (G.level - 1)) →
      (∑ d : ↥(Finset.Icc 2 Dm),
        ((coefficientSeminorm ρ n a b (G.physCoeff v u γ d.1)).toReal * c (d.1 - 2)) /
          (D.kap G.level * (G.fam.identity v u γ).record.width ^ (d.1 - 2))) ≤
        A * (‖(G.fam.identity v u γ).map‖ * (G.fam.identity v u γ).record.size *
          constituentPrice (G.fam.identity v u γ).record) := by
  obtain ⟨C, Cs, hC, hCs, m₀, hm₀, hphysical⟩ := uniform_native_physical_kernel_price
    α s q hα0 hα1 hs0 hs1 hq Λ hΛ ζ hζ bw hb n N
  let Ct := (((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C *
    (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ Dm)
  let T := ∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j / (j.factorial : ℝ)
  let B := 4 * (2 : ℝ) ^ Dm * Ct * Cs * (Dm : ℝ) * T
  let S := ∑ d : ↥(Finset.Icc 2 Dm), c (d.1 - 2)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCt : 0 ≤ Ct := by dsimp [Ct]; positivity
  have hT : 0 ≤ T := Finset.sum_nonneg fun j _ =>
    div_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg fun d _ => hc _ (by
    have hd := Finset.mem_Icc.mp d.property
    omega)
  refine ⟨S * B, mul_nonneg hS hB, m₀, hm₀, ?_⟩
  intro hr _ _ D hDα hDq hDΛ hDζ hseq j₀ M G k hG hnat hlevel hi hj hE he hν hpar
    a b v u γ hm hm2 ρ hρ hρE hρe hlength
  have hcoef (d : ↥(Finset.Icc 2 Dm)) :
      (coefficientSeminorm ρ n a b (G.physCoeff v u γ d.1)).toReal /
          (D.kap G.level * (G.fam.identity v u γ).record.width ^ (d.1 - 2)) ≤
        B * (‖(G.fam.identity v u γ).map‖ * (G.fam.identity v u γ).record.size *
          constituentPrice (G.fam.identity v u γ).record) := by
    have horder := (G.fam.identity v u γ).le_D
    have hp := hphysical hr D hDα hDq hDΛ hDζ hseq Dm j₀ M G k hG hnat hlevel hi hj
      hE he hν hpar a b v u γ hm hm2 Dm d.1 horder
      (Finset.mem_Icc.mp d.property).1 (Finset.mem_Icc.mp d.property).2 (by omega)
      ρ (G.fam.identity v u γ).record.width hρ (G.fam.identity v u γ).record.width_pos
      hρE hρe hlength
    have hcost := constituentPrice_order_bound (G.fam.identity v u γ).record
      ((G.fam.identity v u γ).maxOrder - 2) (by
        have := (G.fam.identity v u γ).le_birth
        omega)
    have horderR : ((G.fam.identity v u γ).maxOrder : ℝ) ≤ (Dm : ℝ) := by exact_mod_cast horder
    have hsize := (G.fam.identity v u γ).record.size_nonneg
    have hprice0 := constituentPrice_nonneg (G.fam.identity v u γ).record
    apply hp.trans
    calc
      _ ≤ (4 * (2 : ℝ) ^ Dm * ‖(G.fam.identity v u γ).map‖ * Ct * Cs *
          constituentPrice (G.fam.identity v u γ).record * (Dm : ℝ) *
          (G.fam.identity v u γ).record.size) * T := by
        change (4 * (2 : ℝ) ^ Dm * ‖(G.fam.identity v u γ).map‖ * Ct * Cs *
          max 1 (((G.fam.identity v u γ).record.length / (G.fam.identity v u γ).record.width) ^
            ((G.fam.identity v u γ).maxOrder - 2)) *
          ((G.fam.identity v u γ).maxOrder : ℝ) * (G.fam.identity v u γ).record.size) * T ≤ _
        gcongr
      _ = _ := by dsimp [B]; ring
  calc
    _ = ∑ d : ↥(Finset.Icc 2 Dm), c (d.1 - 2) *
        ((coefficientSeminorm ρ n a b (G.physCoeff v u γ d.1)).toReal /
          (D.kap G.level * (G.fam.identity v u γ).record.width ^ (d.1 - 2))) := by
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ ∑ d : ↥(Finset.Icc 2 Dm), c (d.1 - 2) *
        (B * (‖(G.fam.identity v u γ).map‖ * (G.fam.identity v u γ).record.size *
          constituentPrice (G.fam.identity v u γ).record)) := by
      apply Finset.sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left (hcoef d) (hc _ (by
        have hd := Finset.mem_Icc.mp d.property
        omega))
    _ = _ := by rw [← Finset.sum_mul]; dsimp only [S]; ring

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Uniform actual production Schur estimates from the context certificate and original priced ledger. -/

theorem uniform_native_kernel_schur_of_certificates (α s q : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (bw : ℝ) (hb : 0 < bw) (n N Dm : ℕ)
    (hN : n + Dm ≤ N) (c : ℕ → ℝ) (hc : ∀ j, j + 2 ≤ Dm → 0 ≤ c j) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → ∀ (j₀ M : ℕ) (G : GenStage D hr Dm bw j₀) (k : InvConsts),
      G.IsContextCertified k → G.IsNatural M → m₀ + 1 ≤ G.level →
      ∀ (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
      0 < D.eps (G.level - 1) → 0 < D.eps G.level → 0 < D.kap G.level →
      G.IsSlotTransverse → (∀ v : CompIn G.comps, 0 ≤ compReserve k v.1) →
      (∀ v : CompIn G.comps, compReserve k v.1 ≤ 2) →
      ∀ (P : ProvParams) (seedK freshK : ℕ → KernelSpec),
      (∀ v u γ, (G.kernelOf P seedK freshK v u γ).width = (G.fam.identity v u γ).record.width) →
      ∀ (a b ρ Sbound : ℝ) (π marker : CompIn G.comps → ℝ),
      0 < ρ → ρ ≤ D.eps (G.level - 1) → ρ ≤ D.eps G.level →
      (∀ v u (γ : G.fam.Γ v u), 3 ≤ (G.fam.identity v u γ).maxOrder →
        (G.fam.identity v u γ).record.length ≤ D.eps (G.level - 1)) →
      (∀ v, 0 < π v) → (∀ v, 0 < marker v) → markedLedger π marker G.fam ≤ Sbound →
      ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = marker →
        SchurBound (A * Sbound)
          (kernelSchurMatrix (D.kap G.level) ρ (fun v => π v / w v ^ 2) n Dm a b c
            (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
            (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
            (fun v u γ d => G.physCoeff v u γ d.1)) := by
  obtain ⟨A, hA, m₀, hm₀, hidentity⟩ := uniform_native_identity_kernel_price α s q
    hα0 hα1 hs0 hs1 hq Λ hΛ ζ hζ bw hb n N Dm hN c hc
  refine ⟨A, hA, m₀, hm₀, ?_⟩
  intro hr _ _ D hDα hDq hDΛ hDζ hseq j₀ M G k hG hnat hlevel hi hj hE he hν hpar hm hm2
    P seedK freshK hwidth a b ρ Sbound π marker hρ hρE hρe hlength hπ hmarker hledger
  apply native_kernel_schur_of_marked_ledger G P seedK freshK (D.kap G.level) ρ a b A Sbound
    π marker n c hν hA hπ hmarker
    (fun v u γ => by rw [hwidth v u γ]; exact (G.fam.identity v u γ).record.width_pos)
    hc _ hledger
  intro v u γ
  simp_rw [hwidth v u γ]
  exact hidentity hr D hDα hDq hDΛ hDζ hseq j₀ M G k hG hnat hlevel hi hj hE he hν
    hpar a b v u γ (hm v) (hm2 v) ρ hρ hρE hρe (hlength v u γ)

end AVRegularity.Construction.Preservation.FullLift
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift

/-! Upgrade the specified retained solution using its actual complete prepared covariance trace. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_retained_solution_higher_extension (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ} {k l : ℕ} (hkl : k ≤ l)
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν 0 Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    (hθ : R.θ < 1 / 8)
    {kI : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified kI) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (hρε : ρ ≤ D.eps (G.level - 1))
    (hm : ∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1)
    (hm2 : ∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ j, 1 ≤ j → j ≤ l → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) j x‖ ≤
        α * B ^ j * (j.factorial : ℝ) * lam ^ ((1 : ℤ) - j))
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y)
    (Gin : GenStage D hr Dm bw j₀) (m p Nout : ℕ)
    (hreserve : l + 2 * p + 2 ≤ Nout)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (fsource : ∀ v : CompIn Gin.comps, TorusHk Nout (hr v.1.root))
    (htrace : IsRetainedTrace Gin G m p a fsource f) :
    ∃ (Uhi : ∀ v : CompIn G.comps, ℝ → TorusHk l (hr v.1.root)),
      ∀ v, ∀ t ∈ Set.Icc a b, U v t = truncateTorusHk hkl (Uhi v t) := by
  obtain ⟨fhi, _htracehi, hinit⟩ := retained_trace_higher_exists_at_order Gin G m p a
    hkl hreserve hΛ hζ fsource f htrace
  exact native_reg_solution_higher_extension_of_context P seedK freshK φ₀ hφ₀ G hkl
    R hB hC hS hθ hG hpar hnat hi hj hb hε hρε hm hm2
    hφ α B lam hα hBdrift hlam hsmall hstrain hjets f U W Y hsol fhi hinit
end

/-! A single same-order retained kernel operator supplies higher qualitative retained values. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_retained_solution_higher_extension_of_same_order_operator (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ} {k l : ℕ} (hkl : k ≤ l)
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν k Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    (hθ : R.θ < 1 / 8)
    (hSzero : ∀ i j γ, IsSpatialRegularizerTorus ρ 0 Dm a b R.c (R.r i j γ) (R.S i j γ))
    {kI : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified kI) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (hρε : ρ ≤ D.eps (G.level - 1))
    (hm : ∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1)
    (hm2 : ∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ j, 1 ≤ j → j ≤ l → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) j x‖ ≤
        α * B ^ j * (j.factorial : ℝ) * lam ^ ((1 : ℤ) - j))
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y)
    (Gin : GenStage D hr Dm bw j₀) (m p Nout : ℕ)
    (hreserve : l + 2 * p + 2 ≤ Nout)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (fsource : ∀ v : CompIn Gin.comps, TorusHk Nout (hr v.1.root))
    (htrace : IsRetainedTrace Gin G m p a fsource f) :
    ∃ (Uhi : ∀ v : CompIn G.comps, ℝ → TorusHk l (hr v.1.root)),
      ∀ v, ∀ t ∈ Set.Icc a b, U v t = truncateTorusHk hkl (Uhi v t) := by
  let Rzero := kernelOperator_order_restrict R (Nat.zero_le k) hSzero
  exact native_retained_solution_higher_extension P seedK freshK φ₀ hφ₀ G hkl
    Rzero hB hC hS hθ hG hpar hnat hi hj hb hε hρε hm hm2
    hφ α B lam hα hBdrift hlam hsmall hstrain hjets f U W Y hsol
    Gin m p Nout hreserve hΛ hζ fsource htrace
end

end AVRegularity.Construction.Preservation.FullLift
end
