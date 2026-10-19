-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.Assembly.WeakQuietCoefficientOfIngredients
import AVRegularity.Applications.Global.CompactRangeMain

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Providers.QuietAtlas
open AVRegularity.Construction.Preservation.Ledger
open Filter Topology
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Assembly

/-! The parent-jet assembly separates native sampling from the positive stored
ledger. All scalar prices precede Dm. Only the trimmed quiet margin middle half is used. -/

abbrev WeakQuietPrice :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℝ

/-- The native Cauchy/Piola price, before any component incidence sum. Its
coefficient input is the actual certified common case, through the plan floors. -/
def WeakQuietNativeJetsStatement (plan : WeakPassagePlan) (price : WeakQuietPrice) : Prop :=
  WeakPassageCommonOK plan →
  ∀ {B} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → WeakQuietWindow c r i →
    IsHistoryQuiet c.D (c.M + A.Jw) i (weakMiddleHalf c r i) →
    (∀ v u (γ : (c.stage i).fam.Γ v u) d, 2 ≤ d → d ≤ c.Dm →
      ∀ t ∈ weakMiddleHalf c r i,
        ContDiff ℝ (plan.jetOrder R) ((c.stage i).physCoeff v u γ d t)) ∧
    ∀ v u,
      ENNReal.ofReal (Real.sqrt (weakMass c.D A.Nw A.Jw A.η₀ u.1 /
        weakMass c.D A.Nw A.Jw A.η₀ v.1)) *
      ∑ γ : (c.stage i).fam.Γ v u, ∑ d ∈ Finset.Icc 2 c.Dm,
        coefficientSeminorm (c.D.eps (i - 1)) (plan.jetOrder R)
          (r.tq i - ocTauP c.D.α c.D.q c.D.Λ i / 2) (r.tq i)
          ((c.stage i).physCoeff v u γ d) *
          (ENNReal.ofReal (c.D.κ c.M * c.D.eps (i - 1) ^ (d - 2)))⁻¹ ≤
      ENNReal.ofReal (price R * ∑ γ : (c.stage i).fam.Γ v u,
        weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀ ⟨v, u, γ⟩)

/-- A single request-uniform bound on the whole positive ledger controls the
row and column sums at every incoming stage. -/
def WeakQuietStoredTotalStatement (plan : WeakPassagePlan) (ledger : WeakQuietPrice) : Prop :=
  ∀ {B} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ), c.M < i → i ≤ c.M + A.Jw →
    weakStoredTotal (c.stage i) A.Nw A.Jw A.η₀ ≤ ledger R

/-- The exact parent-jet statement from a native scalar price and the proved
finite incidence algebra. This is a conditional assembly. -/
theorem weak_middle_half_jets_of_native_price (plan : WeakPassagePlan)
    (price ledger : WeakQuietPrice) (hp : ∀ {B} {A : WeakCoefficientPhysical B}
      (R : WeakPassageRequest A), 0 ≤ price R)
    (hbudget : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      price R * ledger R ≤ plan.coeffC R)
    (hnative : WeakQuietNativeJetsStatement plan price)
    (hledger : WeakQuietStoredTotalStatement plan ledger) : WeakMiddleHalfJetsStatement plan := by
  intro hcommon B A R c r i hi hit hw hhistory
  obtain ⟨hs, hjets⟩ := hnative hcommon c r i hi hit hw hhistory
  let a := fun v u : CompIn (c.stage i).comps =>
    ∑ γ : (c.stage i).fam.Γ v u,
      weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀ ⟨v, u, γ⟩
  have ha (v u) : 0 ≤ a v u :=
    Finset.sum_nonneg fun γ _ => weakStoredEdgeWeight_nonneg _ _ _ _ _
  have htotal : (∑ v, ∑ u, a v u) ≤ ledger R := by
    simpa only [weakStoredTotal, LedgerEdge, Fintype.sum_sigma, a] using hledger c i hi hit
  have hrow (v) : (∑ u, a v u) ≤ ledger R :=
    (Finset.single_le_sum (fun v _ => Finset.sum_nonneg fun u _ => ha v u)
      (Finset.mem_univ v)).trans htotal
  have hcol (u) : (∑ v, a v u) ≤ ledger R := by
    have hh : (∑ v, a v u) ≤ ∑ u, ∑ v, a v u :=
      Finset.single_le_sum (fun u _ => Finset.sum_nonneg fun v _ => ha v u)
        (Finset.mem_univ u)
    rw [Finset.sum_comm] at hh
    exact hh.trans htotal
  refine ⟨fun v u => price R * a v u, fun v u => mul_nonneg (hp R) (ha v u), ?_, ?_, hs, hjets⟩
  · intro v
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (hrow v) (hp R)).trans (hbudget R)
  · intro u
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (hcol u) (hp R)).trans (hbudget R)

/-- The existing stored-ledger induction bounds every incoming stage by one at
one late threshold. No parameter of the actual construction enters the choice. -/
theorem exists_weak_quiet_stored_threshold {B : WeakCoefficientBase}
    (A : WeakCoefficientPhysical B) :
    ∃ M₀ : ℕ, 128 ≤ A.Λ → ∀ M, M₀ ≤ M → ∀ D : OCData,
      D.α = B.α → D.q = B.q → D.Λ = A.Λ → D.term = M →
      IsOCBandChain B.α B.q A.Λ B.ζ M D.κ → ∀ (Dm j₀ : ℕ) (P : ProvParams)
        (sX sZ : ℕ) (stage : ℕ → GenStage D ScalarH Dm A.bw j₀),
      IsWeakConstruction D P ⟨A.Nw, A.Rw, sX, sZ, A.η₀, M + A.Jw⟩ M A.Jw
        (D.termRW A.σw M) 0 stage →
      ∀ i, M ≤ i → i ≤ M + A.Jw → weakStoredTotal (stage i) A.Nw A.Jw A.η₀ ≤ 1 := by
  obtain ⟨Ce, hCe, heddy⟩ := exists_weakStoredEddy_constant B A
  let Q : ℝ := weakStoredPassageBudget A.Nw A.Jw A.Rw
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    exact_mod_cast weakStoredPassageBudget_one_le A.Nw A.Jw A.Rw
  have h2Q : 1 ≤ 2 * Q := hQ.trans
    (le_mul_of_one_le_left (zero_le_one.trans hQ) (by norm_num))
  let C : ℝ := (2 * Q) ^ A.Jw * Ce
  have hC : 0 < C := mul_pos (pow_pos (zero_lt_one.trans_le h2Q) _)
    (zero_lt_one.trans_le hCe)
  by_cases hΛ : 128 ≤ A.Λ
  · have hχ := weakChi_pos B.hα₀ B.hq.1 B.hq.2.1 A.η₀_small
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
      ((EntryScales.epsilon_rpow_tendsto_zero B.hq.1 hΛ hχ).eventually
        (gt_mem_nhds (inv_pos.mpr hC)))
    refine ⟨M₀, fun _ M hM D hα hq hbase ht hband Dm j₀ P sX sZ stage hc i hi hit => ?_⟩
    have heps (j : ℕ) : 0 < D.eps j :=
      Construction.Stream.ocEpsilon_pos (by rw [hbase]; omega)
    let e : ℝ := Ce * D.eps M ^ weakChi B.α B.q A.η₀
    have he : 0 ≤ e := mul_nonneg (zero_lt_one.trans_le hCe).le
      (Real.rpow_nonneg (heps M).le _)
    have hsmall : (2 * Q) ^ A.Jw * e ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_left (hM₀ M hM).le hC.le
      rw [mul_inv_cancel₀ hC.ne'] at hh
      simpa only [C, e, OCData.eps, hq, hbase, mul_assoc] using hh
    have hh := weakConstruction_storedTotal_stage_bound P
      (⟨A.Nw, A.Rw, sX, sZ, A.η₀, M + A.Jw⟩ : WeakMenu) M A.Jw 0
      (D.termRW A.σw M) stage hc A.Nw_pos A.Jw_pos heps e he
      (fun j hj _ => heddy M D hα hq hbase ht hband hΛ j hj) hsmall
      (M + A.Jw - i) (by omega)
    rw [show M + A.Jw - (M + A.Jw - i) = i by omega] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ h2Q (by omega : M + A.Jw - i ≤ A.Jw)) he).trans hsmall)
  · exact ⟨0, fun hh => (hΛ hh).elim⟩

/-- This floor is chosen only from the physical request, before Dm or a stage. -/
def weakQuietStoredFloor {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ :=
  (exists_weak_quiet_stored_threshold A).choose

/-- Parent-jet refinement: common-case floors, the whole-stage ledger floor,
and the native scalar price. Its ceiling also absorbs the native analytic
threshold. The actual jet order is retained. -/
def weakQuietParentJetPlan (plan : WeakPassagePlan) (price : WeakQuietPrice) : WeakPassagePlan :=
  { plan with
    baseFloor := fun B => max (plan.baseFloor B) (weakCommonCoeffPlan.baseThreshold B)
    base_ge := fun B => (plan.base_ge B).trans (le_max_left _ _)
    coeffC := fun R => max (plan.coeffC R) (max 0 (price R))
    levelFloor := fun {_B} {A} R j => max (plan.levelFloor R j)
      (max (weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) j)
        (max (weakQuietStoredFloor A) ⌈max 0 (price R)⌉₊)) }

/-- Every finite incidence ingredient of the parent-jet assembly is discharged.
Only the actual native Cauchy/Piola estimate remains analytic. -/
theorem weak_quiet_parent_jet_plan_spec (plan : WeakPassagePlan) (price : WeakQuietPrice) :
    let p := weakQuietParentJetPlan plan price
    WeakPassageCommonOK p ∧ WeakQuietStoredTotalStatement p (fun _ => 1) ∧
      ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
        max 0 (price R) * 1 ≤ p.coeffC R := by
  refine ⟨⟨fun B => le_max_right _ _, fun R j => ?_⟩, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · intro B A R c i hi hit
    have hfloor : weakQuietStoredFloor A ≤ c.M :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans c.level_ge
    exact (exists_weak_quiet_stored_threshold A).choose_spec
      ((weakQuietParentJetPlan plan price).base_ge B |>.trans c.base_ge)
      c.M hfloor c.D c.alpha c.q_eq c.base_eq c.terminal c.band c.Dm c.j₀ c.P R.sX R.sZ
      c.stage c.construction i hi.le hit
  · intro B A R
    rw [mul_one]
    exact le_max_right _ _

/-- The coefficient layer with the common carrier and positive ledger discharged internally.
The conditional input is solely the named native parent-jet estimate. -/
theorem weak_middle_half_jets_of_native_budget (plan : WeakPassagePlan)
    (price : WeakQuietPrice)
    (hnative : WeakQuietNativeJetsStatement (weakQuietParentJetPlan plan price)
      (fun R => max 0 (price R))) :
    WeakMiddleHalfJetsStatement (weakQuietParentJetPlan plan price) := by
  have hs := weak_quiet_parent_jet_plan_spec plan price
  exact weak_middle_half_jets_of_native_price _ _ (fun _ => 1)
    (fun R => le_max_left _ _) hs.2.2 hnative hs.2.1

open AVRegularity.Providers.WeakGen
open AVRegularity.Construction.StageEnvelopes.Cauchy

/-- One positive budget dominates all certificate constants across the finite
weak depth. It depends only on the request, before Dm and the actual stages. -/
def weakQuietCertificatePrice {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) : ℝ :=
  ∑ k ∈ Finset.range (A.Jw + 1), max 0 ((weakCertConst weakBasePlan (weakCoeffRequestOne R))^[k] 1)

/-- The common case supplies genuine native scalar Cauchy witnesses at every
incoming stage, with a request-uniform size budget. No encoded stage is substituted. -/
theorem weak_quiet_stage_scalar_certificate {plan : WeakPassagePlan}
    (hcommon : WeakPassageCommonOK plan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M ≤ i) (hit : i ≤ c.M + A.Jw) :
    let x := weakCommonCase R ((hcommon.1 B).trans c.base_ge) c.j₀ c.carrier c.M
      ((hcommon.2 R c.j₀).trans c.level_ge) c.D c.alpha c.q_eq c.base_eq c.profile_eq
      c.streams c.band c.terminal c.Dm c.order_ge c.P c.stage c.construction
    ∀ k : InvConsts, k.Lstar = weakWeight x.inst i →
      (∀ v : CompIn (c.stage i).comps, compReserve k v.1 ≤ 1) →
      ∀ (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u)
        (d : ℕ) (I : DerivativeWord2 (d - 1)) (a : Fin 2),
      Nonempty (StageScalarCertificate (c.stage i) k v u γ d I a
        (weakQuietCertificatePrice R * ((c.stage i).fam.identity v u γ).record.size *
          (((c.stage i).fam.identity v u γ).record.length / c.D.eps (c.stage i).level) ^
            (((c.stage i).fam.identity v u γ).maxOrder - 2))) := by
  dsimp only
  let x := weakCommonCase R ((hcommon.1 B).trans c.base_ge) c.j₀ c.carrier c.M
    ((hcommon.2 R c.j₀).trans c.level_ge) c.D c.alpha c.q_eq c.base_eq c.profile_eq
    c.streams c.band c.terminal c.Dm c.order_ge c.P c.stage c.construction
  intro k hL hres v u γ d I a
  have hn : c.M + A.Jw - i ≤ A.Jw := by omega
  obtain ⟨_hC, hw⟩ := weakCommonCase_certified R ((hcommon.1 B).trans c.base_ge)
    c.j₀ c.carrier c.M ((hcommon.2 R c.j₀).trans c.level_ge)
    c.D c.alpha c.q_eq c.base_eq c.profile_eq c.streams c.band c.terminal c.Dm c.order_ge
    c.P c.stage c.construction (c.M + A.Jw - i) hn
  rw [show c.M + A.Jw - (c.M + A.Jw - i) = i by omega] at hw
  obtain ⟨f, F, hf, hc, hsize⟩ := hw v u γ d I a
  have hCp : (weakCertConst weakBasePlan (weakCoeffRequestOne R))^[c.M + A.Jw - i] 1 ≤
      weakQuietCertificatePrice R := by
    apply (le_max_right 0 _).trans
    unfold weakQuietCertificatePrice
    exact Finset.single_le_sum
      (f := fun n => max 0 ((weakCertConst weakBasePlan (weakCoeffRequestOne R))^[n] 1))
      (fun n _ => le_max_left (0 : ℝ) _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  have heps (j : ℕ) : 0 < c.D.eps j := Construction.Stream.ocEpsilon_pos (by
    rw [c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge B).trans c.base_ge))
  have hreserve : 1 ≤ weakReserve x.inst i :=
    le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hprice : 0 ≤ weakQuietCertificatePrice R :=
    Finset.sum_nonneg (fun n _ => le_max_left 0 _)
  refine ⟨{ f := f
            F := F
            hol := fun p => (hf p).2
            realize := hc
            nonneg := mul_nonneg
              (mul_nonneg hprice ((c.stage i).fam.identity v u γ).record.size_nonneg)
              (pow_nonneg (div_nonneg ((c.stage i).fam.identity v u γ).record.length_pos.le
                (heps _).le) _)
            modes := ?_ }⟩
  rw [hL]
  apply (ctxSize_mono_reserve A.bw_pos.le (fun j => (heps j).le)
    (F := F) ((hres v).trans hreserve) (weakWeight x.inst i)).trans
  apply hsize.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCp ((c.stage i).fam.identity v u γ).record.size_nonneg)
    (pow_nonneg (div_nonneg ((c.stage i).fam.identity v u γ).record.length_pos.le (heps _).le) _)

/-- The actual incoming coefficients are phase independent on the history-quiet
middle half. This is a consequence of the carried passage invariant, not of
membership in the untrimmed quiet set. -/
theorem weak_middle_half_flux_phase {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M ≤ i) (hit : i ≤ c.M + A.Jw)
    (hquiet : IsHistoryQuiet c.D (c.M + A.Jw) i (weakMiddleHalf c r i)) :
    ∀ p (ch : StageCtx c.D A.bw c.j₀ (c.stage i).level p) t,
      t ∈ weakMiddleHalf c r i →
      t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ (c.stage i).level p.1 →
      ∀ v u (γ : (c.stage i).fam.Γ v u) d (I : DerivativeWord2 (d - 1)) (Y z z' : Vec 2),
        (c.stage i).fam.flux p ch v u γ d I t Y z =
          (c.stage i).fam.flux p ch v u γ d I t Y z' := by
  by_cases htop : i = c.M + A.Jw
  · subst i
    intro p ch t ht htp v u γ
    exact ((c.construction.2.1.2.2.1 v u).false γ).elim
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge B).trans c.base_ge)
  have hζ : IsFastProfile c.D.ζ := by rw [c.profile_eq]; exact B.hζ
  have hκ : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [c.alpha, c.q_eq, c.base_eq, c.profile_eq, c.terminal]
    exact c.band
  have hcarrier : IsCarrierStart c.D.α c.D.q c.D.Λ A.bw 1 400 c.j₀ := by
    rw [c.alpha, c.q_eq, c.base_eq]
    exact c.carrier
  have hstart := AVRegularity.Providers.GenSem.startBound_of_carrierStart
    hΛ (le_refl 1) (by norm_num : (1 : ℝ) ≤ 400) hcarrier
  have hcell : ∀ m, 0 < c.D.cellScaleSq m :=
    EntryWeakProofs.weakData_cellScaleSq_pos c.D hΛ hζ hκ
  obtain ⟨hinv, hcov⟩ := weakConstruction_history hΛ hζ A.bw_pos hstart hcell
    c.construction (c.M + A.Jw - (i + 1)) (by omega)
  rw [show c.M + A.Jw - (c.M + A.Jw - (i + 1)) = i + 1 by omega] at hinv hcov
  have hp := (c.construction.2.2 (i + 1) (by omega) (by omega)).1
  rw [Nat.add_sub_cancel] at hp
  obtain ⟨w⟩ := IsWeakPassage.witness hp
  have hlv := EntryWeakProofs.weakConstruction_level _ _ _ _ _ _ _ c.construction
  have hlev : (c.stage (i + 1)).level = (c.stage i).level + 1 := by
    rw [hlv (i + 1) (by omega) (by omega), hlv i hi hit]
  let P := weakPassagePresentation w hlev
  have hfiner := weakPassage_finerHistory hζ hΛ w hlev (hcell _) hcov hinv
  have hquiet' : IsHistoryQuiet c.D (c.M + A.Jw) (c.stage i).level
      (weakMiddleHalf c r i) := by rwa [hlv i hi hit]
  have hQC := quietPhaseBlind_of_finerHistory A.bw_pos hΛ hζ (c.stage i) P
    (c.M + A.Jw) (weakMiddleHalf c r i) hquiet' hfiner
  exact quietPhaseTransfer_of_source (quietSourcePhase c.D) (c.stage i) P (c.M + A.Jw)
    (weakMiddleHalf c r i) hΛ hζ hquiet' hQC

end AVRegularity.WeakEntryProofs.Assembly
end

section
open Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Ordinary parent-scale slow jets from the actual scalar context certificate.
The Cauchy constants depend only on the width and derivative order. -/

open AVRegularity.Construction.StageEnvelopes.Cauchy
open AVRegularity.Providers.ComplexFlow AVRegularity.Providers.WeakGen
open AVRegularity.Providers.QuietAtlas

/-- The auxiliary certificate reserve has a fixed positive gap at the selected
row, independently of its grade and the ambient order cap. -/
def weakQuietRowConsts (k : InvConsts) (v : Comp) : InvConsts :=
  { k with G0 := 0, Hprod := 2 * compGrade v }

theorem weak_quiet_row_reserve_upper (k : InvConsts) (v u : Comp) :
    compReserve (weakQuietRowConsts k v) u ≤ 1 := by
  unfold compReserve weakQuietRowConsts
  simp only [Nat.zero_add]
  exact sub_le_self _ (div_nonneg (Nat.cast_nonneg _) (by positivity))

theorem weak_quiet_row_reserve_gap (k : InvConsts) (v : Comp) :
    (1 : ℝ) / 2 ≤ compReserve (weakQuietRowConsts k v) v := by
  have hd : 0 < ((2 * compGrade v : ℕ) : ℝ) + 1 := by positivity
  have hh : (compGrade v : ℝ) / (((2 * compGrade v : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
    apply (div_le_iff₀ hd).mpr
    push_cast
    linarith only
  unfold compReserve weakQuietRowConsts
  simp only [Nat.zero_add]
  linarith only [hh]

/-- Setting the fast order to zero in the all-history mixed Cauchy estimate
bounds the ordinary slow jet. The zero-ary multilinear identification is an
isometry, so this step introduces no additional price. -/
theorem weak_quiet_exists_scalar_slow_jet_bounds (bw : ℝ) (hb : 0 < bw) (N : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      (D : OCData) (Dm j₀ : ℕ) (G : GenStage D hr Dm bw j₀) (k : InvConsts)
      (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (a : Fin 2) (θ CH Υ : ℝ),
      StageScalarCertificate G k v u γ d I a θ → ChainEnv D bw CH Υ j₀ →
      (1 : ℝ) / 2 ≤ compReserve k v.1 → compReserve k v.1 ≤ 2 →
      ∀ (p : OddSlot) (ch : StageCtx D bw j₀ G.level p) (t : ℝ) (Y z : Vec 2),
      t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
      IsCarrierChain D bw j₀ G.level p.1 0 (ch.1.recenter D Y) →
      ContDiffAt ℝ (N : ℕ∞)
        (fun H => G.fam.slowFlux (D.eps (G.level - 1)) p ch v u γ d I t H z a) Y ∧
      ∀ n ≤ N, (D.eps (G.level - 1)) ^ n *
        ‖iteratedFDeriv ℝ n
          (fun H => G.fam.slowFlux (D.eps (G.level - 1)) p ch v u γ d I t H z a) Y‖ ≤
          C n * θ := by
  obtain ⟨C, hC, hbound⟩ := stage_exists_scalar_mixed_jet_bounds bw (1 / 2) hb (by norm_num) N
  refine ⟨C, hC, ?_⟩
  intro hr _ _ D Dm j₀ G k v u γ d I a θ CH Υ s env hgap hupper p ch t Y z ht hchain
  obtain ⟨hreg, hj⟩ := hbound hr D Dm j₀ G k v u γ d I a θ CH Υ 0 s env
    le_rfl (by simpa only [zero_add] using hgap) hupper p ch t Y z ht hchain 0
  let f : Vec 2 → ℝ :=
    fun H => G.fam.slowFlux (D.eps (G.level - 1)) p ch v u γ d I t H z a
  let e := (continuousMultilinearCurryFin0 ℝ (Vec 2) ℝ).symm
  have he : (fun H => iteratedFDeriv ℝ 0
      (fun w => G.fam.slowFlux (D.eps (G.level - 1)) p ch v u γ d I t H w a) z) =
      e ∘ f := rfl
  rw [he] at hreg hj
  have hs : ContDiffAt ℝ (N : ℕ∞) f Y :=
    e.toContinuousLinearEquiv.comp_contDiffAt_iff.mp hreg
  refine ⟨hs, ?_⟩
  intro n hn
  have hh := hj n hn
  rw [e.norm_iteratedFDeriv_comp_left] at hh
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one, one_mul] at hh
  have hE : 0 < D.eps (G.level - 1) := Construction.Stream.ocEpsilon_pos env.hΛ1
  have hh' := (le_div_iff₀ (pow_pos hE n)).mp hh
  exact (mul_comm _ _).trans_le hh'

/-- Quiet phase removal can be performed before differentiating: the sampled
fast diagonal and the zero-phase slow field are literally the same function. -/
theorem weak_quiet_phase_diagonal_eq {hr : ℕ → Type}
    [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} (G : GenStage D hr Dm bw j₀)
    (p : OddSlot) (ch : StageCtx D bw j₀ G.level p)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (t E e : ℝ)
    (hphase : ∀ Y z z', G.fam.flux p ch v u γ d I t Y z =
      G.fam.flux p ch v u γ d I t Y z') :
    (fun Y => G.fam.slowFlux E p ch v u γ d I t Y (e⁻¹ • Y)) =
      (fun Y => G.fam.slowFlux E p ch v u γ d I t Y 0) := by
  funext Y
  exact hphase (E⁻¹ • Y) (e⁻¹ • Y) 0

/-- Every native incoming stage has uniform parent-scale slow jets. The scalar
price is chosen before Dm, the construction and the row grades. -/
theorem weak_quiet_native_slow_jets {B : WeakCoefficientBase}
    (A : WeakCoefficientPhysical B) (N : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
    ∀ (plan : WeakPassagePlan), WeakPassageCommonOK plan →
    ∀ (R : WeakPassageRequest A) (c : WeakPassageInstance plan R) (i : ℕ),
    c.M ≤ i → i ≤ c.M + A.Jw →
    ∀ (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u)
      (d : ℕ) (I : DerivativeWord2 (d - 1)) (p : OddSlot) (t : ℝ),
    t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ (c.stage i).level p.1 →
    ContDiff ℝ (N : ℕ∞) (fun Y => (c.stage i).fam.slowFlux
      (c.D.eps (i - 1)) p ((c.stage i).actual p) v u γ d I t Y 0) ∧
    ∀ n ≤ N, ∀ Y : Vec 2, c.D.eps (i - 1) ^ n *
      ‖iteratedFDeriv ℝ n (fun H => (c.stage i).fam.slowFlux
        (c.D.eps (i - 1)) p ((c.stage i).actual p) v u γ d I t H 0) Y‖ ≤
      C n * (weakQuietCertificatePrice R * ((c.stage i).fam.identity v u γ).record.size *
        (((c.stage i).fam.identity v u γ).record.length / c.D.eps i) ^
          (((c.stage i).fam.identity v u γ).maxOrder - 2)) := by
  obtain ⟨C, hC, hbound⟩ := weak_quiet_exists_scalar_slow_jet_bounds A.bw A.bw_pos N
  refine ⟨fun n => 2 * C n, fun n => mul_nonneg (by norm_num) (hC n), ?_⟩
  intro plan hcommon R c i hi hit v u γ d I p t ht
  let x := weakCommonCase R ((hcommon.1 B).trans c.base_ge) c.j₀ c.carrier c.M
    ((hcommon.2 R c.j₀).trans c.level_ge) c.D c.alpha c.q_eq c.base_eq c.profile_eq
    c.streams c.band c.terminal c.Dm c.order_ge c.P c.stage c.construction
  let k := weakQuietRowConsts { R.kReq with Lstar := weakWeight x.inst i } v.1
  have hL : k.Lstar = weakWeight x.inst i := rfl
  have hres (w : CompIn (c.stage i).comps) : compReserve k w.1 ≤ 1 :=
    weak_quiet_row_reserve_upper _ _ _
  let θ := weakQuietCertificatePrice R * ((c.stage i).fam.identity v u γ).record.size *
    (((c.stage i).fam.identity v u γ).record.length / c.D.eps (c.stage i).level) ^
      (((c.stage i).fam.identity v u γ).maxOrder - 2)
  have hs (a : Fin 2) : Nonempty (StageScalarCertificate (c.stage i) k v u γ d I a θ) :=
    weak_quiet_stage_scalar_certificate hcommon c i hi hit k hL hres v u γ d I a
  let s (a : Fin 2) := Classical.choice (hs a)
  have hg2 := weakCommonPlan_complexContext weakBasePlan (weakCertConst weakBasePlan) weakBasePlan_complexContext
  have env := (case_complexContextBase hg2 x.inst 0).env
  have hlev := EntryWeakProofs.weakConstruction_level _ _ _ _ _ _ _ c.construction i hi hit
  have hstart : c.j₀ + 2 ≤ c.M :=
    (hg2.2 (weakCoeffRequestOne R) c.j₀).trans ((hcommon.2 R c.j₀).trans c.level_ge)
  have hi' : 1 ≤ (c.stage i).level := by omega
  have hj' : c.j₀ ≤ (c.stage i).level := by omega
  have hnat : (c.stage i).IsNatural (c.M + A.Jw) := by
    by_cases he : i = c.M + A.Jw
    · subst i
      exact c.construction.2.1.2.2.2
    · exact EntryWeakProofs.weakConstruction_output_natural _ _ _ _ _ _ _ c.construction
        i hi (by omega)
  have hchain (Y : Vec 2) : IsCarrierChain c.D A.bw c.j₀ (c.stage i).level p.1 0
      (((c.stage i).actual p).1.recenter c.D Y) := by
    rw [hnat.2.2.1 p, nativeChain_recenter]
    exact nativeChain_isCarrier _ _ _ _ _ _ hi' hj' p.2 Y
  have hscalar (a : Fin 2) (Y : Vec 2) := hbound ScalarH c.D c.Dm c.j₀ (c.stage i)
    k v u γ d I a θ _ _ (s a) env (weak_quiet_row_reserve_gap _ _)
    ((hres v).trans (by norm_num)) p ((c.stage i).actual p) t Y 0 ht (hchain Y)
  have hreg (a : Fin 2) : ContDiff ℝ (N : ℕ∞) (fun Y => (c.stage i).fam.slowFlux
      (c.D.eps ((c.stage i).level - 1)) p ((c.stage i).actual p) v u γ d I t Y 0 a) :=
    contDiff_iff_contDiffAt.mpr (fun Y => (hscalar a Y).1)
  have hvreg := contDiff_pi.mpr hreg
  refine ⟨by simpa only [hlev] using hvreg, ?_⟩
  intro n hn Y
  have hE : 0 ≤ c.D.eps ((c.stage i).level - 1) ^ n :=
    pow_nonneg (Construction.Stream.ocEpsilon_pos env.hΛ1).le n
  have hh := mul_le_mul_of_nonneg_left
    (AVRegularity.Construction.Preservation.FullLift.norm_iteratedFDeriv_vector_le_sum 2 n _
      (fun a => (hreg a).of_le (by exact_mod_cast hn)) Y) hE
  rw [Finset.mul_sum] at hh
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => (hscalar a Y).2 n hn)
  have hh' := hh.trans hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh'
  simpa only [θ, hlev, Nat.cast_ofNat, mul_assoc] using hh'

/-- The exact finer record length at every incoming stage, with the empty root
handled by elimination of its identity type. -/
theorem weak_quiet_native_record_length {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M ≤ i) (hit : i ≤ c.M + A.Jw)
    (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u) :
    ((c.stage i).fam.identity v u γ).record.length = c.D.eps (i + 1) := by
  by_cases he : i = c.M + A.Jw
  · subst i
    exact ((c.construction.2.1.2.2.1 v u).false γ).elim
  have hp := c.construction.2.2 (i + 1) (by omega) (by omega)
  rw [Nat.add_sub_cancel] at hp
  have hrec := weakPassage_record_lengths _ _ _ _ _ _ hp.1 hp.2 v u γ
  have hlev := EntryWeakProofs.weakConstruction_level _ _ _ _ _ _ _ c.construction
    (i + 1) (by omega) (by omega)
  exact hrec.1.trans (congrArg c.D.eps hlev)

/-- The record factor in the native certificate costs at most one. The estimate
uses the actual finer wavelength, with no dependence on the ambient cap. -/
theorem weak_quiet_native_record_factor_le_one {plan : WeakPassagePlan}
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M ≤ i) (hit : i ≤ c.M + A.Jw)
    (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u) :
    (((c.stage i).fam.identity v u γ).record.length / c.D.eps i) ^
      (((c.stage i).fam.identity v u γ).maxOrder - 2) ≤ 1 := by
  have hΛ : 128 ≤ c.D.Λ := by rw [c.base_eq]; exact (plan.base_ge B).trans c.base_ge
  have hq : 1 < c.D.q := by rw [c.q_eq]; exact B.hq.1
  have hE : 0 < c.D.eps i := Applications.eps_pos hq hΛ
  have hlen : ((c.stage i).fam.identity v u γ).record.length ≤ c.D.eps i := by
    rw [weak_quiet_native_record_length c i hi hit v u γ]
    exact Applications.eps_antitone hq hΛ (Nat.le_succ i)
  exact pow_le_one₀ (div_nonneg ((c.stage i).fam.identity v u γ).record.length_pos.le hE.le)
    ((div_le_one hE).mpr hlen)

/-- On the history-quiet trimmed middle half, sampling the fast variable on the
physical diagonal costs no derivatives. The resulting price is uniform in Dm. -/
theorem weak_quiet_native_diagonal_jets {B : WeakCoefficientBase}
    (A : WeakCoefficientPhysical B) (N : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
    ∀ (plan : WeakPassagePlan), WeakPassageCommonOK plan →
    ∀ (R : WeakPassageRequest A) (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
      (i : ℕ), c.M ≤ i → i ≤ c.M + A.Jw →
    IsHistoryQuiet c.D (c.M + A.Jw) i (weakMiddleHalf c r i) →
    ∀ (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u)
      (d : ℕ) (I : DerivativeWord2 (d - 1)) (p : OddSlot) (t : ℝ),
    t ∈ weakMiddleHalf c r i →
    t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ (c.stage i).level p.1 →
    ContDiff ℝ (N : ℕ∞) (fun Y => (c.stage i).fam.slowFlux
      (c.D.eps (i - 1)) p ((c.stage i).actual p) v u γ d I t Y ((c.D.eps i)⁻¹ • Y)) ∧
    ∀ n ≤ N, ∀ Y : Vec 2, c.D.eps (i - 1) ^ n *
      ‖iteratedFDeriv ℝ n (fun H => (c.stage i).fam.slowFlux
        (c.D.eps (i - 1)) p ((c.stage i).actual p) v u γ d I t H ((c.D.eps i)⁻¹ • H)) Y‖ ≤
      C n * (weakQuietCertificatePrice R * ((c.stage i).fam.identity v u γ).record.size) := by
  obtain ⟨C, hC, hbound⟩ := weak_quiet_native_slow_jets A N
  refine ⟨C, hC, ?_⟩
  intro plan hcommon R c r i hi hit hquiet v u γ d I p t ht htp
  have he := weak_quiet_phase_diagonal_eq (c.stage i) p ((c.stage i).actual p) v u γ d I
    t (c.D.eps (i - 1)) (c.D.eps i)
    (weak_middle_half_flux_phase c r i hi hit hquiet p ((c.stage i).actual p) t ht htp
      v u γ d I)
  rw [he]
  obtain ⟨hs, hj⟩ := hbound plan hcommon R c i hi hit v u γ d I p t htp
  refine ⟨hs, ?_⟩
  intro n hn Y
  apply (hj n hn Y).trans
  apply mul_le_mul_of_nonneg_left _ (hC n)
  have hp : 0 ≤ weakQuietCertificatePrice R :=
    Finset.sum_nonneg (fun _ _ => le_max_left 0 _)
  exact mul_le_of_le_one_right
    (mul_nonneg hp ((c.stage i).fam.identity v u γ).record.size_nonneg)
    (weak_quiet_native_record_factor_le_one c i hi hit v u γ)

end AVRegularity.WeakEntryProofs.Assembly
end
