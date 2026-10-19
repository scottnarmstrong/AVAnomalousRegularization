-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.Assembly.PassageInterfaces

/-! Datum-independent choices and actual solution objects for the weak-entry
composition. Exact statements are copied as types. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Assembly

/-- Exact `entry_coefficients` type. -/
def EntryCoefficientsStatement : Prop :=
  ∀ (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∀ (Nw Rw Lw : ℕ), 1 ≤ Nw → Lw ≤ Jw * Nw →
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → L + 1 ≤ 2 * (nW : ℕ) →
      Lw + 5 ≤ Kw →
    ∀ cK : ℝ, 0 < cK → cK ≤ 1 →
    ∃ (CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams),
      (∃ stage : ℕ → GenStage D ScalarH Dm bw j₀, IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage) ∧
      ∀ stage : ℕ → GenStage D ScalarH Dm bw j₀, IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
      ∃ (Gw : GenStage D ScalarH Dm bw j₀) (rootM rootR : ℕ → ℝ) (ι : CompIn (stage M).comps ≃ CompIn Gw.comps),
        IsWeakEncoding Nw Jw η₀ rootM rootR (stage M) Gw ι ∧ (∀ r, 0 < rootM r) ∧ (∀ r, 0 < rootR r) ∧
      ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
      ∀ a aM : ℝ, a ≤ aM → aM ≤ a + 6 * Jw * ocTauPP α q Λ (M + 1) →
        IsWeakStage law P φ₀ hφ₀ M (M + Jw) Jw (Jw * Rw) (1 + Jw * Nw) nW kW a T₀ σw CL Cχ (weakChi α q η₀)
          Gw aM

/-- Exact `entry_weak` type, including the lift-order floors. -/
def EntryWeakStatement : Prop :=
  ∀ (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∃ (Nw Rw Lw : ℕ), 1 ≤ Nw ∧ Lw = Jw * Nw ∧
      Pw + 2 * q ^ Jw + 1 + 2 < Nw * (q - 1) ∧
      Pw + 2 * q ^ Jw + 1 + q ^ Jw + 1 < 2 * weakAStar α q * (Rw + 1) ∧
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ SX SZ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → SX ≤ sX → SZ ≤ sZ →
      L + 1 ≤ 2 * (nW : ℕ) → Lw + 5 ≤ Kw →
    ∃ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams) (a : ℝ),
    ∃ (stage : ℕ → GenStage D ScalarH Dm bw j₀) (Gw : GenStage D ScalarH Dm bw j₀) (rootM rootR : ℕ → ℝ)
      (ι : CompIn (stage M).comps ≃ CompIn Gw.comps) (aM : ℝ)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage ∧
      IsWeakEncoding Nw Jw η₀ rootM rootR (stage M) Gw ι ∧
      (∀ r, 0 < rootM r) ∧ (∀ r, 0 < rootR r) ∧
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sX sZ (stage i) (CcR i)) ∧
      IsWeakReadoutChain M Jw Nw 0 η₀ (fun _ => (Jw * Rw)) stage CcR W ∧
      ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
        IsWeakStage law P φ₀ hφ₀ M (M + Jw) Jw (Jw * Rw) (1 + Jw * Nw) nW kW a T₀ σw CL Cχ (weakChi α q η₀)
          Gw aM ∧
        ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
          IsWeakSolutionOn (streamVel (D.Φ (M + Jw))) (D.κ M) a (a + T₀) f θ →
        ∃ (tq : ℕ → ℝ)
          (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk Kw (ScalarH v.1.root))
          (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
          (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root))
          (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
          (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
          (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
          (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root)),
          IsWeakReduction P φ₀ hφ₀ nW M Jw Kw 0 a (a + T₀) θ stage tq Ur Urw Urk ∧
          tq (M + 1) = aM ∧ (U₀ = fun v => rerootFamily ι (Ur M) v aM) ∧ U = rerootFamily ι (Ur M) ∧
          IsWeakPaired P φ₀ hφ₀ law M Kw L nW a T₀ σw (weakChi α q η₀) cK CK f Gw aM
            U₀ U V Uw Vw Uk Vk ∧
          IsWeakReadout law M Jw Lw Kw (D.κ M) a τ T₀ s Pw cK Cread Cid f θ Gw
            (fun t g x => W M t (fun v x' => g (ι v) x') x) V

/-- Physical choices before the weak menu and before sigma. -/
structure WeakEntryPhysical (B : WeakCoefficientBase) where
  Λ : ℕ
  φ₀ : Vec 2 → ℝ
  hφ₀ : Integrable φ₀
  smooth : ContDiff ℝ (⊤ : ℕ∞) φ₀
  nonneg : ∀ z, 0 ≤ φ₀ z
  mass : ∫ z, φ₀ z = 1
  support : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall
  bw : ℝ
  bw_pos : 0 < bw
  bw_small : bw ≤ 1 / 10000
  Jw : ℕ
  τ : ℝ
  T₀ : ℝ
  Pw : ℝ
  η₀ : ℝ
  Jw_pos : 1 ≤ Jw
  τ_pos : 0 < τ
  τ_small : τ < T₀
  Pw_pos : 0 < Pw
  η₀_pos : 0 < η₀
  η₀_small : η₀ ≤ ocDelta B.α B.q / 8

/-- A fixed physical menu, independent of all subsequent reserve requests. -/
structure WeakEntryOrders {B : WeakCoefficientBase} (A : WeakEntryPhysical B) where
  N : ℕ
  R : ℕ
  L : ℕ
  N_pos : 1 ≤ N
  L_le : L ≤ A.Jw * N
  L_eq : L = A.Jw * N
  order_N : A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < N * (B.q - 1)
  order_R : A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 <
    2 * weakAStar B.α B.q * (R + 1)

/-- The two source order inequalities admit a finite menu before sigma or any
reserve request. Taking the full finite composition order fixes the readout. -/
theorem weak_entry_orders_exists {B : WeakCoefficientBase} (A : WeakEntryPhysical B) :
    Nonempty (WeakEntryOrders A) := by
  have hq : 0 < B.q - 1 := sub_pos.mpr B.hq.1
  have hα := B.hα₀
  have hq1 := B.hq.1
  have hstar : 0 < 2 * weakAStar B.α B.q := by
    unfold weakAStar ocGamma
    positivity
  obtain ⟨n, hn⟩ := exists_nat_gt ((A.Pw + 2 * B.q ^ A.Jw + 1 + 2) / (B.q - 1))
  obtain ⟨r, hr⟩ := exists_nat_gt
    ((A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1) / (2 * weakAStar B.α B.q))
  refine ⟨⟨n + 1, r, A.Jw * (n + 1), by omega, le_rfl, rfl, ?_, ?_⟩⟩
  · have hb := (div_lt_iff₀ hq).mp hn
    exact hb.trans_le (mul_le_mul_of_nonneg_right (by norm_cast; omega) hq.le)
  · have hb := (div_lt_iff₀ hstar).mp hr
    apply hb.trans_le
    calc
      (r : ℝ) * (2 * weakAStar B.α B.q) = (2 * weakAStar B.α B.q) * r := mul_comm _ _
      _ ≤ (2 * weakAStar B.α B.q) * (r + 1) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hstar.le

/-- The finite physical menu is fixed before all later requests. -/
def weakEntryOrdersChoice {B : WeakCoefficientBase} (A : WeakEntryPhysical B) : WeakEntryOrders A :=
  Classical.choice (weak_entry_orders_exists A)

/-- Add the menu fixed earlier and the later choice of `σ`. -/
def WeakEntryPhysical.withOrders {B} (A : WeakEntryPhysical B) (o : WeakEntryOrders A)
    (σ : ℝ) (hσ : 0 < σ) (hσsmall : σ < min (ocC B.α B.q) (B.q - 1)) :
    WeakCoefficientPhysical B :=
  ⟨A.Λ, A.φ₀, A.hφ₀, A.smooth, A.nonneg, A.mass, A.support, A.bw, A.bw_pos, A.bw_small,
    A.Jw, A.τ, A.T₀, A.Pw, A.η₀, A.Jw_pos, A.τ_pos, A.τ_small, A.Pw_pos, A.η₀_pos,
    A.η₀_small, o.N, o.R, o.L, o.N_pos, o.L_le, σ, hσ, hσsmall⟩

/-- What coefficient production actually supplies, at the radius already chosen.
Its auxiliary energy/readout constants are unused; analytic bounds get their own constants. -/
structure WeakEntryAllocation {B} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (cK : ℝ) where
  CL : ℝ
  Cχ : ℝ
  kW : InvConsts
  radius : kW.c₀ = cK
  allocation : IsWeakAllocation kW R.kReq R.L
  CH : ℝ
  Υ : ℝ
  history : 1 ≤ CH
  chain : 0 < Υ

/-- Finite pre-data prices used to choose the radius, before any coefficient
stage is certified. The analytic leaves prove that these prices bound the drift. -/
structure WeakEntryRadiusBudget where
  quietMargin : ℝ
  quietMargin_pos : 0 < quietMargin
  drift : ℝ
  drift_nonneg : 0 ≤ drift

/-- One radius pays the quiet margin cap and the quadratic drift strain price. -/
def WeakEntryRadiusBudget.radius (b : WeakEntryRadiusBudget) : ℝ :=
  min 1 (min b.quietMargin (1 / (8 * (b.drift + 1))))

/-- Numeric drift-radius selection, independent of every terminal data object. -/
theorem weak_entry_radius_spec (b : WeakEntryRadiusBudget) :
    0 < b.radius ∧ b.radius ≤ 1 ∧ b.radius ≤ b.quietMargin ∧
      b.drift * b.radius ≤ 1 / 8 ∧ b.drift * b.radius ^ 2 ≤ 1 / 8 := by
  have hd : 0 < 8 * (b.drift + 1) := by linarith [b.drift_nonneg]
  have hp : 0 < b.radius := lt_min (by norm_num)
    (lt_min b.quietMargin_pos (one_div_pos.mpr hd))
  have h1 : b.radius ≤ 1 := min_le_left _ _
  have hc : b.radius ≤ b.quietMargin := (min_le_right _ _).trans (min_le_left _ _)
  have hr : b.radius ≤ 1 / (8 * (b.drift + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hprod := (le_div_iff₀ hd).mp hr
  have hlinear : (b.drift + 1) * b.radius ≤ 1 / 8 := by linarith only [hprod]
  have hsq : b.radius ^ 2 ≤ b.radius := by nlinarith only [hp.le, h1]
  have hprice : b.drift * b.radius ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hp.le).trans hlinear
  exact ⟨hp, h1, hc, hprice, (mul_le_mul_of_nonneg_left hsq b.drift_nonneg).trans hprice⟩

/-- Shared analytic choices. The radius is selected before calling entry_coefficients;
it must pay both the drift prices and quiet margin smoothing radius in the analytic leaves.
The three output constants and the threshold can then depend on its allocation. -/
structure WeakEntryGluePlan where
  baseFloor : WeakCoefficientBase → ℕ
  momentFloor : ∀ {B}, WeakCoefficientPhysical B → ℕ
  radiusBudget : ∀ {B} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → WeakEntryRadiusBudget
  CK : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A), WeakEntryAllocation R ((radiusBudget R).radius) → ℝ
  Cread : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A), WeakEntryAllocation R ((radiusBudget R).radius) → ℝ
  Cid : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A), WeakEntryAllocation R ((radiusBudget R).radius) → ℝ
  levelFloor : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    WeakEntryAllocation R ((radiusBudget R).radius) → ℕ → ℕ
  /-- The floor of the lift orders `sX`, `sZ`, chosen with the moment floor, before the
  request. -/
  liftFloor : ∀ {B}, WeakCoefficientPhysical B → ℕ

/-- The final radius, fixed before coefficient production. -/
abbrev WeakEntryGluePlan.radius (plan : WeakEntryGluePlan) {B} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) : ℝ := (plan.radiusBudget R).radius

/-- Actual data after the analytic choices and the coefficient threshold. -/
structure WeakEntryData (plan : WeakEntryGluePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (C : WeakEntryAllocation R (plan.radius R)) where
  base_ge : plan.baseFloor B ≤ A.Λ
  base128 : 128 ≤ A.Λ
  menu_N : A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1)
  menu_R : A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 < 2 * weakAStar B.α B.q * (A.Rw + 1)
  readout_order : A.Lw = A.Jw * A.Nw
  moment_ge : plan.momentFloor A ≤ R.L
  /-- The lift orders are above the plan's floor. -/
  sX_ge : plan.liftFloor A ≤ R.sX
  sZ_ge : plan.liftFloor A ≤ R.sZ
  j₀ : ℕ
  carrier : IsCarrierStart B.α B.q A.Λ A.bw C.CH C.Υ j₀
  /-- The carrier start at the common plan's constants `CH = 1`, `Υ = 400`, read by the
  passage statements and the certified case. -/
  carrier400 : IsCarrierStart B.α B.q A.Λ A.bw 1 400 j₀
  M : ℕ
  level_ge : plan.levelFloor R C j₀ ≤ M
  D : OCData
  alpha : D.α = B.α
  q_eq : D.q = B.q
  base_eq : D.Λ = A.Λ
  profile_eq : D.ζ = B.ζ
  streams : IsOCStreamSeq B.α B.q A.Λ B.ζ D.Φ
  band : IsOCBandChain B.α B.q A.Λ B.ζ M D.κ
  terminal : D.term = M
  Dm : ℕ
  order_ge : 1 + A.Jw * A.Nw ≤ Dm
  P : ProvParams
  a : ℝ

/-- The datum-independent encoded construction supplied by entry_coefficients. -/
structure WeakEntryStages {plan : WeakEntryGluePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} (x : WeakEntryData plan C) where
  stage : ℕ → GenStage x.D ScalarH x.Dm A.bw x.j₀
  Gw : GenStage x.D ScalarH x.Dm A.bw x.j₀
  rootM : ℕ → ℝ
  rootR : ℕ → ℝ
  relabel : CompIn (stage x.M).comps ≃ CompIn Gw.comps
  construction : IsWeakConstruction x.D x.P
    (⟨A.Nw, A.Rw, R.sX, R.sZ, A.η₀, x.M + A.Jw⟩ : WeakMenu)
    x.M A.Jw (x.D.termRW A.σw x.M) 0 stage
  encoding : IsWeakEncoding A.Nw A.Jw A.η₀ rootM rootR (stage x.M) Gw relabel
  rootM_pos : ∀ r, 0 < rootM r
  rootR_pos : ∀ r, 0 < rootR r
  invariant : ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
    ∀ aM : ℝ, x.a ≤ aM → aM ≤ x.a + 6 * A.Jw * ocTauPP B.α B.q A.Λ (x.M + 1) →
    IsWeakStage law x.P A.φ₀ A.hφ₀ x.M (x.M + A.Jw) A.Jw (A.Jw * A.Rw)
      (1 + A.Jw * A.Nw) R.nW C.kW x.a A.T₀ A.σw C.CL C.Cχ (weakChi B.α B.q A.η₀) Gw aM

/-- Clock and lifts chosen before f. The root enters strictly after a; the output
is no later than a+tau. Interior quiet margin conditions, rather than independence on
ocQuietTimes, are the geometric inputs of the reduction and identity proofs. -/
structure WeakEntrySchedule {plan : WeakEntryGluePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) where
  tq : ℕ → ℝ
  start : x.a < tq (x.M + A.Jw + 1)
  finish : tq (x.M + 1) ≤ x.a + A.τ
  start_le : x.a ≤ tq (x.M + 1)
  start_upper : tq (x.M + 1) ≤ x.a + 6 * A.Jw * ocTauPP B.α B.q A.Λ (x.M + 1)
  quietMargins : ∀ i, x.M < i → i ≤ x.M + A.Jw →
    (∃ l : ℤ, tq i = ((l : ℝ) + 1 / 2) * ocTauPP x.D.α x.D.q x.D.Λ i) ∧
    tq (i + 1) + ocTauP x.D.α x.D.q x.D.Λ i ≤ tq i ∧
    tq i < tq (i + 1) + ocTauPP x.D.α x.D.q x.D.Λ i + ocTauP x.D.α x.D.q x.D.Λ i ∧
    tq i ≤ tq (i + 1) + 2 * ocTauPP x.D.α x.D.q x.D.Λ i ∧
    tq i ∈ ocQuietTimes x.D.α x.D.q x.D.Λ x.D.ζ i
  CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (g.stage i).comps) (fun v => ScalarH v.1.root)
  lifts : ∀ i, x.M < i → i ≤ x.M + A.Jw →
    IsWeakReadoutLifts i A.Nw (A.Jw * A.Rw) R.sX R.sZ (g.stage i) (CcR i)
  W : (i : ℕ) → ℝ → (CompIn (g.stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ
  chain : IsWeakReadoutChain x.M A.Jw A.Nw 0 A.η₀ (fun _ => A.Jw * A.Rw) g.stage CcR W

/-- The genuinely solved reduction at the selected clock. -/
structure WeakEntryReduced {plan : WeakEntryGluePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    {g : WeakEntryStages x} (s : WeakEntrySchedule g) (θ : ℝ → Vec 2 → ℝ) where
  Ur : (i : ℕ) → ∀ v : CompIn (g.stage i).comps, ℝ → TorusHk R.Kw (ScalarH v.1.root)
  Urw : (i : ℕ) → ∀ v : CompIn (g.stage i).comps, ℝ → TorusHk (R.Kw + 1) (ScalarH v.1.root)
  Urk : (i : ℕ) → ∀ v u (_ : (g.stage i).fam.Γ v u), ℝ → TorusHk (R.Kw + x.Dm - 1) (ScalarH u.1.root)
  reduction : IsWeakReduction x.P A.φ₀ A.hφ₀ R.nW x.M A.Jw R.Kw 0 x.a (x.a + A.T₀)
    θ g.stage s.tq Ur Urw Urk

/-- Unknown paired trajectories. The initial trace and raw value are fixed by the
reduction, so this data cannot reset any generated row. -/
structure WeakEntryPair {plan : WeakEntryGluePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    {g : WeakEntryStages x} where
  V : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk R.Kw (ScalarH v.1.root)
  Uw : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk (R.Kw + 1) (ScalarH v.1.root)
  Vw : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk (R.Kw + 1) (ScalarH v.1.root)
  Uk : ∀ v u (_ : g.Gw.fam.Γ v u), ℝ → TorusHk (R.Kw + x.Dm - 1) (ScalarH u.1.root)
  Vk : ∀ v u (_ : g.Gw.fam.Γ v u), ℝ → TorusHk (R.Kw + x.Dm - 1) (ScalarH u.1.root)

end AVRegularity.WeakEntryProofs.Assembly
