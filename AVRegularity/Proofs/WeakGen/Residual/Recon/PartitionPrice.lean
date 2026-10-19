-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Ingredients.Recon.Family.Main
public import AVRegularity.Proofs.WeakGen.Residual.Window.Bill
import AVRegularity.Applications.Local.LabelTrace
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.EntryWeakAssembly.QuietMarginPlan
import AVRegularity.Proofs.WeakGen.Residual.Gluing.TransitionPlan
import AVRegularity.EntryTerminal.Ingredients.Recon.Partition.Scale

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.ChartTransport
namespace AVRegularity.Providers.WeakGen.Residual

/-! The weak window's partition field and the already estimated factory transition
are negatives on the window interior. This is an algebraic identity of the lift
values: no pointwise time derivative of a lifted weak solution is taken. -/

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift CycleComparison.Reconstruction
variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

private theorem weakReconPulse_eq_slot (c : WeakPassageInstance plan R) (i : ℕ)
    (hi : c.M < i)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn (c.stage i).comps) (fun v => ScalarH v.1.root))
    (f : WeakField (c.stage i)) (k : ℤ) :
    pulsePhysicalLift (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2) (c.D.eps (i - 1))
        (c.D.eps i) (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / c.D.eps (i - 1))
        A.Nw (A.Jw * A.Rw) (Cc k)
        (ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
        (ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k)) f =
      weakSlotLift i A.Nw (A.Jw * A.Rw) (c.stage i) Cc k f := by
  have h128 := (plan.base_ge B).trans c.base_ge
  have hΛ : 1 ≤ c.D.Λ := by rw [c.base_eq]; omega
  have hκ : 0 < c.D.κ c.M := lt_of_lt_of_le
    (div_pos (Real.rpow_pos_of_pos
      (Scales.epsilon_basic (m := c.M) B.hq.1 h128).1 _) (by norm_num)) c.band.1.1
  have hc : ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2 = c.D.cellScaleSq i := by
    simp only [ocEll, OCData.cellScaleSq, weak_passage_kap_eq c i hi.le, OCData.eps]
    rw [div_pow, Real.sq_sqrt hκ.le]
  have hd : ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) = c.D.eps i := by
    simp only [ocDStar, div_self hκ.ne', Real.sqrt_one, mul_one, OCData.eps]
  have ha := ocLabel_eq_ocPulseChartIndex c.D.α c.D.q c.D.Λ i k
    (Construction.Stream.ocTauPP_pos hΛ)
  have hchart : ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k) =
      fun s y => c.D.flowOf (i - 1) s y (c.D.slotAnchor i k) := by
    unfold ocChart OCData.flowOf OCData.slotAnchor
    rw [ha]
  have hinv : ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k) =
      fun s y => c.D.flowOf (i - 1) (c.D.slotAnchor i k) y s := by
    unfold ocChartInv OCData.flowOf OCData.slotAnchor
    rw [ha]
  rw [hc, hd, hchart, hinv]
  rfl

/-- The partition input of the free-length window is the negative factory source,
pointwise on the open window; its closed endpoints are irrelevant for the integral. -/
theorem weakReconPartitionField_eq_neg_time (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn (c.stage i).comps) (fun v => ScalarH v.1.root))
    (f : WeakField (c.stage i)) {t : ℝ}
    (ht : t ∈ Set.Ioo (r.tq i) (r.a + A.T₀)) :
    weakReconPartitionField c r i Cc f t =
      -weakResidualGlueTime i A.Nw (A.Jw * A.Rw) (c.stage i) Cc f t := by
  classical
  have hΛ : 1 ≤ c.D.Λ := by rw [c.base_eq]; have := (plan.base_ge B).trans c.base_ge; omega
  have hpart := EntryTerminal.Ingredients.Recon.Family.reconFamily_liftPartition
    (α := c.D.α) (q := c.D.q) (m := i) hΛ
    (c.profile_eq.symm ▸ B.hζ) (r.tq i) (r.a + A.T₀)
  have hz := sum_deriv_eq_zero hpart ht
  funext x v
  change _ = -weakResidualGlueTime i A.Nw (A.Jw * A.Rw) (c.stage i) Cc f t x v
  rw [weak_gluing_time_eq_fixed_sum _ _ _ _ _ _ hΛ (Set.Ioo_subset_Icc_self ht), neg_neg]
  simp only [weakReconPartitionField, weakReconPulse_eq_slot c i hi, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hz, zero_mul, sub_zero]

/-- Multiplication by minus one does not change any squared spatial jet integral. -/
theorem weakReconScalInt_word_neg {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ v, NormedAddCommGroup (h v)] [∀ v, NormedSpace ℝ (h v)]
    (π : ι → ℝ) (rs : ℝ) {j : ℕ} (w : DerivativeWord2 j) (f : Vec 2 → ∀ v, h v) :
    scalInt π (fun x => rs ^ j • orderedDerivative w (fun y => -f y) x) =
      scalInt π (fun x => rs ^ j • orderedDerivative w f x) := by
  have he : (fun y => -f y) = fun y => (-1 : ℝ) • f y := by
    funext y
    exact (neg_one_smul ℝ (f y)).symm
  rw [he, scalInt_word_smul]
  norm_num

end AVRegularity.Providers.WeakGen.Residual
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.ChartTransport
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! Instantiate the original-window partition estimate at the weak slot-lift
factory. The only analytic estimate is the differentiated partition estimate
`cycle_residual_partition_differentiated`. The named raw price is independent of the ambient cap;
its numerical choices precede the plan. -/

open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs Finite.WeakLift
open CycleComparison.Reconstruction Construction.Preservation.FullLift
variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- Both constants in the raw partition factor have the required sign. -/
theorem weakReconPartitionConstants_pos (O : WeakReconPartitionOrders A)
    (R : WeakPassageRequest A) :
    0 ≤ (weakReconPartitionConstants O R).1 ∧
    0 < (weakReconPartitionConstants O R).2 := by
  let P := weakSlotLiftParams A O.Lr R.sX R.sZ
  let hp := weak_gluing_slot_lift_factory_orders A O.Lr
    ((le_max_left _ _).trans O.reserve) R.sX R.sZ
  let g := weak_gluing_time_transition_sum P hp O.reserve O.Acl_pos
    (weakReconPartitionChartBound O) (weakChartJetBudget_ge_one _ _)
  exact ⟨g.choose_spec.choose_spec.1, g.choose_spec.choose_spec.2.1⟩

/-- Nonnegativity of Xp, the additional sign premise of physical_lift. -/
theorem weakReconPartitionFactor_nonneg (O : WeakReconPartitionOrders A)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) :
    0 ≤ weakReconPartitionFactor O c r i := by
  have h128 := (plan.base_ge B).trans c.base_ge
  have he : 0 < c.D.eps i := by
    simpa only [OCData.eps, c.q_eq, c.base_eq] using Applications.eps_pos B.hq.1 h128 (m := i)
  have hC := (weakReconPartitionConstants_pos O R).1
  unfold weakReconPartitionFactor
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (sliceConst_nonneg _ _ _) _)
    (Nat.cast_nonneg _))
    (mul_nonneg (mul_nonneg (mul_nonneg hC (div_nonneg he.le (Real.sqrt_nonneg _)))
      (Real.sqrt_nonneg _)) (Real.exp_pos _).le)

/-- The literal hPB partition bound of the weak reconstruction window. -/
theorem weakReconPartition (plan : WeakPassagePlan)
    (orders : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → WeakReconPartitionOrders A) :
    WeakReconPartitionStatement plan orders := by
  intro hok B A R c r i hi hiJ sX sZ Cc hseq rs hrs hrse f hf hper hmeas
  classical
  let O := orders R
  let P := weakSlotLiftParams A O.Lr R.sX R.sZ
  let hP := weak_gluing_slot_lift_factory_orders A O.Lr
    ((le_max_left _ _).trans O.reserve) R.sX R.sZ
  let K := weakReconPartitionOrder O
  let gate := weak_gluing_time_transition_sum P hP O.reserve O.Acl_pos
    (weakReconPartitionChartBound O) (weakChartJetBudget_ge_one _ _)
  have hK : 4 * (A.Nw + P.capMax) + 2 * O.Acl + 16 + O.Kmax = K := by
    rw [hP.capMax_eq]
    rfl
  have h128 : 128 ≤ A.Λ := (plan.base_ge B).trans c.base_ge
  have hΛ : 1 ≤ c.D.Λ := by rw [c.base_eq]; omega
  obtain ⟨_, _, _, hmodels⟩ := weakSlotLiftAt_planOK hok.2.1 A R
    ((le_max_left _ _).trans O.reserve)
  obtain ⟨hgeo, ⟨slotLifts⟩⟩ := hmodels c i hi hiJ
  have hflowfloor := (hok.2.2 R c.j₀).trans c.level_ge
  rw [weakReconPartitionFlowFloor, dite_eq_left h128] at hflowfloor
  change (uniform_native_physical_flow_jets B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁
    B.hq A.Λ h128 B.ζ B.hζ (K + 2)).choose ≤ c.M at hflowfloor
  have hflow := (uniform_native_physical_flow_jets B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁
    B.hq A.Λ h128 B.ζ B.hζ (K + 2)).choose_spec.2 c.D c.alpha c.q_eq c.base_eq
      c.profile_eq c.streams i (by omega)
  have heps : c.D.eps i ≤ c.D.eps (i - 1) := by
    simpa only [OCData.eps, c.q_eq, c.base_eq] using
      EntryScales.epsilon_antitone B.hq.1 h128 (Nat.sub_le i 1)
  have hkap := weak_passage_kap_eq c i hi.le
  have hkapP := weak_passage_kap_eq c (i - 1) (by omega)
  have hquiet := weak_gluing_slot_lift_original_gaps (weakSlotNativeQuiet hok.1) c hi hiJ slotLifts
  let f₀ : WeakField (c.stage i) := fun t =>
    if t ∈ Set.Icc (r.tq i) (r.a + A.T₀) then f t else 0
  have hf₀ : ∀ t, ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (f₀ t) := by
    intro t
    by_cases ht : t ∈ Set.Icc (r.tq i) (r.a + A.T₀)
    · simpa only [f₀, ht, ite_true] using hf t ht
    · simp only [f₀, ht, ite_false]
      exact contDiff_const
  have hp₀ : ∀ t, IsZ2Periodic (f₀ t) := by
    intro t p x
    by_cases ht : t ∈ Set.Icc (r.tq i) (r.a + A.T₀)
    · simpa only [f₀, ht, ite_true] using hper t ht p x
    · simp only [f₀, ht, ite_false, Pi.zero_apply]
  have hm₀ : Measurable (Function.uncurry f₀) := by
    simpa only [f₀, Function.uncurry_def, ite_apply, Pi.zero_apply] using hmeas
  have hb := gate.choose_spec.choose_spec.2.2 slotLifts hgeo Cc hseq rs hrs hrse heps
    (hkapP.trans hkap.symm)
    (fun slot t ht => by
      rw [hK]
      exact hflow slot.1 slot.2 (c.D.eps (i - 1)) (slotLifts slot).setting.E_pos le_rfl t ht)
    hquiet (r.tq i) (r.a + A.T₀) f₀ (by rw [hK]; exact hf₀) hp₀ hm₀
  generalize hd₀ : gate.choose_spec.choose = d₀ at hb
  generalize hC₀ : gate.choose = C₀ at hb
  rw [hK, hkap, hkapP] at hb
  rw [← hd₀, ← hC₀] at hb
  have hef : ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), f₀ t = f t :=
    fun t ht => by simp only [f₀, ht, ite_true]
  have henergy : classicalStrongEnergy (c.D.eps (i - 1)) (c.D.κ c.M)
      (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (Set.Icc (r.tq i) (r.a + A.T₀)) K f₀ =
      classicalStrongEnergy (c.D.eps (i - 1)) (c.D.κ c.M)
      (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (Set.Icc (r.tq i) (r.a + A.T₀)) K f := by
    unfold classicalStrongEnergy
    apply congrArg (fun z : ℝ≥0∞ => z ^ (1 / 2 : ℝ))
    refine Finset.sum_congr rfl fun v _ => congrArg (fun z => ENNReal.ofReal
      (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ * z) ?_
    apply congrArg₂ (· + ·)
    · exact iSup_congr fun t => iSup_congr fun ht => by rw [hef t ht]
    · apply congrArg (fun z => ENNReal.ofReal (c.D.κ c.M) * z)
      exact setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hef t ht]
  rw [henergy] at hb
  have hc0 : c.D.cellScaleSq i ≠ 0 :=
    (weakData_cellScaleSq_pos c.D hΛ hgeo.fast hgeo.band i).ne'
  have heq : (∫⁻ t in Set.Icc (r.tq i) (r.a + A.T₀),
      (∑ j ∈ Finset.range (O.Kmax + 1), ∑ w : DerivativeWord2 j,
        scalInt (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun x => rs ^ j • orderedDerivative w (weakReconPartitionField c r i Cc f t) x)) ^
          (1 / 2 : ℝ)) =
      ∫⁻ t in Set.Icc (r.tq i) (r.a + A.T₀),
      (∑ j ∈ Finset.range (O.Kmax + 1), ∑ w : DerivativeWord2 j,
        scalInt (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun x => rs ^ j • orderedDerivative w
            (weakResidualGlueTime i A.Nw (A.Jw * A.Rw) (c.stage i) Cc f₀ t) x)) ^
          (1 / 2 : ℝ) := by
    rw [← setLIntegral_congr Ioo_ae_eq_Icc, ← setLIntegral_congr Ioo_ae_eq_Icc]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [weak_gluing_time_input_congr i A.Nw (A.Jw * A.Rw) (c.stage i) Cc hc0
      (hef t (Set.Ioo_subset_Icc_self ht))]
    rw [weakReconPartitionField_eq_neg_time c r i hi Cc f ht]
    apply congrArg (fun z : ℝ≥0∞ => z ^ (1 / 2 : ℝ))
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro w _
    exact weakReconScalInt_word_neg _ rs w _
  rw [heq]
  have hS : 0 ≤ sliceConst (A.Jw * A.Rw) O.Kmax
      (weakReconPartitionChartBound O) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (sliceConst_nonneg _ _ _) _
  have hcount : (0 : ℝ) ≤ ((ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.a + A.T₀)).card * 2 *
      ∑ j ∈ Finset.range (O.Kmax + 1), 2 ^ j * (A.Jw * A.Rw + 1) : ℕ) := Nat.cast_nonneg _
  have hprice : ENNReal.ofReal (weakReconPartitionFactor O c r i) =
      ENNReal.ofReal (sliceConst (A.Jw * A.Rw) O.Kmax
        (weakReconPartitionChartBound O) ^ (1 / 2 : ℝ)) *
      (((ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.a + A.T₀)).card * 2 *
        ∑ j ∈ Finset.range (O.Kmax + 1), 2 ^ j * (A.Jw * A.Rw + 1) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal ((weakReconPartitionConstants O R).1 *
        (c.D.eps i / Real.sqrt (c.D.κ c.M)) * Real.sqrt (1 / ocTau c.D.α c.D.q c.D.Λ i) *
        Real.exp (-((weakReconPartitionConstants O R).2 * ocTau c.D.α c.D.q c.D.Λ i /
          (c.D.eps i / Real.sqrt (c.D.κ c.M)) ^ 2))) := by
    unfold weakReconPartitionFactor
    rw [ENNReal.ofReal_mul (mul_nonneg hS hcount), ENNReal.ofReal_mul hS,
      ENNReal.ofReal_natCast]
  rw [hprice]
  simpa only [weakReconPartitionConstants, gate, mul_assoc] using hb

end AVRegularity.Providers.WeakGen.Residual
end

section
open Homogenization
namespace AVRegularity.Providers.WeakGen.Residual

/-! The scalar partition input. Half the factory exponential absorbs the pulse count,
at a named uniform level floor. The other half is the ordinary gluing term of
the reconstruction bill, as in the terminal model. The degenerate cases are included: no
pulse has zero raw price, Jw=1 has one parent level, and zero datum does not
alter these scalar choices. Every constant and floor precedes the instance. -/

section
open WeakEntryProofs.Assembly
open CycleComparison.Reconstruction

/-- The retained half-rate of the partition exponential. -/
def weakReconPartitionGap {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (O : WeakReconPartitionOrders A) (R : WeakPassageRequest A) : ℝ :=
  (weakReconPartitionConstants O R).2 / 2

/-- The scalar constant multiplying the uncounted gluing term. -/
def weakReconPartitionBillConstant {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (O : WeakReconPartitionOrders A) (R : WeakPassageRequest A) : ℝ :=
  sliceConst (A.Jw * A.Rw) O.Kmax (weakReconPartitionChartBound O) ^ (1 / 2 : ℝ) *
    2 * (∑ j ∈ Finset.range (O.Kmax + 1), 2 ^ j * (A.Jw * A.Rw + 1) : ℕ) *
    (weakReconPartitionConstants O R).1 * Real.sqrt (weakReconPartitionGap O R)

/-- The pulse-count absorption floor is independent of the plan, data and Dm. -/
def weakReconPartitionCountFloor {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (O : WeakReconPartitionOrders A) (R : WeakPassageRequest A) : ℕ :=
  if hΛ : 128 ≤ A.Λ then
    (weak_gluing_quiet_price_eventually B.hq.1 hΛ
      (K := 5 * (1 + A.T₀ * (2 ^ (26 : ℕ) * 81)))
      (A := 2 - (1 + B.α) + 4 * ocDelta B.α B.q)
      (c := weakReconPartitionGap O R / (weak_gluing_parent_scale_prices B).choose)
      (p := 2 * (B.q - 1) + ocGamma B.α B.q - 4 * ocDelta B.α B.q)
      (P := 0) (δ := 1)
      (div_pos (half_pos (weakReconPartitionConstants_pos O R).2)
        (zero_lt_one.trans_le (weak_gluing_parent_scale_prices B).choose_spec.1))
      (weak_gluing_quiet_exponent_pos B.hα₀ B.hq.1) zero_lt_one).choose else 0

/-- Only the fixed pulse-count absorption floor is added to the plan. -/
def WeakReconPartitionPricePlanOK (plan : WeakPassagePlan)
    (orders : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → WeakReconPartitionOrders A) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (j₀ : ℕ),
    weakReconPartitionCountFloor (orders R) R ≤ plan.levelFloor R j₀

/-- The uncounted gluing term of the weak reconstruction bill. -/
def weakReconPartitionBillTerm {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (O : WeakReconPartitionOrders A) (c : WeakPassageInstance plan R) (i : ℕ) : ℝ :=
  let ℓ := c.D.eps i / Real.sqrt (c.D.κ c.M)
  let τ := ocTau c.D.α c.D.q c.D.Λ i
  let cg := weakReconPartitionGap O R
  ℓ * Real.sqrt (1 / (cg * τ)) * Real.exp (-(cg * τ / ℓ ^ 2))

/-- Scalar `hPM`: the raw hPB factor is paid by the uncounted gluing term.
Any bill containing that nonnegative term therefore pays hPM at the named constant. -/
def WeakReconPartitionPriceStatement (plan : WeakPassagePlan)
    (orders : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → WeakReconPartitionOrders A) : Prop :=
  WeakReconPartitionPricePlanOK plan orders →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw →
    weakReconPartitionFactor (orders R) c r i ≤
      weakReconPartitionBillConstant (orders R) R * weakReconPartitionBillTerm (orders R) c i
end

/-! **The partition term of the weak bill is super-polynomially small**:
`weakReconPartitionBillTerm ≤ δ ε_M^{P_w + 2q^{J_w} + 1}` above the named floor
`weakPricePartFloor`. The floor and the constant precede the instance. The degenerate cases are
included: `δ ≤ 0` or `Λ < 128` give floor `0` and no claim; `J_w = 1` has one parent level,
`i - 1 = M`. -/

section
open WeakEntryProofs.Assembly CycleComparison.Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The constant `√(1/c_g) (1 + C_q)` of the partition term against the quiet exponential. -/
def weakPricePartConst (O : WeakReconPartitionOrders A) (R : WeakPassageRequest A) : ℝ :=
  Real.sqrt (1 / weakReconPartitionGap O R) *
    (1 + (weak_gluing_parent_scale_prices B).choose)

theorem weakReconPartitionGap_pos (O : WeakReconPartitionOrders A) (R : WeakPassageRequest A) :
    0 < weakReconPartitionGap O R :=
  half_pos (weakReconPartitionConstants_pos O R).2

/-- The level floor of the partition term at the factor `δ`. -/
def weakPricePartFloor (O : WeakReconPartitionOrders A) (R : WeakPassageRequest A)
    (δ : ℝ) : ℕ :=
  if h : 128 ≤ A.Λ ∧ 0 < δ then
    (weak_gluing_quiet_price_eventually B.hq.1 h.1
      (K := weakPricePartConst O R) (A := 0)
      (c := weakReconPartitionGap O R / (weak_gluing_parent_scale_prices B).choose)
      (p := 2 * (B.q - 1) + ocGamma B.α B.q - 4 * ocDelta B.α B.q)
      (P := A.Pw + 2 * B.q ^ A.Jw + 1) (δ := δ)
      (div_pos (weakReconPartitionGap_pos O R)
        (zero_lt_one.trans_le (weak_gluing_parent_scale_prices B).choose_spec.1))
      (weak_gluing_quiet_exponent_pos B.hα₀ B.hq.1) h.2).choose
  else 0

/-- **The partition term is below `δ ε_M^{P}`** above the floor. -/
theorem weakReconPartitionBillTerm_price (O : WeakReconPartitionOrders A)
    (plan : WeakPassagePlan) (c : WeakPassageInstance plan R) (i : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hi : c.M < i) (hfl : weakPricePartFloor O R δ ≤ c.M) :
    weakReconPartitionBillTerm O c i ≤
      δ * c.D.eps c.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) := by
  have h128 := (plan.base_ge B).trans c.base_ge
  set cg := weakReconPartitionGap O R with hcgd
  set Cq := (weak_gluing_parent_scale_prices B).choose with hCqd
  set p := 2 * (B.q - 1) + ocGamma B.α B.q - 4 * ocDelta B.α B.q with hpd
  set E := c.D.eps (i - 1) with hEd
  set ℓ := c.D.eps i / Real.sqrt (c.D.κ c.M) with hℓd
  set τ := ocTau c.D.α c.D.q c.D.Λ i with hτd
  have hcg : 0 < cg := weakReconPartitionGap_pos O R
  have hCq : 0 < Cq := zero_lt_one.trans_le (weak_gluing_parent_scale_prices B).choose_spec.1
  have hp : 0 < p := weak_gluing_quiet_exponent_pos B.hα₀ B.hq.1
  have hE : 0 < E := by
    simpa only [E, OCData.eps, c.q_eq, c.base_eq] using
      (Scales.epsilon_basic (m := i - 1) B.hq.1 h128).1
  have hE1 : E ≤ 1 := by
    simpa only [E, OCData.eps, c.q_eq, c.base_eq] using
      (Scales.epsilon_basic (m := i - 1) B.hq.1 h128).2.1
  have hν : 0 < c.D.κ c.M := lt_of_lt_of_le
    (div_pos (Real.rpow_pos_of_pos
      (Scales.epsilon_basic (m := c.M) B.hq.1 h128).1 _) (by norm_num)) c.band.1.1
  have hℓ : 0 < ℓ := div_pos
    (by simpa only [OCData.eps, c.q_eq, c.base_eq] using
      (Scales.epsilon_basic (m := i) B.hq.1 h128).1) (Real.sqrt_pos.mpr hν)
  have hτ : 0 < τ := Construction.Stream.ocTau_pos (by rw [c.base_eq]; omega)
  have hs := (weak_gluing_parent_scale_prices B).choose_spec.2 A.Λ h128 c.M
    (c.D.κ c.M) c.band.1 i hi
  have hquiet : Cq⁻¹ * E ^ (-p) ≤ τ / ℓ ^ 2 := by
    simpa only [Cq, E, p, τ, ℓ, OCData.eps, c.alpha, c.q_eq, c.base_eq] using hs.1
  have hheat := weak_gluing_heat_price hE hE1 hCq hcg.le hp.le hℓ hτ hquiet
  -- the term
  have hterm : weakReconPartitionBillTerm O c i =
      Real.sqrt (1 / cg) * (ℓ * Real.sqrt (1 / τ) * Real.exp (-(cg * τ / ℓ ^ 2))) := by
    unfold weakReconPartitionBillTerm
    have : Real.sqrt (1 / (cg * τ)) = Real.sqrt (1 / cg) * Real.sqrt (1 / τ) := by
      rw [← Real.sqrt_mul (by positivity), one_div_mul_one_div]
    simp only [← hcgd, ← hℓd, ← hτd]
    rw [this]; ring
  have hfl' : (weak_gluing_quiet_price_eventually B.hq.1 h128
      (K := weakPricePartConst O R) (A := 0) (c := cg / Cq) (p := p)
      (P := A.Pw + 2 * B.q ^ A.Jw + 1) (δ := δ) (div_pos hcg hCq) hp hδ).choose ≤ c.M := by
    unfold weakPricePartFloor at hfl
    simp only [h128, hδ, and_self, dite_true] at hfl
    exact hfl
  have hd := (weak_gluing_quiet_price_eventually B.hq.1 h128
      (K := weakPricePartConst O R) (A := 0) (c := cg / Cq) (p := p)
      (P := A.Pw + 2 * B.q ^ A.Jw + 1) (δ := δ) (div_pos hcg hCq) hp hδ).choose_spec
    (i - 1) (by omega)
  simp only [Real.rpow_zero, mul_one, neg_zero] at hd
  have hP : 0 ≤ A.Pw + 2 * B.q ^ A.Jw + 1 := by
    have := A.Pw_pos
    have : 0 ≤ B.q ^ A.Jw := pow_nonneg (zero_lt_one.trans B.hq.1).le _
    linarith
  have hEM : E ^ (A.Pw + 2 * B.q ^ A.Jw + 1) ≤ c.D.eps c.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) := by
    refine Real.rpow_le_rpow hE.le ?_ hP
    simp only [E, OCData.eps, c.q_eq, c.base_eq]
    exact EntryScales.epsilon_antitone B.hq.1 h128 (by omega)
  rw [hterm]
  have hK : 0 ≤ Real.sqrt (1 / cg) := Real.sqrt_nonneg _
  calc Real.sqrt (1 / cg) * (ℓ * Real.sqrt (1 / τ) * Real.exp (-(cg * τ / ℓ ^ 2)))
      ≤ Real.sqrt (1 / cg) * ((1 + Cq) * Real.exp (-(cg / Cq * E ^ (-p)))) :=
        mul_le_mul_of_nonneg_left hheat hK
    _ = weakPricePartConst O R * Real.exp (-(cg / Cq * E ^ (-p))) := by
        unfold weakPricePartConst; ring
    _ ≤ δ * E ^ (A.Pw + 2 * B.q ^ A.Jw + 1) := by
        simpa only [hEd, OCData.eps, c.q_eq, c.base_eq] using hd
    _ ≤ δ * c.D.eps c.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) :=
        mul_le_mul_of_nonneg_left hEM hδ.le
end

/-! **The price of the bill of the weak reconstruction window**.

`weakReconBill c r i (ε_M^{2a_*(R_w+1)}) (weakReconPartitionBillTerm O c i) ≤
δ · ε_M^{P_w + 2q^{J_w} + 1}` for every `δ > 0` above the named level floor
`weakReconPriceFloor O R δ`, under the two menu inequalities of `WeakLiftedComparisonStatement`,
for every passage `M < i ≤ M + J_w` and every run with `r.a ≤ r.tq i`.

The constant is `weakReconPriceConst B A` (a function of the base and the physical data); the floor
is `max 1` of the point where `ε_m ≤ δ/(2·const)` and the partition floor at `δ/2`. The degenerate
cases are included: `T_obs = 0` kills the cleanup factor; `J_w = 1` has `ε_{i-1} = ε_M`; `δ ≥ 1`
still needs the floor; the bill reads the run only through `T_obs ≤ T₀`, and `D_m` does not
occur. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Window

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The constant of the five analytic summands. -/
def weakReconPriceConst (B : WeakCoefficientBase) (A : WeakCoefficientPhysical B) : ℝ :=
  weakPriceConst A.Nw (Real.sqrt A.T₀ * Real.sqrt 2) (weakPriceLowerConst B.q A.Jw)

theorem weakReconPriceConst_pos (B : WeakCoefficientBase) (A : WeakCoefficientPhysical B) :
    0 < weakReconPriceConst B A := by
  have hc := weakPriceLowerConst_pos B.q A.Jw
  unfold weakReconPriceConst weakPriceConst
  have : 0 ≤ Real.sqrt A.T₀ * Real.sqrt 2 := by positivity
  have h2 : 0 ≤ (2 : ℝ) ^ A.Nw := by positivity
  positivity

/-- **The level floor of the price**, at the factor `δ`. -/
def weakReconPriceFloor (O : WeakReconPartitionOrders A) (R : WeakPassageRequest A)
    (δ : ℝ) : ℕ :=
  if h : 128 ≤ A.Λ ∧ 0 < δ then
    max 1 (max (EntryWeakProofs.weak_epsilon_rpow_eventually_small B.hq.1 h.1
      (p := 1) one_pos (div_pos h.2 (mul_pos two_pos (weakReconPriceConst_pos B A)))).choose
      (weakPricePartFloor O R (δ / 2)))
  else 0

/-- The five analytic summands and the flux price, at an instance (abstract form). -/
theorem weakReconBill_eq_abstract (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (i : ℕ) (tt Xp : ℝ) (h128 : 128 ≤ A.Λ) :
    weakReconBill c r i tt Xp =
      (c.D.eps i / c.D.eps (i - 1)) ^ A.Nw + Real.sqrt (c.D.κ c.M / c.D.κ c.M) * tt +
        (c.D.eps i / c.D.eps (i - 1)) ^ 2 * tt +
        (c.D.eps i / c.D.eps (i - 1)) ^ A.Nw *
          (Real.sqrt (wTobs c r i) / (c.D.eps i / Real.sqrt (c.D.κ c.M)) *
            (c.D.eps i / c.D.eps (i - 1)) ^ 1) +
        (c.D.eps i / c.D.eps (i - 1)) ^ 2 *
          (Real.sqrt (wTobs c r i) / (c.D.eps i / Real.sqrt (c.D.κ c.M)) *
            (c.D.eps i / c.D.eps (i - 1)) ^ 1) * tt + Xp := by
  have hν : 0 < c.D.κ c.M := lt_of_lt_of_le
    (div_pos (Real.rpow_pos_of_pos
      (Scales.epsilon_basic (m := c.M) B.hq.1 h128).1 _) (by norm_num)) c.band.1.1
  have hc : weakReconContrast c i = c.D.eps i / c.D.eps (i - 1) := by
    unfold weakReconContrast ocDStar
    rw [div_self hν.ne', Real.sqrt_one, mul_one]; rfl
  have hZ : weakReconZ c r i = Real.sqrt (wTobs c r i) / (c.D.eps i / Real.sqrt (c.D.κ c.M)) *
      (c.D.eps i / c.D.eps (i - 1)) ^ 1 := by
    unfold weakReconZ ocEll; rfl
  unfold weakReconBill
  rw [hc, hZ]

/-- The terminal diffusivity is positive and at most `2`. -/
theorem weakReconPrice_kappa (c : WeakPassageInstance plan R) (h128 : 128 ≤ A.Λ) :
    0 < c.D.κ c.M ∧ c.D.κ c.M ≤ 2 := by
  have he := Scales.epsilon_basic (m := c.M) B.hq.1 h128
  have hp := Applications.band_exponent_pos B.hα₀ B.hq.1
  have h1 : ocEpsilon B.q A.Λ c.M ^ ((1 + B.α) - ocGamma B.α B.q) ≤ 1 :=
    Real.rpow_le_one he.1.le he.2.1 hp.le
  have h2 : 0 < ocEpsilon B.q A.Λ c.M ^ ((1 + B.α) - ocGamma B.α B.q) :=
    Real.rpow_pos_of_pos he.1 _
  have hb := c.band.1
  exact ⟨lt_of_lt_of_le (by positivity) hb.1, by linarith [hb.2]⟩

/-- **The price of the bill of the weak window.** -/
theorem weakReconBill_price (O : WeakReconPartitionOrders A) (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) (i : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hN : A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1))
    (hR : A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 < 2 * weakAStar B.α B.q * (A.Rw + 1))
    (hi : c.M < i) (hiJ : i ≤ c.M + A.Jw) (hat : r.a ≤ r.tq i)
    (hfl : weakReconPriceFloor O R δ ≤ plan.levelFloor R c.j₀) :
    weakReconBill c r i (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1)))
        (weakReconPartitionBillTerm O c i) ≤
      δ * c.D.eps c.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) := by
  have h128 := (plan.base_ge B).trans c.base_ge
  have hfM := hfl.trans c.level_ge
  unfold weakReconPriceFloor at hfM
  simp only [h128, hδ, and_self, dite_true] at hfM
  have hM1 : 1 ≤ c.M := (le_max_left _ _).trans hfM
  have hMe := ((le_max_left _ _).trans ((le_max_right _ _).trans hfM))
  have hMp : weakPricePartFloor O R (δ / 2) ≤ c.M :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hfM)
  have hq := B.hq
  set Cb := weakReconPriceConst B A with hCb
  have hCb0 := weakReconPriceConst_pos B A
  set P := A.Pw + 2 * B.q ^ A.Jw + 1 with hPd
  set S := B.q ^ A.Jw with hSd
  have hS0 : 0 ≤ S := pow_nonneg (zero_lt_one.trans hq.1).le _
  have hP0 : 0 ≤ P := by have := A.Pw_pos; linarith
  have eq_eps : ∀ k, c.D.eps k = ocEpsilon B.q A.Λ k := fun k => by
    simp only [OCData.eps, c.q_eq, c.base_eq]
  have hbasic := fun k => Scales.epsilon_basic (m := k) hq.1 h128
  have hanti := EntryScales.epsilon_antitone hq.1 h128
  obtain ⟨hκ0, hκ2⟩ := weakReconPrice_kappa c h128
  -- the scale facts
  set e := ocEpsilon B.q A.Λ c.M with hed
  set a := ocEpsilon B.q A.Λ (i - 1) with had
  set b := ocEpsilon B.q A.Λ i with hbd
  have he0 : 0 < e := (hbasic _).1
  have he1 : e ≤ 1 := (hbasic _).2.1
  have ha0 : 0 < a := (hbasic _).1
  have hb0 : 0 < b := (hbasic _).1
  have hae : a ≤ e := hanti (by omega)
  have hba : b ≤ a := hanti (by omega)
  have hbq : b ≤ 2 * a ^ B.q := by
    have := Scales.epsilon_q_step hq.1 hq.2.1 h128 (m := i) (by omega)
    simpa only [Nat.add_sub_cancel] using this
  -- the lower chain
  have hlow : weakPriceLowerConst B.q A.Jw * e ^ S ≤ a := by
    obtain ⟨k, hk⟩ : ∃ k, i - 1 = c.M + k := ⟨i - 1 - c.M, by omega⟩
    have hkJ : k ≤ A.Jw := by omega
    have h1 := weakPrice_eps_lower hq.1 h128 hM1 k
    have h2 : weakPriceLowerConst B.q A.Jw ≤ weakPriceLowerConst B.q k :=
      weakPriceLowerConst_antitone hq.1 hkJ
    have h3 : e ^ S ≤ e ^ (B.q ^ k) :=
      Real.rpow_le_rpow_of_exponent_ge he0 he1
        (pow_le_pow_right₀ hq.1.le hkJ)
    have h4 := weakPriceLowerConst_pos B.q A.Jw
    rw [had, hk]
    calc weakPriceLowerConst B.q A.Jw * e ^ S
        ≤ weakPriceLowerConst B.q k * e ^ (B.q ^ k) :=
          mul_le_mul h2 h3 (Real.rpow_nonneg he0.le _) (weakPriceLowerConst_pos B.q k).le
      _ ≤ _ := h1
  -- the flux price
  have htt0 : 0 ≤ e ^ (2 * weakAStar B.α B.q * (A.Rw + 1)) := Real.rpow_nonneg he0.le _
  have htt : e ^ (2 * weakAStar B.α B.q * (A.Rw + 1)) ≤ e ^ (P + S + 1) :=
    Real.rpow_le_rpow_of_exponent_ge he0 he1 (by linarith)
  have hT : wTobs c r i ≤ A.T₀ := by unfold wTobs; linarith
  have hfive := weakPrice_five_le (N := A.Nw) (e := e) (a := a) (b := b) (q := B.q) (P := P)
    (S := S) (T := wTobs c r i) (T₀ := A.T₀) (κ := c.D.κ c.M)
    (tt := e ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) (cL := weakPriceLowerConst B.q A.Jw)
    he1 ha0 hae hb0 hba hbq hq.1 hP0 hS0 (by linarith) hκ0 hκ2 hT
    (weakPriceLowerConst_pos B.q A.Jw) hlow htt0 htt
  rw [weakReconBill_eq_abstract c r i _ _ h128]
  simp only [eq_eps] at hfive ⊢
  -- the partition term
  have hpart := weakReconPartitionBillTerm_price O plan c i (half_pos hδ) hi hMp
  have hsmall : e ≤ δ / (2 * Cb) := by
    have := (EntryWeakProofs.weak_epsilon_rpow_eventually_small hq.1 h128 (p := 1) one_pos
      (div_pos hδ (mul_pos two_pos hCb0))).choose_spec c.M hMe
    simpa only [Real.rpow_one] using this
  have hCe : Cb * e ^ (P + 1) ≤ δ / 2 * e ^ P := by
    rw [Real.rpow_add_one he0.ne']
    have : Cb * e ≤ δ / 2 := by
      rw [le_div_iff₀ (mul_pos two_pos hCb0)] at hsmall
      linarith
    have hP : 0 ≤ e ^ P := Real.rpow_nonneg he0.le _
    nlinarith [mul_le_mul_of_nonneg_right this hP]
  have hpart' : weakReconPartitionBillTerm O c i ≤ δ / 2 * e ^ P := by
    simpa only [eq_eps] using hpart
  have hsum := add_le_add (hfive.trans hCe) hpart'
  calc _ ≤ δ / 2 * e ^ P + δ / 2 * e ^ P := hsum
    _ = δ * e ^ P := by ring
end

end AVRegularity.Providers.WeakGen.Residual
end
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Providers.WeakGen.Residual

/-! Partition price. The weak scale ledger absorbs the pulse count into half the
exponential above the named floor. The terminal abstract-real algebra then
pays the raw factor by its usual uncounted gluing term. No new analytic estimate. -/

open WeakEntryProofs.Assembly CycleComparison.Reconstruction CycleComparison.Assembly
variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The named constant required by hPM is nonnegative. -/
theorem weakReconPartitionBillConstant_nonneg (O : WeakReconPartitionOrders A)
    (R : WeakPassageRequest A) : 0 ≤ weakReconPartitionBillConstant O R := by
  have hS := Real.rpow_nonneg (sliceConst_nonneg (A.Jw * A.Rw) O.Kmax
    (weakReconPartitionChartBound O)) (1 / 2 : ℝ)
  have hC := (weakReconPartitionConstants_pos O R).1
  unfold weakReconPartitionBillConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hS (by norm_num))
    (Nat.cast_nonneg _)) hC) (Real.sqrt_nonneg _)

/-- The partition price is paid by the standard weak-window gluing term. -/
theorem weakReconPartitionPrice (plan : WeakPassagePlan)
    (orders : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → WeakReconPartitionOrders A) :
    WeakReconPartitionPriceStatement plan orders := by
  intro hok B A R c r i hi hiJ
  let O := orders R
  let cg := weakReconPartitionGap O R
  let Cq := (weak_gluing_parent_scale_prices B).choose
  let a := 2 - (1 + B.α) + 4 * ocDelta B.α B.q
  let p := 2 * (B.q - 1) + ocGamma B.α B.q - 4 * ocDelta B.α B.q
  let Cτ : ℝ := 2 ^ (26 : ℕ) * 81
  let E := c.D.eps (i - 1)
  let ℓ := c.D.eps i / Real.sqrt (c.D.κ c.M)
  let τ := ocTau c.D.α c.D.q c.D.Λ i
  let Kg := sliceConst (A.Jw * A.Rw) O.Kmax (weakReconPartitionChartBound O) ^ (1 / 2 : ℝ) *
    2 * (∑ j ∈ Finset.range (O.Kmax + 1), 2 ^ j * (A.Jw * A.Rw + 1) : ℕ) *
      (weakReconPartitionConstants O R).1
  have h128 := (plan.base_ge B).trans c.base_ge
  have hΛ : 1 ≤ c.D.Λ := by rw [c.base_eq]; omega
  have hcg : 0 < cg := half_pos (weakReconPartitionConstants_pos O R).2
  have hCq : 0 < Cq := zero_lt_one.trans_le (weak_gluing_parent_scale_prices B).choose_spec.1
  have hp : 0 < p := weak_gluing_quiet_exponent_pos B.hα₀ B.hq.1
  have hδ := (Scales.admissible_exponent_facts B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq).2.1
  have ha : 0 ≤ a := by dsimp only [a]; linarith only [B.hα₁, hδ]
  have hE : 0 < E := by
    simpa only [E, OCData.eps, c.q_eq, c.base_eq] using
      (Scales.epsilon_basic (m := i - 1) B.hq.1 h128).1
  have hE1 : E ≤ 1 := by
    simpa only [E, OCData.eps, c.q_eq, c.base_eq] using
      (Scales.epsilon_basic (m := i - 1) B.hq.1 h128).2.1
  have hν : 0 < c.D.κ c.M := lt_of_lt_of_le
    (div_pos (Real.rpow_pos_of_pos
      (Scales.epsilon_basic (m := c.M) B.hq.1 h128).1 _) (by norm_num)) c.band.1.1
  have hℓ : 0 < ℓ := div_pos
    (by simpa only [OCData.eps, c.q_eq, c.base_eq] using
      (Scales.epsilon_basic (m := i) B.hq.1 h128).1) (Real.sqrt_pos.mpr hν)
  have hτ : 0 < τ := Construction.Stream.ocTau_pos hΛ
  have hs := (weak_gluing_parent_scale_prices B).choose_spec.2 A.Λ h128 c.M
    (c.D.κ c.M) c.band.1 i hi
  have hquiet : Cq⁻¹ * E ^ (-p) ≤ τ / ℓ ^ 2 := by
    simpa only [Cq, E, p, τ, ℓ, OCData.eps, c.alpha, c.q_eq, c.base_eq] using hs.1
  have hτinv : τ⁻¹ ≤ Cτ * E ^ (-a) := by
    simpa only [Cτ, a, E, τ, OCData.eps, c.alpha, c.q_eq, c.base_eq] using hs.2
  have hw := weak_quiet_window c r i hi hiJ
  have hatq : r.a ≤ r.tq i := hw.1.trans hw.2.2.1.le
  have hT : 0 ≤ r.a + A.T₀ - r.tq i := sub_nonneg.mpr hw.2.1
  have hT₀ : r.a + A.T₀ - r.tq i ≤ A.T₀ := by linarith only [hatq]
  let Bp := (ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.a + A.T₀)).card
  have hBp : (Bp : ℝ) ≤ 5 * (1 + (r.a + A.T₀ - r.tq i) / τ) := by
    have h := obsPulses_card_le c.D.α c.D.q hΛ i (r.tq i) hT
    rw [show r.tq i + (r.a + A.T₀ - r.tq i) = r.a + A.T₀ by ring] at h
    exact h
  have hcount : (Bp : ℝ) ≤ 5 * (1 + A.T₀ * Cτ) * E ^ (-a) := by
    simpa only [neg_zero, Real.rpow_zero, mul_one, zero_add] using
      pulseCount_le_powerLaw hE hE1 (a := 0) (by norm_num) ha hT
        (by simpa only [neg_zero, Real.rpow_zero, mul_one] using hT₀) hτ hτinv hBp
  have hexp : Real.exp (-(cg * τ / ℓ ^ 2)) ≤ Real.exp (-(cg / Cq * E ^ (-p))) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    calc cg / Cq * E ^ (-p) = cg * (Cq⁻¹ * E ^ (-p)) := by ring
      _ ≤ cg * (τ / ℓ ^ 2) := mul_le_mul_of_nonneg_left hquiet hcg.le
      _ = cg * τ / ℓ ^ 2 := (mul_div_assoc _ _ _).symm
  let decay := weak_gluing_quiet_price_eventually B.hq.1 h128
    (K := 5 * (1 + A.T₀ * Cτ)) (A := a) (c := cg / Cq) (p := p) (P := 0) (δ := 1)
    (div_pos hcg hCq) hp zero_lt_one
  have hfloor := (hok R c.j₀).trans c.level_ge
  rw [weakReconPartitionCountFloor, dite_eq_left h128] at hfloor
  change decay.choose ≤ c.M at hfloor
  have hd := decay.choose_spec (i - 1) (by omega)
  have hd' : 5 * (1 + A.T₀ * Cτ) * E ^ (-a) * Real.exp (-(cg / Cq * E ^ (-p))) ≤ 1 := by
    simpa only [E, OCData.eps, c.q_eq, c.base_eq, Real.rpow_zero, mul_one] using hd
  have hKcount : 0 ≤ 5 * (1 + A.T₀ * Cτ) := by
    have : 0 ≤ A.T₀ := hT.trans hT₀
    dsimp only [Cτ]
    positivity
  have hcard : (Bp : ℝ) * Real.exp (-(cg * τ / ℓ ^ 2)) ≤ 1 :=
    (mul_le_mul hcount hexp (Real.exp_pos _).le
      (mul_nonneg hKcount (Real.rpow_nonneg hE.le _))).trans hd'
  have hKg : 0 ≤ Kg := by
    have hS := Real.rpow_nonneg (sliceConst_nonneg (A.Jw * A.Rw) O.Kmax
      (weakReconPartitionChartBound O)) (1 / 2 : ℝ)
    have hC := (weakReconPartitionConstants_pos O R).1
    dsimp only [Kg]
    exact mul_nonneg (mul_nonneg (mul_nonneg hS (by norm_num)) (Nat.cast_nonneg _)) hC
  have key := EntryTerminal.Ingredients.Recon.reconPartScale_alg Kg Bp ℓ τ cg 1
    (weakReconPartitionBillTerm O c i) hKg (Nat.cast_nonneg _) hℓ.le hτ hcg hcard le_rfl
  have h2 : 2 * cg = (weakReconPartitionConstants O R).2 := by
    dsimp only [cg, weakReconPartitionGap]
    ring
  rw [h2, mul_one] at key
  convert key using 1
  · dsimp only [weakReconPartitionFactor, Kg, Bp, ℓ, τ]
    push_cast
    ring
  · rfl

/-- The sign and payment fields of physical_lift for any bill containing its gluing term. -/
theorem weakReconPartition_pay_bill (plan : WeakPassagePlan)
    (orders : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → WeakReconPartitionOrders A)
    (hok : WeakReconPartitionPricePlanOK plan orders)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (hiJ : i ≤ c.M + A.Jw) {bill : ℝ}
    (hbill : weakReconPartitionBillTerm (orders R) c i ≤ bill) :
    0 ≤ weakReconPartitionBillConstant (orders R) R ∧
    0 ≤ weakReconPartitionFactor (orders R) c r i ∧
    weakReconPartitionFactor (orders R) c r i ≤
      weakReconPartitionBillConstant (orders R) R * bill := by
  have hC := weakReconPartitionBillConstant_nonneg (orders R) R
  exact ⟨hC, weakReconPartitionFactor_nonneg (orders R) c r i,
    (weakReconPartitionPrice plan orders hok c r i hi hiJ).trans
      (mul_le_mul_of_nonneg_left hbill hC)⟩

end AVRegularity.Providers.WeakGen.Residual
end
end
