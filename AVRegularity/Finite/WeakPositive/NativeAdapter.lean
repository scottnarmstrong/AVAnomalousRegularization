-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Finite.WeakPositive.PositiveInputJets
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Construction.TerminalLift.Assembly
public import AVRegularity.Proofs.WeakGen.Assembly.WeakCommonCase
public import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.EntryTerminal.Ingredients.LiftField.LiftField
import AVRegularity.Finite.WeakLift.IdentitySeparation
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleResidualDifferentiated
import Mathlib.Tactic.PNatToNat

section
section
/-! The actual active weak pulse transfers positive input jets with one Schur budget. -/

@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Finite.WeakLift
open CycleComparison.Lift Construction.Preservation.FullLift EntryWeakProofs

/-- Numerical word price, fixed before the level, component family, phase or datum. -/
def weakPositiveChartWordPrice {N H U : ℕ} (P : WeakPositiveParameters N H U) (K r : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, nativeChartTransportConstant P.chartC (K + N) (n + 1) r) *
    ((2 : ℝ) ^ (K + N) * (K + N + 1) ^ 2)

/-- Every active normalized pulse has a dimension-free positive input jet bound. -/
theorem weak_positive_chart_pulse_word_bound {N H U : ℕ} {P : WeakPositiveParameters N H U}
    (C : WeakPositiveChartCase P) (slot : OddSlot)
    (hcut : ocCutoff C.D.α C.D.q C.D.Λ C.i slot.1 C.t ≠ 0)
    {r : ℕ} (hr : r ≤ C.K) (β : DerivativeWord2 r) (x : Vec 2) :
    C.D.eps C.i ^ r * ‖orderedDerivative β
      (fun X => toCompSpace C.π (weakPositiveChartPulse C slot.1 X)) x‖ ≤
      (weakPositiveChartWordPrice P C.K r * C.Cpath) *
        (C.D.eps C.i / C.D.eps (C.i - 1)) *
        ∑ α ∈ multiIndicesBetween 1 (C.K + N), C.D.eps (C.i - 1) ^ (α 0 + α 1) *
          ‖partialDerivative α C.r.value x‖ := by
  let A := C.slotLift slot
  let e := C.D.eps C.i
  let E := C.D.eps (C.i - 1)
  let ε := e / E
  let f := fun X v => C.f v X
  let Φ := fun X => C.D.flowOf (C.i - 1) C.t X (C.D.slotAnchor C.i slot.1)
  let Ψ := fun X => C.D.flowOf (C.i - 1) (C.D.slotAnchor C.i slot.1) X C.t
  let Dc := fun hh n => if n = 0 then 0 else A.coeff hh n
  let M := fun hh => weakPositiveMatrix A hh
  let ct := ∑ n ∈ Finset.range N, nativeChartTransportConstant P.chartC (C.K + N) (n + 1) r
  have hct : 0 ≤ ct := Finset.sum_nonneg fun n _ =>
    nativeChartTransportConstant_nonneg P.chartC_ge _ _ _
  have hΛ : 1 ≤ C.D.Λ := by have := C.geometry.Λ_ge; omega
  have he : 0 < e := Construction.Stream.ocEpsilon_pos hΛ
  have hE : 0 < E := Construction.Stream.ocEpsilon_pos hΛ
  have heE : e ≤ E := Applications.eps_antitone C.geometry.q_gt C.geometry.Λ_ge (by omega)
  have hε : 0 ≤ ε := (div_pos he hE).le
  have hε1 : ε ≤ 1 := (div_le_one hE).mpr heE
  have hf := (weak_positive_chart_input_regular C).1
  have hΦ : ContDiff ℝ (C.K + N : ℕ) Φ :=
    (CycleReference.streamFlow_spatial_smooth (C.D.hΦ (C.i - 1)) C.t
      (C.D.slotAnchor C.i slot.1)).of_le (by simp)
  have hΨ : ContDiff ℝ (r : ℕ) Ψ :=
    (CycleReference.streamFlow_spatial_smooth (C.D.hΦ (C.i - 1))
      (C.D.slotAnchor C.i slot.1) C.t).of_le (by simp)
  have hJ : ChartTransport.JetBound Φ (C.K + N) P.chartC E :=
    fun n hn hnK X => C.geometry.forward C.t slot hcut n hn
      (hnK.trans (Nat.add_le_add_right C.K_le N)) X
  have hJΨ : ChartTransport.JetBound Ψ r P.chartC E :=
    fun n hn hnr X => C.geometry.backward C.t slot hcut n hn
      (hnr.trans (hr.trans (C.K_le.trans (Nat.le_add_right U N)))) X
  have ht := weak_positive_chart_active_time C slot hcut
  have hid := (C.identified slot).1
  have hp : weakPositiveChartPulse C slot.1 = fun X =>
      pulsePhysicalLift (C.D.cellScaleSq C.i) E e ε N H Dc
        (fun _ => Φ) (fun _ => Ψ) (fun _ => f) C.t X := by
    funext X
    apply pulsePhysicalLift_coeff_congr
    intro hh hhh n _hn m α Y z v u
    by_cases hn0 : n = 0
    · simp only [positiveLiftCoefficients, Dc, hn0, ite_true]
    · simpa only [positiveLiftCoefficients, Dc, hn0, ite_false] using
        hid hh hhh n m α _ ht Y z v u
  have hd (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ N) :
      AmbientLiftCoefficientData (pulseParallel slot.1) (weakSlotLeft C.D C.i slot.1)
        (weakSlotRight C.D C.i slot.1) A.setting.window (E / E) n C.K C.K (Dc hh n) (M hh) := by
    simpa only [Dc, ite_eq_right (by omega : n ≠ 0)] using
      (C.graded slot hh hhh n hn).mono C.K_le C.K_le
  have hm (hh : ℕ) (hhh : hh ≤ H) (v u : CompIn C.G.comps) : 0 ≤ M hh v u :=
    (C.graded slot hh hhh 0 (Nat.zero_le N)).nonneg v u
  have hb (v : CompIn C.G.comps) : e ^ r *
      ‖orderedDerivative β (fun X => weakPositiveChartPulse C slot.1 X v) x‖ ≤
      (ε * ct) * ∑ u, (∑ hh ∈ Finset.range (H + 1), M hh v u) *
        ∑ j ∈ Finset.range (C.K + N + 1), if j = 0 then 0 else
          E ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖ := by
    rw [hp]
    exact positive_pulse_fixed_matrix_word_bound_of_data Dc M hm hd
      (div_nonneg hE.le hE.le) ((div_self hE.ne').le) r hr hr f hf Φ hΦ
      P.chartC_ge hJ he le_rfl heE Ψ hΨ hJΨ β x
      (weak_chart_inverse C.D (C.i - 1) C.t (C.D.slotAnchor C.i slot.1) x)
      (C.D.cellScaleSq C.i) ε C.t hε hε1 ht
      (fun hh _ => by simp only [Dc, ite_eq_left rfl])
      (fun hh hhh n hn1 hn α Y z v u => by
        simpa only [Dc, ite_eq_right (by omega : n ≠ 0)] using
          (C.identified slot).2 hh hhh n hn1 hn α _ ht Y z v u) v
  have hg : ContDiff ℝ (r : ℕ) (fun X => weakPositiveChartPulse C slot.1 X) :=
    contDiff_pi.mpr fun v => ((weak_positive_chart_pulse_regular C slot hcut).1 v).of_le
      (by exact_mod_cast hr)
  have hout := weakPositive_weighted_word_bound β C.π C.mass _ hg x he.le
    (mul_nonneg hε hct) C.Cpath_nonneg _ (C.paths slot) _ hb
  have hin := weakPositive_weighted_input_density_le hE.le C.π C.mass f hf x
  have hv : (fun X => weakPositiveWeightedVector C.π (f X)) = C.r.value := C.value.symm
  rw [hv] at hin
  apply hout.trans ((mul_le_mul_of_nonneg_left hin
    (mul_nonneg (mul_nonneg hε hct) C.Cpath_nonneg)).trans_eq ?_)
  dsimp only [weakPositiveChartWordPrice, ct, ε, e, E]
  simp only [Nat.cast_add]
  ac_rfl

end AVRegularity.Finite.WeakLift
end
end

section
/-! The exact positive physical chart leaf: normalized pulse bounds and convex gluing. -/

@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Finite.WeakLift
open Construction.Preservation.FullLift

private theorem weakPositive_chart_word_price_nonneg {N H U : ℕ}
    (P : WeakPositiveParameters N H U) (K r : ℕ) : 0 ≤ weakPositiveChartWordPrice P K r :=
  mul_nonneg (Finset.sum_nonneg fun n _ => nativeChartTransportConstant_nonneg P.chartC_ge _ _ _)
    (mul_nonneg (by positivity) (sq_nonneg _))

private theorem weakPositive_chart_glued_word_bound {N H U : ℕ}
    {P : WeakPositiveParameters N H U} (Ct : ℝ) (hCt : 0 ≤ Ct)
    (hprice : ∀ K ≤ U, ∀ r ≤ K, weakPositiveChartWordPrice P K r ≤ Ct)
    (C : WeakPositiveChartCase P) {r : ℕ} (hr : r ≤ C.K) (β : DerivativeWord2 r) (x : Vec 2) :
    C.D.eps C.i ^ r * ‖orderedDerivative β C.correction x‖ ≤
      (Ct * C.Cpath) * (C.D.eps C.i / C.D.eps (C.i - 1)) *
        ∑ α ∈ multiIndicesBetween 1 (C.K + N), C.D.eps (C.i - 1) ^ (α 0 + α 1) *
          ‖partialDerivative α C.r.value x‖ := by
  have hΛ : 1 ≤ C.D.Λ := by have := C.geometry.Λ_ge; omega
  have he := Construction.Stream.ocEpsilon_pos (q := C.D.q) (n := C.i) hΛ
  have hE := Construction.Stream.ocEpsilon_pos (q := C.D.q) (n := C.i - 1) hΛ
  have hτ := Construction.Stream.ocTau_pos (α := C.D.α) (q := C.D.q) (m := C.i) hΛ
  let kset := ocObsPulses C.D.α C.D.q C.D.Λ C.i C.t C.t
  let F := fun k X => toCompSpace C.π (weakPositiveChartPulse C k X)
  let B := (Ct * C.Cpath) * (C.D.eps C.i / C.D.eps (C.i - 1)) *
    ∑ α ∈ multiIndicesBetween 1 (C.K + N), C.D.eps (C.i - 1) ^ (α 0 + α 1) *
      ‖partialDerivative α C.r.value x‖
  have hreg (k : ℤ) (hk : k ∈ kset)
      (hcut : ocCutoff C.D.α C.D.q C.D.Λ C.i k C.t ≠ 0) :
      ContDiff ℝ (r : ℕ∞) (F k) := by
    let slot : OddSlot := ⟨k, (Finset.mem_filter.mp hk).2.1⟩
    obtain ⟨hcd, hp⟩ := weak_positive_chart_pulse_regular C slot hcut
    exact (EntryTerminal.Ingredients.compField_contDiff_periodic (S := C.G.comps) C.π r
      (fun v X => weakPositiveChartPulse C k X v)
      (fun v => (hcd v).of_le (by exact_mod_cast hr))
      (fun v p X => congrFun (hp p X) v)).1
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (mul_nonneg hCt C.Cpath_nonneg) (div_pos he hE).le)
    (Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hE.le _) (norm_nonneg _))
  have hb (k : ℤ) (hk : k ∈ kset)
      (hcut : ocCutoff C.D.α C.D.q C.D.Λ C.i k C.t ≠ 0) :
      C.D.eps C.i ^ r * ‖orderedDerivative β (F k) x‖ ≤ B := by
    let slot : OddSlot := ⟨k, (Finset.mem_filter.mp hk).2.1⟩
    exact (weak_positive_chart_pulse_word_bound C slot hcut hr β x).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hprice C.K C.K_le r hr) C.Cpath_nonneg)
          (div_pos he hE).le)
        (Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hE.le _) (norm_nonneg _)))
  rw [weak_positive_chart_correction_eq_pulses C]
  exact convex_spatial_word_norm_le kset (fun k => ocCutoff C.D.α C.D.q C.D.Λ C.i k C.t)
    (fun k _ => Providers.CascadeInvariants.ocCutoff_nonneg k C.t)
    (le_of_eq (obs_cutoff_sum_one _ _ _ _ _ hτ)) F hreg he.le hB β x hb

/-- The pointwise positive chart estimate, with constants chosen before all data. -/
theorem weak_positive_pointwise_chart : WeakPositivePointwiseChartStatement := by
  intro N H U P
  let Ct := ∑ K ∈ Finset.range (U + 1), ∑ r ∈ Finset.range (K + 1),
    weakPositiveChartWordPrice P K r
  have hCt : 0 ≤ Ct := Finset.sum_nonneg fun K _ =>
    Finset.sum_nonneg fun r _ => weakPositive_chart_word_price_nonneg P K r
  have hprice (K : ℕ) (hK : K ≤ U) (r : ℕ) (hr : r ≤ K) :
      weakPositiveChartWordPrice P K r ≤ Ct :=
    (Finset.single_le_sum (s := Finset.range (K + 1)) (a := r)
      (fun r _ => weakPositive_chart_word_price_nonneg P K r)
      (Finset.mem_range.mpr (by omega))).trans
      (Finset.single_le_sum (s := Finset.range (U + 1)) (a := K)
        (fun K _ => Finset.sum_nonneg (s := Finset.range (K + 1)) fun r _ =>
        weakPositive_chart_word_price_nonneg P K r) (Finset.mem_range.mpr (by omega)))
  refine ⟨Ct, hCt, ?_⟩
  intro C
  constructor
  · intro x
    simpa only [pow_zero, orderedDerivative_zero, one_mul] using
      weakPositive_chart_glued_word_bound Ct hCt hprice C (Nat.zero_le C.K)
        (fun j : Fin 0 => j.elim0) x
  · intro β hβ x
    have horder : β 0 + β 1 ≤ C.K := (Finset.mem_filter.mp hβ).2.2
    have hβeq : ![β 0, β 1] = β := by ext j; fin_cases j <;> rfl
    rw [← hβeq, ← weakPositive_sorted_word_eq_partial (β 0) (β 1) C.correction]
    exact weakPositive_chart_glued_word_bound Ct hCt hprice C horder _ x

end AVRegularity.Finite.WeakLift
end
end

section
/-! The actual weak coefficient templates give native Cauchy bounds without a unit
context certificate or a replacement stage. The original record size is retained. -/

@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped Classical ENNReal
namespace AVRegularity.Finite.WeakLift
open Providers.WeakGen Construction.Preservation.FullLift Construction.Preservation.Buffer

variable {D : OCData} {Dm j₀ : ℕ} {bw : ℝ}

/-- Enlarging the actual scalar certificate price preserves its witnesses. -/
theorem weakCertified_mono_cost {G : GenStage D ScalarH Dm bw j₀}
    {cost cost' mres : ℝ} {L : ℕ} (hc : WeakCertified cost mres L G)
    (hcost : cost ≤ cost') (hε : 0 ≤ D.eps G.level) : WeakCertified cost' mres L G := by
  intro v u γ d I c
  obtain ⟨f, F, hf, he, hs⟩ := hc v u γ d I c
  refine ⟨f, F, hf, he, hs.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcost (G.fam.identity v u γ).record.size_nonneg)
    (pow_nonneg (div_nonneg (G.fam.identity v u γ).record.length_pos.le hε) _)

/-- Remove only the non-increasing record-length power from the actual certificate. -/
theorem weakCertified_coefficient_forms {G : GenStage D ScalarH Dm bw j₀}
    {cost mres : ℝ} {L : ℕ} (hc : WeakCertified cost mres L G) (hcost : 0 ≤ cost)
    (hε : 0 < D.eps G.level) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hlen : (G.fam.identity v u γ).record.length ≤ D.eps G.level)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
    ∃ (f : OddSlot → GenSort.Sem .ctx)
      (F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ),
      (∀ p, IsHolExtension D bw j₀ G.level p.1 (f p) (F p)) ∧
      CoeffIs G v u γ d I c f ∧
      ctxSize D bw j₀ G.level F mres L ≤
        ENNReal.ofReal (cost * (G.fam.identity v u γ).record.size) := by
  obtain ⟨f, F, hf, he, hs⟩ := hc v u γ d I c
  refine ⟨f, F, fun p => (hf p).2, he, hs.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have hr0 : 0 ≤ (G.fam.identity v u γ).record.length / D.eps G.level :=
    div_nonneg (G.fam.identity v u γ).record.length_pos.le hε.le
  have hr1 : (G.fam.identity v u γ).record.length / D.eps G.level ≤ 1 :=
    (div_le_one hε).2 hlen
  exact mul_le_of_le_one_right
    (mul_nonneg hcost (G.fam.identity v u γ).record.size_nonneg) (pow_le_one₀ hr0 hr1)

/-- Time measurability uses holomorphic template realization, independently of its price. -/
theorem weakHolGen_flux_time_measurable {G : GenStage D ScalarH Dm bw j₀}
    (hG : WeakHolGen G) (p : OddSlot) (ctx : StageCtx D bw j₀ G.level p)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (X z : Vec 2) :
    Measurable (fun t : ocPulseWindow D.α D.q D.Λ G.level p.1 =>
      G.fam.flux p ctx v u γ d I t X z) := by
  apply Measurable.of_eval
  intro c
  obtain ⟨f, F, hf, he⟩ := hG v u γ d I c
  let ch := ctx.1.recenter D (D.eps (G.level - 1) • X)
  by_cases hch : IsAdmissibleChain D bw j₀ G.level p.1 ch
  · have hm := holExtension_time_measurable (hf p).2 ch hch z
    have hfun : (fun t : ocPulseWindow D.α D.q D.Λ G.level p.1 =>
        G.fam.flux p ctx v u γ d I t X z c) =
        (fun t : ocPulseWindow D.α D.q D.Λ G.level p.1 => f p t ch z) := by
      funext t
      simpa only [ch, ite_eq_left hch] using he p ctx t t.property X z
    rw [hfun]
    exact hm
  · have hfun : (fun t : ocPulseWindow D.α D.q D.Λ G.level p.1 =>
        G.fam.flux p ctx v u γ d I t X z c) = fun _ => (0 : ℝ) := by
      funext t
      simpa only [ch, ite_eq_right hch] using he p ctx t t.property X z
    rw [hfun]
    exact measurable_const

/-- The Cauchy constant precedes the actual stage, every record and its ambient order. -/
theorem uniform_weak_native_coefficient_jet_bounds (bw : ℝ) (hb : 0 < bw) (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
    ∀ (D : OCData) (Dm j₀ : ℕ) (G : GenStage D ScalarH Dm bw j₀),
      1 ≤ G.level → j₀ ≤ G.level → 0 < D.eps (G.level - 1) →
      0 < D.eps G.level → G.IsSlotTransverse →
    ∀ (cost mres : ℝ) (L : ℕ), 0 ≤ cost → 0 ≤ mres → mres ≤ 2 →
      WeakCertified cost mres L G →
    ∀ (p : OddSlot), (G.actual p).1 = nativeChain G.level p.1 →
    ∀ (v u : CompIn G.comps) (γ : G.fam.Γ v u),
      (G.fam.identity v u γ).record.length ≤ D.eps G.level →
    ∀ (d : ℕ) (I : DerivativeWord2 (d - 1)) (lam : ℝ), 0 ≤ lam →
    ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
    ∀ r q : ℕ, r + q ≤ n → ∀ X z : Vec 2,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
        (fun w => G.fam.flux p (G.actual p) v u γ d I t (lam • Y) w) z) X‖ ≤
        B (r + q) * lam ^ r * (2 * cost * (G.fam.identity v u γ).record.size) := by
  obtain ⟨B, hB, hjet⟩ := uniform_native_actual_scaled_mixed_exists_jet_bounds bw hb n
  refine ⟨B, hB, ?_⟩
  intro D Dm j₀ G hi hj hε hεi hpar cost mres L hcost hm hm2 hc p ha v u γ hlen d I lam hlam
    t ht r q hrq X z
  choose f F hhol he hsize using fun c : Fin 2 =>
    weakCertified_coefficient_forms hc hcost hεi v u γ hlen d I c
  have hs := hjet ScalarH D Dm j₀ G hi hj hε hpar p v u γ d I mres hm hm2 L
    (fun _ => cost * (G.fam.identity v u γ).record.size)
    (fun _ => mul_nonneg hcost (G.fam.identity v u γ).record.size_nonneg)
    (fun c => f c p) F (fun c => hhol c p) hsize
    (fun c ctx t ht X z => he c p ctx t ht X z) ha lam hlam t ht r q hrq X z
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, mul_assoc] using hs

/-- Actual native coefficient regularity follows from the same witnesses. -/
theorem weakCertified_native_flux_joint_contDiff {G : GenStage D ScalarH Dm bw j₀}
    {cost mres : ℝ} {L : ℕ} (hc : WeakCertified cost mres L G)
    (hcost : 0 ≤ cost) (hm : 0 ≤ mres) (hm2 : mres ≤ 2)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (hεi : 0 < D.eps G.level) (hpar : G.IsSlotTransverse)
    (p : OddSlot) (ha : (G.actual p).1 = nativeChain G.level p.1)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hlen : (G.fam.identity v u γ).record.length ≤ D.eps G.level)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (n : ℕ)
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1) :
    ContDiff ℝ (n : ℕ∞) (Function.uncurry (G.fam.flux p (G.actual p) v u γ d I t)) := by
  obtain ⟨B, _hB, hreg⟩ := uniform_native_normalized_vector_joint_exists_jet_bounds bw hb n
  choose f F hhol he hsize using fun c : Fin 2 =>
    weakCertified_coefficient_forms hc hcost hεi v u γ hlen d I c
  have hn := (hreg ScalarH D Dm j₀ G hi hj hε hpar p v u γ d I mres hm hm2 L
    (fun _ => cost * (G.fam.identity v u γ).record.size)
    (fun _ => mul_nonneg hcost (G.fam.identity v u γ).record.size_nonneg)
    (fun c => f c p) F (fun c => hhol c p) hsize
    (fun c ctx t ht X z => he c p ctx t ht X z) t ht).1
  let pack : Vec 2 × Vec 2 → Vec (2 + 2) := fun Y =>
    EntryWeakProofs.independentIntrinsicParameterPacking 2 Y.1 Y.2
  have hpack : ContDiff ℝ (n : ℕ∞) pack := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [pack, EntryWeakProofs.independentIntrinsicParameterPacking, Fin.addCases_left]
      fun_prop
    · simp only [pack, EntryWeakProofs.independentIntrinsicParameterPacking, Fin.addCases_right]
      fun_prop
  have hn' := hn.comp hpack
  have heq : (fun Y : Vec 2 × Vec 2 => G.fam.flux p
      (nativeStageContext G hi hj p (D.eps (G.level - 1) •
        EntryWeakProofs.independentIntrinsicSlowProjection 2 (pack Y)))
      v u γ d I t 0 (EntryWeakProofs.independentStoredParameterProjection 2 (pack Y))) =
      Function.uncurry (G.fam.flux p (G.actual p) v u γ d I t) := by
    funext Y c
    simp only [pack, EntryWeakProofs.independentIntrinsicParameterPacking_slow,
      EntryWeakProofs.independentIntrinsicParameterPacking_stored]
    exact (actual_native_flux_eq G hi hj p ha v u γ d I c t (f c p)
      (fun ctx X z => he c p ctx t ht X z) Y.1 Y.2).symm
  exact heq ▸ hn'

end AVRegularity.Finite.WeakLift
end
end

section
/-! Match the finite weak factory's fixed scalar/menu data with the weak-case construction.
The auxiliary normalized kernel and time parameters are chosen before the actual stage;
they add no premise to the representation statement. -/

@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.Finite.WeakLift
open WeakEntryProofs.Assembly

/-- One fixed admissible auxiliary kernel template. -/
structure WeakParentMollifier where
  value : Vec 2 → ℝ
  integrable : Integrable value
  smooth : ContDiff ℝ (⊤ : ℕ∞) value
  nonneg : ∀ z, 0 ≤ value z
  mass : ∫ z, value z = 1
  support : Function.support value ⊆ Analysis.Convolution.closedEuclideanUnitBall

/-- Select the auxiliary template independently of every menu and stage. -/
def weakParentMollifier : WeakParentMollifier :=
  Classical.choice (show Nonempty WeakParentMollifier from by
    obtain ⟨φ, hi, hs, hn, hm, hc⟩ := exists_mollifier
    exact ⟨⟨φ, hi, hs, hn, hm, hc⟩⟩)

/-- The common base of the existing coefficient plan, with the exact same scalar parameters. -/
def weakParentCoefficientBase (B : WeakParentBase) : WeakCoefficientBase where
  α := B.α
  s := B.s
  hα₀ := B.hα₀
  hα₁ := B.hα₁
  hs₀ := B.hs₀
  hs₁ := B.hs₁
  q := B.q
  hq := B.hq
  ζ := B.ζ
  hζ := B.hζ

/-- The weak case's auxiliary physical choices are harmless fixed witnesses. -/
def weakParentCoefficientPhysical {B : WeakParentBase} (R : WeakParentMenu B) :
    WeakCoefficientPhysical (weakParentCoefficientBase B) where
  Λ := R.Λ
  φ₀ := (weakParentMollifier).value
  hφ₀ := (weakParentMollifier).integrable
  smooth := (weakParentMollifier).smooth
  nonneg := (weakParentMollifier).nonneg
  mass := (weakParentMollifier).mass
  support := (weakParentMollifier).support
  bw := R.bw
  bw_pos := R.hbw
  bw_small := R.hbw1
  Jw := R.J
  τ := 1 / 2
  T₀ := 1
  Pw := 1
  η₀ := R.η
  Jw_pos := R.hJ
  τ_pos := by norm_num
  τ_small := by norm_num
  Pw_pos := zero_lt_one
  η₀_pos := R.hη
  η₀_small := R.hη1
  Nw := R.N
  Rw := R.R
  Lw := R.J * R.N
  Nw_pos := R.hN
  Lw_le := le_rfl
  σw := R.σ
  σw_pos := R.hσ
  σw_small := R.hσ1

end AVRegularity.Finite.WeakLift
end
end
end

section
section
/-! The actual weak stored ledger bounds every stage's record matrix. No component-count
factor or new passage induction is introduced; the all-stage induction is reused. -/

@[expose] public noncomputable section
open Homogenization Filter Topology
namespace AVRegularity.Finite.WeakLift
open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs
  Construction.Preservation.Ledger CycleComparison.Lift

/-- The record matrix's total is dominated by the scalar stored-weight total. -/
theorem weak_parent_record_total_le {B : WeakParentBase} {R : WeakParentMenu B} {sX sZ : ℕ}
    (C : WeakParentCase R sX sZ) :
    (∑ v, ∑ u, weakParentPrice C v u) ≤ weakStoredTotal C.G R.N R.J R.η := by
  have hmap (v u : CompIn C.G.comps) (γ : C.G.fam.Γ v u) :
      ‖(C.G.fam.identity v u γ).map‖ ≤ 1 := by
    by_cases hi : C.i = C.M + R.J
    · have hempty := C.construction.2.1.2.2.1
      rw [← hi] at hempty
      exact (hempty v u).false γ |>.elim
    · exact weakConstruction_identity_map_norm_le_one C.PW
        (⟨R.N, R.R, sX, sZ, R.η, C.M + R.J⟩ : WeakMenu) C.M R.J 0
        (C.D.termRW R.σ C.M) C.stage C.construction C.i C.hi.le (by have := C.hiJ; omega) v u γ
  simp only [weakStoredTotal, LedgerEdge, Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro u _
  unfold weakParentPrice recordMajorant
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro γ _
  exact mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_right (hmap v u γ)
      (C.G.fam.identity v u γ).record.size_nonneg).trans_eq (one_mul _))
    (Real.sqrt_nonneg _)

/-- The mass sums are bounded uniformly, with a floor before construction and phase. -/
theorem weak_parent_mass_sums : WeakParentMassSumsStatement := by
  intro B
  refine ⟨128, le_rfl, ?_⟩
  intro R _ _hscope
  let A := weakParentCoefficientPhysical R
  obtain ⟨Ce, hCe, heddy⟩ := exists_weakStoredEddy_constant (weakParentCoefficientBase B) A
  let Q : ℝ := weakStoredPassageBudget R.N R.J R.R
  let Ctot : ℝ := (2 * Q) ^ R.J * Ce
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    exact_mod_cast weakStoredPassageBudget_one_le R.N R.J R.R
  have h2Q : 1 ≤ 2 * Q := hQ.trans (le_mul_of_one_le_left (zero_le_one.trans hQ) (by norm_num))
  have hCtot : 0 < Ctot := mul_pos (pow_pos (by linarith only [hQ]) _)
    (zero_lt_one.trans_le hCe)
  have hχ : 0 < weakChi B.α B.q R.η := weakChi_pos B.hα₀ B.hq.1 B.hq.2.1 R.hη1
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    ((EntryScales.epsilon_rpow_tendsto_zero B.hq.1 R.hΛ hχ).eventually
      (gt_mem_nhds (inv_pos.mpr hCtot)))
  refine ⟨0, 0, ?_⟩
  intro sX sZ _ _
  refine ⟨⟨1, zero_le_one⟩, fun _ => ⟨M₀, ?_⟩⟩
  intro C _ hM
  have hΛ : 1 ≤ C.D.Λ := by rw [C.hΛ]; have := R.hΛ; omega
  have heps (i : ℕ) : 0 < C.D.eps i := Construction.Stream.ocEpsilon_pos hΛ
  have hsmall : Ctot * C.D.eps C.M ^ weakChi B.α B.q R.η ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hM₀ C.M hM).le hCtot.le
    rw [mul_inv_cancel₀ hCtot.ne'] at hh
    simpa only [OCData.eps, C.hq, C.hΛ] using hh
  have hbound := weakConstruction_storedTotal_stage_bound C.PW
    (⟨R.N, R.R, sX, sZ, R.η, C.M + R.J⟩ : WeakMenu) C.M R.J 0
    (C.D.termRW R.σ C.M) C.stage C.construction R.hN R.hJ heps
    (Ce * C.D.eps C.M ^ weakChi B.α B.q R.η)
    (mul_nonneg (zero_lt_one.trans_le hCe).le (Real.rpow_nonneg (heps _).le _))
    (fun i hi _ => heddy C.M C.D C.hα C.hq C.hΛ C.term C.band R.hΛ i hi)
    (by simpa only [Ctot, Q, mul_assoc] using hsmall)
    (C.M + R.J - C.i) (by have := C.hi; omega)
  have hidx : C.M + R.J - (C.M + R.J - C.i) = C.i := by have := C.hi; have := C.hiJ; omega
  rw [hidx] at hbound
  have hpow := pow_le_pow_right₀ h2Q (show C.M + R.J - C.i ≤ R.J by have := C.hi; omega)
  have htotal : weakStoredTotal C.G R.N R.J R.η ≤ 1 := hbound.trans
    ((mul_le_mul_of_nonneg_right hpow
      (mul_nonneg (zero_lt_one.trans_le hCe).le (Real.rpow_nonneg (heps _).le _))).trans
      (by simpa only [Ctot, Q, mul_assoc] using hsmall))
  have hsum : (∑ v, ∑ u, weakParentPrice C v u) ≤ 1 :=
    (weak_parent_record_total_le C).trans htotal
  have hn (v u : CompIn C.G.comps) : 0 ≤ weakParentPrice C v u :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun γ _ =>
      mul_nonneg (norm_nonneg _) (C.G.fam.identity v u γ).record.size_nonneg)
  refine ⟨hn, ?_, ?_⟩
  · intro v
    exact (Finset.single_le_sum (fun v _ => Finset.sum_nonneg (fun u _ => hn v u))
      (Finset.mem_univ v)).trans hsum
  · intro u
    rw [Finset.sum_comm] at hsum
    exact (Finset.single_le_sum (fun u _ => Finset.sum_nonneg (fun v _ => hn v u))
      (Finset.mem_univ u)).trans hsum

end AVRegularity.Finite.WeakLift
end
end

section
/-! The physical flow budgets and shift induction provide all geometry of the
parent-radius factory. The charts are tested on the odd pulses used by the glued lift. -/

@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Finite.WeakLift
open Construction.Preservation.FullLift EntryWeakProofs

private theorem weakParent_active_in_window {α q : ℝ} {Λ i : ℕ} (hΛ : 1 ≤ Λ)
    (slot : ℤ) (t : ℝ) (ht : ocCutoff α q Λ i slot t ≠ 0) :
    t ∈ ocPulseWindow α q Λ i slot := by
  have h := CycleReference.cutoff_nonzero_distance hΛ slot t ht
  have hτ := Construction.Stream.ocTau_pos (α := α) (q := q) (m := i) hΛ
  rw [abs_lt] at h
  constructor <;> linarith only [h.1, h.2, hτ]

/-- The geometry selector is already uniform for every weak menu, including the root case. -/
theorem weak_parent_geometry : WeakParentGeometryStatement := by
  intro B
  refine ⟨128, le_rfl, ?_⟩
  intro R _ _
  let K := R.Lr + 3 + R.N
  obtain ⟨Mflow, _hMflow, hflow⟩ := uniform_native_physical_flow_jets B.α B.s B.q
    B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq R.Λ R.hΛ B.ζ B.hζ K
  refine ⟨0, 0, ?_⟩
  intro sX sZ _ _
  refine ⟨⟨weakChartJetBudget K 0, weakChartJetBudget_ge_one K 0⟩,
    fun _ => ⟨Mflow, ?_⟩⟩
  intro C _ hM
  have hΛ : 1 ≤ C.D.Λ := by rw [C.hΛ]; have := R.hΛ; omega
  have hζ : IsFastProfile C.D.ζ := C.hζ.symm ▸ B.hζ
  have hband : IsOCBandChain C.D.α C.D.q C.D.Λ C.D.ζ C.D.term C.D.κ := by
    rw [C.hα, C.hq, C.hΛ, C.hζ, C.term]
    exact C.band
  have heps (n : ℕ) : 0 < C.D.eps n := Construction.Stream.ocEpsilon_pos hΛ
  have hlevel : C.G.level = C.i :=
    weakConstruction_level C.PW _ C.M R.J 0 _ C.stage C.construction C.i C.hi.le C.hiJ
  have hnatural : C.G.IsNatural (C.M + R.J) := by
    by_cases hi : C.i = C.M + R.J
    · simpa only [WeakParentCase.G, hi] using C.construction.2.1.2.2.2
    · exact weakConstruction_output_natural C.PW _ C.M R.J 0 _ C.stage
        C.construction C.i C.hi.le (by have := C.hiJ; omega)
  have hshift := WeakEntryProofs.Assembly.weakConstruction_shiftInvariant C.PW _
    C.M R.J 0 _ C.stage C.construction hζ
    (fun _ => Construction.Stream.ocTau_pos hΛ) heps
    (fun i _ _ => (weakData_cellScaleSq_pos C.D hΛ hζ hband i).le) C.i C.hi.le C.hiJ
  have htorus : IsTorusCompatible C.G.fam C.G.actual (C.D.eps (C.i - 1)) := by
    simpa only [hlevel] using GenStage.isTorusCompatible_of_shiftInvariant hnatural hshift
  refine {
    level := hlevel
    q_gt := C.hq.symm ▸ B.hq.1
    Λ_ge := C.hΛ.symm ▸ R.hΛ
    fast := hζ
    stream := ?_
    band := hband
    plateau := C.term.symm ▸ C.hi.le
    torus := htorus
    forward := ?_
    backward := ?_ }
  · simpa only [C.hα, C.hq, C.hΛ, C.hζ] using C.stream
  · intro t slot ht
    exact (hflow C.D C.hα C.hq C.hΛ C.hζ C.stream C.i
      (by have := C.hi; omega) slot.1 slot.2 (C.D.eps (C.i - 1))
      (heps _) le_rfl t (weakParent_active_in_window hΛ slot.1 t ht)).1
  · intro t slot ht
    exact (hflow C.D C.hα C.hq C.hΛ C.hζ C.stream C.i
      (by have := C.hi; omega) slot.1 slot.2 (C.D.eps (C.i - 1))
      (heps _) le_rfl t (weakParent_active_in_window hΛ slot.1 t ht)).2

end AVRegularity.Finite.WeakLift
end
end

section
/-! The full setting assembly from actual native facts. Nonempty families use their capped
source on the original window; empty families may be padded to degree two. Metric/drift
constants precede the data, and the assembly returns both original recurrences. -/

@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Finite.WeakLift
open Construction.Preservation.FullLift Construction.TerminalLift CycleComparison.Lift
  EntryWeakProofs

/-- The setting and both recurrences from the actual source, geometry and mass certificates. -/
theorem weak_parent_setting_selector : WeakParentSettingAssemblyStatement := by
  intro B
  refine ⟨128, le_rfl, ?_⟩
  intro R _ _hscope
  let H := R.J * R.R
  let K := weakParentSlow R
  let k := weakParentFast R
  let qs := K + 4 * (H + 1) * (R.N + weakParentCap R) ^ 2
  obtain ⟨CG, m₀, _hCG, hm₀, hmetric⟩ := terminal_lift_metric_certificates
    B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq R.Λ R.hΛ B.ζ B.hζ qs
  let Cw : ℕ → ℝ := fun n => 2 * pulseFastDerivativeConstant n
  refine ⟨0, 0, ?_⟩
  intro sX sZ _ _
  refine ⟨(CG, Cw), fun _ => ⟨m₀, ?_⟩⟩
  intro C _ hM c Cj S P hgeom hn hS
  have hΛ : 1 ≤ C.D.Λ := by rw [C.hΛ]; have := R.hΛ; omega
  have hζ : IsFastProfile C.D.ζ := C.hζ.symm ▸ B.hζ
  have hi : 1 ≤ C.i := by have := C.hi; omega
  have hterm : C.D.term < C.i := by rw [C.term]; exact C.hi
  obtain ⟨hρ, hcell, hlam⟩ := plateau_parent_lift_radius_bounds C.D hgeom.q_gt
    hgeom.Λ_ge hζ hgeom.band C.i hterm
  let ρ := C.D.eps (C.i - 1)
  refine ⟨fun slot => ?_⟩
  by_cases hzero : R.R = 0
  · let emptyEdge : ConstituentEdges 2 (fun v : CompIn C.G.comps => ScalarH v.1.root) :=
      fun _ _ _ => []
    let Q := familyLiftData C.D C.i slot.1 (nativeChain C.i slot.1) ρ emptyEdge
    have hz (v u : CompIn C.G.comps) (d : Finset.Icc 2 2) : Q.edge v u d = [] := by
      simp only [Q, familyLiftData, liftEdges, emptyEdge, List.map_nil]
    have hzNative (v u : CompIn C.G.comps) (d : Finset.Icc 2 C.Dm) :
        (weakPositiveNativeData C.i C.G slot).edge v u d = [] := by
      let weakParentZeroDepthIsEmpty : IsEmpty (C.G.fam.Γ v u) := hn.empty_zero hzero v u
      simp [weakPositiveNativeData, familyLiftData, liftEdges, ChartedFamily.fiber]
    have hg := hmetric (CompIn C.G.comps) (fun v => ScalarH v.1.root) 2 C.D
      C.hα C.hq C.hΛ C.hζ C.stream hgeom.band C.i (by have := C.hi; omega)
      slot.1 slot.2 ρ hρ.le emptyEdge
    let a := weakSlotLeft C.D C.i slot.1
    let b := weakSlotRight C.D C.i slot.1
    let qsEmpty := K + 4 * (H + 1) * (R.N + 2) ^ 2
    have hres := effective_lift_reserves_le K k k H R.N (weakParentCap R) 2
      (le_max_left _ _)
    let qf := max k (k + 2) + H * 2 + 2 * R.N + 2 * 2
    have hw := native_lift_balanced_drift_sup_of_bound C.D C.i slot.1
      (nativeChain C.i slot.1) ρ emptyEdge a b qf Cw
      (fun n _hn t _ht z => terminal_plateau_balanced_drift_bound
        B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq R.Λ R.hΛ B.ζ B.hζ C.D
        C.hα C.hq C.hΛ C.hζ hgeom.band C.i hterm.le hi slot.1 slot.2 n t z)
    have hdepth : HasDepthAtMost Q.edge H := by
      intro path
      refine ⟨0, ?_⟩
      intro d
      rw [hz]
    have hsource : IsScaledJetEnvelope (weakParentMass C) Q.edge (Set.Icc a b)
        (ρ / C.D.eps (C.i - 1)) Cj qsEmpty qf (weakParentPrice C) S.1 := by
      refine ⟨hS.nonneg, hS.row_sum, hS.col_sum, ?_⟩
      intro v u r _ q _
      simp only [hz, List.map_nil, List.sum_nil, Finset.sum_const_zero, mul_zero]
      exact zero_le
    have hsetting := native_lift_setting_of_fiber_facts C.D C.i hi hΛ hζ hgeom.band
      slot ρ hρ hcell hlam Q rfl rfl rfl (weakParentMass C) hn.mass_pos
      H R.N K k k R.hN (le_refl 2) CG Cw Cj (weakParentPrice C) S.1
      hg.2 (fun r hr => hg.1 r (hr.trans hres.1)) hw hdepth
      (fun v u d γ hγ => by rw [hz] at hγ; contradiction)
      (fun v u d γ hγ => by rw [hz] at hγ; contradiction)
      (fun v u d γ hγ => by rw [hz] at hγ; contradiction) hsource
    have hex := Providers.cycle_lift_exists R.N K k k 2 H CG Cw Cj Q
      (weakParentMass C) a b (C.D.eps C.i) (C.D.kap C.i) (C.D.kap (C.i - 1))
      ρ (C.D.eps (C.i - 1)) (C.D.eps C.i / Real.sqrt (C.D.kap C.i))
      (ocDStar C.D.q C.D.Λ C.i (C.D.kap C.i) (C.D.kap (C.i - 1)))
      (ocDStar C.D.q C.D.Λ C.i (C.D.kap C.i) (C.D.kap (C.i - 1)) / ρ)
      (ρ / C.D.eps (C.i - 1)) (pulseParallel slot.1)
      (pulseShearProfile C.D.α C.D.q C.D.Λ C.i C.D.ζ (C.D.kap C.i) slot.1)
      qsEmpty qf (weakParentPrice C) S.1 hsetting
    let Cc := Classical.choose hex
    have hc := Classical.choose_spec hex
    refine {
      cap := 2
      cap_ge := le_rfl
      cap_le := le_max_left _ _
      Q := Q
      price := weakParentPrice C
      metric_eq := rfl
      drift_eq := rfl
      eta_eq := rfl
      edge_agree := Or.inl ⟨hz, hzNative⟩
      source_eq := ?_
      edge_fast := by
        intro S _hS _hn v u d γ hγ _α
        rw [hz] at hγ
        contradiction
      setting := hsetting
      coeff := Cc
      sequence := hc
      ambient := weak_root_sequence_degree_congr Q (weakPositiveNativeData C.i C.G slot)
        rfl rfl rfl hz hzNative _ _ R.N H a b Cc hc }
    intro Dc a₀ hh n _hn t _ht X z
    exact congrFun (congrFun
      (weak_root_source_degree_congr Q (weakPositiveNativeData C.i C.G slot)
        rfl rfl rfl hz hzNative Dc a₀ hh n t) X) z
  · have hR : 1 ≤ R.R := by omega
    have hprod : 1 ≤ R.J * R.N := by
      simpa only [one_mul] using Nat.mul_le_mul R.hJ R.hN
    have hKD : weakParentCap R ≤ C.Dm := by
      have hb := hn.cap_nonempty hR
      unfold weakParentCap
      omega
    have hcapN : R.N ≤ weakParentCap R := by
      have hp : R.N ≤ R.J * R.N := by
        simpa only [one_mul] using Nat.mul_le_mul_right R.N R.hJ
      exact hp.trans ((Nat.le_add_left _ _).trans (le_max_right _ _))
    let raw := weakPositiveNativeData C.i C.G slot
    let a := weakSlotLeft C.D C.i slot.1
    let b := weakSlotRight C.D C.i slot.1
    let Q := restrictLiftData (weakParentCap R) hKD {raw with edge := windowEdges a b raw.edge}
    let qf := max k (k + 2) + H * weakParentCap R + 2 * R.N + 2 * weakParentCap R
    have hz (v u : CompIn C.G.comps) (d : Finset.Icc 2 C.Dm)
        (hd : weakParentCap R < d.1) : raw.edge v u d = [] := hn.cap slot v u d hd
    have hzClip (v u : CompIn C.G.comps) (d : Finset.Icc 2 C.Dm)
        (hd : weakParentCap R < d.1) : windowEdges a b raw.edge v u d = [] := by
      simp only [windowEdges, hz v u d hd, List.map_nil]
    have hg := hmetric (CompIn C.G.comps) (fun v => ScalarH v.1.root) C.Dm C.D
      C.hα C.hq C.hΛ C.hζ C.stream hgeom.band C.i (by have := C.hi; omega)
      slot.1 slot.2 ρ hρ.le (C.G.fam.fiber slot (C.G.actual slot))
    have hw := native_lift_balanced_drift_sup_of_bound C.D C.i slot.1
      (nativeChain C.i slot.1) ρ (C.G.fam.fiber slot (C.G.actual slot)) a b qf Cw
      (fun n _hn t _ht z => terminal_plateau_balanced_drift_bound
        B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq R.Λ R.hΛ B.ζ B.hζ C.D
        C.hα C.hq C.hΛ C.hζ hgeom.band C.i hterm.le hi slot.1 slot.2 n t z)
    have hdepth : HasDepthAtMost Q.edge H :=
      restrictSource_depth _ hKD _ (windowEdges_depth a b raw.edge
        (liftEdges_depth _ _ _ (chartedFiber_depth C.G.fam slot (C.G.actual slot) hn.depth)))
    have hsource : IsScaledJetEnvelope (weakParentMass C) Q.edge (Set.Icc a b)
        (ρ / C.D.eps (C.i - 1)) Cj qs qf (weakParentPrice C) S.1 := by
      have he := restrictSource_scaled_envelope (weakParentCap R) hKD
        (windowEdges a b raw.edge) hzClip (weakParentMass C) (Set.Icc a b) 1 Cj
        qs qf (weakParentPrice C) S.1 (hn.source S.1 hS slot)
      simpa only [Q, restrictLiftData, ρ, div_self hρ.ne'] using he
    have hsetting := native_lift_setting_of_fiber_facts C.D C.i hi hΛ hζ hgeom.band
      slot ρ hρ hcell hlam Q rfl rfl rfl (weakParentMass C) hn.mass_pos
      H R.N K k k R.hN (le_max_left _ _) CG Cw Cj (weakParentPrice C) S.1
      hg.2 hg.1 hw hdepth
      (fun v u d γ hγ => hn.transverse slot v u (degreeRangeInclusion _ _ hKD d) γ hγ)
      (fun v u d γ hγ => hn.measurable slot v u (degreeRangeInclusion _ _ hKD d) γ hγ)
      (fun v u d γ hγ => hn.smooth slot v u (degreeRangeInclusion _ _ hKD d) γ hγ) hsource
    have hex := effective_window_lift_exists_with_restricted hsetting hz
    let Cc := Classical.choose hex
    have hc := Classical.choose_spec hex
    refine {
      cap := weakParentCap R
      cap_ge := le_max_left _ _
      cap_le := le_rfl
      Q := Q
      price := weakParentPrice C
      metric_eq := rfl
      drift_eq := rfl
      eta_eq := rfl
      edge_agree := Or.inr ⟨hKD, hz, by
        intro t ht
        exact windowEdges_agree a b
          (restrictConstituentEdges (weakParentCap R) hKD raw.edge) t ht⟩
      source_eq := ?_
      edge_fast := by
        intro S hS hn v u d γ hγ α
        exact weakPositive_windowEdges_fast raw.edge a b S hS hn v u
          (degreeRangeInclusion _ _ hKD d) γ hγ α
      setting := hsetting
      coeff := Cc
      sequence := hc.1
      ambient := hc.2 }
    intro Dc a₀ hh n hnN t ht X z
    have hs := liftCellSource_restrict_effective_order (weakParentCap R) hKD
      {raw with edge := windowEdges a b raw.edge} hzClip Dc a₀ hh n (hnN.trans hcapN) t
    calc
      _ = liftCellSource {raw with edge := windowEdges a b raw.edge} Dc a₀ hh n t X z :=
        congrFun (congrFun hs.symm X) z
      _ = liftCellSource raw Dc a₀ hh n t X z :=
        (liftCellSource_edge_slow_open_congr isOpen_univ raw (windowEdges a b raw.edge)
          Dc a₀ hh n t (windowEdges_agree a b raw.edge t ht) X (Set.mem_univ X) z).symm

/-- Geometry, mass sums and setting assembly are proved; only actual native source facts remain. -/
theorem weak_parent_setting_of_native (hn : WeakParentNativeFactsStatement) :
    WeakPlateauParentSettingStatement :=
  weak_parent_setting_of_ingredients weak_parent_geometry hn weak_parent_mass_sums
    weak_parent_setting_selector

end AVRegularity.Finite.WeakLift
end
end

section
/-! The actual finite weak construction is a case of the common coefficient plan.
Only numerical floors are supplied; no unit context certificate or encoded stage replaces
its original family. Positive response depth supplies the ambient floor proved in RootFacts. -/

@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Finite.WeakLift
open WeakEntryProofs.Assembly Providers.WeakGen

/-- Concrete numerical request used solely for the common plan's coefficient certificates. -/
def weakParentCertificateRequest {B : WeakParentBase} (R : WeakParentMenu B) (sX sZ : ℕ) :
    WeakPassageRequest (weakParentCoefficientPhysical R) where
  L := 0
  Kw := R.J * R.N + 5
  sX := sX
  sZ := sZ
  nW := ⟨1, Nat.zero_lt_one⟩
  kReq := {
    c₀ := 1
    cr := 1
    Γk := 1
    Cwid := 1
    σf := R.σ
    lamC := 1
    Ca := 0
    mEnv := 0
    Cm := 0
    cker := 0
    Kan := 0
    Lan := 0
    Jm := 0
    Ks := 0
    Lker := 0
    Lstar := 0
    G0 := 1
    Hprod := R.J * R.R }
  request_grade := le_rfl
  kernel_order := by norm_num
  field_order := le_rfl

/-- Literal case of the common weak plan, preserving the entire supplied stage function. -/
def weakParentCommonCase {B : WeakParentBase} {R : WeakParentMenu B} {sX sZ : ℕ}
    (C : WeakParentCase R sX sZ) (hR : 1 ≤ R.R)
    (hb : weakCommonCoeffPlan.baseThreshold (weakParentCoefficientBase B) ≤ R.Λ)
    (hl : weakCommonCoeffPlan.levelThreshold
      (weakCoeffRequestOne (weakParentCertificateRequest R sX sZ)) C.j₀ ≤ C.M) :
    WeakCoefficientCase weakCommonCoeffPlan :=
  weakCommonCase (weakParentCertificateRequest R sX sZ) hb C.j₀ C.carrier C.M hl
    C.D C.hα C.hq C.hΛ C.hζ C.stream C.band C.term C.Dm
    (weak_parent_case_cap C hR) C.PW C.stage C.construction

/-- The actual intermediate stage carries the common plan's size certificate at its
correct reserve and weight; its cost is a finite iterate chosen from the request. -/
theorem weak_parent_case_certified {B : WeakParentBase} {R : WeakParentMenu B} {sX sZ : ℕ}
    (C : WeakParentCase R sX sZ) (hR : 1 ≤ R.R)
    (hb : weakCommonCoeffPlan.baseThreshold (weakParentCoefficientBase B) ≤ R.Λ)
    (hl : weakCommonCoeffPlan.levelThreshold
      (weakCoeffRequestOne (weakParentCertificateRequest R sX sZ)) C.j₀ ≤ C.M) :
    let x := weakParentCommonCase C hR hb hl
    let cost := (weakCertConst weakBasePlan (weakCoeffRequestOne
      (weakParentCertificateRequest R sX sZ)))^[C.M + R.J - C.i] 1
    0 ≤ cost ∧ WeakCertified cost (weakReserve x.inst C.i) (weakWeight x.inst C.i) C.G := by
  intro x cost
  have hi : C.M + R.J - (C.M + R.J - C.i) = C.i := by have := C.hi; have := C.hiJ; omega
  have hn : C.M + R.J - C.i ≤ R.J := by have := C.hi; omega
  have hc := weakCommonCase_certified (weakParentCertificateRequest R sX sZ) hb
    C.j₀ C.carrier C.M hl C.D C.hα C.hq C.hΛ C.hζ C.stream C.band C.term C.Dm
    (weak_parent_case_cap C hR) C.PW C.stage C.construction
    (C.M + R.J - C.i) hn
  change 0 ≤ cost ∧ WeakCertified cost
    (weakReserve x.inst (C.M + R.J - (C.M + R.J - C.i)))
    (weakWeight x.inst (C.M + R.J - (C.M + R.J - C.i)))
    (C.stage (C.M + R.J - (C.M + R.J - C.i))) at hc
  simpa only [hi] using hc

end AVRegularity.Finite.WeakLift
end
end
end
