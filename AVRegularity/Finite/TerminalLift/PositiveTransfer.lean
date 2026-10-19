-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Finite.TerminalLift.PositiveInput
public import AVRegularity.Finite.WeakPositive.NativeAdapter
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Finite.TerminalLift.PositiveGeometry
public import AVRegularity.Finite.Assembly.WeakParentNativeFactsOfIngredients
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.EntryTerminal.Ingredients.LiftField.LiftField
import AVRegularity.Finite.TerminalLift.CovarianceIdentification
import AVRegularity.Finite.WeakLift.IdentitySeparation

@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Finite.TerminalLift

/-! Radius-generic positive terminal pulse bounds. The same finite matrix/Schur and chart
lemmas used in the weak case act at the actual terminal preparation radius. -/

open WeakLift Construction.Preservation.FullLift EntryWeakProofs CycleComparison.Lift

/-- The terminal pulse costs its cell ratio times positive jets at its slow radius. -/
theorem terminal_positive_pulse_word_bound {B : WeakParentBase}
    {R : TerminalPositiveRequest B} {C : TerminalPositiveConstants}
    {P : WeakPositiveParameters R.N R.H R.order}
    (V : TerminalPositiveChartCase (R := R) (C := C) P) (slot : OddSlot)
    (hcut : ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M slot.1 V.t ≠ 0)
    {r : ℕ} (hr : r ≤ R.order) (β : DerivativeWord2 r) (x : Vec 2) :
    V.A.D.eps V.A.M ^ r * ‖orderedDerivative β
      (fun X => toCompSpace (V.A.G.mass V.A.law) (terminalPositivePulse V slot.1 X)) x‖ ≤
      (weakPositiveChartWordPrice P R.order r * weakPositivePathCost P) *
        (ocDStar V.A.D.q V.A.D.Λ V.A.M (V.A.D.κ V.A.M) (V.A.D.κ (V.A.M - 1)) / V.A.radius) *
        ∑ α ∈ multiIndicesBetween 1 (R.order + R.N), V.A.radius ^ (α 0 + α 1) *
          ‖partialDerivative α (compField (V.A.G.mass V.A.law) V.f) x‖ := by
  let A := V.slotLift slot
  let e := V.A.D.eps V.A.M
  let ρ := V.A.radius
  let ε := ocDStar V.A.D.q V.A.D.Λ V.A.M (V.A.D.κ V.A.M)
    (V.A.D.κ (V.A.M - 1)) / ρ
  let Φ := fun X => V.A.D.flowOf (V.A.M - 1) V.t X (V.A.D.slotAnchor V.A.M slot.1)
  let Ψ := fun X => V.A.D.flowOf (V.A.M - 1) (V.A.D.slotAnchor V.A.M slot.1) X V.t
  let Dc := fun hh n => if n = 0 then 0 else A.coeff hh n
  let Mat := fun hh => weakPositiveMatrix A hh
  let ct := ∑ n ∈ Finset.range R.N,
    nativeChartTransportConstant P.chartC (R.order + R.N) (n + 1) r
  have hct : 0 ≤ ct := Finset.sum_nonneg fun n _ =>
    nativeChartTransportConstant_nonneg P.chartC_ge _ _ _
  have he : 0 < e := A.setting.e_pos
  have hρ : 0 < ρ := V.radius_pos
  have hkap : V.A.D.kap V.A.M = V.A.D.κ V.A.M := by
    simp only [OCData.kap, V.A.term, Nat.min_self]
  have hprev : V.A.D.kap (V.A.M - 1) = V.A.D.κ (V.A.M - 1) := by
    simp only [OCData.kap, V.A.term, Nat.min_eq_left (Nat.sub_le V.A.M 1)]
  have hε : 0 ≤ ε := div_nonneg (mul_nonneg he.le (Real.sqrt_nonneg _)) hρ.le
  have hε1 : ε ≤ 1 := by simpa only [hkap, hprev] using A.setting.εc_le
  have heρ : e ≤ ρ := cell_scale_le_lift_radius he.le A.setting.ν_pos
    ((div_le_one A.setting.B_pos).mp (A.setting.η_eq.symm ▸ A.setting.η_le)) hρ
    (by simpa only [ε, ocDStar, hkap, hprev, e, OCData.eps] using hε1)
  have hΦ : ContDiff ℝ (R.order + R.N : ℕ) Φ :=
    (CycleReference.streamFlow_spatial_smooth (V.A.D.hΦ (V.A.M - 1)) V.t
      (V.A.D.slotAnchor V.A.M slot.1)).of_le (by simp)
  have hΨ : ContDiff ℝ (r : ℕ) Ψ :=
    (CycleReference.streamFlow_spatial_smooth (V.A.D.hΦ (V.A.M - 1))
      (V.A.D.slotAnchor V.A.M slot.1) V.t).of_le (by simp)
  have hJ := V.geometry.forward V.t slot hcut
  have hJΨ : ChartTransport.JetBound Ψ r P.chartC ρ := fun n hn hnr X =>
    V.geometry.backward V.t slot hcut n hn (hnr.trans (hr.trans (Nat.le_add_right _ _))) X
  have ht := terminal_positive_active_time V slot hcut
  have hid := weak_positive_support_identification R.N R.H R.order P V.A.D R.cap V.A.j₀
    R.bw V.A.M V.A.G (V.A.G.mass V.A.law) slot ρ A V.sX V.sZ
    (V.coeff slot.1) (V.sequence slot)
  have hg := weak_positive_graded_recurrence R.N R.H R.order P V.A.D R.cap V.A.j₀
    R.bw V.A.M V.A.G (V.A.G.mass V.A.law) slot ρ A
  have hp : terminalPositivePulse V slot.1 = fun X =>
      pulsePhysicalLift (V.A.D.cellScaleSq V.A.M) ρ e ε R.N R.H Dc
        (fun _ => Φ) (fun _ => Ψ) (fun _ => V.f) V.t X := by
    funext X
    apply pulsePhysicalLift_coeff_congr
    intro hh hhh n _hn m α Y z v u
    by_cases hn0 : n = 0
    · simp only [positiveLiftCoefficients, Dc, hn0, ite_true]
    · simpa only [positiveLiftCoefficients, Dc, hn0, ite_false] using
        hid.1 hh hhh n m α _ ht Y z v u
  have hd (hh : ℕ) (hhh : hh ≤ R.H) (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ R.N) :
      AmbientLiftCoefficientData (pulseParallel slot.1) (weakSlotLeft V.A.D V.A.M slot.1)
        (weakSlotRight V.A.D V.A.M slot.1) A.setting.window
        (ρ / V.A.D.eps (V.A.M - 1)) n R.order R.order (Dc hh n) (Mat hh) := by
    simpa only [Dc, ite_eq_right (by omega : n ≠ 0)] using hg hh hhh n hn
  have hm (hh : ℕ) (hhh : hh ≤ R.H) (v u : CompIn V.A.G.comps) : 0 ≤ Mat hh v u :=
    (hg hh hhh 0 (Nat.zero_le R.N)).nonneg v u
  have hb (v : CompIn V.A.G.comps) : e ^ r *
      ‖orderedDerivative β (fun X => terminalPositivePulse V slot.1 X v) x‖ ≤
      (ε * ct) * ∑ u, (∑ hh ∈ Finset.range (R.H + 1), Mat hh v u) *
        ∑ j ∈ Finset.range (R.order + R.N + 1), if j = 0 then 0 else
          ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => V.f X u) x‖ := by
    rw [hp]
    exact positive_pulse_fixed_matrix_word_bound_of_data Dc Mat hm hd
      (div_nonneg hρ.le A.setting.E_pos.le) A.setting.lam_le r hr hr V.f V.regular Φ hΦ
      P.chartC_ge hJ he le_rfl heρ Ψ hΨ hJΨ β x
      (weak_chart_inverse V.A.D (V.A.M - 1) V.t (V.A.D.slotAnchor V.A.M slot.1) x)
      (V.A.D.cellScaleSq V.A.M) ε V.t hε hε1 ht
      (fun hh _ => by simp only [Dc, ite_eq_left rfl])
      (fun hh hhh n hn1 hn α Y z v u => by
        simpa only [Dc, ite_eq_right (by omega : n ≠ 0)] using
          hid.2 hh hhh n hn1 hn α _ ht Y z v u) v
  have hreg : ContDiff ℝ (r : ℕ) (terminalPositivePulse V slot.1) :=
    contDiff_pi.mpr fun v => ((terminal_positive_pulse_regular V slot hcut).1 v).of_le
      (by exact_mod_cast hr)
  have hpath := weak_positive_weighted_path_sums R.N R.H R.order P V.A.D R.cap V.A.j₀
    R.bw V.A.M V.A.G (V.A.G.mass V.A.law) slot ρ A
  have hcost : 0 ≤ weakPositivePathCost P := by
    unfold weakPositivePathCost
    exact mul_nonneg (zero_le_one.trans (nativeLiftScalarBudget_ge_one _ _ _ _ _ _ _ _))
      (Finset.sum_nonneg fun _ _ => pow_nonneg P.S_nonneg _)
  have hout := weakPositive_weighted_word_bound β (V.A.G.mass V.A.law) A.setting.mass_pos _
    hreg x he.le (mul_nonneg hε hct) hcost _ hpath _ hb
  have hin := weakPositive_weighted_input_density_le hρ.le (V.A.G.mass V.A.law)
    A.setting.mass_pos V.f V.regular x
  apply hout.trans ((mul_le_mul_of_nonneg_left hin
    (mul_nonneg (mul_nonneg hε hct) hcost)).trans_eq ?_)
  dsimp only [weakPositiveChartWordPrice, ct, ε, e, ρ]
  simp only [Nat.cast_add]
  ac_rfl

/-- A uniform finite chart price controls the normalized glued positive correction. -/
theorem terminal_positive_glue_pointwise {B : WeakParentBase}
    {R : TerminalPositiveRequest B} {C : TerminalPositiveConstants}
    (P : WeakPositiveParameters R.N R.H R.order) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧
    ∀ (V : TerminalPositiveChartCase (R := R) (C := C) P) {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H']
      (kin : ℕ) (g : Vec 2 → H') (Cin Cδ : ℝ), 0 ≤ Cin → 0 ≤ Cδ →
      ocDStar V.A.D.q V.A.D.Λ V.A.M (V.A.D.κ V.A.M) (V.A.D.κ (V.A.M - 1)) ≤
        Cδ * V.A.D.eps V.A.M →
      (∀ x, ∑ α ∈ multiIndicesBetween 1 (R.order + R.N), V.A.radius ^ (α 0 + α 1) *
        ‖partialDerivative α (compField (V.A.G.mass V.A.law) V.f) x‖ ≤
        Cin * (V.A.radius / V.A.D.eps (V.A.M - 1)) *
          ∑ α ∈ multiIndicesBetween 1 kin, V.A.D.eps (V.A.M - 1) ^ (α 0 + α 1) *
            ‖partialDerivative α g x‖) →
      PositivePhysicalJetEstimate (V.A.D.eps V.A.M) (V.A.D.eps (V.A.M - 1))
        R.order kin (Ct * weakPositivePathCost P * Cin * Cδ) g (terminalPositiveGlue V) := by
  let Ct := ∑ r ∈ Finset.range (R.order + 1), weakPositiveChartWordPrice P R.order r
  have hprice0 (r : ℕ) : 0 ≤ weakPositiveChartWordPrice P R.order r :=
    mul_nonneg (Finset.sum_nonneg fun _ _ => nativeChartTransportConstant_nonneg P.chartC_ge _ _ _)
      (mul_nonneg (by positivity) (sq_nonneg _))
  have hCt : 0 ≤ Ct := Finset.sum_nonneg fun _ _ => hprice0 _
  have hcost : 0 ≤ weakPositivePathCost P := by
    unfold weakPositivePathCost
    exact mul_nonneg (zero_le_one.trans (nativeLiftScalarBudget_ge_one _ _ _ _ _ _ _ _))
      (Finset.sum_nonneg fun _ _ => pow_nonneg P.S_nonneg _)
  refine ⟨Ct, hCt, ?_⟩
  intro V H' _ _ kin g Cin Cδ hCin hCδ hδ hin
  have hΛ : 1 ≤ V.A.D.Λ := by have := V.geometry.Λ_ge; omega
  have he : 0 < V.A.D.eps V.A.M := Construction.Stream.ocEpsilon_pos hΛ
  have hE : 0 < V.A.D.eps (V.A.M - 1) := Construction.Stream.ocEpsilon_pos hΛ
  have hτ := Construction.Stream.ocTau_pos (α := V.A.D.α) (q := V.A.D.q) (m := V.A.M) hΛ
  let Y := fun x => ∑ α ∈ multiIndicesBetween 1 kin,
    V.A.D.eps (V.A.M - 1) ^ (α 0 + α 1) * ‖partialDerivative α g x‖
  have hY (x : Vec 2) : 0 ≤ Y x :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hE.le _) (norm_nonneg _)
  have hword (r : ℕ) (hr : r ≤ R.order) (β : DerivativeWord2 r) (x : Vec 2) :
      V.A.D.eps V.A.M ^ r * ‖orderedDerivative β (terminalPositiveGlue V) x‖ ≤
      (Ct * weakPositivePathCost P * Cin * Cδ) *
        (V.A.D.eps V.A.M / V.A.D.eps (V.A.M - 1)) * Y x := by
    let kset := ocObsPulses V.A.D.α V.A.D.q V.A.D.Λ V.A.M V.t V.t
    let F := fun k X => toCompSpace (V.A.G.mass V.A.law) (terminalPositivePulse V k X)
    let bound := (Ct * weakPositivePathCost P * Cin * Cδ) *
      (V.A.D.eps V.A.M / V.A.D.eps (V.A.M - 1)) * Y x
    have hbound : 0 ≤ bound := mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCt hcost) hCin) hCδ) (div_pos he hE).le) (hY x)
    apply convex_spatial_word_norm_le kset
      (fun k => ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M k V.t)
      (fun k _ => Providers.CascadeInvariants.ocCutoff_nonneg k V.t)
      (le_of_eq (obs_cutoff_sum_one _ _ _ _ _ hτ)) F ?_ he.le hbound β x ?_
    · intro k hk hw
      obtain ⟨hcd, hp⟩ := terminal_positive_pulse_regular V ⟨k, (Finset.mem_filter.mp hk).2.1⟩ hw
      exact (EntryTerminal.Ingredients.compField_contDiff_periodic (V.A.G.mass V.A.law) r
        (fun v x => terminalPositivePulse V k x v) (fun v => (hcd v).of_le (by exact_mod_cast hr))
        (fun v p X => congrFun (hp p X) v)).1
    · intro k hk hw
      have hb := terminal_positive_pulse_word_bound V ⟨k, (Finset.mem_filter.mp hk).2.1⟩ hw hr β x
      have hd0 : 0 ≤ ocDStar V.A.D.q V.A.D.Λ V.A.M (V.A.D.κ V.A.M)
          (V.A.D.κ (V.A.M - 1)) := mul_nonneg he.le (Real.sqrt_nonneg _)
      have hprice : weakPositiveChartWordPrice P R.order r ≤ Ct :=
        Finset.single_le_sum (fun r _ => hprice0 r) (Finset.mem_range.mpr (by omega))
      apply hb.trans
      calc
        _ ≤ (weakPositiveChartWordPrice P R.order r * weakPositivePathCost P) *
            (ocDStar V.A.D.q V.A.D.Λ V.A.M (V.A.D.κ V.A.M) (V.A.D.κ (V.A.M - 1)) / V.A.radius) *
            (Cin * (V.A.radius / V.A.D.eps (V.A.M - 1)) * Y x) :=
          mul_le_mul_of_nonneg_left (hin x)
            (mul_nonneg (mul_nonneg (hprice0 r) hcost) (div_nonneg hd0 V.radius_pos.le))
        _ = (weakPositiveChartWordPrice P R.order r * weakPositivePathCost P * Cin) *
            (ocDStar V.A.D.q V.A.D.Λ V.A.M (V.A.D.κ V.A.M) (V.A.D.κ (V.A.M - 1)) /
              V.A.D.eps (V.A.M - 1)) * Y x := by field_simp [hE.ne', V.radius_pos.ne']
        _ ≤ (Ct * weakPositivePathCost P * Cin) *
            (Cδ * (V.A.D.eps V.A.M / V.A.D.eps (V.A.M - 1))) * Y x := by
          apply mul_le_mul_of_nonneg_right _ (hY x)
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprice hcost) hCin
          · exact (div_le_div_of_nonneg_right hδ hE.le).trans_eq (mul_div_assoc _ _ _)
          · exact div_nonneg hd0 hE.le
          · exact mul_nonneg (mul_nonneg hCt hcost) hCin
        _ = bound := by dsimp only [bound]; ring
  constructor
  · intro x
    simpa only [pow_zero, orderedDerivative_zero, one_mul] using hword 0 (Nat.zero_le _) Fin.elim0 x
  · intro α hα x
    have heq : ![α 0, α 1] = α := by ext i; fin_cases i <;> rfl
    have hw := hword (α 0 + α 1) (Finset.mem_filter.mp hα).2.2
      (Fin.append (fun _ : Fin (α 0) => (0 : Fin 2)) (fun _ : Fin (α 1) => (1 : Fin 2))) x
    rw [weakPositive_sorted_word_eq_partial, heq] at hw
    exact hw

end AVRegularity.Finite.TerminalLift
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open scoped ENNReal Classical
namespace AVRegularity.Finite.TerminalLift

/-! Uniform terminal positive transfer: the slot lift, covariance input and finite chart glue
are assembled before the carrier and datum. The zero-degree schedule is handled separately. -/

open WeakLift Construction.Preservation.FullLift EntryWeakProofs

/-- Transport a uniform menu through a pointwise implication without moving its constants. -/
theorem terminal_uniform_profile_map (Q R : TerminalProfileProperty)
    (hmap : ∀ {H H' : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
      [NormedAddCommGroup H'] [NormedSpace ℝ H']
      (s E e C : ℝ) (k kin : ℕ) (r : Representation H) (L : H →L[ℝ] H')
      (cov osc : Vec 2 → H'), Q s E e C k kin r L cov osc → R s E e C k kin r L cov osc)
    (hQ : TerminalUniformProfileStatement Q) : TerminalUniformProfileStatement R := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, htail⟩ := hQ α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1 Jw Lw dW DW T₀ η₀ σw χw
    hJ hT hη hη1 hσ hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT hsched Lr
  obtain ⟨SX, SZ, hreserve⟩ := htail Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1
    Jw Lw dW DW T₀ η₀ σw χw hJ hT hη hη1 hσ hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT
    tT hsched Lr
  refine ⟨SX, SZ, ?_⟩
  intro sXT sZT hsXT hsZT cr hcr hcr1 Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  obtain ⟨Cb, hCb, hstart⟩ := hreserve sXT sZT hsXT hsZT cr hcr hcr1
    Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  refine ⟨Cb, hCb, ?_⟩
  intro j₀
  obtain ⟨M₀, hMtail⟩ := hstart j₀
  refine ⟨M₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage tp Pterm hprep
    lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
  exact hmap s (D.eps (M - 1)) (D.eps M) Cb (Lr + 3) (Lr + (NT + 2 * pT) + 4) r
    (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW) ((Gt'.retained M 1 RT).mass lawT)) _ _
    (hMtail M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage tp Pterm hprep
      lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv)

/-- One menu gives both the actual positive pointwise bound and its spatial regularity. -/
def TerminalPositiveCombinedProperty : TerminalProfileProperty := fun s E e C k kin r R cov osc =>
  TerminalPositivePointwiseProperty s E e C k kin r R cov osc ∧
    TerminalPositiveSpatialProperty s E e C k kin r R cov osc

/-- A zero positive response has the exact gain bound, at every output and input order. -/
theorem terminal_zero_positive_estimate {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H'] (e E : ℝ) (k kin : ℕ) (f : Vec 2 → H) :
    PositivePhysicalJetEstimate e E k kin 0 f (0 : Vec 2 → H') := by
  constructor
  · intro x
    simp only [Pi.zero_apply, norm_zero, zero_mul, le_refl]
  · intro α _hα x
    rw [terminal_partial_zero]
    simp only [Pi.zero_apply, norm_zero, mul_zero, zero_mul, le_refl]

/-- The actual terminal positive correction has its uniform physical gain and torus regularity. -/
theorem terminal_positive_combined : TerminalUniformProfileStatement TerminalPositiveCombinedProperty := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let B : WeakParentBase := ⟨α, s, q, ζ, hα₀, hα₁, hs₀, hs₁, hq, hζ⟩
  obtain ⟨Lp, hLp, hp⟩ := terminal_positive_slot_lift B
  obtain ⟨Aδ, hAδ, Lδ, _hLδ, hδ⟩ := terminal_effective_cell_length_bound
    hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Bc, hBc, Lc, _hLc, hcov⟩ := terminal_covariance_uniform_matrix_bound
    hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Ls, _hLs, hs⟩ := band_enhanced_lift_scale_bounds hα₀ hα₁ hs₀ hs₁ hq hζ
  let L₀ := max (max Lp Lδ) (max Lc Ls)
  refine ⟨L₀, hLp.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro Λ hΛ φ₀ hφ₀ _hφcd _hφnn _hφint _hφsupp bw hbw hbw1 Jw Lw dW DW T₀ η₀ σw χw
    hJ _hT hη _hη1 _hσ _hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT _hsched Lr
  have hpΛ : Lp ≤ Λ := (le_max_left _ _).trans ((le_max_left _ _).trans hΛ)
  have hδΛ : Lδ ≤ Λ := (le_max_right _ _).trans ((le_max_left _ _).trans hΛ)
  have hcΛ : Lc ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans hΛ)
  have hsΛ : Ls ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans hΛ)
  have hΛ128 : 128 ≤ Λ := hLp.trans hpΛ
  refine ⟨0, 0, ?_⟩
  intro sXT sZT _hsXT _hsZT cr hcr hcr1 Kw Kp nW kW CL Cχ c Cpre Cw cH _hc _hcH hkw
  by_cases hNT : 1 ≤ NT
  · let R : TerminalPositiveRequest B := ⟨Λ, hΛ128, bw, hbw, hbw1, NT, dW, DW, pT, Lr, hNT⟩
    let C : TerminalPositiveConstants := ⟨cr, hcr, hcr1, kW, hkw, CL, Cχ, χw, hχ⟩
    obtain ⟨P, _hcap, _hslow, _hfast, hslotLift⟩ := hp R hpΛ C
    obtain ⟨Ct, hCt, hchart⟩ := terminal_positive_glue_pointwise (C := C) P
    let kin := Lr + (NT + 2 * pT) + 4
    let Bn := max Bc (terminalReadoutConstant (termAlphabet NT pT DW dW) RT cH)
    have hBn : 0 ≤ Bn := (zero_le_one.trans hBc).trans (le_max_left _ _)
    let Cin := ((multiIndicesBetween 1 (R.order + R.N)).card : ℝ) *
      (((kin : ℝ) * (1 + 4 * Bn) ^ kin * Bn + Bn) * ((2 : ℝ) ^ kin * (kin + 1)))
    have hCin : 0 ≤ Cin := by dsimp only [Cin]; positivity
    have hcost : 0 ≤ weakPositivePathCost P := by
      unfold weakPositivePathCost
      exact mul_nonneg (zero_le_one.trans (nativeLiftScalarBudget_ge_one _ _ _ _ _ _ _ _))
        (Finset.sum_nonneg fun _ _ => pow_nonneg P.S_nonneg _)
    refine ⟨Ct * weakPositivePathCost P * Cin * Aδ,
      mul_nonneg (mul_nonneg (mul_nonneg hCt hcost) hCin) (zero_le_one.trans hAδ), ?_⟩
    intro j₀
    obtain ⟨Mp, hslotLiftM⟩ := hslotLift j₀
    refine ⟨max Mp 2, ?_⟩
    intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage tp Pterm _hprep
      lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
    have hM2 : 2 ≤ M := (le_max_right _ _).trans hM
    have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
      simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
    let A : TerminalPositiveCase R C := {
      j₀ := j₀, M := M, D := D, hα := hDα, hq := hDq, hΛ := hDΛ, hζ := hDζ,
      stream := hstream, band := hband, term := hterm, Jw := Jw, hJw := hJ,
      nW := nW, PW := PW, φ₀ := φ₀, hφ₀ := hφ₀, a := a, T₀ := T₀, σw := σw,
      aM := aM, law := lawW, G := Gw, stage := hstage }
    have hpack := hslotLiftM A rfl ((le_max_left _ _).trans hM)
    let slotLifts := Classical.choice hpack.2.2.2.2.2
    have hπ (v : CompIn Gw.comps) : 0 < Gw.mass lawW v :=
      Construction.Preservation.Buffer.birth_compMass_pos (hDq.symm ▸ hq.1)
        (hDΛ.symm ▸ hΛ128) lawW v.1
    have he (m : ℕ) : 0 < D.eps m := by
      change 0 < ocEpsilon D.q D.Λ m
      rw [hDq, hDΛ]
      exact (Scales.epsilon_basic hq.1 hΛ128).1
    let L := readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW) ((Gt'.retained M 1 RT).mass lawT)
    let Ac := termCovPrimitive D M tp t
    have hroots : ∀ v ∈ Gw.comps, v.births = [] := fun v hv => hstage.2.2.2.2.1 ⟨v, hv⟩
    have hsub : (Gt'.retained M 1 RT).comps ⊆
        succExtComps M (termAlphabet NT pT DW dW) RT Gw.comps := by
      intro v hv
      have hv' : v ∈ Gt'.comps := (Finset.mem_filter.mp hv).1
      rw [hactual.2.2.1, hstage.2.2.1] at hv'
      exact hv'
    have hL := terminal_readout_bounds D.q D.Λ M (hDq.symm ▸ hq.1)
      (hDΛ.symm ▸ hΛ128) (by omega) lawW lawT η₀ (termAlphabet NT pT DW dW) RT
      Gw.comps (Gt'.retained M 1 RT).comps hlaw.1
      (by rw [hlaw.2.2.2.2.2.1]; positivity) hη.le hroots hsub
    rw [hlaw.2.2.1] at hL
    have hLn : ‖L‖ ≤ Bn := hL.trans (le_max_right _ _)
    have hband' : IsOCBandChain α q Λ ζ M D.κ := by
      simpa only [hDα, hDq, hDΛ, hDζ] using hband
    have hAc : ∀ i j, |Ac i j| ≤ Bn * D.eps (M - 1) ^ 2 := by
      intro i j
      have hc := hcov Λ hcΛ M hM2 D.κ hband' tp t i j
      change |ocCovariance D.α D.q D.Λ D.ζ M (D.κ M) (D.κ (M - 1)) tp t i j| ≤
        Bn * ocEpsilon D.q D.Λ (M - 1) ^ 2
      rw [hDα, hDq, hDΛ, hDζ]
      exact hc.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    have hmodel : compField (Gw.mass lawW) (aRep t) =
        covPolyP Ac pT (fun x => L (r.value x)) :=
      terminal_covariance_classical_model M (D.eps (M - 1)) η₀ (Gw.mass lawW)
        ((Gt'.retained M 1 RT).mass lawT) hπ Ac
        (EntryTerminal.Ingredients.termCovPrimitive_entry_symm D (by omega)
          (hDζ.symm ▸ hζ) M tp t) pT r hr (by omega)
        (fun v => Z v t) (fun v => PZ v t) (aRep t) hv
        (fun v => (hlift.2 v t ht).1) (fun v => (hlift.2 v t ht).2)
    change IsRepresentationAt (D.eps (M - 1)) kin r at hr
    obtain ⟨hrcd, hrp⟩ := representation_value_contDiff_periodic r hr
    have hinputcd : ContDiff ℝ (R.order + R.N : ℕ) (compField (Gw.mass lawW) (aRep t)) := by
      rw [hmodel, ← covariancePolynomial_eq_P]
      apply covariancePolynomial_contDiff
      exact (L.contDiff.comp hrcd).of_le (by
        exact_mod_cast (by dsimp only [R, TerminalPositiveRequest.order, kin]; omega :
          R.order + R.N + 2 * pT ≤ kin))
    have hinputp : IsZ2Periodic (compField (Gw.mass lawW) (aRep t)) := by
      rw [hmodel, ← covariancePolynomial_eq_P]
      exact covariancePolynomial_periodic Ac pT _ _
        ((L.contDiff.comp hrcd).of_le (by exact_mod_cast (by omega : 2 * pT ≤ kin)))
        (fun n x => congrArg L (hrp n x))
    have hf := terminal_normalized_input_regular Gw.comps (Gw.mass lawW) hπ
      (R.order + R.N) (aRep t) hinputcd hinputp
    let V : TerminalPositiveChartCase (R := R) (C := C) P := {
      A := A, radius_pos := hpack.1, geometry := hpack.2.2.2.2.1, slotLift := slotLifts,
      sX := sXT, sZ := sZT, coeff := CcT,
      sequence := fun slot => hlift.1 slot.1 slot.2,
      t := t, f := aRep t, regular := hf.1, periodic := hf.2 }
    have hδbound : ocDStar D.q D.Λ M (D.κ M) (D.κ (M - 1)) ≤ Aδ * D.eps M := by
      simpa only [OCData.eps, hDq, hDΛ] using hδ Λ hδΛ M hM2 D.κ hband'
    have hpoint := hchart V kin r.value Cin Aδ hCin (zero_le_one.trans hAδ) hδbound (by
      intro x
      change (∑ α ∈ multiIndicesBetween 1 (R.order + R.N), A.radius ^ (α 0 + α 1) *
        ‖partialDerivative α (compField (Gw.mass lawW) (aRep t)) x‖) ≤
        Cin * (A.radius / D.eps (M - 1)) *
          ∑ α ∈ multiIndicesBetween 1 kin, D.eps (M - 1) ^ (α 0 + α 1) *
            ‖partialDerivative α r.value x‖
      rw [hmodel]
      exact terminal_covariance_input_partial_sum_bound Ac (D.eps (M - 1)) A.radius Bn
        (he _) hpack.1.le hpack.2.2.1 hBn hAc L hLn (R.order + R.N) kin pT
        (by dsimp only [R, TerminalPositiveRequest.order, kin]; omega) r.value hrcd x)
    have hspatial := terminal_positive_glue_regular V
    have hfreeze := terminal_lift_freeze_input Gw M NT dW cr CcT aRep t
      (weakData_cellScaleSq_pos D (by rw [hDΛ]; omega) (hDζ.symm ▸ hζ) hbandD M)
    have hosc : compField (Gw.mass lawW) (termLiftedRep Gw M NT dW cr CcT aRep t) -
        compField (Gw.mass lawW) (aRep t) = terminalPositiveGlue V := by
      rw [hfreeze]
      exact terminal_positive_difference_eq_glue V
    rw [← hosc] at hpoint hspatial
    exact ⟨⟨he _, he _, hpoint⟩, hspatial⟩
  · have hNT0 : NT = 0 := by omega
    subst NT
    obtain ⟨Ms, _hMs, hscale⟩ := hs Λ hsΛ cr hcr
    refine ⟨0, le_rfl, fun j₀ => ⟨Ms, ?_⟩⟩
    intro M hM D hDα hDq hDΛ hDζ _hstream hband hterm PW a Gw lawW aM _hstage tp Pterm _hprep
      lawT Gt' _hlaw _hactual Kz Z CcT PZ aRep hlift t _ht r _hr _hv
    have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
      simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
    have hscaleM := hscale M D.κ (by simpa only [hDα, hDq, hDΛ, hDζ] using hband) M hM le_rfl
    have hρ : 0 < cr * liftLength D M := by
      simpa only [liftLength, hDα, hDq, hDΛ] using hscaleM.2.1
    have he (m : ℕ) : 0 < D.eps m := by
      change 0 < ocEpsilon D.q D.Λ m
      rw [hDq, hDΛ]
      exact (Scales.epsilon_basic hq.1 hΛ128).1
    have hz := terminal_zero_order_lift_eq Gw M dW sXT sZT cr CcT
      (fun slot => hlift.1 slot.1 slot.2) (by rw [hDΛ]; omega)
      (hDζ.symm ▸ hζ) hbandD hρ aRep t
    have hosc : compField (Gw.mass lawW) (termLiftedRep Gw M 0 dW cr CcT aRep t) -
        compField (Gw.mass lawW) (aRep t) = 0 := by rw [hz]; exact sub_self _
    refine ⟨⟨he _, he _, ?_⟩, ?_⟩
    · rw [hosc]
      exact terminal_zero_positive_estimate _ _ _ _ r.value
    · rw [hosc]
      exact ⟨contDiff_const, fun _ _ => rfl⟩

/-- The pointwise input of the bounded terminal assembly is fully discharged. -/
theorem terminal_positive_pointwise : TerminalPositivePointwiseStatement :=
  terminal_uniform_profile_map TerminalPositiveCombinedProperty TerminalPositivePointwiseProperty
    (fun _ _ _ _ _ _ _ _ _ _ h => h.1) terminal_positive_combined

/-- The spatial input retains the exact regularity and periodicity clause. -/
theorem terminal_positive_spatial : TerminalPositiveSpatialStatement :=
  terminal_uniform_profile_map TerminalPositiveCombinedProperty TerminalPositiveSpatialProperty
    (fun _ _ _ _ _ _ _ _ _ _ h => h.2) terminal_positive_combined

/-- Complete terminal positive physical transfer, including the zero output jet. -/
theorem terminal_positive_lift_transfer : TerminalPositiveLiftTransferStatement :=
  terminal_positive_lift_transfer_of_ingredients terminal_positive_pointwise terminal_positive_spatial

/-- Both terminal physical differences have a common uniform profile budget. -/
theorem terminal_shared_physical_transfer : TerminalSharedPhysicalTransferStatement :=
  terminal_shared_physical_transfer_of_ingredients terminal_covariance_transfer terminal_positive_lift_transfer

/-- The exact finite terminal-lift statement, through the profile assembly. -/
theorem terminal_lift_rep_proved : Assembly.TerminalLiftRepStatement :=
  terminal_lift_rep_of_difference_jets
    (terminal_difference_jets_of_physical_transfer terminal_shared_physical_transfer)

end AVRegularity.Finite.TerminalLift
end
