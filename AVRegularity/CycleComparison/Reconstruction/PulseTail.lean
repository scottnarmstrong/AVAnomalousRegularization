-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.LiftJetBound
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleComparison.Reconstruction.PulseTailPeriodic
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.CycleComparison.Reconstruction.PiolaTested
import AVRegularity.CycleComparison.Reconstruction.PulseIdentity
import AVRegularity.CycleComparison.Residual.BoundPointwise
import AVRegularity.Families.TorusCompatible.WeakStage
public import AVRegularity.CycleComparison.Lift.SettingLiftSourceBlockCoefficient
public import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
public import AVRegularity.Statements.Construction.IsOCStreamSeq
import AVRegularity.CycleComparison.Lift.SettingConstructedLiftSequence
import AVRegularity.CycleComparison.Residual.TailJets
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Smoothness, linearity and jets of the glued lift of a coarse field** (physical derivatives
are expanded before sampling, scalars are transported by composition, and chart jets pay the
chain rule).

The physical lift of one pulse is the label lift of the chart-frame field `X ↦ a(t, χ(t, ρX))`
composed with the label map `ψ(t, ·)` (`pulsePhysicalLift_eq_comp`). Hence, at a time whose cell
time is in the lift window and for a coarse field of class `C^{N+J}`:

* the physical lift of a pulse is of class `C^J` (`pulsePhysicalLift_contDiff`) and additive in
  the coarse field (`pulsePhysicalLift_sub_input`);
* for charts and label maps whose jets of positive order are bounded by fixed constants, the jets
  of order `j ≤ J` of the physical lift are bounded by a constant times a bound `A` of the jets of
  order at most `N + J` of the coarse field (`pulsePhysicalLift_jet_le`): the label lift costs
  `setting_labelLift_jet_bound`, the chart-frame read and the composition with the label map cost
  the chain rule (`exists_chartRead_jet_bound`, `exists_comp_chart_jet_bound`).

The glued lift `𝒯a = ∑_k ϖ_k 𝒯_k a` over the observed pulses inherits all three at every time of
the observation window (`gluedLift_contDiff_oc`, `gluedLift_sub_input_oc`, `gluedLift_jet_le_oc`):
a pulse with `ϖ_k(t) ≠ 0` has `t` in its pulse window, hence its cell time in its lift window
(`weighted_cellTime_mem_liftWindow`), and the weights lie in `[0, 1]`. With the jet bounds of the
renewal charts on the pulse windows (`pulseChart_jetBound`) the chart hypotheses are discharged
(`gluedLift_jet_le_pulseChart`). -/

section Generic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A sum of `j + 1` terms bounded by `B ≥ 0` is at most `(J + 1) B` for `j ≤ J`. -/
theorem sum_range_succ_le_mul_of_le (f : ℕ → ℝ) {j J : ℕ} (hj : j ≤ J) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i ≤ j, f i ≤ B) : ∑ i ∈ Finset.range (j + 1), f i ≤ ((J : ℝ) + 1) * B := by
  calc ∑ i ∈ Finset.range (j + 1), f i ≤ ∑ _i ∈ Finset.range (j + 1), B :=
        Finset.sum_le_sum fun i hi => hf i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    _ = ((j : ℝ) + 1) * B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    _ ≤ ((J : ℝ) + 1) * B :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hj 1) hB

/-- **Uniform jets of a field read in a chart.** For a chart whose jets of orders `1, …, P` are
bounded by `Cχ ≥ 1` and a field whose jets of order at most `P` are bounded by `A`, the jets of
order at most `P` of `X ↦ a₀(χ(ρX))` are bounded by `K A`, with `K` depending only on `P`, `Cχ`
and `ρ`. -/
theorem exists_chartRead_jet_bound (P : ℕ) {Cχ : ℝ} (hC : 1 ≤ Cχ) (ρ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a₀ : Vec 2 → F) (χ : Vec 2 → Vec 2), ContDiff ℝ (P : ℕ∞) a₀ →
      ContDiff ℝ (P : ℕ∞) χ → (∀ i, 1 ≤ i → i ≤ P → ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ Cχ) →
      ∀ A : ℝ, (∀ i ≤ P, ∀ y, ‖iteratedFDeriv ℝ i a₀ y‖ ≤ A) →
      ∀ j ≤ P, ∀ X, ‖iteratedFDeriv ℝ j (fun X' : Vec 2 => a₀ (χ (ρ • X'))) X‖ ≤ K * A := by
  have hC0 : 0 ≤ Cχ := zero_le_one.trans hC
  have hR0 : 0 ≤ (max |ρ| 1) ^ P := pow_nonneg (zero_le_one.trans (le_max_right _ _)) P
  have hF0 : 0 ≤ (P.factorial : ℝ) * Cχ ^ P := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hC0 P)
  refine ⟨(P.factorial : ℝ) * Cχ ^ P * (max |ρ| 1) ^ P * ((P : ℝ) + 1),
    mul_nonneg (mul_nonneg hF0 hR0) (by positivity), ?_⟩
  intro a₀ χ ha hχ hχb A hA j hj X
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) X)
  have hS := sum_range_succ_le_mul_of_le (fun i => ‖iteratedFDeriv ℝ i a₀ (χ (ρ • X))‖) hj hA0
    fun i hi => hA i (hi.trans hj) (χ (ρ • X))
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i a₀ (χ (ρ • X))‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hf : (j.factorial : ℝ) ≤ P.factorial := by exact_mod_cast Nat.factorial_le hj
  have hl : (j.factorial : ℝ) * Cχ ^ j * |ρ| ^ j ≤
      (P.factorial : ℝ) * Cχ ^ P * (max |ρ| 1) ^ P :=
    mul_le_mul (mul_le_mul hf (pow_le_pow_right₀ hC hj) (pow_nonneg hC0 j) (Nat.cast_nonneg _))
      (pow_le_max_one_pow (abs_nonneg ρ) hj) (pow_nonneg (abs_nonneg ρ) j) hF0
  refine (norm_iteratedFDeriv_chartRead_le ha hχ hC hχb ρ hj X).trans ?_
  exact (mul_le_mul hl hS hS0 (mul_nonneg hF0 hR0)).trans_eq (by ring)

/-- **Uniform jets of a composition with a chart.** For a map `ψ` whose jets of orders
`1, …, J` are bounded by `Cψ ≥ 1` and a field `Φ` whose jets of order at most `J` are bounded by
`B`, the jets of order at most `J` of `Φ ∘ ψ` are bounded by `K B`, with `K` depending only on
`J` and `Cψ`. -/
theorem exists_comp_chart_jet_bound (J : ℕ) {Cψ : ℝ} (hC : 1 ≤ Cψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Φ : Vec 2 → F) (ψ : Vec 2 → Vec 2), ContDiff ℝ (J : ℕ∞) Φ →
      ContDiff ℝ (J : ℕ∞) ψ → (∀ i, 1 ≤ i → i ≤ J → ∀ x, ‖iteratedFDeriv ℝ i ψ x‖ ≤ Cψ) →
      ∀ B : ℝ, (∀ i ≤ J, ∀ y, ‖iteratedFDeriv ℝ i Φ y‖ ≤ B) →
      ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (Φ ∘ ψ) x‖ ≤ K * B := by
  have hC0 : 0 ≤ Cψ := zero_le_one.trans hC
  have hF0 : 0 ≤ (J.factorial : ℝ) * Cψ ^ J := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hC0 J)
  refine ⟨(J.factorial : ℝ) * Cψ ^ J * ((J : ℝ) + 1), mul_nonneg hF0 (by positivity), ?_⟩
  intro Φ ψ hΦ hψ hψb B hB j hj x
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) x)
  have hS := sum_range_succ_le_mul_of_le (fun i => ‖iteratedFDeriv ℝ i Φ (ψ x)‖) hj hB0
    fun i hi => hB i (hi.trans hj) (ψ x)
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i Φ (ψ x)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hf : (j.factorial : ℝ) ≤ J.factorial := by exact_mod_cast Nat.factorial_le hj
  have hl : (j.factorial : ℝ) * Cψ ^ j ≤ (J.factorial : ℝ) * Cψ ^ J :=
    mul_le_mul hf (pow_le_pow_right₀ hC hj) (pow_nonneg hC0 j) (Nat.cast_nonneg _)
  refine (norm_iteratedFDeriv_comp_chart_le hΦ hψ hC hψb hj x).trans ?_
  exact (mul_le_mul hl hS hS0 hF0).trans_eq (by ring)

/-- A normalized jet bound of a chart through the order `P` is a uniform bound of its jets of
orders `1, …, P`. -/
theorem jetBound_le_uniform {Θ : Vec 2 → Vec 2} {P : ℕ} {Dχ Rχ : ℝ} (hD : 1 ≤ Dχ)
    (hJ : JetBound Θ P Dχ Rχ) :
    ∀ i, 1 ≤ i → i ≤ P → ∀ y, ‖iteratedFDeriv ℝ i Θ y‖ ≤ Dχ * (max |Rχ⁻¹| 1) ^ P := by
  intro i hi hiP y
  refine (hJ i hi hiP y).trans (mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans hD))
  exact ((le_abs_self (Rχ⁻¹ ^ (i - 1))).trans_eq (abs_pow Rχ⁻¹ (i - 1))).trans
    (pow_le_max_one_pow (abs_nonneg Rχ⁻¹) (by omega : i - 1 ≤ P))

/-- The chart-frame field `X ↦ a(c𝗍, χ(c𝗍, ρX))` at the cell time `𝗍 = t/c` is of class `C^n`
when the field and the chart at the time `t` are. -/
theorem contDiff_chartFrame {n : ℕ} (a : ℝ → Vec 2 → F) (chart : ℝ → Vec 2 → Vec 2) {c : ℝ}
    (hc : c ≠ 0) {t : ℝ} (ha : ContDiff ℝ (n : ℕ∞) (a t)) (hχ : ContDiff ℝ (n : ℕ∞) (chart t))
    (ρ : ℝ) :
    ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 => a (c * (c⁻¹ * t)) (chart (c * (c⁻¹ * t)) (ρ • X))) := by
  rw [mul_inv_cancel_left₀ hc t]
  exact ha.comp (hχ.comp (contDiff_const_smul ρ))

end Generic

section Pi

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The jet of a field is bounded by a common bound of the jets of its components. -/
theorem norm_iteratedFDeriv_le_of_apply_le {g : Vec 2 → ∀ i, h i} {n : ℕ}
    (hg : ContDiff ℝ (n : ℕ∞) g) (x : Vec 2) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ v, ‖iteratedFDeriv ℝ n (fun y => g y v) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
  refine ContinuousMultilinearMap.opNorm_le_bound hC fun w => ?_
  have hw : 0 ≤ ∏ i, ‖w i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC hw)).2 fun v => ?_
  have he := (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).iteratedFDeriv_comp_left
    (hg.contDiffAt (x := x)) (i := n) (by exact_mod_cast le_rfl)
  have hev := congrArg (fun G => G w) he
  change iteratedFDeriv ℝ n (fun y => g y v) x w = (iteratedFDeriv ℝ n g x w) v at hev
  rw [← hev]
  exact (ContinuousMultilinearMap.le_opNorm _ w).trans (mul_le_mul_of_nonneg_right (hb v) hw)

end Pi

/-- A time of the observation window at which an observed pulse is weighted is, in cell time,
in the clipped lift window of the pulse. -/
theorem weighted_cellTime_mem_liftWindow {α q : ℝ} {Λ m : ℕ} {ν tA tZ : ℝ} {ϖ : ℤ → ℝ → ℝ}
    {quiet : Set ℝ} {Cpart : ℝ} (hℓ : ocEll q Λ m ν ≠ 0)
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) ϖ (ocPulseWindow α q Λ m) quiet
      (Icc tA tZ) (ocTau α q Λ m) Cpart)
    {k : ℤ} (hk : k ∈ ocObsPulses α q Λ m tA tZ) {t : ℝ} (ht : t ∈ Icc tA tZ)
    (hw : ϖ k t ≠ 0) :
    (ocEll q Λ m ν ^ 2)⁻¹ * t ∈
      Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) := by
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have htk : t ∈ Icc (((k : ℝ) - 61 / 48) * ocTau α q Λ m)
      (((k : ℝ) + 61 / 48) * ocTau α q Λ m) := hpart.2.2.2.1 k hk t hw
  exact AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 htk ht

section Lift

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

/-- The physical lift of a pulse is the label lift of its chart-frame field read at the
label. -/
theorem pulsePhysicalLift_eq_labelLift (c ρ e εc : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) :
    pulsePhysicalLift c ρ e εc N H Cc chart label a t x =
      labelLift Cc N H εc (fun s X => a (c * s) (chart (c * s) (ρ • X))) ρ e c t (label t x) :=
  rfl

/-- The physical lift of a pulse at the time `t` is the label lift of its chart-frame field
composed with the label map. -/
theorem pulsePhysicalLift_eq_comp (c ρ e εc : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) :
    pulsePhysicalLift c ρ e εc N H Cc chart label a t =
      labelLift Cc N H εc (fun s X => a (c * s) (chart (c * s) (ρ • X))) ρ e c t ∘ label t :=
  rfl

/-- **The physical lift of a pulse is additive in the coarse field** at a time `t` at which the
chart and the two coarse fields are of class `C^N`. -/
theorem pulsePhysicalLift_sub_input (c ρ e εc : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℝ → Vec 2 → Vec 2) (a b : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (hc : c ≠ 0)
    (hχ : ContDiff ℝ (N : ℕ∞) (chart t)) (ha : ContDiff ℝ (N : ℕ∞) (a t))
    (hb : ContDiff ℝ (N : ℕ∞) (b t)) (x : Vec 2) :
    pulsePhysicalLift c ρ e εc N H Cc chart label (fun s y => a s y - b s y) t x =
      pulsePhysicalLift c ρ e εc N H Cc chart label a t x -
        pulsePhysicalLift c ρ e εc N H Cc chart label b t x := by
  simp only [pulsePhysicalLift_eq_labelLift]
  exact labelLift_sub_input Cc N H εc (fun s X => a (c * s) (chart (c * s) (ρ • X)))
    (fun s X => b (c * s) (chart (c * s) (ρ • X))) ρ e c t
    (contDiff_chartFrame a chart hc ha hχ ρ) (contDiff_chartFrame b chart hc hb hχ ρ) (label t x)

/-- **Smoothness of a glued lift from its weighted pulses.** If the physical lift of every pulse
weighted at the time `t` is of class `C^J`, so is the glued lift. -/
theorem gluedLift_contDiff_of_weighted (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ e εc : ℝ)
    (N H : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) {J : ℕ}
    (hk : ∀ k ∈ kset, ϖ k t ≠ 0 →
      ContDiff ℝ (J : ℕ∞) (pulsePhysicalLift c ρ e εc N H (Cc k) (chart k) (label k) a t)) :
    ContDiff ℝ (J : ℕ∞) (gluedLift kset ϖ c ρ e εc N H Cc chart label a t) := by
  have he : gluedLift kset ϖ c ρ e εc N H Cc chart label a t = fun x =>
      ∑ k ∈ kset, ϖ k t • pulsePhysicalLift c ρ e εc N H (Cc k) (chart k) (label k) a t x :=
    rfl
  rw [he]
  refine ContDiff.sum fun k hks => ?_
  by_cases hw : ϖ k t = 0
  · simp only [hw, zero_smul]
    exact contDiff_const
  · exact (hk k hks hw).const_smul (ϖ k t)

/-- **Jets of a glued lift from its weighted pulses.** If the weights at the time `t` are
nonnegative with sum one and the jets of order at most `J` of the physical lift of every pulse
weighted at `t` are bounded by `Mk k * A`, the jets of order at most `J` of the glued lift are
bounded by `(∑_k Mk k) A`. -/
theorem norm_iteratedFDeriv_gluedLift_le_of_weighted (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ)
    (c ρ e εc : ℝ) (N H : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) {J : ℕ}
    (hϖ0 : ∀ k ∈ kset, 0 ≤ ϖ k t) (hϖ1 : ∑ k ∈ kset, ϖ k t = 1) (Mk : ℤ → ℝ) {A : ℝ}
    (hk : ∀ k ∈ kset, ϖ k t ≠ 0 →
      ContDiff ℝ (J : ℕ∞) (pulsePhysicalLift c ρ e εc N H (Cc k) (chart k) (label k) a t) ∧
      ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j
        (pulsePhysicalLift c ρ e εc N H (Cc k) (chart k) (label k) a t) x‖ ≤ Mk k * A)
    (hMA : ∀ k ∈ kset, 0 ≤ Mk k * A) {j : ℕ} (hj : j ≤ J) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (gluedLift kset ϖ c ρ e εc N H Cc chart label a t) x‖ ≤
      (∑ k ∈ kset, Mk k) * A := by
  have hle1 : ∀ k ∈ kset, ϖ k t ≤ 1 := fun k hks =>
    (Finset.single_le_sum (f := fun k => ϖ k t) hϖ0 hks).trans_eq hϖ1
  have he : gluedLift kset ϖ c ρ e εc N H Cc chart label a t = fun x =>
      ∑ k ∈ kset, ϖ k t • pulsePhysicalLift c ρ e εc N H (Cc k) (chart k) (label k) a t x :=
    rfl
  have hf : ∀ k ∈ kset, ContDiff ℝ (j : ℕ∞)
      (fun x => ϖ k t • pulsePhysicalLift c ρ e εc N H (Cc k) (chart k) (label k) a t x) := by
    intro k hks
    by_cases hw : ϖ k t = 0
    · simp only [hw, zero_smul]
      exact contDiff_const
    · exact ContDiff.const_smul (ϖ k t) ((hk k hks hw).1.of_le (by exact_mod_cast hj))
  have hb : ∀ k ∈ kset, ‖iteratedFDeriv ℝ j
      (fun x => ϖ k t • pulsePhysicalLift c ρ e εc N H (Cc k) (chart k) (label k) a t x) x‖ ≤
        Mk k * A := by
    intro k hks
    by_cases hw : ϖ k t = 0
    · simp only [hw, zero_smul, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact hMA k hks
    · have h1 := norm_iteratedFDeriv_const_smul_le_mul (ϖ k t)
        ((hk k hks hw).1.of_le (by exact_mod_cast hj)) ((hk k hks hw).2 j hj x)
      have habs : |ϖ k t| ≤ 1 := (abs_of_nonneg (hϖ0 k hks)).le.trans (hle1 k hks)
      refine h1.trans ?_
      rw [mul_assoc]
      exact mul_le_of_le_one_left (hMA k hks) habs
  rw [he]
  exact norm_iteratedFDeriv_sum_le_mul kset hf hb

/-- **The glued lift is additive in the coarse field** at a time `t` at which the charts of the
pulses and the two coarse fields are of class `C^N`. -/
theorem gluedLift_sub_input (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ e εc : ℝ) (N H : ℕ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    (a b : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (hc : c ≠ 0)
    (hχ : ∀ k ∈ kset, ContDiff ℝ (N : ℕ∞) (chart k t)) (ha : ContDiff ℝ (N : ℕ∞) (a t))
    (hb : ContDiff ℝ (N : ℕ∞) (b t)) (x : Vec 2) :
    gluedLift kset ϖ c ρ e εc N H Cc chart label (fun s y => a s y - b s y) t x =
      gluedLift kset ϖ c ρ e εc N H Cc chart label a t x -
        gluedLift kset ϖ c ρ e εc N H Cc chart label b t x := by
  simp only [gluedLift]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [pulsePhysicalLift_sub_input c ρ e εc N H (Cc k) (chart k) (label k) a b hc (hχ k hk) ha
    hb x, smul_sub]

/-- **The glued lift in the renewal charts is additive in the coarse field** at every time at
which the two coarse fields are of class `C^N`. -/
theorem gluedLift_sub_input_oc {α q : ℝ} {Λ m : ℕ} {φs : ℝ → Vec 2 → ℝ}
    (hφs : IsAdmissibleStream φs) {ν : ℝ} (hℓ : ocEll q Λ m ν ≠ 0) (kset : Finset ℤ)
    (ϖ : ℤ → ℝ → ℝ) (ρ e εc : ℝ) (N H : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (ha : ContDiff ℝ (N : ℕ∞) (a t))
    (hb : ContDiff ℝ (N : ℕ∞) (b t)) (x : Vec 2) :
    gluedLift kset ϖ (ocEll q Λ m ν ^ 2) ρ e εc N H Cc
        (fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
        (fun s y => a s y - b s y) t x =
      gluedLift kset ϖ (ocEll q Λ m ν ^ 2) ρ e εc N H Cc
          (fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a t x -
        gluedLift kset ϖ (ocEll q Λ m ν ^ 2) ρ e εc N H Cc
          (fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) b t x :=
  gluedLift_sub_input kset ϖ (ocEll q Λ m ν ^ 2) ρ e εc N H Cc
    (fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
    (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a b (pow_ne_zero 2 hℓ)
    (fun k _ => (contDiff_ocChart hφs α q Λ m (ocPulseChartIndex α q Λ m k) t).of_le
      (by exact_mod_cast le_top)) ha hb x

variable [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

/-- **The physical lift of a pulse is of class `C^J`** at a time whose cell time is in the lift
window, for a coarse field and a chart of class `C^{N+J}` and a label map of class `C^J`. -/
theorem pulsePhysicalLift_contDiff {D H N K k₀ L qs qf : ℕ} {Q : LiftOperatorData ι h D}
    {π : ι → ℝ} {t₀ t₁ e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : Fin 2}
    {V : ℝ → ℝ → ℝ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π t₀ t₁ e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ par V H N K k₀ L qs qf CG Cw
      Cj edgeM Θ)
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {J : ℕ} (hJp : J ≤ K + N + 2 * D + 2)
    (hJq : J ≤ max k₀ (L + 2) + 2 * D) {c : ℝ} (hc : c ≠ 0) (ρ e εc : ℝ)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ}
    (ht : c⁻¹ * t ∈ Icc t₀ t₁) (hχ : ContDiff ℝ ((N + J : ℕ) : ℕ∞) (chart t))
    (hψ : ContDiff ℝ (J : ℕ∞) (label t)) (ha : ContDiff ℝ ((N + J : ℕ) : ℕ∞) (a t)) :
    ContDiff ℝ (J : ℕ∞) (pulsePhysicalLift c ρ e εc N H Cc chart label a t) := by
  rw [pulsePhysicalLift_eq_comp]
  exact (setting_labelLift_contDiff_finite P sX sZ hsZ Cc hseq εc ρ e c hJp hJq
    (fun s X => a (c * s) (chart (c * s) (ρ • X))) t ht
    (contDiff_chartFrame a chart hc ha hχ ρ)).comp hψ

/-- **Jets of the physical lift of a pulse.** For charts and label maps whose jets of positive
order are bounded by `Cχ` and `Cψ`, there is a constant `M`, independent of the charts, the
coarse field and the time, such that at every time whose cell time is in the lift window the jets
of order `j ≤ J` of the physical lift are bounded by `M` times a bound `A` of the jets of order at
most `N + J` of the coarse field. -/
theorem pulsePhysicalLift_jet_le {D H N K k₀ L qs qf : ℕ} {Q : LiftOperatorData ι h D}
    {π : ι → ℝ} {t₀ t₁ e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : Fin 2}
    {V : ℝ → ℝ → ℝ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π t₀ t₁ e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ par V H N K k₀ L qs qf CG Cw
      Cj edgeM Θ)
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {J : ℕ} (hJp : J ≤ K + N + 2 * D + 2)
    (hJq : J ≤ max k₀ (L + 2) + 2 * D) {c : ℝ} (hc : c ≠ 0) (ρ e εc : ℝ) {Cχ Cψ : ℝ}
    (hCχ : 1 ≤ Cχ) (hCψ : 1 ≤ Cψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ),
      c⁻¹ * t ∈ Icc t₀ t₁ → ContDiff ℝ ((N + J : ℕ) : ℕ∞) (chart t) →
      (∀ i, 1 ≤ i → i ≤ N + J → ∀ y, ‖iteratedFDeriv ℝ i (chart t) y‖ ≤ Cχ) →
      ContDiff ℝ (J : ℕ∞) (label t) →
      (∀ i, 1 ≤ i → i ≤ J → ∀ y, ‖iteratedFDeriv ℝ i (label t) y‖ ≤ Cψ) →
      ContDiff ℝ ((N + J : ℕ) : ℕ∞) (a t) → ∀ A : ℝ,
      (∀ i ≤ N + J, ∀ y, ‖iteratedFDeriv ℝ i (a t) y‖ ≤ A) →
      ∀ j ≤ J, ∀ x,
        ‖iteratedFDeriv ℝ j (pulsePhysicalLift c ρ e εc N H Cc chart label a t) x‖ ≤ M * A := by
  choose ML hML0 hML using fun v : ι =>
    setting_labelLift_jet_bound P sX sZ hsZ Cc hseq εc ρ e c hJp hJq v
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_chartRead_jet_bound (F := ∀ i, h i) (N + J) hCχ ρ
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_comp_chart_jet_bound (F := ∀ i, h i) J hCψ
  have hMℓ0 : 0 ≤ ∑ v, ML v := Finset.sum_nonneg fun v _ => hML0 v
  have hN0 : (0 : ℝ) ≤ ((N + J : ℕ) : ℝ) + 1 := by positivity
  refine ⟨K₂ * ((∑ v, ML v) * ((((N + J : ℕ) : ℝ) + 1) * K₁)),
    mul_nonneg hK₂0 (mul_nonneg hMℓ0 (mul_nonneg hN0 hK₁0)), ?_⟩
  intro chart label a t ht hχ hχb hψ hψb ha A hA j hj x
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) 0)
  have hg := contDiff_chartFrame a chart hc ha hχ ρ
  -- the jets of the chart-frame field
  have hread : ∀ i ≤ N + J, ∀ X, ‖iteratedFDeriv ℝ i
      (fun X' : Vec 2 => a (c * (c⁻¹ * t)) (chart (c * (c⁻¹ * t)) (ρ • X'))) X‖ ≤ K₁ * A := by
    rw [mul_inv_cancel_left₀ hc t]
    exact hK₁ (a t) (chart t) ha hχ hχb A hA
  -- the jets of the label lift, componentwise and then in full
  have hLC := setting_labelLift_contDiff_finite P sX sZ hsZ Cc hseq εc ρ e c hJp hJq
    (fun s X => a (c * s) (chart (c * s) (ρ • X))) t ht hg
  have hlab : ∀ i ≤ J, ∀ y, ‖iteratedFDeriv ℝ i
      (labelLift Cc N H εc (fun s X => a (c * s) (chart (c * s) (ρ • X))) ρ e c t) y‖ ≤
        (∑ v, ML v) * ((((N + J : ℕ) : ℝ) + 1) * (K₁ * A)) := by
    intro i hi y
    have hiN : N + i ≤ N + J := Nat.add_le_add_left hi N
    refine norm_iteratedFDeriv_le_of_apply_le (hLC.of_le (by exact_mod_cast hi)) y
      (mul_nonneg hMℓ0 (mul_nonneg hN0 (mul_nonneg hK₁0 hA0))) fun v => ?_
    refine (hML v (fun s X => a (c * s) (chart (c * s) (ρ • X))) t ht hg i hi y).trans ?_
    refine mul_le_mul (Finset.single_le_sum (f := ML) (fun v _ => hML0 v) (Finset.mem_univ v))
      ?_ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hMℓ0
    exact sum_range_succ_le_mul_of_le (fun i' => ‖iteratedFDeriv ℝ i'
      (fun X' : Vec 2 => a (c * (c⁻¹ * t)) (chart (c * (c⁻¹ * t)) (ρ • X'))) (ρ⁻¹ • y)‖) hiN
      (mul_nonneg hK₁0 hA0) fun i' hi' => hread i' (hi'.trans hiN) (ρ⁻¹ • y)
  -- the composition with the label map
  rw [pulsePhysicalLift_eq_comp]
  exact (hK₂ _ (label t) hLC hψ hψb _ hlab j hj x).trans_eq (by ring)

/-- **The glued lift of a coarse field of class `C^{N+J}` is of class `C^J`** at every time of
the observation window: every weighted pulse has its cell
time in its lift window, and the renewal charts are smooth. -/
theorem gluedLift_contDiff_oc {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {φs : ℝ → Vec 2 → ℝ}
    (hφs : IsAdmissibleStream φs) {ν B ρ lam : ℝ} (hℓ : ocEll q Λ m ν ≠ 0) {D : ℕ}
    (edge : ℤ → ConstituentEdges D h) {tA tZ : ℝ} (ϖ : ℤ → ℝ → ℝ) {quiet : Set ℝ}
    {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) ϖ (ocPulseWindow α q Λ m) quiet
      (Icc tA tZ) (ocTau α q Λ m) Cpart)
    {π : ι → ℝ} {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2}
    {V : ℤ → ℝ → ℝ → ℝ} {H N K k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K k₀ L qs qf CG Cw Cj edgeM Θ)
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)) sX sZ
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    {J : ℕ} (hJp : J ≤ K + N + 2 * D + 2) (hJq : J ≤ max k₀ (L + 2) + 2 * D) (e εc : ℝ)
    (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (ht : t ∈ Icc tA tZ)
    (ha : ContDiff ℝ ((N + J : ℕ) : ℕ∞) (a t)) :
    ContDiff ℝ (J : ℕ∞) (gluedLift (ocObsPulses α q Λ m tA tZ) ϖ (ocEll q Λ m ν ^ 2) ρ e εc N H
      Cc (fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
      (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a t) := by
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  apply gluedLift_contDiff_of_weighted
  intro k hk hw
  exact pulsePhysicalLift_contDiff (P k hk) sX sZ hsZ (Cc k) (hseq k hk) hJp hJq hc0.ne' ρ e εc
    (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
    (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a
    (weighted_cellTime_mem_liftWindow hℓ hpart hk ht hw)
    ((contDiff_ocChart hφs α q Λ m (ocPulseChartIndex α q Λ m k) t).of_le
      (by exact_mod_cast le_top))
    ((contDiff_ocChartInv hφs α q Λ m (ocPulseChartIndex α q Λ m k) t).of_le
      (by exact_mod_cast le_top)) ha

/-- **Jets of the glued lift**. If the renewal charts of the
observed pulses and their inverses have normalized jets through `N + J` on the pulse windows,
there is a constant `M`, independent of the coarse field and the time, such that at every time
of the observation window the jets of order `j ≤ J` of the glued lift of a coarse field of class
`C^{N+J}` are bounded by `M` times a bound `A` of the jets of order at most `N + J` of the
field. -/
theorem gluedLift_jet_le_oc {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {φs : ℝ → Vec 2 → ℝ}
    (hφs : IsAdmissibleStream φs) {ν B ρ lam : ℝ} (hℓ : ocEll q Λ m ν ≠ 0) {D : ℕ}
    (edge : ℤ → ConstituentEdges D h) {tA tZ : ℝ} (ϖ : ℤ → ℝ → ℝ) {quiet : Set ℝ}
    {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) ϖ (ocPulseWindow α q Λ m) quiet
      (Icc tA tZ) (ocTau α q Λ m) Cpart)
    {π : ι → ℝ} {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2}
    {V : ℤ → ℝ → ℝ → ℝ} {H N K k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K k₀ L qs qf CG Cw Cj edgeM Θ)
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)) sX sZ
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    {J : ℕ} (hJp : J ≤ K + N + 2 * D + 2) (hJq : J ≤ max k₀ (L + 2) + 2 * D) (e εc : ℝ)
    {Dχ Rχ : ℝ} (hD : 1 ≤ Dχ)
    (hjet : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ s ∈ ocPulseWindow α q Λ m k,
      JetBound (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) s) (N + J) Dχ Rχ ∧
        JetBound (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) s) (N + J) Dχ Rχ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ), t ∈ Icc tA tZ →
      ContDiff ℝ ((N + J : ℕ) : ℕ∞) (a t) → ∀ A : ℝ,
      (∀ i ≤ N + J, ∀ y, ‖iteratedFDeriv ℝ i (a t) y‖ ≤ A) →
      ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (gluedLift (ocObsPulses α q Λ m tA tZ) ϖ
        (ocEll q Λ m ν ^ 2) ρ e εc N H Cc
        (fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a t) x‖ ≤ M * A := by
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hCχ : 1 ≤ Dχ * (max |Rχ⁻¹| 1) ^ (N + J) :=
    one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ (le_max_right _ _))
  -- the jet constant of every observed pulse
  have hMk : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ), t ∈ Icc tA tZ → ϖ k t ≠ 0 →
        ContDiff ℝ ((N + J : ℕ) : ℕ∞) (a t) → ∀ A : ℝ,
        (∀ i ≤ N + J, ∀ y, ‖iteratedFDeriv ℝ i (a t) y‖ ≤ A) →
        ContDiff ℝ (J : ℕ∞) (pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ e εc N H (Cc k)
          (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
          (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a t) ∧
        ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ e εc N H
          (Cc k) (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
          (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a t) x‖ ≤ M * A := by
    intro k hk
    obtain ⟨M, hM0, hM⟩ := pulsePhysicalLift_jet_le (P k hk) sX sZ hsZ (Cc k) (hseq k hk) hJp
      hJq hc0.ne' ρ e εc hCχ hCχ
    refine ⟨M, hM0, fun a t ht hw ha A hA => ?_⟩
    have hct := weighted_cellTime_mem_liftWindow hℓ hpart hk ht hw
    have hjk := hjet k hk t (hpart.2.2.2.1 k hk t hw)
    have hχ : ContDiff ℝ ((N + J : ℕ) : ℕ∞)
        (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) :=
      (contDiff_ocChart hφs α q Λ m (ocPulseChartIndex α q Λ m k) t).of_le
        (by exact_mod_cast le_top)
    have hψ : ContDiff ℝ (J : ℕ∞) (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) :=
      (contDiff_ocChartInv hφs α q Λ m (ocPulseChartIndex α q Λ m k) t).of_le
        (by exact_mod_cast le_top)
    exact ⟨pulsePhysicalLift_contDiff (P k hk) sX sZ hsZ (Cc k) (hseq k hk) hJp hJq hc0.ne' ρ e
        εc (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a hct hχ hψ ha,
      hM (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a t hct hχ
        (jetBound_le_uniform hD hjk.1) hψ
        (fun i hi1 hiJ y => jetBound_le_uniform hD hjk.2 i hi1 (by omega) y) ha A hA⟩
  choose! Mk hMk0 hMk using hMk
  refine ⟨∑ k ∈ ocObsPulses α q Λ m tA tZ, Mk k, Finset.sum_nonneg hMk0,
    fun a t ht ha A hA j hj x => ?_⟩
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) 0)
  exact norm_iteratedFDeriv_gluedLift_le_of_weighted (ocObsPulses α q Λ m tA tZ) ϖ
    (ocEll q Λ m ν ^ 2) ρ e εc N H Cc
    (fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
    (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a t
    (fun k hk => hpart.1 k hk t) (hpart.2.2.1 t ht) Mk
    (fun k hk hw => hMk k hk a t ht hw ha A hA) (fun k hk => mul_nonneg (hMk0 k hk) hA0) hj x

/-- **Jets of the glued lift in the renewal charts of the background stream**: the chart
hypotheses of `gluedLift_jet_le_oc` are the jet bounds of the renewal charts on the pulse
windows (`pulseChart_jetBound`, at the coarse scale `ε_{m-1}`). -/
theorem gluedLift_jet_le_pulseChart {α σ q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hσ₀ : 0 < σ)
    (hσ₁ : σ < (1 - α) / 2) (hq : IsAdmissibleQ α σ q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {Λ : ℕ} (hΛ : 128 ≤ Λ) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsOCStreamSeq α q Λ ζ Φ) {m : ℕ}
    (hm : 2 ≤ m) (hφs : IsAdmissibleStream (Φ (m - 1))) {ν B ρ lam : ℝ}
    (hℓ : ocEll q Λ m ν ≠ 0) {D : ℕ} (edge : ℤ → ConstituentEdges D h) {tA tZ : ℝ}
    (ϖ : ℤ → ℝ → ℝ) {quiet : Set ℝ} {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) ϖ (ocPulseWindow α q Λ m) quiet
      (Icc tA tZ) (ocTau α q Λ m) Cpart)
    {π : ι → ℝ} {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2}
    {V : ℤ → ℝ → ℝ → ℝ} {H N K k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (edge k)) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K k₀ L qs qf CG Cw Cj edgeM Θ)
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam k (edge k)) sX sZ
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    {J : ℕ} (hJp : J ≤ K + N + 2 * D + 2) (hJq : J ≤ max k₀ (L + 2) + 2 * D) (e εc : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ), t ∈ Icc tA tZ →
      ContDiff ℝ ((N + J : ℕ) : ℕ∞) (a t) → ∀ A : ℝ,
      (∀ i ≤ N + J, ∀ y, ‖iteratedFDeriv ℝ i (a t) y‖ ≤ A) →
      ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (gluedLift (ocObsPulses α q Λ m tA tZ) ϖ
        (ocEll q Λ m ν ^ 2) ρ e εc N H Cc
        (fun k => ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) a t) x‖ ≤
          M * A :=
  gluedLift_jet_le_oc hφs hℓ edge ϖ hpart P sX sZ hsZ Cc hseq hJp hJq e εc
    (one_le_pulseChartD (N + J)) fun k _ _ hs =>
      pulseChart_jetBound α σ hα₀ hα₁ hσ₀ hσ₁ q hq ζ hζ Λ hΛ Φ hΦ m hm hφs k hs (N + J)

end Lift

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The tail of one pulse in physical divergence form** (exact Piola transports flux by
`(DΦR)∘Φ⁻¹`).

The tail part `restTail` of the rest of a pulse lift (`labelRest_split`) is, for each degree
`hh ≤ H`, `c⁻¹ ε^{N+1}` times the label divergence of the sampled cleanup flux plus the sampled
cleanup remainder of a cleanup chain `Vc hh` of the explicit tail presentation
(`setting_tail_presentation`, `tail_sample_eq_cleanup`). Summing over `hh`:

* `setting_restTail_label`: `c⁻¹ restTail(y) = div_y tailFluxLabel(y) + ∑_hh c⁻¹ ε^{N+1} q_hh(y)`;
* `setting_restTail_phys`: for a chart `χ` with inverse `ψ` and `det Dχ = 1`, at `y = ψ x`
  this is the physical divergence of the Piola transport `tailFluxPhys` of the label flux plus
  `tailForcePhys` (`chartInvJacobian_piola`);
* `setting_restTail_tested`: tested against a `C¹` periodic test on the cell, the divergence
  is integrated by parts (`cell_ibp_div`). The physical flux is `C¹` (the chains are box smooth,
  the chart and its inverse Jacobian are smooth) and `ℤ²`-periodic: the chains are slow invariant
  for `ρ⁻¹ℤ²` (`setting_tail_cleanupChain_slowShift`) and fast periodic, `e⁻¹ ∈ ℕ`, and the chart
  is lattice equivariant (`tailFluxLabel_isZ2Periodic`, `tailFluxPhys_isZ2Periodic`). The force is
  continuous (`continuous_tailForcePhys`).
* `setting_pulse_restTail_tested`: the same for the renewal chart
  `ocChart … l t` and the chart-frame field `chartField cf φ (ocChart … l) c ρs` of a finite-rank
  coarse field. -/

section Coord

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

omit [Fintype ι] in
/-- A coordinate of the derivative of a field differentiable at `x` is the derivative of the
coordinate. -/
theorem tail_fderiv_pi_coord {f : Vec 2 → ∀ i, h i} {x : Vec 2} (hf : DifferentiableAt ℝ f x)
    (w : Vec 2) (v : ι) : fderiv ℝ f x w v = fderiv ℝ (fun y => f y v) x w := by
  simp only [_root_.fderiv_apply hf v, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

end Coord

section Sample

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `1 ≤ 1` through the casts of the smoothness orders. -/
theorem one_le_withTop_natCast_one : (1 : WithTop ℕ∞) ≤ (((1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
  simp

/-- The sampled cleanup flux of a chain of box-smooth fields of orders `≥ (1, 1)` is `C¹` in the
label. -/
theorem contDiff_cleanupFlux_sample {sX sZ A : ℕ} (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) (c ρ e : ℝ)
    {Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E} (t : ℝ)
    (hV : ∀ j, j < A → IsBoxSmooth sX sZ (Vc j (c * t))) (kk : Fin 2) :
    ContDiff ℝ 1 (fun y => cleanupFlux c ρ e A Vc t y kk) := by
  have hg : ContDiff ℝ 1 (fun y : Vec 2 => (ρ⁻¹ • y, e⁻¹ • y)) :=
    (contDiff_const_smul _).prodMk (contDiff_const_smul _)
  have hj : ∀ j ∈ Finset.range A, ContDiff ℝ 1
      (fun y => (e / ρ) ^ j • Vc j (c * t) (ρ⁻¹ • y) (e⁻¹ • y) kk) := fun j hj => by
    have hu : ContDiff ℝ 1 (Function.uncurry (Vc j (c * t))) :=
      ((hV j (Finset.mem_range.1 hj)).contDiff_uncurry hX hZ).of_le one_le_withTop_natCast_one
    exact ((contDiff_apply ℝ E kk).comp (hu.comp hg)).const_smul _
  show ContDiff ℝ 1 (fun y => e • ∑ j ∈ Finset.range A, (e / ρ) ^ j •
    Vc j (c * t) (ρ⁻¹ • y) (e⁻¹ • y) kk)
  exact (ContDiff.sum hj).const_smul e

/-- The sampled cleanup remainder of a chain of box-smooth fields of slow order `≥ 1` is
continuous in the label. -/
theorem continuous_cleanupRemainder_sample {sX sZ A : ℕ} (hA : 1 ≤ A) (hX : 1 ≤ sX)
    (c ρ e : ℝ) {Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E} (t : ℝ)
    (hV : ∀ j, j < A → IsBoxSmooth sX sZ (Vc j (c * t))) :
    Continuous (fun y => cleanupRemainder c ρ e A Vc t y) := by
  have h1 : ∀ kk : Fin 2, IsBoxSmooth 0 0
      (slowPartial kk (fun X z => Vc (A - 1) (c * t) X z kk)) := fun kk =>
    (((hV (A - 1) (by omega)).mono (by omega : 0 + 1 ≤ sX) (Nat.zero_le sZ)).clm_comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) kk)).slowPartial kk
  have hS : IsBoxSmooth 0 0 (cleanupSource (fun j => Vc j (c * t)) A) :=
    (IsBoxSmooth.sum Finset.univ fun kk _ => h1 kk).neg
  have hcont : Continuous (Function.uncurry (cleanupSource (fun j => Vc j (c * t)) A)) :=
    (hS.contDiff_uncurry le_rfl le_rfl).continuous
  have hg : Continuous (fun y : Vec 2 => (ρ⁻¹ • y, e⁻¹ • y)) :=
    (continuous_const_smul ρ⁻¹).prodMk (continuous_const_smul e⁻¹)
  show Continuous (fun y => (e / ρ) ^ A •
    cleanupSource (fun j => Vc j (c * t)) A (ρ⁻¹ • y) (e⁻¹ • y))
  exact (hcont.comp hg).fun_const_smul _

/-- **Periodicity of the sampled cleanup flux.** If `e⁻¹ = M ∈ ℕ`, the members of the chain at
the cell time are invariant under the slow translations by `ρ⁻¹ℤ²` and `ℤ²`-periodic in the fast
variable, then the sampled cleanup flux is `ℤ²`-periodic in the label. -/
theorem cleanupFlux_isZ2Periodic (c ρ e : ℝ) (A : ℕ) (W : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (t : ℝ) (M : ℕ) (hM : e⁻¹ = M)
    (hslow : ∀ j, j < A → ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      W j (c * t) (X + ρ⁻¹ • latticeShift n) = W j (c * t) X)
    (hfast : ∀ j, j < A → ∀ X, IsZ2Periodic (W j (c * t) X)) (kk : Fin 2) :
    IsZ2Periodic (fun y => cleanupFlux c ρ e A W t y kk) := by
  intro n y
  have hX : ρ⁻¹ • (y + latticeShift n) = ρ⁻¹ • y + ρ⁻¹ • latticeShift n := smul_add _ _ _
  have hz : e⁻¹ • (y + latticeShift n) = e⁻¹ • y + latticeShift (fun i => (M : ℤ) * n i) := by
    rw [smul_add, hM, natCast_smul_latticeShift]
  show e • ∑ j ∈ Finset.range A, (e / ρ) ^ j •
      W j (c * t) (ρ⁻¹ • (y + latticeShift n)) (e⁻¹ • (y + latticeShift n)) kk =
    e • ∑ j ∈ Finset.range A, (e / ρ) ^ j • W j (c * t) (ρ⁻¹ • y) (e⁻¹ • y) kk
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjA : j < A := Finset.mem_range.1 hj
  have hf : W j (c * t) (ρ⁻¹ • y) (e⁻¹ • y + latticeShift (fun i => (M : ℤ) * n i)) =
      W j (c * t) (ρ⁻¹ • y) (e⁻¹ • y) :=
    hfast j hjA (ρ⁻¹ • y) (fun i => (M : ℤ) * n i) (e⁻¹ • y)
  rw [hX, hz, hslow j hjA n, hf]

end Sample

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The entries of the inverse Jacobian `K = chartInvJacobian ψ` of a smooth chart with smooth
inverse are smooth. -/
theorem contDiff_chartInvJacobian_apply {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    (a₀ i₀ : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => chartInvJacobian ψ x a₀ i₀) := by
  have he : (fun x => chartInvJacobian ψ x a₀ i₀) = fun x => chartJacobian χ (ψ x) a₀ i₀ := by
    funext x
    rw [chartInvJacobian_eq_of_inverse (hχ.differentiable (by simp))
      (hψ.differentiable (by simp)) hψχ hχψ x]
  rw [he]
  let Lc : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) a₀).comp
      (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec i₀))
  exact (Lc.contDiff.comp (hχ.fderiv_right (by simp))).comp hψ

/-- **The label tail flux** of one pulse at the physical time `t` and the label `y`: the sum
over the degrees `hh ≤ H` of `c⁻¹ ε^{N+1}` times the sampled cleanup flux of the chain `Vc hh`
(the normalization of `tail_sample_eq_cleanup`, with cell time `c⁻¹ t`). -/
def tailFluxLabel (H N Acl : ℕ) (ε c ρs es : ℝ) (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (t : ℝ) (y : Vec 2) (i₀ : Fin 2) : E :=
  ∑ hh ∈ Finset.range (H + 1), c⁻¹ • ε ^ (N + 1) • cleanupFlux c⁻¹ ρs es Acl (Vc hh) t y i₀

/-- **The physical tail flux** of one pulse: the Piola transport
`x ↦ ∑_{i₀} K_{a₀ i₀}(x) F(ψ x)_{i₀}`, `K = chartInvJacobian ψ`, of the label tail flux `F`. -/
def tailFluxPhys (ψ : Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ) (x : Vec 2) (a₀ : Fin 2) : E :=
  ∑ i₀ : Fin 2, chartInvJacobian ψ x a₀ i₀ • tailFluxLabel H N Acl ε c ρs es Vc t (ψ x) i₀

/-- **The physical tail force** of one pulse: the sum over the degrees `hh ≤ H` of `c⁻¹ ε^{N+1}`
times the sampled cleanup remainder of the chain `Vc hh`, at the label `ψ x`. -/
def tailForcePhys (ψ : Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ) (x : Vec 2) : E :=
  ∑ hh ∈ Finset.range (H + 1), c⁻¹ • ε ^ (N + 1) • cleanupRemainder c⁻¹ ρs es Acl (Vc hh) t (ψ x)

/-- The label tail flux of chains box smooth of orders `≥ (1, 1)` at the cell time is `C¹`. -/
theorem contDiff_tailFluxLabel {sX sZ : ℕ} (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) (H N Acl : ℕ)
    (ε c ρs es : ℝ) (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ)
    (hV : ∀ hh, hh ≤ H → ∀ j, j < Acl → IsBoxSmooth sX sZ (Vc hh j (c⁻¹ * t))) (i₀ : Fin 2) :
    ContDiff ℝ 1 (fun y => tailFluxLabel H N Acl ε c ρs es Vc t y i₀) := by
  show ContDiff ℝ 1 (fun y => ∑ hh ∈ Finset.range (H + 1),
    c⁻¹ • ε ^ (N + 1) • cleanupFlux c⁻¹ ρs es Acl (Vc hh) t y i₀)
  exact ContDiff.sum fun hh hhm => ((contDiff_cleanupFlux_sample hX hZ c⁻¹ ρs es t
    (hV hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm))) i₀).const_smul (ε ^ (N + 1))).const_smul
      c⁻¹

/-- The label tail flux is `ℤ²`-periodic in the label when `e⁻¹ ∈ ℕ` and the chains at the cell
time are invariant under the slow translations by `ρ⁻¹ℤ²` and periodic in the fast variable. -/
theorem tailFluxLabel_isZ2Periodic (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ) (M : ℕ) (hM : es⁻¹ = M)
    (hslow : ∀ hh, hh ≤ H → ∀ j, j < Acl → ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      Vc hh j (c⁻¹ * t) (X + ρs⁻¹ • latticeShift n) = Vc hh j (c⁻¹ * t) X)
    (hfast : ∀ hh, hh ≤ H → ∀ j, j < Acl → ∀ X, IsZ2Periodic (Vc hh j (c⁻¹ * t) X))
    (i₀ : Fin 2) : IsZ2Periodic (fun y => tailFluxLabel H N Acl ε c ρs es Vc t y i₀) := by
  intro n y
  show ∑ hh ∈ Finset.range (H + 1), c⁻¹ • ε ^ (N + 1) •
      cleanupFlux c⁻¹ ρs es Acl (Vc hh) t (y + latticeShift n) i₀ =
    ∑ hh ∈ Finset.range (H + 1), c⁻¹ • ε ^ (N + 1) • cleanupFlux c⁻¹ ρs es Acl (Vc hh) t y i₀
  refine Finset.sum_congr rfl fun hh hhm => ?_
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
  have hp : cleanupFlux c⁻¹ ρs es Acl (Vc hh) t (y + latticeShift n) i₀ =
      cleanupFlux c⁻¹ ρs es Acl (Vc hh) t y i₀ :=
    cleanupFlux_isZ2Periodic c⁻¹ ρs es Acl (Vc hh) t M hM (hslow hh hhh) (hfast hh hhh) i₀ n y
  rw [hp]

/-- The physical tail flux of a `C¹` label flux, read through a smooth chart with smooth inverse,
is `C¹`. -/
theorem contDiff_tailFluxPhys {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    (H N Acl : ℕ) (ε c ρs es : ℝ) (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ)
    (hG : ∀ i₀, ContDiff ℝ 1 (fun y => tailFluxLabel H N Acl ε c ρs es Vc t y i₀))
    (a₀ : Fin 2) : ContDiff ℝ 1 (fun x => tailFluxPhys ψ H N Acl ε c ρs es Vc t x a₀) := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  show ContDiff ℝ 1 (fun x => ∑ i₀ : Fin 2,
    chartInvJacobian ψ x a₀ i₀ • tailFluxLabel H N Acl ε c ρs es Vc t (ψ x) i₀)
  exact ContDiff.sum fun i₀ _ =>
    ((contDiff_chartInvJacobian_apply hχ hψ hψχ hχψ a₀ i₀).of_le (by simp)).fun_smul
      ((hG i₀).comp hψ1)

/-- The physical tail flux of a `ℤ²`-periodic label flux, read through a lattice equivariant
chart, is `ℤ²`-periodic. -/
theorem tailFluxPhys_isZ2Periodic {ψ : Vec 2 → Vec 2}
    (hψl : ∀ (n : Fin 2 → ℤ) (x : Vec 2), ψ (x + latticeShift n) = ψ x + latticeShift n)
    (H N Acl : ℕ) (ε c ρs es : ℝ) (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ)
    (hG : ∀ i₀, IsZ2Periodic (fun y => tailFluxLabel H N Acl ε c ρs es Vc t y i₀))
    (a₀ : Fin 2) : IsZ2Periodic (fun x => tailFluxPhys ψ H N Acl ε c ρs es Vc t x a₀) := by
  intro n x
  have hK : chartInvJacobian ψ (x + latticeShift n) = chartInvJacobian ψ x :=
    TorusCompatible.isZ2Periodic_chartInvJacobian hψl n x
  show ∑ i₀ : Fin 2, chartInvJacobian ψ (x + latticeShift n) a₀ i₀ •
      tailFluxLabel H N Acl ε c ρs es Vc t (ψ (x + latticeShift n)) i₀ =
    ∑ i₀ : Fin 2, chartInvJacobian ψ x a₀ i₀ • tailFluxLabel H N Acl ε c ρs es Vc t (ψ x) i₀
  refine Finset.sum_congr rfl fun i₀ _ => ?_
  have hGi : tailFluxLabel H N Acl ε c ρs es Vc t (ψ x + latticeShift n) i₀ =
      tailFluxLabel H N Acl ε c ρs es Vc t (ψ x) i₀ := hG i₀ n (ψ x)
  rw [hK, hψl n x, hGi]

/-- **Piola for the tail flux.** For an area preserving chart `χ` with inverse `ψ`, the physical
divergence of the tail flux at `x` is the label divergence of the label tail flux at `ψ x`. -/
theorem div_tailFluxPhys {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    (hd : ∀ y, (jacMatrix χ y).det = 1) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ)
    (hG : ∀ i₀, Differentiable ℝ (fun y => tailFluxLabel H N Acl ε c ρs es Vc t y i₀))
    (x : Vec 2) :
    ∑ a₀ : Fin 2, fderiv ℝ (fun x' => tailFluxPhys ψ H N Acl ε c ρs es Vc t x' a₀) x
        (basisVec a₀) =
      ∑ i₀ : Fin 2, fderiv ℝ (fun y => tailFluxLabel H N Acl ε c ρs es Vc t y i₀) (ψ x)
        (basisVec i₀) :=
  chartInvJacobian_piola hχ hψ hψχ hχψ hd
    (F := fun y i₀ => tailFluxLabel H N Acl ε c ρs es Vc t y i₀) hG x

/-- The physical tail force of continuous sampled remainders, read through a continuous label
map, is continuous. -/
theorem continuous_tailForcePhys {ψ : Vec 2 → Vec 2} (hψ : Continuous ψ) (H N Acl : ℕ)
    (ε c ρs es : ℝ) (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ)
    (hR : ∀ hh, hh ≤ H → Continuous (fun y => cleanupRemainder c⁻¹ ρs es Acl (Vc hh) t y)) :
    Continuous (fun x => tailForcePhys ψ H N Acl ε c ρs es Vc t x) := by
  show Continuous (fun x => ∑ hh ∈ Finset.range (H + 1),
    c⁻¹ • ε ^ (N + 1) • cleanupRemainder c⁻¹ ρs es Acl (Vc hh) t (ψ x))
  exact continuous_finsetSum _ fun hh hhm =>
    (((hR hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm))).comp hψ).fun_const_smul
      (ε ^ (N + 1))).fun_const_smul c⁻¹

end Chart

section Setting

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- The members of the cleanup chains of the divided tails are box smooth at a window time of a
smooth coarse field. -/
theorem setting_tail_cleanupChain_box (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    {sXc sZc Acl : ℕ} (hX : sXc ≤ K + D + 2) (hZ : sZc ≤ max (k + 1) (L + 2)) (ε : ℝ)
    (A : ℝ → Vec 2 → ∀ i, h i) (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → ∀ τ ∈ Set.Icc a b, IsCleanupChain sXc sZc Acl
      (tailScalarField (fun _ => 0) N D ε A τ)
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ)
      (fun j => Vc hh j τ))
    {τ : ℝ} (hτ : τ ∈ Set.Icc a b) (hA : ContDiff ℝ (⊤ : ℕ∞) (A τ)) :
    ∀ hh, hh ≤ H → ∀ j, j < Acl → IsBoxSmooth sXc sZc (Vc hh j τ) := fun hh hhh =>
  IsCleanupChain.isBoxSmooth
    ((isBoxSmooth_tailFluxField_of_presentation (f := fun _ => 0)
      (F := fun n => tailFluxCoefficient par Q Cc N hh n)
      (fun n hn1 hn2 => setting_tail_presentation P sX sZ hsX hsZ Cc hseq hh hhh n (by omega) hn2)
      ε A hτ hA).mono hX hZ) (hV hh hhh τ hτ)

include P in
/-- **The tail of the rest in label divergence form.** At a physical time `t` with cell time
`c⁻¹ t` in the window and a smooth coarse field there, `c⁻¹` times the tail of the rest at the
label `y` is the label divergence of the label tail flux plus the sampled cleanup remainders. -/
theorem setting_restTail_label (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (sXc sZc Acl : ℕ) (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc ≤ K + D + 2) (hZ : sZc ≤ max (k + 1) (L + 2)) (ε : ℝ) {c ρs es : ℝ}
    (hρ : ρs ≠ 0) (he : es ≠ 0) (A : ℝ → Vec 2 → ∀ i, h i)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → ∀ τ ∈ Set.Icc a b, IsCleanupChain sXc sZc Acl
      (tailScalarField (fun _ => 0) N D ε A τ)
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ)
      (fun j => Vc hh j τ))
    {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b) (hA : ContDiff ℝ (⊤ : ℕ∞) (A (c⁻¹ * t)))
    (y : Vec 2) :
    c⁻¹ • restTail Q Cc N H ε A ρs es c t y =
      ∑ i₀ : Fin 2, fderiv ℝ (fun y' => tailFluxLabel H N Acl ε c ρs es Vc t y' i₀) y
          (basisVec i₀)
        + ∑ hh ∈ Finset.range (H + 1),
          c⁻¹ • ε ^ (N + 1) • cleanupRemainder c⁻¹ ρs es Acl (Vc hh) t y := by
  have hpres := fun (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn1 : N + 1 ≤ n) (hn2 : n ≤ 2 * N + D) =>
    setting_tail_presentation P sX sZ hsX hsZ Cc hseq hh hhh n (by omega) hn2
  have hbox := setting_tail_cleanupChain_box P sX sZ hsX hsZ Cc hseq hX hZ ε A Vc hV ht hA
  have hcl : ∀ hh ∈ Finset.range (H + 1),
      c⁻¹ • ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ n •
          liftTailCoeff Q Cc N (fun _ => A (c⁻¹ * t)) hh n (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y)
        = ∑ i₀ : Fin 2, fderiv ℝ (fun y' => c⁻¹ • ε ^ (N + 1) •
              cleanupFlux c⁻¹ ρs es Acl (Vc hh) t y' i₀) y (basisVec i₀)
          + c⁻¹ • ε ^ (N + 1) • cleanupRemainder c⁻¹ ρs es Acl (Vc hh) t y := by
    intro hh hhm
    have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
    exact tail_sample_eq_cleanup (f := fun _ => 0)
      (F := fun n => tailFluxCoefficient par Q Cc N hh n) sXc sZc Acl hAcl hXc hZc hX hZ
      (hpres hh hhh) ε c⁻¹ hρ he A (Vc hh) (hV hh hhh) ht hA y
  have hdiff : ∀ hh ∈ Finset.range (H + 1), ∀ i₀ : Fin 2, DifferentiableAt ℝ
      (fun y' => c⁻¹ • ε ^ (N + 1) • cleanupFlux c⁻¹ ρs es Acl (Vc hh) t y' i₀) y :=
    fun hh hhm i₀ => (((contDiff_cleanupFlux_sample hXc hZc c⁻¹ ρs es t
      (hbox hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm))) i₀).const_smul
        (ε ^ (N + 1))).const_smul c⁻¹).differentiable one_ne_zero y
  have hdiv : ∑ hh ∈ Finset.range (H + 1), ∑ i₀ : Fin 2, fderiv ℝ (fun y' => c⁻¹ • ε ^ (N + 1) •
        cleanupFlux c⁻¹ ρs es Acl (Vc hh) t y' i₀) y (basisVec i₀) =
      ∑ i₀ : Fin 2, fderiv ℝ (fun y' => tailFluxLabel H N Acl ε c ρs es Vc t y' i₀) y
        (basisVec i₀) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i₀ _ => ?_
    show _ = fderiv ℝ (fun y' => ∑ hh ∈ Finset.range (H + 1),
      c⁻¹ • ε ^ (N + 1) • cleanupFlux c⁻¹ ρs es Acl (Vc hh) t y' i₀) y (basisVec i₀)
    rw [fderiv_fun_sum fun hh hhm => hdiff hh hhm i₀]
    simp only [FunLike.coe_sum, Finset.sum_apply]
  rw [restTail, Finset.smul_sum, Finset.sum_congr rfl hcl, Finset.sum_add_distrib, hdiv]

include P in
/-- **The tail of the rest in physical divergence form.** For a smooth area preserving
chart `χ` with smooth inverse `ψ`, at a physical time `t` with cell time `c⁻¹ t` in the window and
a smooth coarse field there, `c⁻¹` times the tail of the rest at `ψ x` is the physical divergence
of the tail flux plus the tail force. -/
theorem setting_restTail_phys (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (sXc sZc Acl : ℕ) (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc ≤ K + D + 2) (hZ : sZc ≤ max (k + 1) (L + 2)) (ε : ℝ) {c ρs es : ℝ}
    (hρ : ρs ≠ 0) (he : es ≠ 0) (A : ℝ → Vec 2 → ∀ i, h i)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → ∀ τ ∈ Set.Icc a b, IsCleanupChain sXc sZc Acl
      (tailScalarField (fun _ => 0) N D ε A τ)
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ)
      (fun j => Vc hh j τ))
    {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b) (hA : ContDiff ℝ (⊤ : ℕ∞) (A (c⁻¹ * t)))
    {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (hd : ∀ y, (jacMatrix χ y).det = 1)
    (x : Vec 2) :
    c⁻¹ • restTail Q Cc N H ε A ρs es c t (ψ x) =
      ∑ a₀ : Fin 2, fderiv ℝ (fun x' => tailFluxPhys ψ H N Acl ε c ρs es Vc t x' a₀) x
          (basisVec a₀)
        + tailForcePhys ψ H N Acl ε c ρs es Vc t x := by
  have hbox := setting_tail_cleanupChain_box P sX sZ hsX hsZ Cc hseq hX hZ ε A Vc hV ht hA
  show _ = _ + ∑ hh ∈ Finset.range (H + 1),
    c⁻¹ • ε ^ (N + 1) • cleanupRemainder c⁻¹ ρs es Acl (Vc hh) t (ψ x)
  rw [setting_restTail_label P sX sZ hsX hsZ Cc hseq sXc sZc Acl hAcl hXc hZc hX hZ ε hρ he A Vc
      hV ht hA (ψ x),
    div_tailFluxPhys hχ hψ hψχ hχψ hd H N Acl ε c ρs es Vc t (fun i₀ =>
      (contDiff_tailFluxLabel hXc hZc H N Acl ε c ρs es Vc t hbox i₀).differentiable
        one_ne_zero) x]

include P in
/-- The physical tail flux and force of one pulse are continuous at a window time. -/
theorem setting_restTail_continuous (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (sXc sZc Acl : ℕ) (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc ≤ K + D + 2) (hZ : sZc ≤ max (k + 1) (L + 2)) (ε : ℝ) {c ρs es : ℝ}
    (A : ℝ → Vec 2 → ∀ i, h i) (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → ∀ τ ∈ Set.Icc a b, IsCleanupChain sXc sZc Acl
      (tailScalarField (fun _ => 0) N D ε A τ)
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ)
      (fun j => Vc hh j τ))
    {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b) (hA : ContDiff ℝ (⊤ : ℕ∞) (A (c⁻¹ * t)))
    {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (v : ι) :
    (∀ a₀ : Fin 2, Continuous (fun x => tailFluxPhys ψ H N Acl ε c ρs es Vc t x a₀ v)) ∧
      Continuous (fun x => tailForcePhys ψ H N Acl ε c ρs es Vc t x v) := by
  have hbox := setting_tail_cleanupChain_box P sX sZ hsX hsZ Cc hseq hX hZ ε A Vc hV ht hA
  have hLc := contDiff_tailFluxLabel hXc hZc H N Acl ε c ρs es Vc t hbox
  have hF := contDiff_tailFluxPhys hχ hψ hψχ hχψ H N Acl ε c ρs es Vc t hLc
  exact ⟨fun a₀ => (contDiff_pi.1 (hF a₀) v).continuous,
    (continuous_apply v).comp (continuous_tailForcePhys hψ.continuous H N Acl ε c ρs es Vc t
      fun hh hhh => continuous_cleanupRemainder_sample hAcl hXc c⁻¹ ρs es t (hbox hh hhh))⟩

include P in
/-- **The tested tail of the rest.** In the setting of `setting_restTail_phys`, let the
chart inverse `ψ` be lattice equivariant, `e⁻¹ = M ∈ ℕ`, the slow translations by `ρ⁻¹ℤ²` leave
the metric, the source coefficients and the coarse field at the cell time invariant. Then for a
`C¹` periodic test `φt` the tested tail of the rest on the cell is
`-∫ ∑_a ⟪tailFluxPhys_a, ∂_a φt⟫ + ∫ ⟪tailForcePhys, φt⟫`. -/
theorem setting_restTail_tested (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (sXc sZc Acl : ℕ) (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc ≤ K + D + 2) (hZ : sZc ≤ max (k + 1) (L + 2)) (ε : ℝ) {c ρs es : ℝ}
    (hρ : ρs ≠ 0) (he : es ≠ 0) (A : ℝ → Vec 2 → ∀ i, h i)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → ∀ τ ∈ Set.Icc a b, IsCleanupChain sXc sZc Acl
      (tailScalarField (fun _ => 0) N D ε A τ)
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ)
      (fun j => Vc hh j τ))
    {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b) (hA : ContDiff ℝ (⊤ : ℕ∞) (A (c⁻¹ * t)))
    {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (hd : ∀ y, (jacMatrix χ y).det = 1)
    (hψl : ∀ (n : Fin 2 → ℤ) (x : Vec 2), ψ (x + latticeShift n) = ψ x + latticeShift n)
    (M : ℕ) (hM : es⁻¹ = M)
    (hGs : ∀ (n : Fin 2 → ℤ) t X i j, Q.G t (X + ρs⁻¹ • latticeShift n) i j = Q.G t X i j)
    (hcs : ∀ (n : Fin 2 → ℤ) v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z,
      γ.coeff α t (X + ρs⁻¹ • latticeShift n) z = γ.coeff α t X z)
    (hAp : ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      A (c⁻¹ * t) (X + ρs⁻¹ • latticeShift n) = A (c⁻¹ * t) X)
    (v : ι) (φt : Vec 2 → h v) (hφt : ContDiff ℝ 1 φt) (hφtp : IsZ2Periodic φt) :
    ∫ x in AVenhance.unitCube, inner ℝ ((c⁻¹ • restTail Q Cc N H ε A ρs es c t (ψ x)) v) (φt x) =
      -(∫ x in AVenhance.unitCube, ∑ a₀ : Fin 2,
          inner ℝ (tailFluxPhys ψ H N Acl ε c ρs es Vc t x a₀ v) (fderiv ℝ φt x (basisVec a₀)))
        + ∫ x in AVenhance.unitCube,
          inner ℝ (tailForcePhys ψ H N Acl ε c ρs es Vc t x v) (φt x) := by
  have hpres := fun (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn1 : N + 1 ≤ n) (hn2 : n ≤ 2 * N + D) =>
    setting_tail_presentation P sX sZ hsX hsZ Cc hseq hh hhh n (by omega) hn2
  have hbox := setting_tail_cleanupChain_box P sX sZ hsX hsZ Cc hseq hX hZ ε A Vc hV ht hA
  -- the chains at the cell time are slow invariant for `ρ⁻¹ℤ²` and fast periodic
  have hslow : ∀ hh, hh ≤ H → ∀ j, j < Acl → ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      Vc hh j (c⁻¹ * t) (X + ρs⁻¹ • latticeShift n) = Vc hh j (c⁻¹ * t) X :=
    fun hh hhh j hj n X => setting_tail_cleanupChain_slowShift P sX sZ hsX hsZ Cc hseq _ (hGs n)
      (hcs n) hh hhh hZc ε A (c⁻¹ * t) ht (hAp n) (hV hh hhh _ ht) j hj X
  have hfast : ∀ hh, hh ≤ H → ∀ j, j < Acl → ∀ X, IsZ2Periodic (Vc hh j (c⁻¹ * t) X) :=
    fun hh hhh => (hV hh hhh _ ht).periodic
      (tailFluxField_isZ2Periodic_of_presentation (f := fun _ => 0)
        (F := fun n => tailFluxCoefficient par Q Cc N hh n) (hpres hh hhh) ε A ht)
  -- the physical tail flux is `C¹` and periodic, the force continuous
  have hLc := contDiff_tailFluxLabel hXc hZc H N Acl ε c ρs es Vc t hbox
  have hLp := tailFluxLabel_isZ2Periodic H N Acl ε c ρs es Vc t M hM hslow hfast
  have hF := contDiff_tailFluxPhys hχ hψ hψχ hχψ H N Acl ε c ρs es Vc t hLc
  have hFp := tailFluxPhys_isZ2Periodic hψl H N Acl ε c ρs es Vc t hLp
  have hFv : ∀ a₀ : Fin 2, ContDiff ℝ 1 (fun x => tailFluxPhys ψ H N Acl ε c ρs es Vc t x a₀ v) :=
    fun a₀ => contDiff_pi.1 (hF a₀) v
  have hFvp : ∀ a₀ : Fin 2,
      IsZ2Periodic (fun x => tailFluxPhys ψ H N Acl ε c ρs es Vc t x a₀ v) :=
    fun a₀ n x => congrFun (hFp a₀ n x) v
  have hR : Continuous (fun x => tailForcePhys ψ H N Acl ε c ρs es Vc t x v) :=
    (continuous_apply v).comp (continuous_tailForcePhys hψ.continuous H N Acl ε c ρs es Vc t
      fun hh hhh => continuous_cleanupRemainder_sample hAcl hXc c⁻¹ ρs es t (hbox hh hhh))
  -- the pointwise identity, componentwise
  have hpt : ∀ x, (c⁻¹ • restTail Q Cc N H ε A ρs es c t (ψ x)) v =
      ∑ a₀ : Fin 2, fderiv ℝ (fun x' => tailFluxPhys ψ H N Acl ε c ρs es Vc t x' a₀ v) x
          (basisVec a₀)
        + tailForcePhys ψ H N Acl ε c ρs es Vc t x v := by
    intro x
    rw [setting_restTail_phys P sX sZ hsX hsZ Cc hseq sXc sZc Acl hAcl hXc hZc hX hZ ε hρ he A Vc
      hV ht hA hχ hψ hψχ hχψ hd x]
    simp only [Pi.add_apply, Finset.sum_apply]
    congr 1
    exact Finset.sum_congr rfl fun a₀ _ =>
      tail_fderiv_pi_coord ((hF a₀).differentiable one_ne_zero x) (basisVec a₀) v
  have hi1 : Integrable (fun x => inner ℝ (∑ a₀ : Fin 2,
      fderiv ℝ (fun x' => tailFluxPhys ψ H N Acl ε c ρs es Vc t x' a₀ v) x (basisVec a₀))
      (φt x)) (volume.restrict AVenhance.unitCube) :=
    cell_integrable_inner_continuous
      (continuous_finsetSum _ fun a₀ _ => cell_continuous_partial (hFv a₀) a₀) hφt.continuous
  have hi2 : Integrable (fun x => inner ℝ (tailForcePhys ψ H N Acl ε c ρs es Vc t x v) (φt x))
      (volume.restrict AVenhance.unitCube) :=
    cell_integrable_inner_continuous hR hφt.continuous
  simp only [hpt, inner_add_left]
  rw [integral_add hi1 hi2, cell_ibp_div hFv hFvp hφt hφtp]

include P in
/-- **T3 for one pulse.** The tested tail of the rest of the lift of the chart-frame field of a
finite-rank periodic coarse field, in the renewal chart `ocChart … l`, when `e⁻¹ = M ∈ ℕ` and the
slow translations by `ρ⁻¹ℤ²` leave the metric and the source coefficients invariant. -/
theorem setting_pulse_restTail_tested (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (sXc sZc Acl : ℕ) (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc ≤ K + D + 2) (hZ : sZc ≤ max (k + 1) (L + 2)) (ε : ℝ)
    {κ : Type*} [Fintype κ] (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j)) (hφp : ∀ j, IsZ2Periodic (φ j))
    (α q : ℝ) (Λ m : ℕ) {φs : ℝ → Vec 2 → ℝ} (hφs : IsAdmissibleStream φs) (l : ℤ)
    {c ρs es : ℝ} (hρ : 0 < ρs) (he : es ≠ 0) (M : ℕ) (hM : es⁻¹ = M)
    (hGs : ∀ (n : Fin 2 → ℤ) t X i j, Q.G t (X + ρs⁻¹ • latticeShift n) i j = Q.G t X i j)
    (hcs : ∀ (n : Fin 2 → ℤ) v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z,
      γ.coeff α t (X + ρs⁻¹ • latticeShift n) z = γ.coeff α t X z)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → ∀ τ ∈ Set.Icc a b, IsCleanupChain sXc sZc Acl
      (tailScalarField (fun _ => 0) N D ε (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs) τ)
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε
        (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs) τ)
      (fun j => Vc hh j τ))
    {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b)
    (v : ι) (φt : Vec 2 → h v) (hφt : ContDiff ℝ 1 φt) (hφtp : IsZ2Periodic φt) :
    ∫ x in AVenhance.unitCube, inner ℝ
        ((c⁻¹ • restTail Q Cc N H ε (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs) ρs es c t
          (ocChartInv α q Λ m φs hφs l t x)) v) (φt x) =
      -(∫ x in AVenhance.unitCube, ∑ a₀ : Fin 2,
          inner ℝ (tailFluxPhys (ocChartInv α q Λ m φs hφs l t) H N Acl ε c ρs es Vc t x a₀ v)
            (fderiv ℝ φt x (basisVec a₀)))
        + ∫ x in AVenhance.unitCube, inner ℝ
          (tailForcePhys (ocChartInv α q Λ m φs hφs l t) H N Acl ε c ρs es Vc t x v) (φt x) := by
  have hχj := Charts.contDiff_ocChart_joint hφs α q Λ m l
  have hχs : ContDiff ℝ (⊤ : ℕ∞) (ocChart α q Λ m φs hφs l t) :=
    hχj.comp (contDiff_const.prodMk contDiff_id)
  have hψs : ContDiff ℝ (⊤ : ℕ∞) (ocChartInv α q Λ m φs hφs l t) :=
    (Charts.contDiff_ocChartInv_joint hφs α q Λ m l).comp (contDiff_const.prodMk contDiff_id)
  have hψl : ∀ (n : Fin 2 → ℤ) (x : Vec 2), ocChartInv α q Λ m φs hφs l t (x + latticeShift n) =
      ocChartInv α q Λ m φs hφs l t x + latticeShift n := fun n x =>
    CycleReference.streamFlow_lattice_equivariant hφs _ t x n
  have hAp : ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      chartField cf φ (ocChart α q Λ m φs hφs l) c ρs (c⁻¹ * t) (X + ρs⁻¹ • latticeShift n) =
        chartField cf φ (ocChart α q Λ m φs hφs l) c ρs (c⁻¹ * t) X := fun n X =>
    chartField_periodic cf φ hφp (ocChart α q Λ m φs hφs l)
      (fun t' y n' => Charts.ocChart_latticeShift hφs α q Λ m l t' n' y) hρ (c⁻¹ * t) X n
  exact setting_restTail_tested P sX sZ hsX hsZ Cc hseq sXc sZc Acl hAcl hXc hZc hX hZ ε hρ.ne'
    he (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs) Vc hV ht
    (chartField_contDiff cf φ hφ (ocChart α q Λ m φs hφs l) hχj c ρs (c⁻¹ * t)) hχs hψs
    (Charts.ocChartInv_ocChart α q Λ m φs hφs l t) (Charts.ocChart_ocChartInv α q Λ m φs hφs l t)
    (Charts.ocChart_det hφs α q Λ m l t) hψl M hM hGs hcs hAp v φt hφt hφtp

end Setting

end AVRegularity.CycleComparison.Reconstruction
end
