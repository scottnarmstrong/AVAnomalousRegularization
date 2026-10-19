-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.PulseChart
import AVRegularity.CycleComparison.Lift.SettingLiftPolyTimeIntegral
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleComparison.TailConstructed.RawFluxOrderZero
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Lift.SettingLiftSourceBlockCoefficient
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The coefficient form of the label density**. The density
of the label lift (`labelDensity`) is, on the lift window, the explicit coefficient sum
`c⁻¹ ∑_hh (∑_n εⁿ ∑_p Ċ_p(∂^{α_p} f) + Φ_hh[ḟ])`, where `Ċ_p ξ = -𝒫₀(C_p ξ) + (calibrated source)`
is the time density of the lift coefficient `C_p` (`coeffDot`; `setting_lift_coefficient_time_
integral`). In this form every factor is a lift coefficient, a calibrated source, or a jet of the
coarse field, so the density inherits the bounds and the time measurability of these factors; this
is what the space integration of the label identity (`IsPrimOn.integral`) consumes. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

/-- The time density of one lift coefficient applied to a vector: the cell operator plus the
calibrated source. -/
def coeffDot {D : ℕ} (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n m : ℕ)
    (α : DerivativeWord2 m) (lam : ℝ) (u v : ι) (ξ : h u) (s : ℝ) (X z : Vec 2) : h v :=
  -cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u ξ) z +
    calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ s X z

variable {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **The frozen-time density of one degree in coefficient form.** -/
theorem setting_frozen_density_coeff (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (s : ℝ) (hs : s ∈ Icc a b)
    (X z : Vec 2) (v : ι) :
    -cellOperator (Q.G s X) (Q.v s) (fun y => liftApply n (Cc hh n) (fun _ => g) s X y v) z +
        liftCellSource Q Cc (fun _ => g) hh n s X z v =
      ∑ p : LiftActionIndex ι n, coeffDot Q Cc hh n p.1.val p.2.1 lam p.2.2 v
        (orderedDerivative p.2.1 g X p.2.2) s X z := by
  classical
  have hlam : lam ≠ 0 := by
    rw [P.lam_eq]
    exact ne_of_gt (div_pos P.ρ_pos P.E_pos)
  have hc2 : ∀ p : LiftActionIndex ι n, ContDiff ℝ 2 (fun y => Cc hh n p.1.val p.2.1 s X y v
      p.2.2 (orderedDerivative p.2.1 g X p.2.2)) := by
    intro p
    have hm : p.1.val ≤ n := by have := p.1.isLt; omega
    exact (((setting_lift_cross_coefficient_box P sX sZ (by omega) Cc hseq hh hhh
      n hnN p.1.val hm p.2.1 v p.2.2 s hs).1 X).clm_apply contDiff_const).of_le (by norm_num)
  have hcell := cellOperator_finite_synthesis (Q.G s X) (Q.v s)
    (fun _ : LiftActionIndex ι n => (1 : ℝ))
    (fun p y => Cc hh n p.1.val p.2.1 s X y v p.2.2 (orderedDerivative p.2.1 g X p.2.2))
    hc2 z
  simp only [one_smul] at hcell
  have hfield : (fun y => ∑ p : LiftActionIndex ι n, Cc hh n p.1.val p.2.1 s X y v p.2.2
      (orderedDerivative p.2.1 g X p.2.2)) =
      fun y => liftApply n (Cc hh n) (fun _ => g) s X y v := by
    funext y
    exact liftApply_finite_vector_synthesis n (Cc hh n) g s X y v
  have hsrc : (∑ p : LiftActionIndex ι n, calibratedLiftSourceEntry Q Cc hh n p.1.val p.2.1 lam
      p.2.2 v (orderedDerivative p.2.1 g X p.2.2) s X z) =
      liftCellSource Q Cc (fun _ => g) hh n s X z v := by
    rw [← setting_liftSource_blockCoefficient_apply P sX sZ hsX hsZ Cc hseq hh hhh n hn hnN
      g hg s hs X z v, ← liftApply_finite_vector_synthesis]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hm : p.1.val ≤ n := by have := p.1.isLt; omega
    exact setting_calibratedLiftSourceEntry_eq P sX sZ hsX hsZ Cc hseq hh hhh n hn hnN
      p.1.val hm p.2.1 hlam p.2.2 v _ s hs X z
  unfold coeffDot
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← hcell, hfield, hsrc]

include P in
/-- **The label density in coefficient form** on the lift window. -/
theorem setting_labelDensity_coeff (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    (f df : ℝ → Vec 2 → ∀ i, h i) (hf : ∀ s ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (f s))
    (hG : ∀ s i j, Differentiable ℝ (fun X => Q.G s X i j))
    (w : ℝ → Vec 2 → Vec 2) {ρs es c νs c₁ : ℝ}
    (hv : ∀ s z, Q.v s z = c₁ • w s z)
    (h1 : c * νs * es⁻¹ * es⁻¹ = 1) (h2 : ε * Real.sqrt Q.η = c * νs * es⁻¹ * ρs⁻¹)
    (h3 : ε ^ 2 * Q.η = c * νs * ρs⁻¹ * ρs⁻¹) (hc₁ : c₁ = c * es⁻¹)
    (t : ℝ) (ht : c⁻¹ * t ∈ Icc a b) (y : Vec 2) (v : ι) :
    labelDensity Q Cc N H ε f df w ρs es c νs t y v =
      ∑ hh ∈ Finset.range (H + 1), c⁻¹ • ((∑ n ∈ Finset.Icc 1 N, ε ^ n •
          ∑ p : LiftActionIndex ι n, coeffDot Q Cc hh n p.1.val p.2.1 lam p.2.2 v
            (orderedDerivative p.2.1 (f (c⁻¹ * t)) (ρs⁻¹ • y) p.2.2) (c⁻¹ * t)
            (ρs⁻¹ • y) (es⁻¹ • y)) +
        liftPolyField Cc N ε hh df (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y) v) := by
  unfold labelDensity
  refine Finset.sum_congr rfl fun hh hhmem => ?_
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhmem)
  have hΦ := setting_liftPolyField_box P sX sZ Cc hseq hh hhh ε (f (c⁻¹ * t))
    (hf (c⁻¹ * t) ht) (c⁻¹ * t) ht (by omega)
  have hsample := sample_cell_operators hΦ Q.G Q.v (c⁻¹ * t) (hG (c⁻¹ * t)) (w (c⁻¹ * t))
    (η := Q.η) (εc := ε) (ρ := ρs) (e := es) (ℓsq := c) (ν := νs) (c₁ := c₁) (hv (c⁻¹ * t))
    h1 h2 h3 hc₁ y
  simp only [twoScaleSample] at hsample
  rw [← hsample]
  have hid := setting_liftPositiveTimeRhs_identity P sX sZ hsX hsZ Cc hseq hh hhh ε
    (f (c⁻¹ * t)) (hf (c⁻¹ * t) ht) (c⁻¹ * t) ht (ρs⁻¹ • y) (es⁻¹ • y)
  rw [← hid]
  congr 2
  have hcomp : ∀ n ∈ Finset.Icc 1 N,
      (cellOperator (Q.G (c⁻¹ * t) (ρs⁻¹ • y)) (Q.v (c⁻¹ * t))
        (liftApply n (Cc hh n) (fun _ => f (c⁻¹ * t)) (c⁻¹ * t) (ρs⁻¹ • y)) (es⁻¹ • y)) v =
      cellOperator (Q.G (c⁻¹ * t) (ρs⁻¹ • y)) (Q.v (c⁻¹ * t))
        (fun y' => liftApply n (Cc hh n) (fun _ => f (c⁻¹ * t)) (c⁻¹ * t) (ρs⁻¹ • y) y' v)
        (es⁻¹ • y) := by
    intro n hn
    have hbox := setting_lift_cross_field_box P sX sZ (by omega) Cc hseq hh hhh n
      (Finset.mem_Icc.1 hn).2 (f (c⁻¹ * t)) (hf (c⁻¹ * t) ht) (c⁻¹ * t) ht
    exact (cellOperator_postcomposition (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
      (Q.G (c⁻¹ * t) (ρs⁻¹ • y)) (Q.v (c⁻¹ * t))
      (liftApply n (Cc hh n) (fun _ => f (c⁻¹ * t)) (c⁻¹ * t) (ρs⁻¹ • y))
      ((hbox.1 (ρs⁻¹ • y)).of_le (by norm_num)) (es⁻¹ • y)).symm
  simp only [liftPositiveTimeRhs, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [hcomp n hn, setting_frozen_density_coeff P sX sZ hsX hsZ Cc hseq hh n hhh
    (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2 (f (c⁻¹ * t)) (hf (c⁻¹ * t) ht)
    (c⁻¹ * t) ht (ρs⁻¹ • y) (es⁻¹ • y) v]
end

/-! **The label density through the chart modes.** The lift is linear in the coarse field through
its jets (`liftApply_synthesis`, `liftPolyField_synthesis`). For the finite-rank chart-frame field
`ã = ∑_k c_k(t) Ψ_k` (`Ψ_k = φ_k ∘ χ`, `chartMode`) and its material derivative
`∑_k c c_k' Ψ_k + ∑_k c_k Ψ_k'` (`chartModeDot`), the label density is, on the lift window, a part
`D₀` without the rough time factors `c_k'` plus `∑_k c_k'(t) V_k(t, y)`, where `V_k` is the label
lift of the mode `Ψ_k` (`setting_labelDensity_decomp`), and the label lift is `∑_k c_k(t) V_k`
(`labelLift_decomp`). -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

/-- **The lift of one degree is linear in the coarse field through its jets.** -/
theorem liftApply_synthesis {J : Type*} [Fintype J] (n : ℕ) (c : LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (w : J → ℝ) (g : J → Vec 2 → ∀ i, h i)
    (hg : ∀ j, ContDiff ℝ (n : ℕ∞) (g j)) (t : ℝ) (ha : a t = fun Y => ∑ j, w j • g j Y)
    (X z : Vec 2) :
    liftApply n c a t X z = ∑ j, w j • liftApply n c (fun _ => g j) t X z := by
  funext v
  simp only [liftApply, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  rw [ha]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [orderedDerivative_finite_synthesis α w g
    (fun j => (hg j).of_le (by exact_mod_cast hmn)) X]
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]

/-- **The truncated lift is linear in the coarse field through its jets.** -/
theorem liftPolyField_synthesis {J : Type*} [Fintype J] (Cc : ℕ → ℕ → LiftCoeff ι h) (N : ℕ)
    (ε : ℝ) (hh : ℕ) (a : ℝ → Vec 2 → ∀ i, h i) (w : J → ℝ) (g : J → Vec 2 → ∀ i, h i)
    (hg : ∀ j, ContDiff ℝ (N : ℕ∞) (g j)) (t : ℝ) (ha : a t = fun Y => ∑ j, w j • g j Y)
    (X z : Vec 2) :
    liftPolyField Cc N ε hh a t X z =
      ∑ j, w j • liftPolyField Cc N ε hh (fun _ => g j) t X z := by
  simp only [liftPolyField, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnN : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  rw [liftApply_synthesis n (Cc hh n) a w g (fun j => (hg j).of_le (by exact_mod_cast hnN)) t ha
    X z, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

/-- The `k`-th mode of the chart-frame field: `Ψ_k(𝗍, X) = φ_k(χ(c𝗍, ρX))`. -/
def chartMode {κ : Type*} (φ : κ → Vec 2 → ∀ i, h i) (χ : ℝ → Vec 2 → Vec 2) (c ρ : ℝ)
    (k : κ) (s : ℝ) (X : Vec 2) : ∀ i, h i :=
  φ k (χ (c * s) (ρ • X))

/-- The material derivative of the `k`-th mode: `Ψ_k' = c ∇φ_k(χ) · W(χ)`. -/
def chartModeDot {κ : Type*} (φ : κ → Vec 2 → ∀ i, h i) (χ W : ℝ → Vec 2 → Vec 2) (c ρ : ℝ)
    (k : κ) (s : ℝ) (X : Vec 2) : ∀ i, h i :=
  c • fderiv ℝ (φ k) (χ (c * s) (ρ • X)) (W (c * s) (χ (c * s) (ρ • X)))

theorem chartMode_contDiff {κ : Type*} (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (χ : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2)) (c ρ : ℝ) (k : κ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => chartMode φ χ c ρ k p.1 p.2) :=
  (hφ k).comp (hχ.comp (((contDiff_const (c := c)).mul contDiff_fst).prodMk
    ((contDiff_const (c := ρ)).smul contDiff_snd)))

theorem chartModeDot_contDiff {κ : Type*} (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (χ W : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2))
    (hW : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => W p.1 p.2)) (c ρ : ℝ) (k : κ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => chartModeDot φ χ W c ρ k p.1 p.2) := by
  have hpos : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ (c * p.1) (ρ • p.2)) :=
    hχ.comp (((contDiff_const (c := c)).mul contDiff_fst).prodMk
      ((contDiff_const (c := ρ)).smul contDiff_snd))
  have hWj : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => W (c * p.1) (χ (c * p.1) (ρ • p.2))) :=
    hW.comp (((contDiff_const (c := c)).mul contDiff_fst).prodMk hpos)
  exact (contDiff_const (c := c)).smul ((((hφ k).fderiv_right (by simp)).comp hpos).clm_apply hWj)

variable [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- The truncated lift of the chart-frame field is the combination of the lifts of the modes. -/
theorem liftPolyField_chartField {κ : Type*} [Fintype κ] (Cc : ℕ → ℕ → LiftCoeff ι h) (N : ℕ)
    (ε : ℝ) (hh : ℕ) (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (χ : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2)) (c ρ s : ℝ) (X z : Vec 2) :
    liftPolyField Cc N ε hh (chartField cf φ χ c ρ) s X z =
      ∑ k, cf k (c * s) • liftPolyField Cc N ε hh (chartMode φ χ c ρ k) s X z := by
  refine liftPolyField_synthesis Cc N ε hh (chartField cf φ χ c ρ) (fun k => cf k (c * s))
    (fun k => chartMode φ χ c ρ k s) (fun k => ?_) s rfl X z
  exact ((chartMode_contDiff φ hφ χ hχ c ρ k).comp
    (contDiff_const.prodMk contDiff_id)).of_le (by exact_mod_cast le_top)

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- The material derivative of the chart-frame field as a combination of modes. -/
theorem chartFieldDot_eq_sum {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ)
    (φ : κ → Vec 2 → ∀ i, h i) (χ W : ℝ → Vec 2 → Vec 2) (c ρ s : ℝ) :
    chartFieldDot cf dcf φ χ W c ρ s = fun Y => ∑ j : κ ⊕ κ,
      (Sum.elim (fun k => c * dcf k (c * s)) (fun k => cf k (c * s)) j) •
        (Sum.elim (fun k => chartMode φ χ c ρ k s) (fun k => chartModeDot φ χ W c ρ k s) j) Y := by
  funext Y
  simp only [chartFieldDot, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, chartMode,
    chartModeDot]

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- **The label lift through the modes.** -/
theorem labelLift_decomp {κ : Type*} [Fintype κ] (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ)
    (ε : ℝ) (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (χ : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2)) {c : ℝ} (hc : c ≠ 0)
    (ρs es t : ℝ) (y : Vec 2) :
    labelLift Cc N H ε (chartField cf φ χ c ρs) ρs es c t y =
      ∑ k, cf k t • labelLift Cc N H ε (chartMode φ χ c ρs k) ρs es c t y := by
  have hct : c * (c⁻¹ * t) = t := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  simp only [labelLift, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun hh _ => ?_
  rw [liftPolyField_chartField Cc N ε hh cf φ hφ χ hχ c ρs, hct]

/-- The part of the label density without the rough time factors: the frozen coefficient form
of the chart-frame field plus the lifts of the material derivatives of the modes. -/
def labelFrozen {D : ℕ} {κ : Type*} [Fintype κ] (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε lam : ℝ) (cf : κ → ℝ → ℝ)
    (φ : κ → Vec 2 → ∀ i, h i) (χ W : ℝ → Vec 2 → Vec 2) (c ρs es : ℝ) (t : ℝ) (y : Vec 2) :
    ∀ i, h i := fun v =>
  ∑ hh ∈ Finset.range (H + 1), c⁻¹ • ((∑ n ∈ Finset.Icc 1 N, ε ^ n •
      ∑ p : LiftActionIndex ι n, coeffDot Q Cc hh n p.1.val p.2.1 lam p.2.2 v
        (orderedDerivative p.2.1 (chartField cf φ χ c ρs (c⁻¹ * t)) (ρs⁻¹ • y) p.2.2)
        (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y)) +
    ∑ k, cf k t • liftPolyField Cc N ε hh (chartModeDot φ χ W c ρs k) (c⁻¹ * t) (ρs⁻¹ • y)
      (es⁻¹ • y) v)

variable {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **The label density through the modes** on the lift window: the frozen part plus the lifts of
the modes weighted by the time derivatives of the coarse coefficients. -/
theorem setting_labelDensity_decomp (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (χ W : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2))
    (hW : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => W p.1 p.2))
    (hG : ∀ s i j, Differentiable ℝ (fun X => Q.G s X i j))
    (w : ℝ → Vec 2 → Vec 2) {ρs es c νs c₁ : ℝ} (hc : 0 < c)
    (hv : ∀ s z, Q.v s z = c₁ • w s z)
    (h1 : c * νs * es⁻¹ * es⁻¹ = 1) (h2 : ε * Real.sqrt Q.η = c * νs * es⁻¹ * ρs⁻¹)
    (h3 : ε ^ 2 * Q.η = c * νs * ρs⁻¹ * ρs⁻¹) (hc₁ : c₁ = c * es⁻¹)
    (t : ℝ) (ht : c⁻¹ * t ∈ Icc a b) (y : Vec 2) (v : ι) :
    labelDensity Q Cc N H ε (chartField cf φ χ c ρs) (chartFieldDot cf dcf φ χ W c ρs) w ρs es c
        νs t y v =
      labelFrozen Q Cc N H ε lam cf φ χ W c ρs es t y v +
        ∑ k, dcf k t • labelLift Cc N H ε (chartMode φ χ c ρs k) ρs es c t y v := by
  have hct : c * (c⁻¹ * t) = t := by rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [setting_labelDensity_coeff P sX sZ hsX hsZ Cc hseq ε (chartField cf φ χ c ρs)
    (chartFieldDot cf dcf φ χ W c ρs) (fun s _ => chartField_contDiff cf φ hφ χ hχ c ρs s) hG w
    hv h1 h2 h3 hc₁ t ht y v]
  have hsyn : ∀ hh, liftPolyField Cc N ε hh (chartFieldDot cf dcf φ χ W c ρs) (c⁻¹ * t)
      (ρs⁻¹ • y) (es⁻¹ • y) =
      (∑ k, (c * dcf k t) • liftPolyField Cc N ε hh (chartMode φ χ c ρs k) (c⁻¹ * t) (ρs⁻¹ • y)
        (es⁻¹ • y)) +
      ∑ k, cf k t • liftPolyField Cc N ε hh (chartModeDot φ χ W c ρs k) (c⁻¹ * t) (ρs⁻¹ • y)
        (es⁻¹ • y) := by
    intro hh
    rw [liftPolyField_synthesis Cc N ε hh _ _ _ (fun j => ?_) (c⁻¹ * t)
      (chartFieldDot_eq_sum cf dcf φ χ W c ρs (c⁻¹ * t)) (ρs⁻¹ • y) (es⁻¹ • y),
      Fintype.sum_sum_type]
    · simp only [Sum.elim_inl, Sum.elim_inr, hct]
      rfl
    · rcases j with k | k
      · exact ((chartMode_contDiff φ hφ χ hχ c ρs k).comp
          (contDiff_const.prodMk contDiff_id)).of_le (by exact_mod_cast le_top)
      · exact ((chartModeDot_contDiff φ hφ χ W hχ hW c ρs k).comp
          (contDiff_const.prodMk contDiff_id)).of_le (by exact_mod_cast le_top)
  simp only [labelFrozen, labelLift, hsyn, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 1
  rw [add_comm]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun hh _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
end

/-! **Measurability and bounds of the lift coefficients and their time densities** on the lift
window. A field of the cell time and the two cell variables that is continuous in `(X, z)` at
every time of the window and measurable in time after clamping to the window is jointly measurable
(Carathéodory, `measurable_clamp_uncurry`). The lift coefficients (`setting_tailRaw_coefficient_
data`) and the coefficient sources (`setting_liftSequence_source_data`) are of this kind and
bounded, hence so are the coefficient time densities `coeffDot`. -/

section
/-- **Carathéodory on a clamped window.** -/
theorem measurable_clamp_uncurry {E : Type*} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [MeasurableSpace E] [BorelSpace E] {a b : ℝ} (hab : a ≤ b) (G : ℝ → Vec 2 → Vec 2 → E)
    (hc : ∀ s ∈ Icc a b, Continuous (fun p : Vec 2 × Vec 2 => G s p.1 p.2))
    (hm : ∀ X z, Measurable (fun s => G (projIcc a b hab s) X z)) :
    Measurable (fun p : ℝ × (Vec 2 × Vec 2) => G (projIcc a b hab p.1) p.2.1 p.2.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (q : Vec 2 × Vec 2) (s : ℝ) => G (projIcc a b hab s) q.1 q.2)
    (fun s => hc _ (projIcc a b hab s).2) (fun q => hm q.1 q.2)
  exact h.comp measurable_swap

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- The applied lift coefficients are jointly measurable on the clamped window. -/
theorem setting_coeff_measurable (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hnN : n ≤ N)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι) (ξ : h u) :
    Measurable (fun p : ℝ × (Vec 2 × Vec 2) =>
      Cc hh n m α (projIcc a b P.window p.1) p.2.1 p.2.2 v u ξ) := by
  have data := TailConstructed.setting_tailRaw_coefficient_data P sX sZ hsZ Cc hseq 0 0 (by omega) (by omega)
    hh hhh n
  refine measurable_clamp_uncurry P.window (fun s X z => Cc hh n m α s X z v u ξ)
    (fun s hs => ?_) (fun X z => data.applied_measurable m hm α v u ξ X z)
  have hb := setting_lift_cross_coefficient_box P sX sZ hsZ Cc hseq hh hhh n hnN m hm α v u s hs
  exact (ContinuousLinearMap.apply ℝ (h v) ξ).continuous.comp (boxSmooth_continuous hb)

include P in
/-- The lift coefficients are bounded on the window. -/
theorem setting_coeff_bound (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H) (n : ℕ)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc a b, ∀ X z, ‖Cc hh n m α s X z v u‖ ≤ M := by
  have data := TailConstructed.setting_tailRaw_coefficient_data P sX sZ hsZ Cc hseq 0 0 (by omega) (by omega)
    hh hhh n
  refine ⟨(TailConstructed.tailRawCoefficientBudget K k L D H N CG Cw Cj *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) * lam ^ (n - m + 0),
    ?_, fun s hs X z => ?_⟩
  · have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
    exact mul_nonneg (data.nonneg v u) (pow_nonneg hlam _)
  · have hb := data.bound m hm α v u 0 le_rfl 0 le_rfl s hs X z
    simpa only [norm_iteratedFDeriv_zero] using hb

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
include P in
/-- The cell drift is continuous at every time of the window. -/
theorem setting_v_continuous (s : ℝ) (hs : s ∈ Icc a b) : Continuous (Q.v s) := by
  have he : Q.v s = fun z => V s (z par.rev) • basisVec par := funext fun z => P.v_shear s z
  rw [he]
  exact ((P.V_smooth s hs).continuous.comp (continuous_apply par.rev)).smul continuous_const

include P in
/-- **The coefficient time densities are jointly measurable on the clamped window.** -/
theorem setting_coeffDot_measurable (sX sZ : ℕ) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι) (ξ : h u) :
    Measurable (fun p : ℝ × (Vec 2 × Vec 2) =>
      coeffDot Q Cc hh n m α lam u v ξ (projIcc a b P.window p.1) p.2.1 p.2.2) := by
  have data := TailConstructed.setting_tailRaw_coefficient_data P sX sZ (by omega) Cc hseq 0 2
    (by omega) (by omega) hh hhh n
  have src := setting_liftSequence_source_data P sX sZ (by omega) Cc hseq P₀ hh n hreserve hhh
    hn hnN
  have hpm : Measurable (fun s => (projIcc a b P.window s : ℝ)) :=
    (continuous_subtype_val.comp continuous_projIcc).measurable
  refine measurable_clamp_uncurry P.window (fun s X z => coeffDot Q Cc hh n m α lam u v ξ s X z)
    (fun s hs => ?_) (fun X z => ?_)
  · -- continuity in the cell variables
    have hbox : IsBoxSmooth 2 2 (fun X z => Cc hh n m α s X z v u ξ) :=
      (setting_lift_cross_coefficient_box P sX sZ (by omega) Cc hseq hh hhh n hnN m hm α v u s
        hs).map_clm (ContinuousLinearMap.apply ℝ (h v) ξ)
    have h1 : ∀ k, IsBoxSmooth 2 1 (fastPartial k (fun X z => Cc hh n m α s X z v u ξ)) :=
      fun k => hbox.fastPartial k
    have h2 : ∀ i j, IsBoxSmooth 2 0
        (fastPartial i (fastPartial j (fun X z => Cc hh n m α s X z v u ξ))) :=
      fun i j => (h1 j).fastPartial i
    have hv := setting_v_continuous P s hs
    have hsrc := boxSmooth_continuous (calibratedLiftSourceEntry_box src m α u v ξ s hs)
    have hcell : Continuous (fun p : Vec 2 × Vec 2 =>
        cellOperator (Q.G s p.1) (Q.v s) (fun y => Cc hh n m α s p.1 y v u ξ) p.2) := by
      unfold cellOperator
      refine (continuous_finsetSum _ fun k _ => ?_).sub
        (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_)
      · exact ((continuous_apply k).comp (hv.comp continuous_snd)).smul
          (boxSmooth_continuous (h1 k))
      · exact ((P.G_smooth s hs i j).continuous.comp continuous_fst).smul
          (boxSmooth_continuous (h2 i j))
    exact hcell.neg.add hsrc
  · -- measurability in time
    have hv : ∀ k, Measurable fun s => Q.v (projIcc a b P.window s : ℝ) z k := fun k =>
      (measurable_pi_apply k).comp ((P.v_meas z).comp hpm)
    have hG : ∀ i j, Measurable fun s => Q.G (projIcc a b P.window s : ℝ) X i j := fun i j =>
      (P.G_meas X i j).comp hpm
    have hd1 : ∀ k, Measurable fun s => fderiv ℝ
        (fun y => Cc hh n m α (projIcc a b P.window s : ℝ) X y v u ξ) z (basisVec k) := by
      intro k
      have hw := data.applied_fast_word_measurable m hm α v u ξ 1 (by omega) ![k] X z
      simpa [orderedDerivative] using hw
    have hd2 : ∀ i j, Measurable fun s => fderiv ℝ (fun y' => fderiv ℝ
        (fun y => Cc hh n m α (projIcc a b P.window s : ℝ) X y v u ξ) y' (basisVec j))
        z (basisVec i) := by
      intro i j
      have hw := data.applied_fast_word_measurable m hm α v u ξ 2 le_rfl ![j, i] X z
      simpa [orderedDerivative] using hw
    have hsrc : Measurable fun s =>
        calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ (projIcc a b P.window s) X z :=
      measurable_of_all_real_duals _ fun l => calibratedLiftSourceEntry_dual_measurable src m α
        u v ξ l X z
    simp only [coeffDot, cellOperator]
    refine (((Finset.measurable_sum _ fun k _ => (hv k).smul (hd1 k)).sub
      (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
        (hG i j).smul (hd2 i j))).neg).add hsrc

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
include P in
/-- The cell drift is bounded on the window. -/
theorem setting_v_bound (s : ℝ) (hs : s ∈ Icc a b) (z : Vec 2) :
    ‖Q.v s z‖ ≤ max (Cw 0) 0 / Real.sqrt Q.η := by
  have hη : 0 < Real.sqrt Q.η :=
    Real.sqrt_pos.2 (by rw [P.η_eq]; exact div_pos P.ν_pos P.B_pos)
  have h1 : ‖iteratedFDeriv ℝ 0 (fun z' => Real.sqrt Q.η • Q.v s z') z‖ₑ ≤
      ENNReal.ofReal (Cw 0) :=
    le_trans (le_iSup₂_of_le s hs (le_iSup (fun z₁ =>
      ‖iteratedFDeriv ℝ 0 (fun z' => Real.sqrt Q.η • Q.v s z') z₁‖ₑ) z))
      (P.w_jets 0 (Nat.zero_le _))
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [toReal_enorm, ENNReal.toReal_ofReal', norm_iteratedFDeriv_zero, norm_smul,
    Real.norm_of_nonneg hη.le] at h2
  rw [le_div_iff₀ hη, mul_comm]
  exact h2

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
include P in
/-- The metric is bounded on the window. -/
theorem setting_G_bound (s : ℝ) (hs : s ∈ Icc a b) (X : Vec 2) (i j : Fin 2) :
    |Q.G s X i j| ≤ max (CG 0 * lam ^ 0) 0 := by
  have h1 : ‖iteratedFDeriv ℝ 0 (fun X' => Q.G s X') X‖ₑ ≤ ENNReal.ofReal (CG 0 * lam ^ 0) :=
    le_trans (le_iSup₂_of_le s hs (le_iSup (fun X₁ =>
      ‖iteratedFDeriv ℝ 0 (fun X' => Q.G s X') X₁‖ₑ) X)) (P.G_jets 0 (Nat.zero_le _))
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [toReal_enorm, ENNReal.toReal_ofReal', norm_iteratedFDeriv_zero] at h2
  have h3 : ‖Q.G s X i j‖ ≤ ‖Q.G s X‖ :=
    (norm_le_pi_norm (Q.G s X i) j).trans (norm_le_pi_norm (Q.G s X) i)
  rw [Real.norm_eq_abs] at h3
  exact h3.trans h2

include P in
/-- **The coefficient time densities are bounded on the window.** -/
theorem setting_coeffDot_bound (sX sZ : ℕ) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc a b, ∀ X z (ξ : h u),
      ‖coeffDot Q Cc hh n m α lam u v ξ s X z‖ ≤ M * ‖ξ‖ := by
  have data := TailConstructed.setting_tailRaw_coefficient_data P sX sZ (by omega) Cc hseq 0 2
    (by omega) (by omega) hh hhh n
  have src := setting_liftSequence_source_data P sX sZ (by omega) Cc hseq P₀ hh n hreserve hhh
    hn hnN
  set Mc := TailConstructed.tailRawCoefficientBudget K k L D H N CG Cw Cj *
    finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * lam ^ (n - m + 0) with hMc
  set Ms := (∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α lam j| *
      ambientCenteredBudget P₀ (max k (L + 2)) D H (N + D) hh n CG Cw Cj
        (fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m CG Cw Cj)
        ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))) *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * lam ^ (n + 0) with hMs
  set Cv := max (Cw 0) 0 / Real.sqrt Q.η
  set Cg := max (CG 0 * lam ^ 0) 0
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hMc0 : 0 ≤ Mc := mul_nonneg (data.nonneg v u) (pow_nonneg hlam _)
  have hCv : 0 ≤ Cv := div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
  have hCg : 0 ≤ Cg := le_max_right _ _
  have hjet : ∀ s ∈ Icc a b, ∀ X z (q : ℕ), q ≤ 2 →
      ‖iteratedFDeriv ℝ q (fun y => Cc hh n m α s X y v u) z‖ ≤ Mc := by
    intro s hs X z q hq
    have hb := data.bound m hm α v u 0 le_rfl q hq s hs X z
    rwa [norm_iteratedFDeriv_zero] at hb
  have hsrc : ∀ s ∈ Icc a b, ∀ X z (ξ : h u),
      ‖calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ s X z‖ ≤ Ms * ‖ξ‖ := by
    intro s hs X z ξ
    have hb := calibratedLiftSourceEntry_mixed_bound src m α u v ξ 0 0 (Nat.zero_le _)
      (Nat.zero_le _) s hs X z
    rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero] at hb
    calc _ ≤ _ := hb
      _ = Ms * ‖ξ‖ := by rw [hMs]; ring
  have hMs0 : 0 ≤ Ms := by
    have := (hsrc a ⟨le_rfl, P.window⟩ 0 0 0).trans_eq (by simp : Ms * ‖(0 : h u)‖ = 0)
    rw [hMs]
    refine mul_nonneg (mul_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _)
      (src.constant_nonneg _)) (src.matrix_nonneg v u)) (pow_nonneg hlam _)
  refine ⟨2 * Cv * Mc + 4 * Cg * Mc + Ms, by positivity, fun s hs X z ξ => ?_⟩
  have hc2 : ContDiff ℝ 2 (fun y => Cc hh n m α s X y v u) :=
    ((setting_lift_cross_coefficient_box P sX sZ (by omega) Cc hseq hh hhh n hnN m hm α v u s
      hs).1 X)
  have hψ : ContDiff ℝ 2 (fun y => Cc hh n m α s X y v u ξ) := hc2.clm_apply contDiff_const
  have hd1 : ∀ k, ‖fderiv ℝ (fun y => Cc hh n m α s X y v u ξ) z (basisVec k)‖ ≤ Mc * ‖ξ‖ := by
    intro k
    have h1 := AVRegularity.norm_orderedDerivative_le (hψ.of_le (by norm_num)) ![k] z
    have h2 := norm_iteratedFDeriv_clm_apply_const (c := ξ) (n := 1)
      (hc2.contDiffAt (x := z)) (by norm_num)
    have he : orderedDerivative (![k] : DerivativeWord2 1)
        (fun y => Cc hh n m α s X y v u ξ) z =
        fderiv ℝ (fun y => Cc hh n m α s X y v u ξ) z (basisVec k) := by
      simp [orderedDerivative]
    rw [he] at h1
    calc _ ≤ _ := h1
      _ ≤ ‖ξ‖ * ‖iteratedFDeriv ℝ 1 (fun y => Cc hh n m α s X y v u) z‖ := h2
      _ ≤ ‖ξ‖ * Mc := mul_le_mul_of_nonneg_left (hjet s hs X z 1 (by norm_num)) (norm_nonneg _)
      _ = Mc * ‖ξ‖ := mul_comm _ _
  have hd2 : ∀ i j, ‖fderiv ℝ (fun y' => fderiv ℝ (fun y => Cc hh n m α s X y v u ξ) y'
      (basisVec j)) z (basisVec i)‖ ≤ Mc * ‖ξ‖ := by
    intro i j
    have h1 := AVRegularity.norm_orderedDerivative_le hψ ![j, i] z
    have h2 := norm_iteratedFDeriv_clm_apply_const (c := ξ) (n := 2)
      (hc2.contDiffAt (x := z)) le_rfl
    have he : orderedDerivative (![j, i] : DerivativeWord2 2)
        (fun y => Cc hh n m α s X y v u ξ) z =
        fderiv ℝ (fun y' => fderiv ℝ (fun y => Cc hh n m α s X y v u ξ) y' (basisVec j)) z
          (basisVec i) := by
      simp [orderedDerivative]
    rw [he] at h1
    calc _ ≤ _ := h1
      _ ≤ ‖ξ‖ * ‖iteratedFDeriv ℝ 2 (fun y => Cc hh n m α s X y v u) z‖ := h2
      _ ≤ ‖ξ‖ * Mc := mul_le_mul_of_nonneg_left (hjet s hs X z 2 le_rfl) (norm_nonneg _)
      _ = Mc * ‖ξ‖ := mul_comm _ _
  have hvk : ∀ k, |Q.v s z k| ≤ Cv := fun k =>
    (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (Q.v s z) k : |Q.v s z k| ≤ _).trans
      (setting_v_bound P s hs z)
  have hcell : ‖cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u ξ) z‖ ≤
      (2 * Cv * Mc + 4 * Cg * Mc) * ‖ξ‖ := by
    unfold cellOperator
    refine (norm_sub_le _ _).trans ?_
    have hA : ‖∑ k : Fin 2, Q.v s z k • fderiv ℝ (fun y => Cc hh n m α s X y v u ξ) z
        (basisVec k)‖ ≤ 2 * (Cv * (Mc * ‖ξ‖)) := by
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ _k : Fin 2, Cv * (Mc * ‖ξ‖) := Finset.sum_le_sum fun k _ => by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul (hvk k) (hd1 k) (norm_nonneg _) hCv
        _ = 2 * (Cv * (Mc * ‖ξ‖)) := by simp
    have hB : ‖∑ i : Fin 2, ∑ j : Fin 2, Q.G s X i j • fderiv ℝ (fun y' => fderiv ℝ
        (fun y => Cc hh n m α s X y v u ξ) y' (basisVec j)) z (basisVec i)‖ ≤
        4 * (Cg * (Mc * ‖ξ‖)) := by
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, Cg * (Mc * ‖ξ‖) := Finset.sum_le_sum fun i _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
              rw [norm_smul, Real.norm_eq_abs]
              exact mul_le_mul (setting_G_bound P s hs X i j) (hd2 i j) (norm_nonneg _) hCg)
        _ = 4 * (Cg * (Mc * ‖ξ‖)) := by simp; ring
    calc _ ≤ 2 * (Cv * (Mc * ‖ξ‖)) + 4 * (Cg * (Mc * ‖ξ‖)) := add_le_add hA hB
      _ = (2 * Cv * Mc + 4 * Cg * Mc) * ‖ξ‖ := by ring
  unfold coeffDot
  calc _ ≤ ‖cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u ξ) z‖ +
        ‖calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ s X z‖ := by
        rw [← norm_neg (cellOperator _ _ _ z)]
        exact norm_add_le _ _
    _ ≤ (2 * Cv * Mc + 4 * Cg * Mc) * ‖ξ‖ + Ms * ‖ξ‖ := add_le_add hcell (hsrc s hs X z ξ)
    _ = (2 * Cv * Mc + 4 * Cg * Mc + Ms) * ‖ξ‖ := by ring
end

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Space-time integrability of decomposed densities.** A density on the window `[A, B]` that is
a bounded field, measurable after clamping time to the window, plus finitely many such fields with
time-integrable scalar weights, paired with a bounded measurable test, is integrable for the product
of the window and the unit cell (`integrable_inner_decomp`). This is the form in which the label
densities of the lift are integrable: the coefficient factors are bounded and measurable after
clamping, and the only rough time factors are the derivatives of the coarse coefficients. -/

/-- The unit cell has finite measure. -/
theorem isFiniteMeasure_restrict_unitCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  have h : volume AVenhance.unitCube = 1 := by
    unfold AVenhance.unitCube
    rw [volume_pi, Measure.pi_pi]
    simp [Real.volume_Ioo]
  rw [h]
  exact ENNReal.one_lt_top

/-- **Integrability of a decomposed density paired with a bounded test.** -/
theorem integrable_inner_decomp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {A B : ℝ} (hAB : A ≤ B) {κ : Type*} [Fintype κ]
    (D D₀ : ℝ → Vec 2 → E) (Dk : κ → ℝ → Vec 2 → E) (g : κ → ℝ → ℝ) (Φ : ℝ → Vec 2 → E)
    (hdec : ∀ t ∈ Icc A B, ∀ y, D t y = D₀ t y + ∑ k, g k t • Dk k t y)
    (hm0 : Measurable (fun p : ℝ × Vec 2 => D₀ (projIcc A B hAB p.1) p.2))
    (hb0 : ∃ M, ∀ t ∈ Icc A B, ∀ y, ‖D₀ t y‖ ≤ M)
    (hmk : ∀ k, Measurable (fun p : ℝ × Vec 2 => Dk k (projIcc A B hAB p.1) p.2))
    (hbk : ∀ k, ∃ M, ∀ t ∈ Icc A B, ∀ y, ‖Dk k t y‖ ≤ M)
    (hg : ∀ k, IntervalIntegrable (g k) volume A B)
    (hΦm : Measurable (fun p : ℝ × Vec 2 => Φ p.1 p.2)) (hΦb : ∃ M, ∀ t y, ‖Φ t y‖ ≤ M) :
    Integrable (Function.uncurry fun t y => inner ℝ (D t y) (Φ t y))
      ((volume.restrict (Ioc A B)).prod (volume.restrict AVenhance.unitCube)) := by
  have := isFiniteMeasure_restrict_unitCube
  set μ := (volume.restrict (Ioc A B)).prod (volume.restrict AVenhance.unitCube) with hμ
  have hcl : ∀ t, (projIcc A B hAB t : ℝ) ∈ Icc A B := fun t => (projIcc A B hAB t).2
  obtain ⟨M0, hM0⟩ := hb0
  obtain ⟨MΦ, hMΦ⟩ := hΦb
  have hMΦ0 : 0 ≤ MΦ := (norm_nonneg _).trans (hMΦ 0 0)
  let F₀ : ℝ × Vec 2 → ℝ := fun p => inner ℝ (D₀ (projIcc A B hAB p.1) p.2) (Φ p.1 p.2)
  let Fk : κ → ℝ × Vec 2 → ℝ := fun k p =>
    g k p.1 * inner ℝ (Dk k (projIcc A B hAB p.1) p.2) (Φ p.1 p.2)
  have hF₀ : Integrable F₀ μ := by
    refine Integrable.mono' (integrable_const (M0 * MΦ)) (hm0.inner hΦm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (hM0 _ (hcl p.1) p.2) (hMΦ p.1 p.2) (norm_nonneg _)
      ((norm_nonneg _).trans (hM0 _ (hcl p.1) p.2))
  have hFk : ∀ k, Integrable (Fk k) μ := by
    intro k
    obtain ⟨Mk, hMk⟩ := hbk k
    have hgi : Integrable (g k) (volume.restrict (Ioc A B)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hAB).1 (hg k)
    have hint := (hgi.comp_fst (volume.restrict AVenhance.unitCube)).bdd_mul
      (c := Mk * MΦ) ((hmk k).inner hΦm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans ?_
        exact mul_le_mul (hMk _ (hcl p.1) p.2) (hMΦ p.1 p.2) (norm_nonneg _)
          ((norm_nonneg _).trans (hMk _ (hcl p.1) p.2)))
    refine hint.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Fk]
    ring
  have hsum : Integrable (fun p => F₀ p + ∑ k, Fk k p) μ :=
    hF₀.add (integrable_finsetSum _ fun k _ => hFk k)
  refine hsum.congr ?_
  have hae : ∀ᵐ p ∂μ, p.1 ∈ Ioc A B :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hae] with p hp
  have hpI : p.1 ∈ Icc A B := Ioc_subset_Icc_self hp
  have hproj : (projIcc A B hAB p.1 : ℝ) = p.1 := by rw [projIcc_of_mem hAB hpI]
  simp only [F₀, Fk, Function.uncurry, hproj]
  rw [hdec p.1 hpI p.2, inner_add_left, sum_inner]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_left]

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Measurability and bounds of the label lifts of the chart modes.** The jets of a jointly smooth
field of the cell time and the slow variable are jointly continuous, and bounded on the window when
the field is periodic in the slow variable (`continuous_jet_joint`, `jet_bound_periodic`). The label
lift of a chart mode is a finite sum of lift coefficients applied to such jets, so after clamping time
to the lift window it is jointly measurable and bounded (`setting_labelLift_measurable`,
`setting_labelLift_bound`). -/

section
section Generic

/-- Clamping commutes with a positive time scale. -/
theorem inv_mul_projIcc_scale {a b c : ℝ} (hc : 0 < c) (hab : a ≤ b) (hcab : c * a ≤ c * b)
    (t : ℝ) : c⁻¹ * (projIcc (c * a) (c * b) hcab t : ℝ) = projIcc a b hab (c⁻¹ * t) := by
  simp only [coe_projIcc]
  rw [mul_max_of_nonneg _ _ (inv_nonneg.2 hc.le), mul_min_of_nonneg _ _ (inv_nonneg.2 hc.le),
    ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, one_mul]

/-- A linear map is determined by its values on an orthonormal basis. -/
theorem linear_expand {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F] (L : E → F) (hL : IsLinearMap ℝ L)
    (ξ : E) :
    L ξ = ∑ i, inner ℝ ((stdOrthonormalBasis ℝ E) i) ξ • L ((stdOrthonormalBasis ℝ E) i) := by
  conv_lhs => rw [← (stdOrthonormalBasis ℝ E).sum_repr' ξ]
  change IsLinearMap.mk' L hL _ = _
  rw [map_sum]
  simp only [map_smul, IsLinearMap.mk'_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The jets of a jointly smooth field are jointly continuous. -/
theorem continuous_jet_joint (F : ℝ × Vec 2 → E) (hF : ContDiff ℝ (⊤ : ℕ∞) F) {m : ℕ}
    (α : DerivativeWord2 m) :
    Continuous (fun p : ℝ × Vec 2 => orderedDerivative α (fun Y => F (p.1, Y)) p.2) := by
  have hc := (Weighted.joint_partialIteratedFDeriv_right_contDiff 0 m F
    (hF.of_le (by exact_mod_cast le_top))).continuous
  have he : (fun p : ℝ × Vec 2 => orderedDerivative α (fun Y => F (p.1, Y)) p.2) =
      fun p => iteratedFDeriv ℝ m (fun x => F (p.1, x)) p.2
        (fun k => basisVec (α (Fin.rev k))) := by
    funext p
    have hY : ContDiff ℝ (m : ℕ∞) (fun Y => F (p.1, Y)) :=
      (hF.comp (contDiff_const.prodMk contDiff_id)).of_le (by exact_mod_cast le_top)
    rw [Sampling.orderedDerivative_eq_iteratedFDeriv α _ hY]
  rw [he]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Vec 2) E
    (fun k => basisVec (α (Fin.rev k)))).continuous.comp hc

/-- The jets of a field periodic in the slow variable are periodic. -/
theorem orderedDerivative_periodic {g : Vec 2 → E} {m : ℕ} (hg : ContDiff ℝ (m : ℕ∞) g)
    (T : Vec 2) (hT : ∀ Y, g (Y + T) = g Y) (α : DerivativeWord2 m) (X : Vec 2) :
    orderedDerivative α g (X + T) = orderedDerivative α g X := by
  rw [Sampling.orderedDerivative_eq_iteratedFDeriv α g hg]
  have hfun : (fun Y => g (Y + T)) = g := funext hT
  simp only
  rw [← iteratedFDeriv_comp_add_right, hfun]

/-- The jets of a jointly smooth field periodic in the slow variable are bounded on the window. -/
theorem jet_bound_periodic (F : ℝ × Vec 2 → E) (hF : ContDiff ℝ (⊤ : ℕ∞) F) {ρ : ℝ}
    (hρ : 0 < ρ) (hper : ∀ s X (n : Fin 2 → ℤ), F (s, X + ρ⁻¹ • latticeShift n) = F (s, X))
    {m : ℕ} (α : DerivativeWord2 m) (a b : ℝ) :
    ∃ C, ∀ s ∈ Icc a b, ∀ X, ‖orderedDerivative α (fun Y => F (s, Y)) X‖ ≤ C := by
  refine exists_bound_of_periodic hρ (fun p => ‖orderedDerivative α (fun Y => F (p.1, Y)) p.2‖)
    (continuous_jet_joint F hF α).norm (fun s X n => ?_)
  have hY : ContDiff ℝ (m : ℕ∞) (fun Y => F (s, Y)) :=
    (hF.comp (contDiff_const.prodMk contDiff_id)).of_le (by exact_mod_cast le_top)
  simp only
  rw [orderedDerivative_periodic hY (ρ⁻¹ • latticeShift n) (fun Y => hper s Y n) α X]

end Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

omit [Fintype ι] [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
/-- The chart modes are periodic in the slow variable. -/
theorem chartMode_periodic {κ : Type*} (φ : κ → Vec 2 → ∀ i, h i)
    (hφp : ∀ k, IsZ2Periodic (φ k)) (χ : ℝ → Vec 2 → Vec 2)
    (hχl : ∀ t y (n : Fin 2 → ℤ), χ t (y + latticeShift n) = χ t y + latticeShift n)
    {c ρ : ℝ} (hρ : 0 < ρ) (k : κ) (s : ℝ) (X : Vec 2) (n : Fin 2 → ℤ) :
    chartMode φ χ c ρ k s (X + ρ⁻¹ • latticeShift n) = chartMode φ χ c ρ k s X := by
  have hρX : ρ • (X + ρ⁻¹ • latticeShift n) = ρ • X + latticeShift n := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
  simp only [chartMode, hρX, hχl, hφp k n]

variable {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
/-- The label lift as a finite coefficient sum. -/
theorem labelLift_coeff_sum (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε : ℝ)
    (g : ℝ → Vec 2 → ∀ i, h i) (ρs es c t : ℝ) (y : Vec 2) (v : ι) :
    labelLift Cc N H ε g ρs es c t y v =
      ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1), ε ^ n •
        ∑ q : LiftActionIndex ι n, Cc hh n q.1.val q.2.1 (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y) v
          q.2.2 (orderedDerivative q.2.1 (g (c⁻¹ * t)) (ρs⁻¹ • y) q.2.2) := by
  simp only [labelLift, liftPolyField, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun hh _ => Finset.sum_congr rfl fun n _ => ?_
  rw [liftApply_finite_vector_synthesis n (Cc hh n) (g (c⁻¹ * t))]
  rfl

include P in
/-- **The label lift of a smooth field, clamped to the window, is jointly measurable.** -/
theorem setting_labelLift_measurable (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    (g : ℝ → Vec 2 → ∀ i, h i) (hg : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => g p.1 p.2))
    (ρs es : ℝ) {c : ℝ} (hc : 0 < c) (hcab : c * a ≤ c * b) (v : ι) :
    Measurable (fun p : ℝ × Vec 2 =>
      labelLift Cc N H ε g ρs es c (projIcc (c * a) (c * b) hcab p.1) p.2 v) := by
  classical
  simp only [labelLift_coeff_sum, inv_mul_projIcc_scale hc P.window hcab]
  refine Finset.measurable_sum _ fun hh hhmem => Finset.measurable_sum _ fun n hn => ?_
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhmem)
  have hnN : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  refine (Finset.measurable_sum _ fun q _ => ?_).const_smul _
  have hm : q.1.val ≤ n := Nat.lt_succ_iff.1 q.1.isLt
  have hmap : Measurable (fun p : ℝ × Vec 2 => (c⁻¹ * p.1, (ρs⁻¹ • p.2, es⁻¹ • p.2))) := by
    fun_prop
  have hJ : Continuous (fun p : ℝ × Vec 2 => orderedDerivative q.2.1
      (g (projIcc a b P.window (c⁻¹ * p.1))) (ρs⁻¹ • p.2) q.2.2) := by
    have hc1 := continuous_jet_joint (fun p : ℝ × Vec 2 => g p.1 p.2) hg q.2.1
    have hpr : Continuous (fun p : ℝ × Vec 2 => (projIcc a b P.window (c⁻¹ * p.1) : ℝ)) :=
      continuous_subtype_val.comp (continuous_projIcc.comp
        ((continuous_const (y := c⁻¹)).mul continuous_fst))
    have hpos : Continuous (fun p : ℝ × Vec 2 =>
        ((projIcc a b P.window (c⁻¹ * p.1) : ℝ), ρs⁻¹ • p.2)) :=
      hpr.prodMk (by fun_prop)
    exact (continuous_apply q.2.2).comp (hc1.comp hpos)
  have hexp : ∀ p : ℝ × Vec 2, Cc hh n q.1.val q.2.1 (projIcc a b P.window (c⁻¹ * p.1))
      (ρs⁻¹ • p.2) (es⁻¹ • p.2) v q.2.2 (orderedDerivative q.2.1
        (g (projIcc a b P.window (c⁻¹ * p.1))) (ρs⁻¹ • p.2) q.2.2) =
      ∑ i, inner ℝ ((stdOrthonormalBasis ℝ (h q.2.2)) i) (orderedDerivative q.2.1
        (g (projIcc a b P.window (c⁻¹ * p.1))) (ρs⁻¹ • p.2) q.2.2) •
        Cc hh n q.1.val q.2.1 (projIcc a b P.window (c⁻¹ * p.1)) (ρs⁻¹ • p.2) (es⁻¹ • p.2) v
          q.2.2 ((stdOrthonormalBasis ℝ (h q.2.2)) i) := fun p =>
    linear_expand _ (Cc hh n q.1.val q.2.1 _ _ _ v q.2.2).toLinearMap.isLinear _
  simp only [hexp]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (continuous_const.inner hJ).measurable.smul
    ((setting_coeff_measurable P sX sZ hsZ Cc hseq hh hhh n hnN q.1.val hm q.2.1 v q.2.2
      _).comp hmap)

include P in
/-- **The label lift of a smooth field periodic in the slow variable is bounded on the window.** -/
theorem setting_labelLift_bound (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    (g : ℝ → Vec 2 → ∀ i, h i) (hg : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => g p.1 p.2))
    {ρs : ℝ} (hρ : 0 < ρs)
    (hper : ∀ s X (n : Fin 2 → ℤ), g s (X + ρs⁻¹ • latticeShift n) = g s X) (es c : ℝ) (v : ι) :
    ∃ M : ℝ, ∀ t, c⁻¹ * t ∈ Icc a b → ∀ y, ‖labelLift Cc N H ε g ρs es c t y v‖ ≤ M := by
  classical
  have hMq : ∀ hh n (q : LiftActionIndex ι n), ∃ M : ℝ, 0 ≤ M ∧
      (hh ≤ H → ∀ s ∈ Icc a b, ∀ X z, ‖Cc hh n q.1.val q.2.1 s X z v q.2.2‖ ≤ M) := by
    intro hh n q
    by_cases hhh : hh ≤ H
    · obtain ⟨M, hM0, hM⟩ := setting_coeff_bound P sX sZ hsZ Cc hseq hh hhh n q.1.val
        (Nat.lt_succ_iff.1 q.1.isLt) q.2.1 v q.2.2
      exact ⟨M, hM0, fun _ => hM⟩
    · exact ⟨0, le_rfl, fun h => absurd h hhh⟩
  choose Mc hMc0 hMc using hMq
  have hJq : ∀ n (q : LiftActionIndex ι n), ∃ C : ℝ, ∀ s ∈ Icc a b, ∀ X,
      ‖orderedDerivative q.2.1 (fun Y => (fun p : ℝ × Vec 2 => g p.1 p.2) (s, Y)) X‖ ≤ C :=
    fun n q => jet_bound_periodic (fun p : ℝ × Vec 2 => g p.1 p.2) hg hρ
      (fun s X m => hper s X m) q.2.1 a b
  choose Cj hCj using hJq
  refine ⟨∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1), |ε| ^ n *
    ∑ q : LiftActionIndex ι n, Mc hh n q * max (Cj n q) 0, fun t ht y => ?_⟩
  rw [labelLift_coeff_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun hh hhmem => ?_)
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhmem)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_smul, norm_pow, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_))
    (pow_nonneg (abs_nonneg _) _)
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  refine mul_le_mul (hMc hh n q hhh _ ht _ _) ?_ (norm_nonneg _) (hMc0 hh n q)
  exact (norm_le_pi_norm _ _).trans ((hCj n q _ ht _).trans (le_max_left _ _))
end

/-! **Measurability and bounds of the frozen part of the label density.** The frozen part
(`labelFrozen`) is the coefficient form `∑_hh c⁻¹ ∑_n εⁿ ∑_p Ċ_p(∂^{α_p} ã)` of the chart-frame field
(`frozenCoeff`) plus `c⁻¹ ∑_k c_k(t) V_k'`, the label lifts of the material derivatives of the modes.
The coefficient densities `Ċ_p` are linear on the window (`setting_coeffDot_linear`), measurable
and bounded (`setting_coeffDot_measurable`, `setting_coeffDot_bound`), and the jets of `ã` are
jointly continuous, so after clamping time to the window the frozen part is jointly measurable and
bounded. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

/-- The coefficient form of the frozen density of the chart-frame field. -/
def frozenCoeff {D : ℕ} {κ : Type*} [Fintype κ] (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε lam : ℝ) (cf : κ → ℝ → ℝ)
    (φ : κ → Vec 2 → ∀ i, h i) (χ : ℝ → Vec 2 → Vec 2) (c ρs es : ℝ) (t : ℝ) (y : Vec 2) :
    ∀ i, h i := fun v =>
  ∑ hh ∈ Finset.range (H + 1), c⁻¹ • ∑ n ∈ Finset.Icc 1 N, ε ^ n •
    ∑ p : LiftActionIndex ι n, coeffDot Q Cc hh n p.1.val p.2.1 lam p.2.2 v
      (orderedDerivative p.2.1 (chartField cf φ χ c ρs (c⁻¹ * t)) (ρs⁻¹ • y) p.2.2)
      (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y)

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- The frozen part is the coefficient form plus the lifts of the material derivatives. -/
theorem labelFrozen_eq {D : ℕ} {κ : Type*} [Fintype κ] (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε lam : ℝ) (cf : κ → ℝ → ℝ)
    (φ : κ → Vec 2 → ∀ i, h i) (χ W : ℝ → Vec 2 → Vec 2) (c ρs es : ℝ) (t : ℝ) (y : Vec 2)
    (v : ι) :
    labelFrozen Q Cc N H ε lam cf φ χ W c ρs es t y v =
      frozenCoeff Q Cc N H ε lam cf φ χ c ρs es t y v +
        c⁻¹ • ∑ k, cf k t • labelLift Cc N H ε (chartModeDot φ χ W c ρs k) ρs es c t y v := by
  simp only [labelFrozen, frozenCoeff, labelLift, Finset.sum_apply, smul_add,
    Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]

variable {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- The coefficient time densities are linear on the window. -/
theorem setting_coeffDot_linear (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N) (m : ℕ) (hm : m ≤ n)
    (α : DerivativeWord2 m) (u v : ι) (s : ℝ) (hs : s ∈ Icc a b) (X z : Vec 2) :
    IsLinearMap ℝ (fun ξ : h u => coeffDot Q Cc hh n m α lam u v ξ s X z) := by
  have hlam : lam ≠ 0 := by
    rw [P.lam_eq]
    exact ne_of_gt (div_pos P.ρ_pos P.E_pos)
  have he : (fun ξ : h u => coeffDot Q Cc hh n m α lam u v ξ s X z) = fun ξ =>
      -cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u ξ) z +
        leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n s w)
          m α s X z v u ξ := by
    funext ξ
    simp only [coeffDot]
    rw [setting_calibratedLiftSourceEntry_eq P sX sZ hsX hsZ Cc hseq hh hhh n hn hnN m hm α hlam
      u v ξ s hs X z]
  rw [he]
  exact coefficient_density_linear P sX sZ hsZ Cc hseq hh n hhh hnN m hm α u v X z s hs

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- The jets of the chart-frame field through the modes. -/
theorem orderedDerivative_chartField {κ : Type*} [Fintype κ] (cf : κ → ℝ → ℝ)
    (φ : κ → Vec 2 → ∀ i, h i) (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (χ : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2)) (c ρ s : ℝ) {m : ℕ}
    (α : DerivativeWord2 m) (X : Vec 2) :
    orderedDerivative α (chartField cf φ χ c ρ s) X =
      ∑ k, cf k (c * s) • orderedDerivative α (chartMode φ χ c ρ k s) X := by
  have he : chartField cf φ χ c ρ s = fun Y => ∑ k, cf k (c * s) • chartMode φ χ c ρ k s Y := rfl
  rw [he]
  exact orderedDerivative_finite_synthesis α (fun k => cf k (c * s))
    (fun k => chartMode φ χ c ρ k s) (fun k => ((chartMode_contDiff φ hφ χ hχ c ρ k).comp
      (contDiff_const.prodMk contDiff_id)).of_le (by exact_mod_cast le_top)) X

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- The clamped jets of the chart-frame field are jointly continuous. -/
theorem continuous_chartField_jet {κ : Type*} [Fintype κ] (cf : κ → ℝ → ℝ)
    (φ : κ → Vec 2 → ∀ i, h i) (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (χ : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2)) {a b c ρs : ℝ} (hab : a ≤ b)
    (hc : 0 < c) {A₀ B₀ : ℝ} (hA : A₀ ≤ c * a) (hB : c * b ≤ B₀)
    (hcf : ∀ k, ContinuousOn (cf k) (Icc A₀ B₀)) {m : ℕ} (α : DerivativeWord2 m) (u : ι) :
    Continuous (fun p : ℝ × Vec 2 => orderedDerivative α
      (chartField cf φ χ c ρs (projIcc a b hab (c⁻¹ * p.1))) (ρs⁻¹ • p.2) u) := by
  simp only [orderedDerivative_chartField cf φ hφ χ hχ c ρs, Finset.sum_apply, Pi.smul_apply]
  have hpr : Continuous (fun p : ℝ × Vec 2 => (projIcc a b hab (c⁻¹ * p.1) : ℝ)) :=
    continuous_subtype_val.comp (continuous_projIcc.comp
      ((continuous_const (y := c⁻¹)).mul continuous_fst))
  refine continuous_finsetSum _ fun k _ => ?_
  have hcfc : Continuous (fun p : ℝ × Vec 2 => cf k (c * (projIcc a b hab (c⁻¹ * p.1) : ℝ))) := by
    refine (hcf k).comp_continuous ((continuous_const (y := c)).mul hpr) fun p => ?_
    have hs := (projIcc a b hab (c⁻¹ * p.1)).2
    exact ⟨hA.trans (mul_le_mul_of_nonneg_left hs.1 hc.le),
      (mul_le_mul_of_nonneg_left hs.2 hc.le).trans hB⟩
  have hjet := continuous_jet_joint (fun p : ℝ × Vec 2 => chartMode φ χ c ρs k p.1 p.2)
    (chartMode_contDiff φ hφ χ hχ c ρs k) α
  have hpos : Continuous (fun p : ℝ × Vec 2 =>
      ((projIcc a b hab (c⁻¹ * p.1) : ℝ), ρs⁻¹ • p.2)) := hpr.prodMk (by fun_prop)
  exact hcfc.smul ((continuous_apply u).comp (hjet.comp hpos))

include P in
/-- A coefficient time density applied to a continuous field, clamped to the window, is jointly
measurable. -/
theorem setting_coeffDot_comp_measurable (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N) (m : ℕ) (hm : m ≤ n)
    (α : DerivativeWord2 m) (u v : ι) (c ρs es : ℝ) (J : ℝ × Vec 2 → h u) (hJ : Continuous J) :
    Measurable (fun p : ℝ × Vec 2 => coeffDot Q Cc hh n m α lam u v (J p)
      (projIcc a b P.window (c⁻¹ * p.1)) (ρs⁻¹ • p.2) (es⁻¹ • p.2)) := by
  have hr : 0 + (N + D) ≤ qs := by
    have := setting_ambient_output_supported P
    omega
  have hmap : Measurable (fun p : ℝ × Vec 2 => (c⁻¹ * p.1, (ρs⁻¹ • p.2, es⁻¹ • p.2))) := by
    fun_prop
  have hlin : (fun p : ℝ × Vec 2 => coeffDot Q Cc hh n m α lam u v (J p)
      (projIcc a b P.window (c⁻¹ * p.1)) (ρs⁻¹ • p.2) (es⁻¹ • p.2)) = fun p =>
      ∑ i, inner ℝ ((stdOrthonormalBasis ℝ (h u)) i) (J p) •
        coeffDot Q Cc hh n m α lam u v ((stdOrthonormalBasis ℝ (h u)) i)
          (projIcc a b P.window (c⁻¹ * p.1)) (ρs⁻¹ • p.2) (es⁻¹ • p.2) := by
    funext p
    exact linear_expand _ (setting_coeffDot_linear P sX sZ hsX hsZ Cc hseq hh n hhh hn hnN m hm
      α u v _ (projIcc a b P.window (c⁻¹ * p.1)).2 _ _) _
  rw [hlin]
  refine Finset.measurable_sum _ fun i _ => ?_
  have h1 := (setting_coeffDot_measurable P sX sZ hsZ Cc hseq 0 hr hh hhh n hn hnN m hm α u v
    ((stdOrthonormalBasis ℝ (h u)) i)).comp hmap
  simp only [Function.comp_def] at h1
  exact (continuous_const.inner hJ).measurable.smul h1

include P in
/-- **The coefficient form of the frozen density, clamped to the window, is jointly
measurable.** -/
theorem setting_frozenCoeff_measurable (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    {κ : Type*} [Fintype κ] (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (χ : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2)) {c ρs es : ℝ} (hc : 0 < c)
    (hcab : c * a ≤ c * b) {A₀ B₀ : ℝ} (hA : A₀ ≤ c * a) (hB : c * b ≤ B₀)
    (hcf : ∀ k, ContinuousOn (cf k) (Icc A₀ B₀)) (v : ι) :
    Measurable (fun p : ℝ × Vec 2 => frozenCoeff Q Cc N H ε lam cf φ χ c ρs es
      (projIcc (c * a) (c * b) hcab p.1) p.2 v) := by
  classical
  have he : (fun p : ℝ × Vec 2 => frozenCoeff Q Cc N H ε lam cf φ χ c ρs es
      (projIcc (c * a) (c * b) hcab p.1) p.2 v) = fun p =>
      ∑ hh ∈ Finset.range (H + 1), c⁻¹ • ∑ n ∈ Finset.Icc 1 N, ε ^ n •
        ∑ q : LiftActionIndex ι n, coeffDot Q Cc hh n q.1.val q.2.1 lam q.2.2 v
          (orderedDerivative q.2.1 (chartField cf φ χ c ρs (projIcc a b P.window (c⁻¹ * p.1)))
            (ρs⁻¹ • p.2) q.2.2)
          (projIcc a b P.window (c⁻¹ * p.1)) (ρs⁻¹ • p.2) (es⁻¹ • p.2) := by
    funext p
    rw [← inv_mul_projIcc_scale hc P.window hcab]
    rfl
  rw [he]
  refine Finset.measurable_sum _ fun hh hhmem => ?_
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhmem)
  refine (Finset.measurable_sum _ fun n hn => ?_).const_smul _
  refine (Finset.measurable_sum _ fun q _ => ?_).const_smul _
  exact setting_coeffDot_comp_measurable P sX sZ hsX hsZ Cc hseq hh n hhh (Finset.mem_Icc.1 hn).1
    (Finset.mem_Icc.1 hn).2 q.1.val (Nat.lt_succ_iff.1 q.1.isLt) q.2.1 q.2.2 v c ρs es _
    (continuous_chartField_jet cf φ hφ χ hχ P.window hc hA hB hcf q.2.1 q.2.2)

include P in
/-- **The coefficient form of the frozen density is bounded on the window.** -/
theorem setting_frozenCoeff_bound (sX sZ : ℕ) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    {κ : Type*} [Fintype κ] (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (hφp : ∀ k, IsZ2Periodic (φ k))
    (χ : ℝ → Vec 2 → Vec 2) (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2))
    (hχl : ∀ t y (n : Fin 2 → ℤ), χ t (y + latticeShift n) = χ t y + latticeShift n)
    {c ρs es : ℝ} (hc : 0 < c) (hρ : 0 < ρs) {A₀ B₀ : ℝ} (hA : A₀ ≤ c * a) (hB : c * b ≤ B₀)
    (hcf : ∀ k, ContinuousOn (cf k) (Icc A₀ B₀)) (v : ι) :
    ∃ M : ℝ, ∀ t, c⁻¹ * t ∈ Icc a b → ∀ y,
      ‖frozenCoeff Q Cc N H ε lam cf φ χ c ρs es t y v‖ ≤ M := by
  classical
  have hr : 0 + (N + D) ≤ qs := by
    have := setting_ambient_output_supported P
    omega
  have hcfb : ∀ k, ∃ C : ℝ, ∀ x ∈ Icc A₀ B₀, ‖cf k x‖ ≤ C := fun k =>
    isCompact_Icc.exists_bound_of_continuousOn (hcf k)
  choose Ccf hCcf using hcfb
  have hJb : ∀ n (q : LiftActionIndex ι n) (k : κ), ∃ C : ℝ, ∀ s ∈ Icc a b, ∀ X,
      ‖orderedDerivative q.2.1 (fun Y =>
        (fun p : ℝ × Vec 2 => chartMode φ χ c ρs k p.1 p.2) (s, Y)) X‖ ≤ C :=
    fun n q k => jet_bound_periodic (fun p : ℝ × Vec 2 => chartMode φ χ c ρs k p.1 p.2)
      (chartMode_contDiff φ hφ χ hχ c ρs k) hρ
      (fun s X m => chartMode_periodic φ hφp χ hχl hρ k s X m) q.2.1 a b
  choose Cj hCj using hJb
  have hDb : ∀ hh n (q : LiftActionIndex ι n), ∃ M : ℝ, 0 ≤ M ∧ (hh ≤ H → 1 ≤ n → n ≤ N →
      ∀ s ∈ Icc a b, ∀ X z (ξ : h q.2.2),
        ‖coeffDot Q Cc hh n q.1.val q.2.1 lam q.2.2 v ξ s X z‖ ≤ M * ‖ξ‖) := by
    intro hh n q
    by_cases hc3 : hh ≤ H ∧ 1 ≤ n ∧ n ≤ N
    · obtain ⟨M, hM0, hM⟩ := setting_coeffDot_bound P sX sZ hsZ Cc hseq 0 hr hh hc3.1 n hc3.2.1
        hc3.2.2 q.1.val (Nat.lt_succ_iff.1 q.1.isLt) q.2.1 q.2.2 v
      exact ⟨M, hM0, fun _ _ _ => hM⟩
    · exact ⟨0, le_rfl, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc3⟩
  choose Md hMd0 hMd using hDb
  refine ⟨∑ hh ∈ Finset.range (H + 1), |c⁻¹| * ∑ n ∈ Finset.Icc 1 N, |ε| ^ n *
    ∑ q : LiftActionIndex ι n, Md hh n q * ∑ k, max (Ccf k) 0 * max (Cj n q k) 0,
    fun t ht y => ?_⟩
  have hcs : c * (c⁻¹ * t) ∈ Icc A₀ B₀ :=
    ⟨hA.trans (mul_le_mul_of_nonneg_left ht.1 hc.le),
      (mul_le_mul_of_nonneg_left ht.2 hc.le).trans hB⟩
  simp only [frozenCoeff]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun hh hhmem => ?_)
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhmem)
  rw [norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_))
    (abs_nonneg _)
  rw [norm_smul, norm_pow, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_))
    (pow_nonneg (abs_nonneg _) _)
  refine (hMd hh n q hhh (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2 _ ht _ _ _).trans
    (mul_le_mul_of_nonneg_left ?_ (hMd0 hh n q))
  rw [orderedDerivative_chartField cf φ hφ χ hχ c ρs, Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [Pi.smul_apply, norm_smul]
  refine mul_le_mul ((hCcf k _ hcs).trans (le_max_left _ _)) ?_ (norm_nonneg _)
    (le_max_right _ _)
  exact (norm_le_pi_norm _ _).trans ((hCj n q k _ ht _).trans (le_max_left _ _))
end

end AVRegularity.CycleComparison.Reconstruction
end
