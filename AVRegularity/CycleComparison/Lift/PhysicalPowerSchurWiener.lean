-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.AmbientPairedCoefficientDataOfTests
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
public import AVRegularity.CycleComparison.Lift.CellB1LeftTerms

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! The literal operator-valued Fourier pair has a uniform summable majorant. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem vector_transverse_fourier_pair_bound (p q r L : ℕ)
    (hr : r ≤ p) (hL : L + 2 ≤ q)
    (par : Fin 2) (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (ht : IsTransverseOn par Set.univ (fun _ : ℝ => f))
    (hp : ∀ X, Function.Periodic (fun z : ℝ => f X (z • basisVec par.rev)) 1)
    (C : ℕ → ℝ) (hC : ∀ a ≤ p, 0 ≤ C a)
    (hb : ∀ a ≤ p, ∀ b ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C a)
    (k : Fin 2 → ℤ) (X : Vec 2) :
    (1 + max |(k 0 : ℝ)| |(k 1 : ℝ)|) ^ L *
      (‖iteratedFDeriv ℝ r (fun Y => ∫ z in AVenhance.unitCube,
        Real.cos (2 * Real.pi * ∑ i, (k i : ℝ) * z i) • f Y z) X‖ +
       ‖iteratedFDeriv ℝ r (fun Y => ∫ z in AVenhance.unitCube,
        Real.sin (2 * Real.pi * ∑ i, (k i : ℝ) * z i) • f Y z) X‖) ≤
      4 * (if k par = 0 then profileJetMajorant (2 ^ r * C r) (2 ^ r * C r) (k par.rev) else 0) := by
  let W : ℝ := (1 + max |(k 0 : ℝ)| |(k 1 : ℝ)|) ^ L
  let S : ℝ := if k par = 0 then profileJetMajorant (2 ^ r * C r) (2 ^ r * C r) (k par.rev) else 0
  have hW : 0 < W := by dsimp [W]; positivity
  have hCr := hC r hr
  have hS : 0 ≤ S := by
    dsimp [S]
    split_ifs
    · exact profileJetMajorant_nonneg _ _ (by positivity) (by positivity) _
    · exact le_rfl
  have hslow : ∀ a ≤ p, ∀ Y z, ‖iteratedFDeriv ℝ a (fun Z => f Z z) Y‖ ≤ C a := by
    intro a ha Y z
    simpa only [norm_mixed_jet_fast_zero] using hb a ha 0 (Nat.zero_le q) Y z
  let w₁ := fun z : Vec 2 => Real.cos (2 * Real.pi * ∑ i, (k i : ℝ) * z i)
  let w₂ := fun z : Vec 2 => Real.sin (2 * Real.pi * ∑ i, (k i : ℝ) * z i)
  have hc₁ := weighted_cell_coefficient_contDiff p f (fun Y => (hf.1 Y).continuous)
    (boxSmooth_slow_contDiff hf) C hslow w₁ (by fun_prop)
    (fun z => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  have hc₂ := weighted_cell_coefficient_contDiff p f (fun Y => (hf.1 Y).continuous)
    (boxSmooth_slow_contDiff hf) C hslow w₂ (by fun_prop)
    (fun z => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one _)
  have hpair := real_fourier_dual_pair_bound p r hr f (fun Y => (hf.1 Y).continuous)
    w₁ w₂ (by fun_prop) (by fun_prop) hc₁ hc₂ X (2 * S / W) (by positivity) (by
      intro l
      have hper : ∀ Y, Function.Periodic
          (fun z : ℝ => ((l (f Y (z • basisVec par.rev)) : ℝ) : ℂ)) 1 :=
        fun Y z => congrArg (fun v : E => (l v : ℂ)) (hp Y z)
      have hdata := complex_dual_transverse_fourier_parameter_data p q r L hr hL par f hf ht l hper C hb k
      have hd := complex_dual_transverse_fourier_bound p q r L hr hL par f hf ht l hper C hb k X
      change W * ‖iteratedFDeriv ℝ r
        (fun Y => smoothFourierCoeff (fun z => ((l (f Y z) : ℝ) : ℂ)) k) X‖ ≤ ‖l‖ * S at hd
      have hs := real_fourier_coefficient_jet_sum_le p r hr (fun Y z => l (f Y z))
        (fun Y => l.continuous.comp (hf.1 Y).continuous) k hdata.1 X
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hW).mpr
      calc
        _ ≤ W * (2 * ‖iteratedFDeriv ℝ r
            (fun Y => smoothFourierCoeff (fun z => ((l (f Y z) : ℝ) : ℂ)) k) X‖) := by
          simpa only [w₁, w₂, mul_comm] using mul_le_mul_of_nonneg_left hs hW.le
        _ ≤ 2 * (‖l‖ * S) := by
          convert mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2) using 1
          ring
        _ = _ := by ring)
  have he := mul_le_mul_of_nonneg_left hpair hW.le
  have heq : W * (2 * (2 * S / W)) = 4 * S := by
    field_simp [ne_of_gt hW]
    ring
  exact he.trans_eq heq

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The actual first cross lift term has a fixed-data budget under its ambient predecessor state. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_first_cross_lift_bound
    (n p q p' q' : ℕ) (hp : p + 1 ≤ qs) (hq : q ≤ qf)
    (hp' : p + 1 ≤ p') (hq' : q + 1 ≤ q')
    (c : LiftCoeff ι h) (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' c M)
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u)
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB1 Q.η Q.G Q.v t
        (liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v) z) X‖ ≤
      (normalizedCellB1UniformConstant p q A (metricParameterBudget (p + 1) CG)
        (metricParameterBudget q Cw) * finiteLiftSymbolBudget n A * M v u * ‖ξ‖) *
          lam ^ ((n + 1) + r) := by
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  exact normalizedCellB1_scaled_drift_lift_test_grading n p q Q.η lam
    (metricParameterBudget (p + 1) CG) (metricParameterBudget q Cw) (M v u)
    P.η_le hlam (metricParameterBudget_nonneg (p + 1) CG) (metricParameterBudget_nonneg q Cw)
    (data.nonneg v u) A Q.G Q.v t c v u ξ
    (fun m hm α v' u' => (data.box m hm α v' u' t ht).mono hp' hq')
    (fun i j => setting_metric_entry_box P (p + 1) q hp t ht i j)
    (fun i => setting_raw_drift_fast_box P p q hq t ht i) X
    (fun i j a ha b _ y => setting_metric_mixed_uniform_bound P (p + 1) a b hp ha t ht X y i j)
    (fun i a _ b hb y => setting_scaled_drift_mixed_uniform_bound P q a b hq hb t ht X y i)
    (fun m hm α a ha b hb y => data.bound m hm α v u a (ha.trans hp') b (hb.trans hq') t ht X y)
    r s hr hs z

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! The actual finite-past Fourier response has a summed weak Hilbert curve with all absolute-series bounds discharged. -/

theorem profileResponseSeries_hilbert_curve (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a b κ M : ℝ) (hab : a ≤ b) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, |g t| ≤ M)
    (hgl : ∀ t ∈ Icc a b, κ ≤ g t) (hfm : Measurable (Function.uncurry f))
    (C : Fin 3 → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hf : ∀ t ∈ Icc a b, ContDiff ℝ 2 (f t))
    (hp : ∀ t ∈ Icc a b, Function.Periodic (f t) 1)
    (hj : ∀ j : Fin 3, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j.val (f t) x‖ ≤ C j) (par : Fin 2) :
    let c := fun t n => profileModeResponse g f a t n
    let dc := fun t n => (-(‖profileFourierFrequency n‖ ^ 2) * g t) • c t n +
      unitProfileFourierCoeff (f t) n
    let m := fun n => transverseFourierModeH1 par n
    CellWeakHilbertCurve a b
      (fun t => ∑' n : ℤ, cellScalarCLM (c t n) (torusHkValueCLM (m n)))
      (fun t => ∑' n : ℤ, cellH1Scalar (c t n) (m n))
      (fun t => ∑' n : ℤ, cellPivotDualCLM (cellScalarCLM (dc t n) (torusHkValueCLM (m n)))) := by
  dsimp only
  have hi : IntegrableOn g (Icc a b) := by
    apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne hgm
    exact Filter.Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using hgb t
  have hzero (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      ‖f t x‖ ≤ C 0 := by simpa using hj 0 t ht x hx
  let B₀ := profileJetMajorant (C 0 / κ) (C 0 * (b - a))
  let B₁ := profileJetMajorant (C 1 / κ) (C 0 * (b - a))
  let Bd := profileJetMajorant (M * (C 2 / κ) + C 2) (C 0)
  have hs₀ : Summable B₀ := profileJetMajorant_summable _ _
  have hs₁ : Summable B₁ := profileJetMajorant_summable _ _
  have hsd : Summable Bd := profileJetMajorant_summable _ _
  have hb₀ (n : ℤ) (t : ℝ) (ht : t ∈ Icc a b) : ‖profileModeResponse g f a t n‖ ≤ B₀ n := by
    simpa only [pow_zero, one_mul] using profileModeResponse_uniform_jet_bound g f a b κ hab hκ hi hgl
      0 (C 0) (C 0) (hC 0) (hC 0) (fun s hs => (hf s hs).of_le (by norm_num)) hp
      (hj 0) hzero n t ht
  have hb₁ (n : ℤ) (t : ℝ) (ht : t ∈ Icc a b) : ‖profileFourierFrequency n * profileModeResponse g f a t n‖ ≤ B₁ n := by
    simpa only [pow_one] using profileModeResponse_uniform_jet_bound g f a b κ hab hκ hi hgl
      1 (C 1) (C 0) (hC 1) (hC 0) (fun s hs => (hf s hs).of_le (by norm_num)) hp
      (hj 1) hzero n t ht
  have hbd (n : ℤ) (t : ℝ) (ht : t ∈ Icc a b) :
      ‖(-(‖profileFourierFrequency n‖ ^ 2) * g t) • profileModeResponse g f a t n +
        unitProfileFourierCoeff (f t) n‖ ≤ Bd n :=
    profileModeResponse_uniform_rhs_bound g f a b κ M (C 2) (C 0) hκ hi hgl
      (fun t _ => hgb t) (hC 2) (hC 0) hf hp (hj 2) hzero n t ht
  apply cellWeakHilbert_series a b _ _ _
    (fun n => profileModeResponse_hilbert_curve g f a b hab M hM hgm hgb hfm (C 0)
      (fun t ht => hzero t (by simpa only [uIcc_of_le hab] using ht)) par n)
    (fun n => ‖cellConstantCLM 1‖ * B₀ n)
    (fun n => ‖cellConstantCLM 1‖ * (B₀ n + B₁ n))
    (fun n => (‖cellPivotDualCLM‖ * ‖cellConstantCLM 1‖) * Bd n)
    (hs₀.mul_left _) ((hs₀.add hs₁).mul_left _) (hsd.mul_left _)
  · intro n t ht
    exact (transverseFourierMode_scalar_value_norm_le par n _).trans
      (mul_le_mul_of_nonneg_left (hb₀ n t ht) (norm_nonneg _))
  · intro n t ht
    exact (transverseFourierMode_scalar_state_norm_le par n _).trans
      (mul_le_mul_of_nonneg_left (add_le_add (hb₀ n t ht) (hb₁ n t ht)) (norm_nonneg _))
  · intro n t ht
    exact (transverseFourierMode_scalar_dual_norm_le par n _).trans
      (mul_le_mul_of_nonneg_left (hbd n t ht)
        (mul_nonneg (norm_nonneg cellPivotDualCLM) (norm_nonneg (cellConstantCLM 1))))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Summing the actual operator-valued coefficient majorants gives a uniform Wiener budget. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem vector_transverse_wienerJet_le (I : Set ℝ) (p q r L : ℕ)
    (hr : r ≤ p) (hL : L + 2 ≤ q)
    (par : Fin 2) (f : ℝ → Vec 2 → Vec 2 → E)
    (hf : ∀ t ∈ I, IsBoxSmooth p q (f t))
    (ht : IsTransverseOn par I f)
    (hp : ∀ t ∈ I, ∀ X, Function.Periodic (fun z : ℝ => f t X (z • basisVec par.rev)) 1)
    (C : ℕ → ℝ) (hC : ∀ a ≤ p, 0 ≤ C a)
    (hb : ∀ a ≤ p, ∀ b ≤ q, ∀ t ∈ I, ∀ X z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f t Y) z) X‖ ≤ C a) :
    wienerJet I L r f ≤
      ENNReal.ofReal (4 * (2 ^ r * C r) * (centeredProfileJetConstant + 1)) := by
  let B : ℝ := 2 ^ r * C r
  have hCr := hC r hr
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let M := fun m : ℤ => 4 * profileJetMajorant B B m
  have hM : ∀ m, 0 ≤ M m := fun m =>
    mul_nonneg (by norm_num) (profileJetMajorant_nonneg B B hB hB m)
  have hMs : Summable M := (profileJetMajorant_summable B B).mul_left 4
  have hsum : (∑' k : Fin 2 → ℤ,
      if k par = 0 then ENNReal.ofReal (M (k par.rev)) else 0) =
      ENNReal.ofReal (4 * B * (centeredProfileJetConstant + 1)) := by
    rw [show (∑' k : Fin 2 → ℤ,
        if k par = 0 then ENNReal.ofReal (M (k par.rev)) else 0) =
        ∑' m : ℤ, ENNReal.ofReal (M m) from by
          simpa only [pow_zero, ENNReal.ofReal_one, one_mul] using
            transverse_wiener_tsum par 0 (fun m => ENNReal.ofReal (M m))]
    rw [← ENNReal.ofReal_tsum_of_nonneg hM hMs]
    congr 1
    dsimp [M]
    rw [tsum_mul_left, profileJetMajorant_tsum_full]
    ring
  unfold wienerJet
  apply le_trans (ENNReal.tsum_le_tsum ?_) hsum.le
  intro k
  simp_rw [ENNReal.mul_iSup]
  apply iSup_le
  intro t
  apply iSup_le
  intro hti
  apply iSup_le
  intro X
  rw [← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  have he := vector_transverse_fourier_pair_bound p q r L hr hL par (f t) (hf t hti)
    (fun _ _ Y z s => ht t hti Y z s) (hp t hti) C hC
    (fun a ha b hb' Y z => hb a ha b hb' t hti Y z) k X
  have he' := ENNReal.ofReal_le_ofReal he
  by_cases hk : k par = 0
  · simpa only [ite_eq_left hk, M, B] using he'
  · simpa only [ite_eq_right hk, mul_zero, ENNReal.ofReal_zero] using he'

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Actual lift periodicity and ambient jets give literal coefficient Wiener bounds. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Q : LiftOperatorData ι h D}

theorem AmbientLiftCoefficientData.wienerJet_le
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} {hh N H sX sZ : ℕ} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n p q (Cc hh n) M)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hhh : hh ≤ H)
    (hlam : 0 ≤ lam) {m r L : ℕ} (hm : m ≤ n) (hr : r ≤ p)
    (hL : L + 2 ≤ q) (α : DerivativeWord2 m) (v u : ι) :
    wienerJet (Set.Icc a b) L r (fun t X z => Cc hh n m α t X z v u) ≤
      ENNReal.ofReal (4 * (2 ^ r * (M v u * lam ^ (n - m + r))) *
        (centeredProfileJetConstant + 1)) := by
  apply vector_transverse_wienerJet_le (Set.Icc a b) p q r L hr hL par
    (fun t X z => Cc hh n m α t X z v u)
    (data.box m hm α v u) (data.transverse m hm α v u)
    (fun t ht X => coordinate_line_periodic _
      ((hseq.2.2.2.2.2.1 hh hhh n m α v u t ht).2 X) par.rev)
    (fun j => M v u * lam ^ (n - m + j))
    (fun _ _ => mul_nonneg (data.nonneg v u) (pow_nonneg hlam _))
  intro j hj s hs t ht X z
  exact data.bound m hm α v u j hj s hs t ht X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The literal drift and molecular mean fluxes retain the paired coefficient grading. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V 0 N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_paired_mean_flux_jet_of_coefficient_data
    (Cc Ci : ℕ → ℕ → LiftCoeff ι h) (n p q : ℕ) (hn : 2 ≤ n)
    (hp : p ≤ qs) (Bd g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (data : AmbientLiftCoefficientData par a b P.window lam (n - 1) p q
      (fun m α t X z v u => Cc 0 (n - 1) m α t X z v u - Ci 0 (n - 1) m α t X z v u)
      (fun v u => (Bd * (if v = u then 1 else 0)) * g))
    (hc : ∀ m ≤ n - 1, ∀ α : DerivativeWord2 m, ∀ v u, ∀ t ∈ Set.Icc a b, ∀ X,
      Continuous (fun z => Cc 0 (n - 1) m α t X z v u))
    (hi : ∀ m ≤ n - 1, ∀ α : DerivativeWord2 m, ∀ v u, ∀ t ∈ Set.Icc a b, ∀ X,
      Continuous (fun z => Ci 0 (n - 1) m α t X z v u))
    (m : ℕ) (hmpos : 1 ≤ m) (hm : m ≤ n - 1) (α : DerivativeWord2 m)
    (r : ℕ) (hr : r ≤ p) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (k₀ : Fin 2) (X z : Vec 2) (v u : ι) :
    ‖iteratedFDeriv ℝ r (fun Y => diagonalMeanFluxCoefficient Q Cc n k₀ m α t Y z v u -
      diagonalMeanFluxCoefficient
        (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
        Ci n k₀ m α t Y z v u) X‖ ≤
      (2 ^ r * max (Cw 0) 0 * Bd + if n = 2 then max (CGI r) 0 else 0) *
        g * (if v = u then 1 else 0) * lam ^ (n - 1 - m + r) := by
  have hw : Continuous (fun y => Real.sqrt Q.η * Q.v t y k₀) :=
    (setting_normalized_drift_contDiff_one P t ht k₀).continuous
  have hW y : ‖Real.sqrt Q.η * Q.v t y k₀‖ ≤ max (Cw 0) 0 := by
    simpa only [norm_iteratedFDeriv_zero] using
      setting_scaled_drift_component_jet_bound P 0 (Nat.zero_le qf) t ht y k₀
  have hd := data.weighted_mean_jet_le m hm α v u t ht r hr _ hw _ hW
  have he Y := diagonalMeanFluxCoefficient_paired_difference Q
    (fun _ _ i j => if i = j then 1 else 0) Cc Ci n k₀ m α t Y z v u hw
    (hc m hm α v u t ht Y) (hi m hm α v u t ht Y)
  simp_rw [he]
  by_cases hn2 : n = 2
  · subst n
    have hm1 : m = 1 := by omega
    subst m
    simp only [ite_true]
    have hrd : ContDiff ℝ (r : ℕ∞) (fun Y => weightedLiftCoefficientMean
        (fun d β s Z y i j => Cc 0 (2 - 1) d β s Z y i j - Ci 0 (2 - 1) d β s Z y i j)
        (fun s y => Real.sqrt Q.η * Q.v s y k₀) 1 α t Y z v u) :=
      hd.1.of_le (by exact_mod_cast hr)
    have hG i j : ContDiff ℝ (r : ℕ∞) (fun Y => Q.G t Y i j) :=
      (P.G_smooth t ht i j).of_le (by exact_mod_cast hr.trans hp)
    have hmetric := (metricFluxCoefficient_contDiff (h := h) Q.η Q.G r t hG k₀ 1 α z v u).sub
      (metricFluxCoefficient_contDiff Q.η (fun _ _ i j => if i = j then 1 else 0)
        r t (fun _ _ => contDiff_const) k₀ 1 α z v u)
    apply (norm_iteratedFDeriv_add_le r _ _ hrd hmetric X).trans
    apply (add_le_add (hd.2 X)
      (setting_metric_flux_coefficient_difference_jet_le P g hg CGI hGI r (hr.trans hp)
        t ht k₀ α X z v u)).trans_eq
    simp only [Nat.reduceSub, zero_add]
    ring
  · simp only [ite_eq_right hn2, add_zero]
    exact (hd.2 X).trans_eq (by ring)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Ordered-word Wiener sums preserve the fixed ambient matrix envelope. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Q : LiftOperatorData ι h D}

theorem AmbientLiftCoefficientData.wienerArray_le
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} {hh N H sX sZ : ℕ} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n p q (Cc hh n) M)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hhh : hh ≤ H)
    (hlam : 0 ≤ lam) {m r L : ℕ} (hm : m ≤ n) (hr : r ≤ p)
    (hL : L + 2 ≤ q) (v u : ι) :
    (∑ α : DerivativeWord2 m,
      wienerJet (Set.Icc a b) L r (fun t X z => Cc hh n m α t X z v u)) ≤
      ENNReal.ofReal ((2 ^ m : ℝ) * 4 * (2 ^ r * (M v u * lam ^ (n - m + r))) *
        (centeredProfileJetConstant + 1)) := by
  have hM := data.nonneg v u
  have hProf := centeredProfileJetConstant_nonneg
  have hB : 0 ≤ 4 * (2 ^ r * (M v u * lam ^ (n - m + r))) *
      (centeredProfileJetConstant + 1) := by positivity
  calc
    _ ≤ ∑ _α : DerivativeWord2 m, ENNReal.ofReal
        (4 * (2 ^ r * (M v u * lam ^ (n - m + r))) * (centeredProfileJetConstant + 1)) :=
      Finset.sum_le_sum fun α _ => data.wienerJet_le hseq hhh hlam hm hr hL α v u
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hB)]
      simp only [Finset.sum_const, card_derivativeWord2, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      congr 1
      ring
end

/-! Uniform Wiener estimates pass through mass-conjugated matrix budgets. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Q : LiftOperatorData ι h D}

theorem AmbientLiftCoefficientData.schurWienerJet_le
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} {hh N H sX sZ : ℕ} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n p q (Cc hh n) M)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hhh : hh ≤ H)
    (hlam : 0 ≤ lam) {m r L : ℕ} (hm : m ≤ n) (hr : r ≤ p)
    (hL : L + 2 ≤ q) (π : ι → ℝ) (C : ℝ)
    (hM : HasRealSchurBudget (massConjugatedMatrix π M) C) :
    schurWienerJet π (Set.Icc a b) L r (Cc hh n m) ≤
      ENNReal.ofReal ((2 ^ m : ℝ) * 4 * 2 ^ r * (centeredProfileJetConstant + 1) *
        lam ^ (n - m + r) * C) := by
  let B : ℝ := (2 ^ m : ℝ) * 4 * 2 ^ r * (centeredProfileJetConstant + 1) * lam ^ (n - m + r)
  have hProf := centeredProfileJetConstant_nonneg
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbudget : HasRealSchurBudget
      (massConjugatedMatrix π (fun v u => B * M v u)) (B * C) := by
    convert hM.const_mul B hB using 1
    funext v u
    simp only [massConjugatedMatrix]
    ring
  apply schurSums_le_of_real_matrix_budget π _ (B * C) hbudget
  intro v u
  exact (data.wienerArray_le hseq hhh hlam hm hr hL v u).trans_eq (by
    congr 1
    dsimp [B]
    ring)
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Source-height powers survive the conversion to literal Wiener jets. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Q : LiftOperatorData ι h D}

theorem physical_power_schurWienerJet_le
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (edge : ι → ι → ℝ)
    (Θ : ℝ) (hΘ : 0 ≤ Θ) (hedge : HasRealSchurBudget edge Θ)
    (hh : ℕ) (B : ℝ) (hB : 0 ≤ B)
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} {N H sX sZ : ℕ}
    (data : AmbientLiftCoefficientData par a b hab lam n p q (Cc hh n)
      (fun v u => B * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u))
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hhh : hh ≤ H)
    (hlam : 0 ≤ lam) {m r fast : ℕ} (hm : m ≤ n) (hr : r ≤ p)
    (hfast : fast + 2 ≤ q) :
    schurWienerJet π (Set.Icc a b) fast r (Cc hh n m) ≤
      ENNReal.ofReal (((2 ^ m : ℝ) * 4 * 2 ^ r * (centeredProfileJetConstant + 1) * B) *
        Θ ^ hh * lam ^ (n - m + r)) := by
  have hmatrix := physicalEdgeEnvelopeMatrix_power_schur_budget π hπ edge Θ hΘ hedge hh
  have hscaled : HasRealSchurBudget
      (massConjugatedMatrix π
        (fun v u => B * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u))
      (B * Θ ^ hh) := by
    convert hmatrix.const_mul B hB using 1
    funext v u
    simp only [massConjugatedMatrix]
    ring
  exact (data.schurWienerJet_le hseq hhh hlam hm hr hfast π (B * Θ ^ hh) hscaled).trans_eq (by
    congr 1
    ring)

end AVRegularity.CycleComparison.Lift
end
