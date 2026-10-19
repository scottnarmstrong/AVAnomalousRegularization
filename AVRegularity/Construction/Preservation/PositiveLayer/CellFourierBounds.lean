-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
public import AVRegularity.Definitions.Construction.Words
import AVenhance.Infra.Section5.AnalyticBridge.Sobolev
public import AVRegularity.CycleComparison.QuietDecay.Final.Main
import AVRegularity.Construction.InitialLayer.Comparison
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleComparison.Lift.PhysicalPowerSchurWiener
public import AVRegularity.CycleComparison.Lift.SourceZeroMean
import AVRegularity.CycleComparison.QuietDecay.Scalar.Weighted
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance.Infra.Torus
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.PositiveLayer

/-! Fourier reconstruction for the entrance conversion of the quiet difference sequence.
The degenerate cases are included: the Fourier sum may be infinite; no finite-dimensional constant
is used. The norming functional with norm at most one also covers a zero or trivial fibre.
The eventual centered readout discards the zero Fourier mode by its actual mean identity. -/

open CycleComparison.Lift

private theorem scalar_fourier_readout_enorm
    {f : Vec 2 → ℂ} (hf : Continuous f) (hper : IsZdPeriodic f) (x : Vec 2) :
    ‖f x‖ₑ ≤ ∑' ξ : Fin 2 → ℤ, ‖smoothFourierCoeff f ξ‖ₑ := by
  by_cases htop : (∑' ξ : Fin 2 → ℤ, ‖smoothFourierCoeff f ξ‖ₑ) = ⊤
  · rw [htop]; exact le_top
  have hsnn : Summable (fun ξ : Fin 2 → ℤ => ‖smoothFourierCoeff f ξ‖₊) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp htop
  have hsn : Summable (fun ξ : Fin 2 → ℤ => ‖smoothFourierCoeff f ξ‖) :=
    NNReal.summable_coe.mpr hsnn
  let g : C(UnitAddTorus (Fin 2), ℂ) :=
    ⟨periodicToTorus f,
      AVenhance.Infra.Section5.AnalyticBridge.Sobolev.continuous_periodicToTorus hf hper⟩
  have hcoeff (ξ : Fin 2 → ℤ) : UnitAddTorus.mFourierCoeff g ξ = smoothFourierCoeff f ξ :=
    AVenhance.Infra.Section5.AnalyticBridge.Sobolev.mFourierCoeff_periodicToTorus f ξ
  have hgs : Summable (UnitAddTorus.mFourierCoeff g) := by
    have he : UnitAddTorus.mFourierCoeff g = smoothFourierCoeff f := funext hcoeff
    rw [he]
    exact hsn.of_norm
  have hseries := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hgs (toUnitTorus 2 x)
  have hgx : g (toUnitTorus 2 x) = f x := congrFun (fromUnitTorus_periodicToTorus hper) x
  rw [hgx] at hseries
  have hpoint : ‖f x‖ ≤ ∑' ξ : Fin 2 → ℤ, ‖smoothFourierCoeff f ξ‖ := by
    refine hseries.norm_le_of_bounded hsn.hasSum (fun ξ => ?_)
    rw [hcoeff, norm_smul]
    have hm : ‖UnitAddTorus.mFourier ξ (toUnitTorus 2 x)‖ ≤ 1 :=
      (ContinuousMap.norm_coe_le_norm _ _).trans_eq UnitAddTorus.mFourier_norm
    exact (mul_le_mul_of_nonneg_left hm (norm_nonneg _)).trans_eq (mul_one _)
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal hpoint).trans_eq ?_
  simpa only [ofReal_norm] using ENNReal.ofReal_tsum_of_nonneg (fun ξ => norm_nonneg _) hsn

private theorem fast_word_fourier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℕ} (β : DerivativeWord2 q) {f : Vec 2 → E}
    (hf : ContDiff ℝ (q : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f)
    (Λ : E →L[ℝ] ℂ) (ξ : Fin 2 → ℤ) :
    smoothFourierCoeff (fun z => Λ (orderedDerivative β f z)) ξ =
      (∏ i : Fin q, (2 * Real.pi * Complex.I * (ξ (β i) : ℂ))) *
        smoothFourierCoeff (fun z => Λ (f z)) ξ := by
  induction q with
  | zero => simp only [orderedDerivative_zero, Fin.prod_univ_zero, one_mul]
  | succ q ih =>
    let β₀ : DerivativeWord2 q := fun i => β i.castSucc
    have hq : ContDiff ℝ (q : ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_succ q)
    rw [orderedDerivative_succ,
      smoothFourierCoeff_fderiv_apply Λ
        (orderedDerivative_contDiff β₀ 1 f (by simpa only [Nat.add_comm 1 q] using hf))
        (orderedDerivative_periodic β₀ f hq hp), ih β₀ hq,
      Fin.prod_univ_castSucc]
    dsimp only [β₀]
    ring

private theorem fast_word_slow_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth p q f)
    (β : DerivativeWord2 q) : IsSlowSmooth p (fun X z => orderedDerivative β (f X) z) := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) E
    (fun i => basisVec (β (Fin.rev i)))
  have he : (fun X z => orderedDerivative β (f X) z) =
      fun X z => L (iteratedFDeriv ℝ q (f X) z) := by
    funext X z
    exact congrFun (orderedDerivative_eq_iteratedFDeriv β (hf.1 X)) z
  rw [he]
  apply IsSlowSmooth.clm_comp _ L
  exact ⟨fun z => hf.2.1 q le_rfl z, fun r hr => hf.2.2 r q hr le_rfl⟩

private theorem scalar_coefficient_eq_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : Vec 2 → E} (hf : Continuous f) (l : E →L[ℝ] ℝ) (ξ : Fin 2 → ℤ) :
    smoothFourierCoeff (fun z => ((l (f z) : ℝ) : ℂ)) ξ =
      ((l (∫ z in AVenhance.unitCube, Real.cos (modePhase ξ z) • f z) : ℝ) : ℂ) -
        Complex.I * ((l (∫ z in AVenhance.unitCube, Real.sin (modePhase ξ z) • f z) : ℝ) : ℂ) := by
  have hi (w : Vec 2 → ℝ) (hw : Continuous w) :
      l (∫ z in AVenhance.unitCube, w z • f z) =
        ∫ z in AVenhance.unitCube, w z • l (f z) := by
    have hint : IntegrableOn (fun z => w z • f z) AVenhance.unitCube :=
      (Calculus.continuous_integrableOn_unitCell (hw.smul hf)).congr_set_ae unitCell_ae_eq_unitCube.symm
    simpa only [map_smul, Function.comp_apply] using (l.integral_comp_comm hint).symm
  rw [hi _ (by unfold modePhase; fun_prop), hi _ (by unfold modePhase; fun_prop)]
  have hc := cosine_cell_coefficient_eq_re (fun z => l (f z)) (l.continuous.comp hf) ξ
  have hs := sine_cell_coefficient_eq_neg_im (fun z => l (f z)) (l.continuous.comp hf) ξ
  change _ = ((∫ z in AVenhance.unitCube, Real.cos (2 * Real.pi * ∑ i, (ξ i : ℝ) * z i) • l (f z) : ℝ) : ℂ) -
    Complex.I * ((∫ z in AVenhance.unitCube, Real.sin (2 * Real.pi * ∑ i, (ξ i : ℝ) * z i) • l (f z) : ℝ) : ℂ)
  rw [hc, hs]
  apply Complex.ext <;> simp

private theorem scalar_fourier_slow_word_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p : ℕ} {f : Vec 2 → Vec 2 → E} (hf : ∀ X, Continuous (f X))
    (l : E →L[ℝ] ℝ) (hl : ‖l‖ ≤ 1) (ξ : Fin 2 → ℤ)
    (hc : ContDiff ℝ (p : ℕ∞) (fun X => ∫ z in AVenhance.unitCube,
      Real.cos (modePhase ξ z) • f X z))
    (hs : ContDiff ℝ (p : ℕ∞) (fun X => ∫ z in AVenhance.unitCube,
      Real.sin (modePhase ξ z) • f X z)) (α : DerivativeWord2 p) (X : Vec 2) :
    ContDiff ℝ (p : ℕ∞) (fun Y => smoothFourierCoeff (fun z => ((l (f Y z) : ℝ) : ℂ)) ξ) ∧
    ‖orderedDerivative α (fun Y => smoothFourierCoeff (fun z => ((l (f Y z) : ℝ) : ℂ)) ξ) X‖ₑ ≤
      modeJet f ξ p X := by
  let c := fun X => ∫ z in AVenhance.unitCube, Real.cos (modePhase ξ z) • f X z
  let s := fun X => ∫ z in AVenhance.unitCube, Real.sin (modePhase ξ z) • f X z
  let Λ := Complex.ofRealCLM.comp l
  let M : ℂ →L[ℝ] ℂ := Complex.I • ContinuousLinearMap.id ℝ ℂ
  have he : (fun Y => smoothFourierCoeff (fun z => ((l (f Y z) : ℝ) : ℂ)) ξ) =
      fun Y => Λ (c Y) - M (Λ (s Y)) := funext fun Y => scalar_coefficient_eq_pair (hf Y) l ξ
  rw [he]
  have hcΛ : ContDiff ℝ (p : ℕ∞) (fun Y => Λ (c Y)) := Λ.contDiff.comp hc
  have hsΛ : ContDiff ℝ (p : ℕ∞) (fun Y => Λ (s Y)) := Λ.contDiff.comp hs
  have hms : ContDiff ℝ (p : ℕ∞) (fun Y => M (Λ (s Y))) := M.contDiff.comp hsΛ
  refine ⟨hcΛ.sub hms, ?_⟩
  rw [orderedDerivative_sub α hcΛ hms,
    orderedDerivative_clm_comp Λ α hc, orderedDerivative_clm_comp M α hsΛ,
    orderedDerivative_clm_comp Λ α hs]
  have hcword := norm_orderedDerivative_le hc α X
  have hsword := norm_orderedDerivative_le hs α X
  have hcl (x : E) : ‖l x‖ ≤ ‖x‖ :=
    (l.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) hl)
  have hb : ‖Λ (orderedDerivative α c X) - M (Λ (orderedDerivative α s X))‖ ≤
      ‖iteratedFDeriv ℝ p c X‖ + ‖iteratedFDeriv ℝ p s X‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · simpa only [Λ, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real,
        Real.norm_eq_abs] using (hcl (orderedDerivative α c X)).trans hcword
    · simpa only [M, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
        norm_mul, Complex.norm_I, one_mul, Λ, ContinuousLinearMap.comp_apply,
        Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs] using
        (hcl (orderedDerivative α s X)).trans hsword
  simpa only [modeJet, ← ofReal_norm, ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)] using
    ENNReal.ofReal_le_ofReal hb

private theorem fourier_word_multiplier_bound {q : ℕ} (β : DerivativeWord2 q)
    (ξ : Fin 2 → ℤ) :
    ‖∏ i : Fin q, (2 * Real.pi * Complex.I * (ξ (β i) : ℂ))‖ ≤
      (1 + 2 * Real.pi) ^ q * (1 + modeLen ξ) ^ q := by
  have hlen : 0 ≤ modeLen ξ := Real.sqrt_nonneg _
  have hcoord (k : Fin 2) : |(ξ k : ℝ)| ≤ modeLen ξ := by
    have hs : 0 ≤ ∑ i : Fin 2, (ξ i : ℝ) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hi : (ξ k : ℝ) ^ 2 ≤ ∑ i : Fin 2, (ξ i : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun i : Fin 2 => (ξ i : ℝ) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    have he := Real.sq_sqrt hs
    change |(ξ k : ℝ)| ≤ Real.sqrt _
    nlinarith only [hi, he, sq_abs (ξ k : ℝ), abs_nonneg (ξ k : ℝ), Real.sqrt_nonneg (∑ i : Fin 2, (ξ i : ℝ) ^ 2)]
  rw [norm_prod, ← mul_pow]
  calc
    _ ≤ ∏ _i : Fin q, (1 + 2 * Real.pi) * (1 + modeLen ξ) := by
      apply Finset.prod_le_prod₀
        (f := fun i : Fin q => ‖(2 * Real.pi * Complex.I * (ξ (β i) : ℂ))‖)
        (g := fun _ : Fin q => ((1 + 2 * Real.pi) * (1 + modeLen ξ) : ℝ))
        (fun _ _ => norm_nonneg _)
      intro i _
      have he : ‖(2 * Real.pi * Complex.I * (ξ (β i) : ℂ))‖ = 2 * Real.pi * |(ξ (β i) : ℝ)| := by
        rw [norm_mul, norm_mul]
        simp only [Complex.norm_I, mul_one]
        have e : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
        rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        norm_cast
      rw [he]
      calc
        _ ≤ 2 * Real.pi * modeLen ξ := mul_le_mul_of_nonneg_left (hcoord _) (by positivity)
        _ ≤ _ := by nlinarith only [hlen, Real.pi_pos]
    _ = _ := by simp

/-- Same-order Fourier control of each mixed entrance derivative word. The only zero-mode
input is the actual cell mean, and the bound is independent of the Banach fibre. -/
theorem positive_layer_entrance_word_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p q : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth p q f)
    (hp : ∀ X, AVenhance.IsZ2Periodic (f X))
    (hmean : ∀ X, fieldCellMean (f X) = 0)
    (hc : ∀ ξ, ContDiff ℝ (p : ℕ∞) (fun X => ∫ z in AVenhance.unitCube,
      Real.cos (modePhase ξ z) • f X z))
    (hs : ∀ ξ, ContDiff ℝ (p : ℕ∞) (fun X => ∫ z in AVenhance.unitCube,
      Real.sin (modePhase ξ z) • f X z))
    (α : DerivativeWord2 p) (β : DerivativeWord2 q) (X z : Vec 2) :
    ‖orderedDerivative α (fun Y => orderedDerivative β (f Y) z) X‖ₑ ≤
      ENNReal.ofReal ((1 + 2 * Real.pi) ^ q) *
        ∑' ξ : NZMode, ENNReal.ofReal ((1 + modeLen ξ.1) ^ q) * ⨆ Y, modeJet f ξ.1 p Y := by
  classical
  let g := fun z => orderedDerivative α (fun Y => orderedDerivative β (f Y) z) X
  obtain ⟨l, hl, hx⟩ := exists_dual_vector'' ℝ (g z)
  let Λ := Complex.ofRealCLM.comp l
  have hgc : Continuous g := QuietDecay.continuous_orderedDerivative_orderedDerivative hf
    le_rfl le_rfl α β X
  have hgp : AVenhance.IsZ2Periodic g := by
    intro n z
    have he : (fun Y => orderedDerivative β (f Y) (z + AVenhance.latticeShift n)) =
        fun Y => orderedDerivative β (f Y) z :=
      funext fun Y => orderedDerivative_periodic β (f Y) (hf.1 Y) (hp Y) n z
    exact congrArg (fun F => orderedDerivative α F X) he
  have hrec := scalar_fourier_readout_enorm (Λ.continuous.comp hgc)
    ((isZdPeriodic_iff_frozen _).mpr (fun n z => congrArg Λ (hgp n z))) z
  have hnorm : ‖Λ (g z)‖ₑ = ‖g z‖ₑ := by
    simp only [Λ, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, hx,
      ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    change ENNReal.ofReal |‖g z‖| = ENNReal.ofReal ‖g z‖
    rw [abs_norm]
  change ‖Λ (g z)‖ₑ ≤ ∑' ξ : Fin 2 → ℤ, ‖smoothFourierCoeff (fun y => Λ (g y)) ξ‖ₑ at hrec
  rw [hnorm] at hrec
  have hFourier (ξ : Fin 2 → ℤ) :
      smoothFourierCoeff (fun y => Λ (g y)) ξ =
        (∏ i : Fin q, (2 * Real.pi * Complex.I * (ξ (β i) : ℂ))) *
          orderedDerivative α (fun Y => smoothFourierCoeff (fun y => Λ (f Y y)) ξ) X := by
    rw [← congrFun (orderedDerivative_smoothFourierCoeff
      (fast_word_slow_smooth hf β) Λ ξ p le_rfl α) X]
    have he : (fun Y => smoothFourierCoeff (fun y => Λ (orderedDerivative β (f Y) y)) ξ) =
        fun Y => (∏ i : Fin q, (2 * Real.pi * Complex.I * (ξ (β i) : ℂ))) *
          smoothFourierCoeff (fun y => Λ (f Y y)) ξ :=
      funext fun Y => fast_word_fourier β (hf.1 Y) (hp Y) Λ ξ
    rw [he]
    exact congrFun (orderedDerivative_clm_comp
      ((∏ i : Fin q, (2 * Real.pi * Complex.I * (ξ (β i) : ℂ))) • ContinuousLinearMap.id ℝ ℂ)
      α (scalar_fourier_slow_word_bound (fun Y => (hf.1 Y).continuous) l hl ξ
        (hc ξ) (hs ξ) α X).1) X
  have hzero : smoothFourierCoeff (fun y => Λ (g y)) 0 = 0 := by
    rw [hFourier]
    have he : (fun Y => smoothFourierCoeff (fun y => Λ (f Y y)) 0) = fun _ => 0 := by
      funext Y
      change smoothFourierCoeff (fun y => ((l (f Y y) : ℝ) : ℂ)) 0 = 0
      rw [scalar_coefficient_eq_pair (hf.1 Y).continuous l 0]
      simp only [modePhase, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero,
        mul_zero, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, integral_zero,
        map_zero, Complex.ofReal_zero, mul_zero, sub_zero]
      change ((l (fieldCellMean (f Y)) : ℝ) : ℂ) = 0
      rw [hmean Y, map_zero, Complex.ofReal_zero]
    rw [he, orderedDerivative_const_zero]
    exact mul_zero _
  have hsum : (∑' ξ : Fin 2 → ℤ, ‖smoothFourierCoeff (fun y => Λ (g y)) ξ‖ₑ) =
      ∑' ξ : NZMode, ‖smoothFourierCoeff (fun y => Λ (g y)) ξ.1‖ₑ := by
    symm
    apply tsum_subtype_eq_of_support_subset
      (f := fun ξ : Fin 2 → ℤ => ‖smoothFourierCoeff (fun y => Λ (g y)) ξ‖ₑ)
      (s := {ξ : Fin 2 → ℤ | ξ ≠ 0})
    intro ξ hξ
    by_contra he
    have hξ0 : ξ = 0 := by simpa only [Set.mem_ofPred_eq, not_not] using he
    subst ξ
    exact hξ (by simp only [hzero, enorm_zero])
  refine hrec.trans (hsum.le.trans ?_)
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro ξ
  rw [hFourier, enorm_mul]
  have hmult := ENNReal.ofReal_le_ofReal (fourier_word_multiplier_bound β ξ.1)
  rw [ofReal_norm, ENNReal.ofReal_mul (by positivity)] at hmult
  have hword := (scalar_fourier_slow_word_bound (fun Y => (hf.1 Y).continuous)
    l hl ξ.1 (hc ξ.1) (hs ξ.1) α X).2
  exact (mul_le_mul' hmult (hword.trans (le_iSup (fun Y => modeJet f ξ.1 p Y) X))).trans_eq
    (mul_assoc _ _ _)

/-- The same-order Fourier entrance norm controls the cell L² trace of every mixed word.
The finite cube has mass one; no time integral or almost-everywhere trace is used. -/
theorem positive_layer_entrance_mixed_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p q F : ℕ} (hqF : q ≤ F) {f : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth p q f)
    (hp : ∀ X, AVenhance.IsZ2Periodic (f X))
    (hmean : ∀ X, fieldCellMean (f X) = 0)
    (hc : ∀ ξ, ContDiff ℝ (p : ℕ∞) (fun X => ∫ z in AVenhance.unitCube,
      Real.cos (modePhase ξ z) • f X z))
    (hs : ∀ ξ, ContDiff ℝ (p : ℕ∞) (fun X => ∫ z in AVenhance.unitCube,
      Real.sin (modePhase ξ z) • f X z)) (a : ℝ) :
    mixedCellL2Jet {a} p q (fun _ => f) ≤
      ENNReal.ofReal ((1 + 2 * Real.pi) ^ F) *
        ∑' ξ : NZMode, ENNReal.ofReal ((1 + modeLen ξ.1) ^ F) * ⨆ Y, modeJet f ξ.1 p Y := by
  unfold mixedCellL2Jet
  refine iSup₂_le fun t _ht => iSup_le fun X => iSup_le fun α => iSup_le fun β => ?_
  have hpoint (z : Vec 2) := positive_layer_entrance_word_bound hf hp hmean hc hs α β X z
  have hmono : ENNReal.ofReal ((1 + 2 * Real.pi) ^ q) *
      (∑' ξ : NZMode, ENNReal.ofReal ((1 + modeLen ξ.1) ^ q) * ⨆ Y, modeJet f ξ.1 p Y) ≤
      ENNReal.ofReal ((1 + 2 * Real.pi) ^ F) *
        (∑' ξ : NZMode, ENNReal.ofReal ((1 + modeLen ξ.1) ^ F) * ⨆ Y, modeJet f ξ.1 p Y) := by
    apply mul_le_mul'
    · exact ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by have := Real.pi_pos; linarith) hqF)
    · apply ENNReal.tsum_le_tsum fun ξ => mul_le_mul_of_nonneg_right ?_ zero_le
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_right₀
        (by have := Real.sqrt_nonneg (∑ i : Fin 2, (ξ.1 i : ℝ) ^ 2); change 1 ≤ 1 + modeLen ξ.1; unfold modeLen; linarith) hqF)
  have hL := eLpNorm_le_of_ae_enorm_bound
    (p := (2 : ℝ≥0∞)) (μ := volume.restrict AVenhance.unitCube)
    (QuietDecay.continuous_orderedDerivative_orderedDerivative hf le_rfl le_rfl α β X).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => (hpoint z).trans hmono)
  simpa only [Measure.restrict_apply_univ, CycleEvolution.cellCube_volume_one,
    ENNReal.one_rpow, smul_eq_mul, mul_one] using hL

end AVRegularity.Construction.Preservation.PositiveLayer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.PositiveLayer

/-! Fourier amplitudes. The amplitudes use actual unit-window energies,
not spatial-jet surrogates. Their orders decrease along the finite triangular recursion.
The entrance traces retain the full original reserve. -/

/-- The finite orders fixed before the operator data. -/
structure Orders where
  D : ℕ
  N : ℕ
  H : ℕ
  K : ℕ
  L : ℕ
  k : ℕ
  sX : ℕ
  sZ : ℕ
  degree_pos : 1 ≤ N
  source_order : 2 ≤ D

def Orders.reserve (o : Orders) : ℕ := o.D * (o.H + 1) * o.N
def Orders.entranceSlow (o : Orders) : ℕ := o.K + o.reserve
def Orders.settingFast (o : Orders) : ℕ := o.L + o.reserve + 2
def Orders.entranceFast (o : Orders) : ℕ := o.L + o.reserve + 4
def Orders.slowReserve (o : Orders) : ℕ :=
  o.entranceSlow + 4 * (o.H + 1) * (o.N + o.D) ^ 2
def Orders.fastReserve (o : Orders) : ℕ :=
  max o.k o.entranceFast + o.H * o.D + 2 * o.N + 2 * o.D
def Orders.levelReserve (o : Orders) (hh n : ℕ) : ℕ :=
  QuietDecay.resv o.D o.H o.N (QuietDecay.rankOf o.N hh n)

variable {ι : Type} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]

/-- Exactly the data and hypotheses after the pre-data constants in the positive-layer statement. -/
structure Input (o : Orders) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) where
  Q : LiftOperatorData ι h o.D
  π : ι → ℝ
  sOld : ℝ
  sNew : ℝ
  s₁ : ℝ
  e : ℝ
  ν : ℝ
  B : ℝ
  ρ : ℝ
  E : ℝ
  ℓ : ℝ
  dstar : ℝ
  εc : ℝ
  lam : ℝ
  par : Fin 2
  V : ℝ → ℝ → ℝ
  bb : ι → ι → ℝ
  Θ : ℝ
  setting : IsLiftSetting Q π sOld s₁ e ν B ρ E ℓ dstar εc lam par V
    o.H o.N o.entranceSlow o.k o.settingFast o.slowReserve o.fastReserve CG Cw Cj bb Θ
  slow_le : o.sX ≤ o.slowReserve
  fast_le : o.sZ ≤ o.fastReserve
  starts : sOld ≤ sNew
  Cc : ℕ → ℕ → LiftCoeff ι h
  Cc' : ℕ → ℕ → LiftCoeff ι h
  sequence : IsLiftSequence Q o.sX o.sZ sOld s₁ o.N o.H Cc
  sequence' : IsLiftSequence Q o.sX o.sZ sNew s₁ o.N o.H Cc'
  a : ℝ
  b : ℝ
  new_le : sNew ≤ a
  interval : a ≤ b
  end_le : b ≤ s₁
  drift_zero : ∀ t ∈ Set.Icc a b, ∀ z, Q.v t z = 0
  independent : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
    IsFastIndependentOn (Set.Icc a b) (γ.coeff α)

/-- Difference on positive degrees, with the original identity at degree zero. -/
def quietLiftDiff (Cc Cc' : ℕ → ℕ → LiftCoeff ι h) : ℕ → ℕ → LiftCoeff ι h :=
  fun hh n => if n = 0 then Cc hh 0 else liftDiff Cc Cc' hh n

/-- The cell amplitudes, retaining the entrywise time suprema. -/
def cellAmplitude {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    (P : Input (ι := ι) (h := h) o CG Cw Cj) : ℕ → ℕ → ι → ι → ℝ≥0∞ :=
  QuietDecay.ampQ (quietLiftDiff P.Cc P.Cc') P.a (P.b - P.a)
    o.K (o.L + 4) o.D o.H o.N

/-- The complete mixed-cell entrance trace used by the recursion. -/
def cellTrace {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    (P : Input (ι := ι) (h := h) o CG Cw Cj) : ℕ → ℕ → ι → ι → ℝ≥0∞ :=
  QuietDecay.traceQ (quietLiftDiff P.Cc P.Cc') P.a o.entranceSlow o.entranceFast o.N

/-- The coefficient majorant on the quiet window, before mass conjugation. -/
def cellEnvelope {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    (P : Input (ι := ι) (h := h) o CG Cw Cj) : ι → ι → ℝ≥0∞ :=
  QuietDecay.envB P.Q.edge (Set.Icc P.a P.b) (o.entranceSlow + o.N)

/-- The degree-`n` summand of `layerEntry`, with its literal trace convention. -/
def degreeEntry (C : ℕ → ℕ → LiftCoeff ι h) (hh n K L : ℕ)
    (J : Set ℝ) (trace : Option ℝ) (v u : ι) : ℝ≥0∞ :=
  ∑ d ∈ Finset.Icc 1 n, ∑ α : DerivativeWord2 d, ∑ j ∈ Finset.range (K + 1),
    ENNReal.ofReal ((j.factorial : ℝ)⁻¹) * ∑' ξ : NZMode,
      ENNReal.ofReal ((1 + modeLen ξ.1) ^ L) * ⨆ X : Vec 2,
        match trace with
        | none => modeE ξ.1 (fun s => modeJet (fun X' z => C hh n d α s X' z v u) ξ.1 j X) J
        | some a => modeJet (fun X' z => C hh n d α a X' z v u) ξ.1 j X

/-- The exponentially weighted Fourier energy of one level on all admissible unit windows.
Empty sets of admissible windows give zero, as required when the quiet interval is short. -/
def amplitude (o : Orders) (C : ℕ → ℕ → LiftCoeff ι h) (a b : ℝ)
    (hh n : ℕ) (v u : ι) : ℝ≥0∞ :=
  if 1 ≤ n ∧ n ≤ o.N then
    ⨆ s ∈ Set.Icc a (b - 1), QuietDecay.growF a s *
      degreeEntry C hh n (o.K + o.levelReserve hh n) (o.L + o.levelReserve hh n)
        (Set.Icc s (s + 1)) none v u
  else 0

/-- The common quiet mean operator. -/
def quietMean {o : Orders} (Q : LiftOperatorData ι h o.D) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (t : ℝ) : Vec 2 → ∀ i, h i :=
  if hh = 0 then
    if n = 2 then fun X => cellB2 Q.η Q.G t (fun X _ => f t X) X 0 else 0
  else if hh = 1 then
    fun X => -sourceCoeff Q.edge Q.η n t (fun X _ => f t X) X 0
  else 0

/-- The raw weak jet of the difference. We subtract the two actual weak jets, so this
definition does not presume classical differentiability when the stored fast order is zero. -/
def differenceJet {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    (P : Input (ι := ι) (h := h) o CG Cw Cj) (hh n : ℕ)
    (f : Vec 2 → ∀ i, h i) (X : Vec 2) (ℓ : (∀ i, h i) →L[ℝ] ℝ) : ℝ → RawJet2 1 ℂ :=
  cellJetOfField ℓ (fun t z => liftApply n (P.Cc hh n) (fun _ => f) t X z) +
    (-1 : ℝ) • cellJetOfField ℓ (fun t z => liftApply n (P.Cc' hh n) (fun _ => f) t X z)

/-- The difference equation with its actual entrance trace, tested by every real functional.
The gradient is the difference of the actual weak gradients, and the value is the difference
of the actual lift values. The source is the literal difference of recursion sources. -/
def DifferenceEquation {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    (P : Input (ι := ι) (h := h) o CG Cw Cj) : Prop :=
  ∀ hh, hh ≤ o.H → ∀ n, 1 ≤ n → n ≤ o.N →
    ∀ f : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) f → ∀ X ℓ,
    IsCellSolution (Set.Icc P.a P.b) ⟨fun t _ => Matrix.of (P.Q.G t X), P.Q.v, 0, 0⟩
      (fun t z => ((ℓ (liftCellSource P.Q P.Cc (fun _ => f) hh n t X z -
        liftCellSource P.Q P.Cc' (fun _ => f) hh n t X z) : ℝ) : ℂ))
      (fun _ _ => 0) (differenceJet P hh n f X ℓ) ∧
    (∀ t ∈ Set.Icc P.a P.b, cellMean (cellValue (differenceJet P hh n f X ℓ) t) = 0)

/-- The identity after the quiet means agree: this is linear in the difference coefficients and
contains only lower cell degrees or the preceding source grade, with no external forcing. -/
def quietDifferenceSource {o : Orders} (Q : LiftOperatorData ι h o.D)
    (C : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) :
    Vec 2 → Vec 2 → ∀ i, h i := fun X z =>
  -(cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (C hh (n - 1)) f t) X z +
    (if 2 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (C hh (n - 2)) f t) X z else 0) -
    (if hh = 0 then 0 else ∑ j ∈ Finset.range (min o.D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (C (hh - 1) (n - j)) f t) X z)) +
  ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
    liftApply j (C p.1 j) (quietMean Q f p.2 (n - j)) t X z

/-- Exact common quiet means and linear triangular source, including the qualitative
regularity needed to justify their derivation from sequences of low stored order. -/
def QuietTriangularSource {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    (P : Input (ι := ι) (h := h) o CG Cw Cj) : Prop :=
  ∀ hh, hh ≤ o.H → ∀ n, 1 ≤ n → n ≤ o.N →
    ∀ f : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) f → ∀ t ∈ Set.Icc P.a P.b,
    (liftMean P.Q P.Cc (fun _ => f) hh n t = quietMean P.Q (fun _ => f) hh n t ∧
      liftMean P.Q P.Cc' (fun _ => f) hh n t = quietMean P.Q (fun _ => f) hh n t) ∧
    (∀ X z, liftCellSource P.Q P.Cc (fun _ => f) hh n t X z -
      liftCellSource P.Q P.Cc' (fun _ => f) hh n t X z =
        quietDifferenceSource P.Q (liftDiff P.Cc P.Cc') (fun _ => f) hh n t X z)

end AVRegularity.Construction.Preservation.PositiveLayer
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.PositiveLayer

/-! The analytic inputs and the proved bookkeeping input for the positive-layer assembly.
The fourth ingredient,
triangular induction with the exact powers of `Θ`, is proved as
`QuietDecay.schur_amplitude_le` and is discharged directly in the assembly.

For the difference recursion (`DifferenceEquation`, proved by `quiet_difference_equation`): at
`H = 0, n = 1` this contains precisely the homogeneous initial-layer weak equation, restricted to
the quiet window and retaining its actual trace at `a`; higher `n` still have lower-degree forcing.
At `Θ = 0` no source-grade coupling is present. The assertion is an equation on the whole quiet
interval, so it includes `s = a` and windows shorter than one. For `D = 2` both cross operators are
retained. Stored orders may be zero: the weak-equation subtraction uses the difference of the actual
weak jets and requires no regularity promotion. The source sub-leaf
`QuietTriangularSourceStatement` is treated the same way. It additionally requires the
common-mean/source algebra at the actual low stored orders; promotion from the recursion
is its main difficulty, not an added premise.

For the one-grade Fourier decay: `H = 0` removes the previous-grade term,
and `n = 1` leaves only entrance decay. `Θ = 0` forces the majorant to vanish on a nonempty
component family. At `s = a` the exponential weight is one. On intervals shorter than one
the concrete amplitudes vanish. For `D = 2` one pays the two derivatives of the cell
operator. This is the Fourier operator-norm bridge; the scalar decay estimate for it
is `QuietDecay.cell_endpoint_bound` (and its integrated-gradient partner
`QuietDecay.cell_weighted_gradient_bound`); the spatial-jet theorem alone does not give the
Fourier norm.

The entrance-norm bookkeeping is purely a statement about
nonnegative sums and suprema, independent of the PDE. At `s = a` the exponential is one;
an interval shorter than one has no admissible unit window. The triangular induction uses
ordinary natural powers in `ℝ≥0∞`, hence `0^0 = 1`, including the diagonal entrance term.
-/

/-- The source simplification remaining after subtracting the weak equations: common
quiet means and the homogeneous triangular difference source. -/
def QuietTriangularSourceStatement (o : Orders) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) : Prop :=
  ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
    (P : Input (ι := ι) (h := h) o CG Cw Cj), QuietTriangularSource P

/-- Cell-amplitude recursion for the homogeneous difference. The trace bound
is supplied separately, in ENNReal so infinite Fourier entrance norms are allowed.
The zero degree amplitude is zero, `H = 0` removes grade coupling, and
`Theta = 0` uses natural powers. -/
def QuietCellAmplitudeStatement (o : Orders) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) : Prop :=
  ∃ κ χ : ℝ, 1 ≤ κ ∧ 1 ≤ χ ∧
    ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, CompleteSpace (h i)] (P : Input (ι := ι) (h := h) o CG Cw Cj)
      (I : ℕ → ℝ≥0∞),
      (∀ hh, hh ≤ o.H → ∀ n, schurSums P.π (cellTrace P hh n) ≤ I hh) →
      QuietDecay.AmpRec P.π o.N o.H (ENNReal.ofReal κ)
        (ENNReal.ofReal χ * ENNReal.ofReal P.Θ) I (cellAmplitude P) (cellTrace P)
        (cellEnvelope P) (cellEnvelope P)
        (fun v u => ENNReal.ofReal χ * ENNReal.ofReal (P.bb v u))

/-- Fourier entrance traces dominate the mixed-cell entrance traces at the same orders.
The zero-th coefficient constituent vanishes at positive degrees, and the original
entrance `a` is retained. No finite-entrance assumption is imposed. -/
def CellEntranceComparisonStatement (o : Orders) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) : Prop :=
  ∃ Ct : ℝ, 1 ≤ Ct ∧
    ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, CompleteSpace (h i)] (P : Input (ι := ι) (h := h) o CG Cw Cj),
      ∀ hh, hh ≤ o.H → ∀ n,
        schurSums P.π (cellTrace P hh n) ≤ ENNReal.ofReal Ct *
          entranceNorm P.π (liftDiff P.Cc P.Cc') hh o.N o.entranceSlow o.entranceFast P.a

/-- Conversion of the cell amplitudes to the literal Fourier unit-window norm.
At `s = a` the exponential is one; windows shorter than one are vacuous.
Four excess fast orders pay the Fourier conversion; no Fourier decay is reproved. -/
def CellWindowComparisonStatement (o : Orders) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) : Prop :=
  ∃ Cf : ℝ, 1 ≤ Cf ∧
    ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, CompleteSpace (h i)] (P : Input (ι := ι) (h := h) o CG Cw Cj),
      ∀ hh, hh ≤ o.H → ∀ s, P.a ≤ s → s + 1 ≤ P.b →
        layerNorm P.π (liftDiff P.Cc P.Cc') hh o.N o.K o.L (Set.Icc s (s + 1)) ≤
          ENNReal.ofReal Cf * QuietDecay.decayF P.a s *
            QuietDecay.gradeSum P.π (cellAmplitude P) hh o.N

end AVRegularity.Construction.Preservation.PositiveLayer
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.PositiveLayer

/-! The actual lift difference satisfies the difference weak equation on the whole quiet
window, with its original entrance value. Subtracting raw weak jets avoids imposing a lower
bound on the stored classical fast order. Quiet source simplification is a separate input.

The degenerate cases are included: `H = 0, n = 1` is the initial homogeneous equation; the algebra
here also applies to higher grades/degrees with their actual difference sources. `Θ = 0`, singleton,
empty, identity metrics and `D = 2` require no changes. The equation holds from `a`, even
when `s = a`; short intervals cause no difficulty. This step neither invokes nor modifies
the held atlas identities.
-/

variable {ι : Type} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}

/-- Subtraction and restriction of the actual equations, without a positive stored order. -/
theorem quiet_difference_equation (P : Input (ι := ι) (h := h) o CG Cw Cj) :
    DifferenceEquation P := by
  intro hh hhH n hn hnN f hf X ℓ
  let c : ℝ → Vec 2 → ∀ i, h i := fun t z => liftApply n (P.Cc hh n) (fun _ => f) t X z
  let c' : ℝ → Vec 2 → ∀ i, h i := fun t z => liftApply n (P.Cc' hh n) (fun _ => f) t X z
  have h1 := P.sequence.2.2.2.2.2.2 hh hhH n hn hnN f hf X
  have h2 := P.sequence'.2.2.2.2.2.2 hh hhH n hn hnN f hf X
  have hold : Icc P.a P.b ⊆ Icc P.sOld P.s₁ :=
    Icc_subset_Icc (P.starts.trans P.new_le) P.end_le
  have hnew : Icc P.a P.b ⊆ Icc P.sNew P.s₁ := Icc_subset_Icc P.new_le P.end_le
  have S1 := cellSolution_restrict hold ordConnected_Icc (h1.2 ℓ).1
  have S2 := cellSolution_restrict hnew ordConnected_Icc (h2.2 ℓ).1
  have S := cellSolution_add S1 (cellSolution_smul S2 (-1))
  refine ⟨?_, ?_⟩
  · exact cellSolution_source_congr_sections _ _ _ _ _ _ _
      (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun z => by
        simp only [Pi.add_apply, neg_one_smul, Pi.neg_apply, sub_eq_add_neg,
          map_add, map_neg, Complex.ofReal_add, Complex.ofReal_neg])
      (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun z => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_zero, add_zero]) S
  · intro t ht
    let : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
      InitialLayer.isFiniteMeasure_unitCube
    have hi1 := ((S1.2.2.1 t ht).1).integrable one_le_two
    have hi2 := ((S2.2.2.1 t ht).1).integrable one_le_two
    have hm1 := (h1.2 ℓ).2.1 t (hold ht)
    have hm2 := (h2.2 ℓ).2.1 t (hnew ht)
    have hv : cellValue (differenceJet P hh n f X ℓ) t =
        fun z => cellValue (cellJetOfField ℓ c) t z - cellValue (cellJetOfField ℓ c') t z := by
      funext z
      simp only [differenceJet, cellValue, Pi.add_apply, neg_one_smul, Pi.neg_apply,
        sub_eq_add_neg, c, c']
    unfold cellMean at hm1 hm2 ⊢
    rw [hv, integral_sub hi1 hi2, hm1, hm2, sub_zero]

end AVRegularity.Construction.Preservation.PositiveLayer
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.PositiveLayer

/-! Pointwise operator and Fourier bounds used to convert the quiet cell amplitudes.
The Sobolev step retains the pointwise estimate before its last cell integral. No decay estimate is reproved.
Two fast derivatives pay the Sobolev step; zero and infinite bounds use the same estimate. -/

open QuietDecay
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The pointwise operator version of the mixed-cell Sobolev estimate. -/
theorem positive_layer_word_operator_bound
    {f : Vec 2 → Vec 2 → (E →L[ℝ] F)} {sX sZ p q : ℕ}
    (hf : IsBoxSmooth sX sZ f) (hper : ∀ X, AVenhance.IsZ2Periodic (f X))
    (hp : p + 1 ≤ sX) (hq : q + 2 ≤ sZ) {B : ℝ≥0∞}
    (hB : ∀ (X : Vec 2) (l mm : List (Fin 2)), l.length = p → mm.length ≤ q + 2 →
      ∀ η : E, ‖η‖ ≤ 1 → vecJ (fun X z => f X z η) X l mm ≤ B)
    (X : Vec 2) (α : DerivativeWord2 p) (β : DerivativeWord2 q) (z : Vec 2) :
    ‖orderedDerivative α (fun X' => orderedDerivative β (f X') z) X‖ₑ ≤ 28 * B := by
  set W : Vec 2 → (E →L[ℝ] F) := fun z => orderedDerivative α
    (fun X' => orderedDerivative β (f X') z) X with hW
  -- the pointwise bound on the vectors
  have hvec : ∀ z (η : E), ‖η‖ ≤ 1 → ‖W z η‖ₑ ≤ 28 * B := by
    intro z η hη
    set l := List.ofFn α
    set mm := List.ofFn β
    have hl : l.length = p := List.length_ofFn
    have hmm : mm.length = q := List.length_ofFn
    set g : Vec 2 → F := fastDerivs mm (slowDerivs l (fun X z => f X z η) X) with hg
    have hgW : ∀ z, g z = W z η := fun z => by
      rw [hg, fastDerivs_slowDerivs_apply hf l mm (by omega) (by omega) X z η]
      rfl
    have hfη : IsBoxSmooth sX sZ (fun X z => f X z η) :=
      hf.clm_comp (ContinuousLinearMap.apply ℝ F η)
    have hBs : IsBoxSmooth (sX - l.length + l.length) sZ (fun X z => f X z η) := by
      rwa [Nat.sub_add_cancel (by omega)]
    have hcd : ContDiff ℝ (sZ : ℕ∞) (slowDerivs l (fun X z => f X z η) X) := by
      have := (isBoxSmooth_slowIter l _ _ hBs).1 X
      rwa [slowIter_eq_slowDerivs] at this
    have hg2 : ContDiff ℝ 2 g := by
      have : ContDiff ℝ ((2 + mm.length : ℕ) : ℕ∞) (slowDerivs l (fun X z => f X z η) X) :=
        hcd.of_le (by exact_mod_cast (by omega))
      exact_mod_cast contDiff_fastDerivsE (k := 2) mm this
    have hgp : AVenhance.IsZ2Periodic g := by
      have hpη : ∀ X', AVenhance.IsZ2Periodic (fun z => f X' z η) := fun X' nn z => by
        simp only [hper X' nn z]
      have h1 := periodic_slowIter l _ hpη X
      have h2 := periodic_fastIter mm (slowIter l (fun X z => f X z η)) (periodic_slowIter l _ hpη) X
      rw [fastIter_eq_fastDerivs, slowIter_eq_slowDerivs] at h2
      exact h2
    have hS := periodic_sup_le_sobolev hg2 hgp z
    rw [← hgW z]
    refine hS.trans ?_
    rw [mul_comm 28 B, show (28 : ℝ≥0∞) = 4 * 7 by norm_num, mul_comm B, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [← sum_words_three_le B, mul_comm] at *
    refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun γ _ => ?_
    have hk3 : k ≤ 2 := by have := Finset.mem_range.1 hk; omega
    have e : orderedDerivative γ g = fastDerivs (mm ++ List.ofFn γ) (slowDerivs l (fun X z => f X z η) X) := by
      rw [fastDerivs_append, FastJets.orderedDerivative_eq_odL]
      rfl
    rw [e]
    have hv := hB X l (mm ++ List.ofFn γ) hl (by simp [hmm]; omega) η hη
    unfold vecJ at hv
    have hc : Continuous (fastDerivs (mm ++ List.ofFn γ) (slowDerivs l (fun X z => f X z η) X)) := by
      have : ContDiff ℝ ((0 + (mm ++ List.ofFn γ).length : ℕ) : ℕ∞)
          (slowDerivs l (fun X z => f X z η) X) :=
        hcd.of_le (by exact_mod_cast (by simp [hmm]; omega))
      exact (contDiff_fastDerivsE (k := 0) _ this).continuous
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hc.aestronglyMeasurable] at hv
    simpa [ENNReal.toReal_ofNat] using hv
  -- operator norms
  rcases eq_or_ne B ⊤ with hBt | hBt
  · simp [hBt]
  have hfin : 28 * B ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hBt
  have hop : ∀ z, ‖W z‖ₑ ≤ 28 * B := by
    intro z
    have hM : ∀ η : E, ‖W z η‖ ≤ (28 * B).toReal * ‖η‖ := by
      intro η
      rcases eq_or_ne η 0 with h0 | h0
      · simp [h0]
      have hn : 0 < ‖η‖ := norm_pos_iff.2 h0
      have hu : ‖‖η‖⁻¹ • η‖ ≤ 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 := hvec z (‖η‖⁻¹ • η) hu
      have h2 : ‖W z (‖η‖⁻¹ • η)‖ ≤ (28 * B).toReal := by
        rw [← ofReal_norm] at h1
        exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1
      rw [ContinuousLinearMap.map_smul, norm_smul, norm_inv, norm_norm] at h2
      have := (inv_mul_le_iff₀ hn).1 h2
      linarith
    have := ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg hM
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal this).trans (le_of_eq (ENNReal.ofReal_toReal hfin))
  exact hop z

/-- Vector cell-word bounds control the full mixed Fréchet jet of the operator.
Only the fixed two-dimensional word counts enter the constant. -/
theorem positive_layer_mixed_operator_bound
    {f : Vec 2 → Vec 2 → (E →L[ℝ] F)} {sX sZ P Q : ℕ}
    (hf : IsBoxSmooth sX sZ f) (hper : ∀ X, AVenhance.IsZ2Periodic (f X))
    (hP : P + 1 ≤ sX) (hQ : Q + 2 ≤ sZ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (X : Vec 2) (l mm : List (Fin 2)), l.length ≤ P → mm.length ≤ Q + 2 →
      ∀ η : E, ‖η‖ ≤ 1 → vecJ (fun X z => f X z η) X l mm ≤ ENNReal.ofReal B)
    {p q : ℕ} (hp : p ≤ P) (hq : q ≤ Q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ ≤
      2 ^ (P + Q) * (28 * B) := by
  have hw (α : DerivativeWord2 p) (β : DerivativeWord2 q) :
      ‖orderedDerivative α (fun X' => orderedDerivative β (f X') z) X‖ ≤ 28 * B := by
    have h := positive_layer_word_operator_bound hf hper (by omega) (by omega)
      (fun X l mm hl hm η hη => hB X l mm (by omega) (by omega) η hη) X α β z
    rw [show (28 : ℝ≥0∞) = ENNReal.ofReal (28 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num), ← ofReal_norm] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num) hB0)).mp h
  have hsum := norm_jetAt_le_sum_words hf (by omega : p ≤ sX) (by omega : q ≤ sZ) X z
  calc
    _ ≤ ∑ _α : DerivativeWord2 p, ∑ _β : DerivativeWord2 q, (28 * B) :=
      hsum.trans (Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hw α β)
    _ = 2 ^ (p + q) * (28 * B) := by
      simp only [Finset.sum_const, Finset.card_univ, DerivativeWord2, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
      ring
    _ ≤ 2 ^ (P + Q) * (28 * B) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega))
        (mul_nonneg (by norm_num) hB0)

/-- A uniform time bound controls the exact unit-window mode energy, including infinite
bounds. The time integral has mass one, so it costs no integrability assumption. -/
theorem positive_layer_modeE_le (ξ : Fin 2 → ℤ) (g : ℝ → ℝ≥0∞) (s : ℝ)
    {B : ℝ≥0∞} (hB : ∀ t ∈ Set.Icc s (s + 1), g t ≤ B) :
    modeE ξ g (Set.Icc s (s + 1)) ≤
      (1 + ENNReal.ofReal (2 * Real.pi * modeLen ξ)) * B := by
  have hi : ∫⁻ t in Set.Icc s (s + 1), g t ^ 2 ≤ B ^ 2 := by
    calc
      _ ≤ ∫⁻ _t in Set.Icc s (s + 1), B ^ 2 :=
        setLIntegral_mono' measurableSet_Icc (fun t ht => pow_le_pow_left' (hB t ht) 2)
      _ = B ^ 2 := by simp [Real.volume_Icc, add_sub_cancel_left]
  have hr : (∫⁻ t in Set.Icc s (s + 1), g t ^ 2) ^ (1 / 2 : ℝ) ≤ B := by
    calc
      _ ≤ (B ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hi (by norm_num)
      _ = B := by rw [← ENNReal.rpow_natCast_mul]; norm_num
  unfold modeE
  calc
    _ ≤ B + ENNReal.ofReal (2 * Real.pi * modeLen ξ) * B :=
      add_le_add (iSup₂_le hB) (mul_le_mul_of_nonneg_left hr zero_le)
    _ = _ := by rw [add_mul, one_mul]

/-- Summing the existing transverse Fourier majorant converts uniform vector cell-word
bounds to the Wiener jet. Only fixed derivative orders enter the constant. -/
theorem positive_layer_wiener_bound
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [CompleteSpace F]
    {f : ℝ → Vec 2 → Vec 2 → (E →L[ℝ] F)} {sX sZ P L : ℕ} {I : Set ℝ}
    (hf : ∀ t ∈ I, IsBoxSmooth sX sZ (f t))
    (hper : ∀ t ∈ I, ∀ X, AVenhance.IsZ2Periodic (f t X))
    (hP : P + 1 ≤ sX) (hL : L + 5 ≤ sZ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ I, ∀ (X : Vec 2) (l mm : List (Fin 2)),
      l.length ≤ P → mm.length ≤ L + 5 →
      ∀ η : E, ‖η‖ ≤ 1 → vecJ (fun X z => f t X z η) X l mm ≤ ENNReal.ofReal B)
    (par : Fin 2) (ht : IsTransverseOn par I f) {r : ℕ} (hr : r ≤ P) :
    wienerJet I (L + 1) r f ≤
      ENNReal.ofReal (4 * (2 ^ r * (2 ^ (P + (L + 3)) * (28 * B))) *
        (CycleComparison.Lift.centeredProfileJetConstant + 1)) := by
  let : MeasurableSpace (E →L[ℝ] F) := borel _
  let : BorelSpace (E →L[ℝ] F) := ⟨rfl⟩
  apply CycleComparison.Lift.vector_transverse_wienerJet_le I P (L + 3) r (L + 1)
    hr (by omega) par f
    (fun t ht => (hf t ht).mono (by omega) (by omega)) ht
    (fun t ht X => CycleComparison.Lift.coordinate_line_periodic _ (hper t ht X) _)
    (fun _ => 2 ^ (P + (L + 3)) * (28 * B)) (fun _ _ => by positivity)
  intro a ha b hb t ht Y z
  exact positive_layer_mixed_operator_bound (hf t ht) (hper t ht) hP (by omega) hB0
    (fun X l mm hl hmm η hη => hB t ht X l mm hl (by omega) η hη) ha hb Y z

private theorem positive_layer_frequency_weight (ξ : Fin 2 → ℤ) (L : ℕ) :
    (1 + modeLen ξ) ^ L * (1 + 2 * Real.pi * modeLen ξ) ≤
      (2 ^ L * (1 + 4 * Real.pi)) *
        (1 + max |(ξ 0 : ℝ)| |(ξ 1 : ℝ)|) ^ (L + 1) := by
  let M : ℝ := max |(ξ 0 : ℝ)| |(ξ 1 : ℝ)|
  have hlen0 : 0 ≤ modeLen ξ := Real.sqrt_nonneg _
  have hM : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  have h0 : |(ξ 0 : ℝ)| ≤ M := le_max_left _ _
  have h1 : |(ξ 1 : ℝ)| ≤ M := le_max_right _ _
  have hsq0 : (ξ 0 : ℝ) ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (ξ 0 : ℝ)) h0 2
  have hsq1 : (ξ 1 : ℝ) ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (ξ 1 : ℝ)) h1 2
  have hlen : modeLen ξ ≤ 2 * M := by
    unfold modeLen
    rw [Real.sqrt_le_iff]
    refine ⟨mul_nonneg (by norm_num) hM, ?_⟩
    simp only [Fin.sum_univ_two]
    nlinarith only [hsq0, hsq1, sq_nonneg M]
  have hw : (1 + modeLen ξ) ^ L ≤ 2 ^ L * (1 + M) ^ L := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hlen]) L
  have hc : 1 + 2 * Real.pi * modeLen ξ ≤ (1 + 4 * Real.pi) * (1 + M) := by
    calc
      _ ≤ 1 + 2 * Real.pi * (2 * M) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hlen
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le))
      _ = 1 + 4 * Real.pi * M := by ring
      _ ≤ (1 + M) + 4 * Real.pi * (1 + M) :=
        add_le_add (le_add_of_nonneg_right hM)
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity))
      _ = _ := by ring
  calc
    _ ≤ (2 ^ L * (1 + M) ^ L) * ((1 + 4 * Real.pi) * (1 + M)) :=
      mul_le_mul hw hc (by positivity) (by positivity)
    _ = _ := by dsimp [M]; rw [pow_succ]; ring

/-- The literal Fourier unit-window energy is bounded by one additional Wiener power.
The supremum over time stays inside each coefficient entry throughout. -/
theorem positive_layer_window_fourier_le_wiener
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (f : ℝ → Vec 2 → Vec 2 → G) (s : ℝ) (L r : ℕ) :
    (∑' ξ : NZMode, ENNReal.ofReal ((1 + modeLen ξ.1) ^ L) *
      ⨆ X, modeE ξ.1 (fun t => modeJet (f t) ξ.1 r X) (Set.Icc s (s + 1))) ≤
      ENNReal.ofReal (2 ^ L * (1 + 4 * Real.pi)) *
        wienerJet (Set.Icc s (s + 1)) (L + 1) r f := by
  let S : (Fin 2 → ℤ) → ℝ≥0∞ := fun ξ =>
    ⨆ t ∈ Set.Icc s (s + 1), ⨆ X, modeJet (f t) ξ r X
  have hb (ξ : Fin 2 → ℤ) (X : Vec 2) :
      modeE ξ (fun t => modeJet (f t) ξ r X) (Set.Icc s (s + 1)) ≤
        (1 + ENNReal.ofReal (2 * Real.pi * modeLen ξ)) * S ξ :=
    positive_layer_modeE_le ξ _ s fun t ht => le_iSup₂_of_le t ht (le_iSup_of_le X le_rfl)
  have hw (ξ : Fin 2 → ℤ) :
      ENNReal.ofReal ((1 + modeLen ξ) ^ L) * (1 + ENNReal.ofReal (2 * Real.pi * modeLen ξ)) ≤
        ENNReal.ofReal (2 ^ L * (1 + 4 * Real.pi)) *
          ENNReal.ofReal ((1 + max |(ξ 0 : ℝ)| |(ξ 1 : ℝ)|) ^ (L + 1)) := by
    have hlen0 : 0 ≤ modeLen ξ := Real.sqrt_nonneg _
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) by norm_num,
      ← ENNReal.ofReal_add (by norm_num) (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (positive_layer_frequency_weight ξ L)
  calc
    _ ≤ ∑' ξ : NZMode, ENNReal.ofReal (2 ^ L * (1 + 4 * Real.pi)) *
        (ENNReal.ofReal ((1 + max |(ξ.1 0 : ℝ)| |(ξ.1 1 : ℝ)|) ^ (L + 1)) * S ξ.1) := by
      apply ENNReal.tsum_le_tsum
      intro ξ
      calc
        _ ≤ ENNReal.ofReal ((1 + modeLen ξ.1) ^ L) *
            ((1 + ENNReal.ofReal (2 * Real.pi * modeLen ξ.1)) * S ξ.1) :=
          mul_le_mul_of_nonneg_left (iSup_le (hb ξ.1)) zero_le
        _ ≤ _ := by rw [← mul_assoc, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (hw ξ.1) zero_le
    _ ≤ ∑' ξ : Fin 2 → ℤ, ENNReal.ofReal (2 ^ L * (1 + 4 * Real.pi)) *
        (ENNReal.ofReal ((1 + max |(ξ 0 : ℝ)| |(ξ 1 : ℝ)|) ^ (L + 1)) * S ξ) :=
      ENNReal.summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun _ _ => zero_le) (fun _ => le_rfl) ENNReal.summable
    _ = _ := by rw [ENNReal.tsum_mul_left]; rfl

end AVRegularity.Construction.Preservation.PositiveLayer
end
