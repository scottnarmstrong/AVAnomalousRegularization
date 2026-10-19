-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.SourceZeroMean
import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
public import AVRegularity.CycleComparison.Lift.LeftTerm
public import AVRegularity.CycleEvolution.TimeEnergy
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Each factorial-weighted physical mean coefficient jet has the same dimensional bound. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)



include P in
theorem setting_dimensional_schur_term (b₀ : MeanCoeff ι h) (C : ℝ) (hC : 0 ≤ C)
    (hΘ : 0 ≤ Θ) (hh n d r : ℕ) (hn : 2 ≤ n) (hd : d ≤ n)
    (hreg : ∀ α k₀ v u, ∀ t ∈ Set.Icc a b,
      ContDiff ℝ (r : ℕ∞) (fun X => b₀ d α t X k₀ v u))
    (hbound : schurSlowJet π (Set.Icc a b) r
      (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ => b₀ d p.1 t X p.2) ≤
        ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - d + r))) :
    ENNReal.ofReal (E ^ r / (r.factorial : ℝ)) *
      schurSlowJet π (Set.Icc (ℓ ^ 2 * a) (ℓ ^ 2 * b)) r
        (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ =>
          scaledMeanCoefficient ((ℓ ^ 2)⁻¹ * εc ^ n) ρ (fun t => t / ℓ ^ 2) b₀ d p.1 t X p.2) ≤
      ENNReal.ofReal (C * Θ ^ hh * B * dstar ^ (n - 2) * (E ^ d / E ^ n)) := by
  let T := (ℓ ^ 2)⁻¹ * εc ^ n * ρ ^ d
  have heps : 0 < εc := by rw [P.εc_eq]; exact div_pos (setting_dstar_pos P) P.ρ_pos
  have hT : 0 ≤ T := mul_nonneg
    (mul_nonneg (inv_nonneg.2 (sq_nonneg ℓ)) (pow_nonneg heps.le n)) (pow_nonneg P.ρ_pos.le d)
  have hinv : 0 ≤ ρ⁻¹ := inv_nonneg.2 P.ρ_pos.le
  have hfactor : 1 ≤ (r.factorial : ℝ) := by exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos r)
  have hw : 0 ≤ E ^ r / (r.factorial : ℝ) := div_nonneg (pow_nonneg P.E_pos.le r) (by positivity)
  have hs := scaledMeanCoefficient_schurSlowJet_le π (Set.Icc a b)
    (Set.Icc (ℓ ^ 2 * a) (ℓ ^ 2 * b)) (fun t => t / ℓ ^ 2)
    (fun t ht => setting_physical_time_mem P t ht) ((ℓ ^ 2)⁻¹ * εc ^ n) ρ b₀ d r hreg
  have hs' := hs.trans (mul_le_mul' le_rfl hbound)
  have he := mul_le_mul' (le_refl (ENNReal.ofReal (E ^ r / (r.factorial : ℝ)))) hs'
  change _ ≤ ENNReal.ofReal (E ^ r / (r.factorial : ℝ)) *
    (ENNReal.ofReal (|T| * |ρ⁻¹| ^ r) * ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - d + r))) at he
  simp only [abs_of_nonneg hT, abs_of_nonneg hinv] at he
  apply he.trans
  rw [← ENNReal.ofReal_mul (mul_nonneg hT (pow_nonneg hinv r)),
    ← ENNReal.ofReal_mul hw]
  apply ENNReal.ofReal_le_ofReal
  have hid : (E ^ r / (r.factorial : ℝ)) * (T * ρ⁻¹ ^ r *
      (C * Θ ^ hh * lam ^ (n - d + r))) =
      (C * Θ ^ hh * B * dstar ^ (n - 2) * (E ^ d / E ^ n)) / (r.factorial : ℝ) := by
    calc
      _ = (C * Θ ^ hh / (r.factorial : ℝ)) *
          (E ^ r * T * ρ⁻¹ ^ r * lam ^ (n - d + r)) := by ring
      _ = _ := by rw [setting_dimensional_scale_identity P n d r hn hd]; ring
  rw [hid]
  apply div_le_self _ hfactor
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC (pow_nonneg hΘ hh)) P.B_pos.le)
    (pow_nonneg (setting_dstar_pos P).le (n - 2)))
    (div_nonneg (pow_nonneg P.E_pos.le d) (pow_nonneg P.E_pos.le n))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A field independent of the fast variable has any fast reserve under its original slow regularity. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isBoxSmooth_slow_field (p q : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (p : ℕ∞) f) : IsBoxSmooth p q (fun X _ => f X) := by
  rw [isBoxSmooth_iff]
  refine ⟨fun _ => contDiff_const, fun b _ => ?_⟩
  have hs : IsSlowSmooth p (fun X _ => f X) :=
    ⟨fun _ => hf, fun a ha => (hf.continuous_iteratedFDeriv (by exact_mod_cast ha)).comp continuous_fst⟩
  cases b with
  | zero =>
    have he : (fun X z => iteratedFDeriv ℝ 0 (fun _ : Vec 2 => f X) z) =
        fun X _ => (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm (f X) := rfl
    rw [he]
    exact isSlowSmooth_clm_comp
      (G := ContinuousMultilinearMap ℝ (fun _ : Fin 0 => Vec 2) E)
      (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm.toLinearIsometry.toContinuousLinearMap hs
  | succ b =>
    have he : (fun X z => iteratedFDeriv ℝ (b + 1) (fun _ : Vec 2 => f X) z) =
        fun _ _ => 0 := by
      funext X z
      rw [iteratedFDeriv_succ_const]
      rfl
    rw [he]
    exact IsSlowSmooth.zero

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set AVenhance.Infra.ODE AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The compiled Fourier ODE gives the genuine strong time representative whenever its actual right-hand side is integrable. -/

theorem complexIntegralSolution_strongTime {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → ℂ →L[ℝ] ℂ) (f c : ℝ → ℂ) (c₀ : ℂ)
    (hc : IsLinearIntegralSolution A f c₀ a b c)
    (hrhs : IntervalIntegrable (linearRhs A f c) volume a b) :
    StrongTimeRegularity a b c (linearRhs A f c) := by
  apply complexStrongTime_of_primitive hab c (linearRhs A f c) hrhs
  have ha : c a = c₀ := by
    simpa only [intervalIntegral.integral_same, add_zero] using hc a ⟨le_rfl, hab⟩
  intro t ht
  rw [ha]
  exact hc t ht

theorem profileModeResponse_strongTime (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a b : ℝ) (hab : a ≤ b) (M : ℝ) (hM : 0 ≤ M)
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, |g t| ≤ M)
    (hfm : Measurable (Function.uncurry f)) (C : ℝ)
    (hfb : ∀ t ∈ uIcc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖f t x‖ ≤ C) (n : ℤ)
    (hrhs : IntervalIntegrable
      (fun t => (-(‖profileFourierFrequency n‖ ^ 2) * g t) • profileModeResponse g f a t n +
        unitProfileFourierCoeff (f t) n) volume a b) :
    StrongTimeRegularity a b (fun t => profileModeResponse g f a t n)
      (fun t => (-(‖profileFourierFrequency n‖ ^ 2) * g t) • profileModeResponse g f a t n +
        unitProfileFourierCoeff (f t) n) := by
  have hs := (profileModeResponse_solves g f a b hab M hM hgm hgb hfm C hfb n).1
  exact complexIntegralSolution_strongTime hab _ _ _ 0 hs hrhs

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! A cell-independent input has no parameter-degree-zero source. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceCoeff_zero_independent (edge : ConstituentEdges D h) (η t : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (D : ℕ∞) f)
    (hfast : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X, ContDiff ℝ 1 (γ.coeff α t X))
    (hslow : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ 1 (fun X => γ.coeff α t X z)) (X z : Vec 2) :
    sourceCoeff edge η 0 t (fun X _ => f X) X z = 0 := by
  simp only [sourceCoeff, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, iteratedDeriv_zero]
  rw [sourceOp_independent_expand edge η 0 t f hf hfast hslow X z]
  apply Finset.sum_eq_zero
  intro d _
  have hd := (Finset.mem_Icc.mp d.2).1
  simp [zero_pow (by omega : d.val - 1 ≠ 0), zero_pow (by omega : d.val ≠ 0)]
end

/-! Positive fast primitive words are literal transverse source words. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem orderedDerivative_transverse_primitive_source_word
    (p : Fin 2) (m : ℕ) (α : DerivativeWord2 (m + 1)) (f : Vec 2 → E)
    (hf : ContDiff ℝ (m : ℕ∞) f)
    (hfactor : ∀ z, f z = f ((z p) • basisVec p)) :
    orderedDerivative α (fun z : Vec 2 =>
      centeredIntervalPrimitive (fun r => f (r • basisVec p)) (z p)) =
      fun z => if (∀ i, α i = p) then
        orderedDerivative (fun _ : Fin m => p) f z else 0 := by
  let line : ℝ →L[ℝ] Vec 2 := (ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec p)
  have hprofile : ContDiff ℝ (m : ℕ∞) (fun r : ℝ => f (r • basisVec p)) :=
    hf.comp line.contDiff
  have he : f = fun z => f ((z p) • basisVec p) := funext hfactor
  have hword : orderedDerivative (fun _ : Fin m => p) f =
      fun z => iteratedDeriv m (fun r : ℝ => f (r • basisVec p)) (z p) := by
    conv_lhs => rw [he]
    funext z
    exact (congrFun (orderedDerivative_transverse_profile
      (fun _ : Fin m => p) (fun r : ℝ => f (r • basisVec p)) hprofile p) z).trans
        (ite_eq_left (fun _ => rfl))
  rw [orderedDerivative_centeredIntervalPrimitive_profile_succ m α _ hprofile p, hword]
end

/-! On coarse inputs the first source coefficient is only an order-two fast divergence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceCoeff_one_independent (edge : ConstituentEdges D h) (η t : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (D : ℕ∞) f)
    (hfast : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X, ContDiff ℝ 1 (γ.coeff α t X))
    (hslow : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ 1 (fun X => γ.coeff α t X z)) (X z : Vec 2) :
    sourceCoeff edge η 1 t (fun X _ => f X) X z =
      ∑ d : Finset.Icc 2 D, (if d.1 = 2 then
        ∑ q : Fin 2, fastPartial q (slowSourceFluxOrder edge η t f d q) X z else 0) := by
  have he := funext (fun ε => sourceOp_independent_expand edge η ε t f hf hfast hslow X z)
  have hh : HasDerivAt (fun ε : ℝ => sourceOp edge η ε t (fun X _ => f X) X z)
      (∑ d : Finset.Icc 2 D, (if d.1 = 2 then
        ∑ q : Fin 2, fastPartial q (slowSourceFluxOrder edge η t f d q) X z else 0)) 0 := by
    rw [he]
    apply HasDerivAt.fun_sum
    intro d _
    have hd : 2 ≤ d.1 := (Finset.mem_Icc.mp d.2).1
    have hfirst := hasDerivAt_power_smul_zero (d.1 - 1) (by omega)
      (∑ q : Fin 2, fastPartial q (slowSourceFluxOrder edge η t f d q) X z)
    have hsecond := hasDerivAt_power_smul_zero d.1 (by omega)
      (Real.sqrt η • ∑ q : Fin 2, slowPartial q (slowSourceFluxOrder edge η t f d q) X z)
    have hnot : d.1 ≠ 1 := by omega
    have hiff : d.1 - 1 = 1 ↔ d.1 = 2 := by omega
    simpa only [ite_eq_right hnot, add_zero, hiff] using hfirst.fun_add hsecond
  simpa only [sourceCoeff, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    iteratedDeriv_one] using hh.deriv
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Products of rectangularly smooth fields retain both original derivative reserves. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem isBoxSmooth_comp_smooth {p q : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth p q f) (g : E → F) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    IsBoxSmooth p q (fun X z => g (f X z)) :=
  isBoxSmooth_comp_of_jet_regularities hf g (hg.of_le (by simp))
    (fun b _ => hg.iteratedFDeriv_right (by simp))

theorem isBoxSmooth_pair {p q : ℕ} {f : Vec 2 → Vec 2 → E} {g : Vec 2 → Vec 2 → F}
    (hf : IsBoxSmooth p q f) (hg : IsBoxSmooth p q g) :
    IsBoxSmooth p q (fun X z => (f X z, g X z)) := by
  have h := (hf.clm_comp (ContinuousLinearMap.inl ℝ E F)).add
    (hg.clm_comp (ContinuousLinearMap.inr ℝ E F))
  simpa only [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk, add_zero, zero_add] using! h

theorem isBoxSmooth_bilinear {p q : ℕ} {f : Vec 2 → Vec 2 → E}
    {g : Vec 2 → Vec 2 → F} (hf : IsBoxSmooth p q f) (hg : IsBoxSmooth p q g)
    (T : E →L[ℝ] F →L[ℝ] G) : IsBoxSmooth p q (fun X z => T (f X z) (g X z)) := by
  have hT : ContDiff ℝ (⊤ : ℕ∞) (fun x : E × F => T x.1 x.2) :=
    (T.contDiff.comp contDiff_fst).clm_apply contDiff_snd
  exact isBoxSmooth_comp_smooth (isBoxSmooth_pair hf hg) _ hT
end

/-! Window-only box reserves and mixed bounds give global reserves for clamped scalar profiles. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem clamped_linear_profile_slow_reserve (p q j : ℕ) (hj : j ≤ q)
    (a b : ℝ) (hab : a ≤ b) (k : Fin 2)
    (f : ℝ → Vec 2 → Vec 2 → E)
    (hf : ∀ t ∈ Set.Icc a b, IsBoxSmooth p q (f t))
    (l : E →L[ℝ] ℝ) (t x : ℝ) :
    ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j
      (fun y => ((l (f (Set.projIcc a b hab t) X (y • basisVec k)) : ℝ) : ℂ)) x) := by
  exact linear_profile_iteratedDeriv_slow_contDiff p q j hj
    (fun X z => ((l (f (Set.projIcc a b hab t) X z) : ℝ) : ℂ))
    (((hf _ (Set.projIcc a b hab t).2).clm_comp l).clm_comp Complex.ofRealCLM)
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec k)) x

theorem clamped_linear_profile_mixed_bound (p q r j δ : ℕ)
    (hr : r ≤ p) (hj : j ≤ q) (a b : ℝ) (hab : a ≤ b) (k : Fin 2)
    (f : ℝ → Vec 2 → Vec 2 → E)
    (hf : ∀ t ∈ Set.Icc a b, IsBoxSmooth p q (f t))
    (S lam : ℝ)
    (hb : ∀ t ∈ Set.Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤
        S * lam ^ (δ + r))
    (l : E →L[ℝ] ℝ) (t x : ℝ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j
      (fun y => ((l (f (Set.projIcc a b hab t) Y (y • basisVec k)) : ℝ) : ℂ)) x) X‖ ≤
      (S * ‖l‖) * lam ^ (δ + r) := by
  have h := norm_mixed_complexified_linear_profile_le p q r j hr hj
    (f (Set.projIcc a b hab t)) (hf _ (Set.projIcc a b hab t).2)
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec k)) l X x
  rw [cell_coordinate_line_norm, one_pow, mul_one] at h
  apply h.trans
  have hh := mul_le_mul_of_nonneg_left
    (hb _ (Set.projIcc a b hab t).2 X (x • basisVec k)) (norm_nonneg l)
  simpa only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    mul_assoc, mul_comm S ‖l‖] using hh
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Actual Fourier forcing and the measurable scalar ODE right-hand side are bounded on each time window. -/

theorem unitProfileFourierCoeff_time_memLp_top (f : ℝ → ℝ → ℂ)
    (hf : Measurable (Function.uncurry f)) (a b C : ℝ)
    (hb : ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖f t x‖ ≤ C) (n : ℤ) :
    MemLp (fun t => unitProfileFourierCoeff (f t) n) ⊤ (volume.restrict (Icc a b)) := by
  apply MemLp.of_bound (unitProfileFourierCoeff_time_measurable f hf n).aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact unitProfileFourierCoeff_norm_le (f t) n C (hb t ht)

theorem profileModeResponse_time_memLp_top (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a b : ℝ) (hab : a ≤ b) (M : ℝ) (hM : 0 ≤ M)
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, |g t| ≤ M)
    (hfm : Measurable (Function.uncurry f)) (C : ℝ)
    (hfb : ∀ t ∈ uIcc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖f t x‖ ≤ C) (n : ℤ) :
    MemLp (fun t => profileModeResponse g f a t n) ⊤ (volume.restrict (Icc a b)) := by
  have ha := (profileModeResponse_solves g f a b hab M hM hgm hgb hfm C hfb n).2
  have hc : ContinuousOn (fun t => profileModeResponse g f a t n) (Icc a b) := by
    simpa only [uIcc_of_le hab] using ha.continuousOn
  obtain ⟨R, hR⟩ := ha.exists_bound
  apply MemLp.of_bound (hc.aestronglyMeasurable measurableSet_Icc) R
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hR t (by simpa only [uIcc_of_le hab] using ht)

theorem scalarModeRhs_memLp_top {a b : ℝ} (rate : ℝ) (g : ℝ → ℝ) (c f : ℝ → ℂ)
    (hg : MemLp g ⊤ (volume.restrict (Icc a b)))
    (hc : MemLp c ⊤ (volume.restrict (Icc a b)))
    (hf : MemLp f ⊤ (volume.restrict (Icc a b))) :
    MemLp (fun t => (-rate * g t) • c t + f t) ⊤ (volume.restrict (Icc a b)) := by
  have hgc : MemLp ((fun t => (-rate) • g t) • c) ⊤ (volume.restrict (Icc a b)) :=
    (hg.const_smul (-rate)).smul hc
  simpa only [Pi.smul_def', smul_eq_mul, Pi.add_def] using hgc.add hf

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Summing finitely many factorial weights restores the dimensional mean coefficient estimate. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)




include P in
theorem setting_dimensional_factorial_bound (b₀ : MeanCoeff ι h) (C : ℝ) (hC : 0 ≤ C)
    (hΘ : 0 ≤ Θ) (hh n d : ℕ) (hn : 2 ≤ n) (hd : d ≤ n)
    (hreg : ∀ α k₀ v u, ∀ t ∈ Set.Icc a b,
      ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (fun X => b₀ d α t X k₀ v u))
    (hbound : ∀ r, r ≤ K → schurSlowJet π (Set.Icc a b) r
      (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ => b₀ d p.1 t X p.2) ≤
        ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - d + r))) :
    schurFactorialJet π (Set.Icc (ℓ ^ 2 * a) (ℓ ^ 2 * b)) E K
      (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ =>
        scaledMeanCoefficient ((ℓ ^ 2)⁻¹ * εc ^ n) ρ (fun t => t / ℓ ^ 2) b₀ d p.1 t X p.2) ≤
      ENNReal.ofReal (((K + 1 : ℕ) : ℝ) * C * Θ ^ hh * B * dstar ^ (n - 2) * (E ^ d / E ^ n)) := by
  let R := C * Θ ^ hh * B * dstar ^ (n - 2) * (E ^ d / E ^ n)
  have hR : 0 ≤ R := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg hC (pow_nonneg hΘ hh)) P.B_pos.le)
      (pow_nonneg (setting_dstar_pos P).le (n - 2)))
    (div_nonneg (pow_nonneg P.E_pos.le d) (pow_nonneg P.E_pos.le n))
  apply (schurFactorialJet_le_sum π _ E K _).trans
  calc
    _ ≤ ∑ r ∈ Finset.range (K + 1), ENNReal.ofReal R := by
      apply Finset.sum_le_sum
      intro r hr
      have hrK : r ≤ K := by have := Finset.mem_range.mp hr; omega
      exact setting_dimensional_schur_term P b₀ C hC hΘ hh n d r hn hd
        (fun α k₀ v u t ht => (hreg α k₀ v u t ht).of_le
          (by exact_mod_cast (show r ≤ K + 1 by omega))) (hbound r hrK)
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hR)]
      congr 1
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, R]
      ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The fast derivative of a rectangular bilinear product splits into its two literal factors. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem fastPartial_bilinear_box {p q : ℕ} {f : Vec 2 → Vec 2 → E}
    {g : Vec 2 → Vec 2 → F} (hf : IsBoxSmooth p (q + 1) f)
    (hg : IsBoxSmooth p (q + 1) g) (T : E →L[ℝ] F →L[ℝ] G) (k : Fin 2) :
    fastPartial k (fun X z => T (f X z) (g X z)) = fun X z =>
      T (fastPartial k f X z) (g X z) + T (f X z) (fastPartial k g X z) := by
  funext X z
  simp only [fastPartial]
  rw [T.fderiv_of_bilinear ((hf.1 X).differentiable (by simp) z)
    ((hg.1 X).differentiable (by simp) z)]
  simp only [add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, add_comm]
end

/-! Finite coefficient sums and plain finite component vectors preserve rectangular jets. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isBoxSmooth_list_sum {α : Type*} (l : List α) (p q : ℕ)
    (f : α → Vec 2 → Vec 2 → E) (hf : ∀ a ∈ l, IsBoxSmooth p q (f a)) :
    IsBoxSmooth p q (fun X z => (l.map fun a => f a X z).sum) := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil] using (IsBoxSmooth.zero (sX := p) (sZ := q) (E := E))
  | cons a l ih =>
    have ha := hf a (List.mem_cons_self)
    have hl := ih (fun b hb => hf b (List.mem_cons_of_mem a hb))
    simpa only [List.map_cons, List.sum_cons] using! ha.add hl

theorem isBoxSmooth_pi {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    (p q : ℕ) (f : Vec 2 → Vec 2 → ∀ i, h i)
    (hf : ∀ i, IsBoxSmooth p q (fun X z => f X z i)) : IsBoxSmooth p q f := by
  classical
  have he : f = fun X z => ∑ i, (ContinuousLinearMap.single ℝ h i) (f X z i) := by
    funext X z
    ext j
    simp [Finset.sum_apply]
  rw [he]
  exact IsBoxSmooth.sum Finset.univ fun i _ =>
    (hf i).clm_comp (ContinuousLinearMap.single ℝ h i)
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Pointwise time measurability and reserved fast continuity yield measurable clamped profiles. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem clamped_linear_profile_fast_reserve (p q : ℕ)
    (a b : ℝ) (hab : a ≤ b) (k : Fin 2)
    (f : ℝ → Vec 2 → Vec 2 → E)
    (hf : ∀ t ∈ Set.Icc a b, IsBoxSmooth p q (f t))
    (l : E →L[ℝ] ℝ) (t : ℝ) (X : Vec 2) :
    ContDiff ℝ (q : ℕ∞)
      (fun y : ℝ => ((l (f (Set.projIcc a b hab t) X (y • basisVec k)) : ℝ) : ℂ)) := by
  exact Complex.ofRealCLM.contDiff.comp (l.contDiff.comp
    (((hf _ (Set.projIcc a b hab t).2).1 X).comp
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec k)).contDiff))

theorem clamped_linear_profile_joint_measurable (p q : ℕ)
    (a b : ℝ) (hab : a ≤ b) (k : Fin 2)
    (f : ℝ → Vec 2 → Vec 2 → E)
    (hf : ∀ t ∈ Set.Icc a b, IsBoxSmooth p q (f t))
    (hm : ∀ l : E →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (l : E →L[ℝ] ℝ) (X : Vec 2) :
    Measurable (fun tx : ℝ × ℝ =>
      ((l (f (Set.projIcc a b hab tx.1) X (tx.2 • basisVec k)) : ℝ) : ℂ)) := by
  have hp := (continuous_projIcc (a := a) (b := b) (h := hab)).measurable.subtype_val
  have hm' : ∀ x : ℝ, Measurable (fun t =>
      ((l (f (Set.projIcc a b hab t) X (x • basisVec k)) : ℝ) : ℂ)) := by
    intro x
    exact Complex.ofRealCLM.continuous.measurable.comp ((hm l X _).comp hp)
  have hh := profile_iteratedDeriv_joint_measurable
    (fun t x => ((l (f (Set.projIcc a b hab t) X (x • basisVec k)) : ℝ) : ℂ))
    hm' q (fun t => clamped_linear_profile_fast_reserve p q a b hab k f hf l t X)
    0 (Nat.zero_le q)
  simpa only [iteratedDeriv_zero] using hh

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A fixed-point exponential majorant keeps its scale power without requiring a global test bound. -/

theorem norm_mixed_slow_exponential_le (p : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam) (a b : ℕ) (ha : a ≤ p) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
      (fun _ : Vec 2 => Real.exp ((lam • A) Y)) z) X‖ ≤
      (Real.exp ((lam • A) X) * (max 1 ‖A‖) ^ p) * lam ^ a := by
  cases b with
  | zero =>
    rw [norm_mixed_fast_zero_eq]
    apply (norm_iteratedFDeriv_exp_linear_scaled_le a A lam hlam X).trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlam a)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact (pow_le_pow_left₀ (norm_nonneg A) (le_max_right 1 ‖A‖) a).trans
      (pow_le_pow_right₀ (le_max_left 1 ‖A‖) ha)
  | succ b =>
    have he : (fun Y => iteratedFDeriv ℝ (b + 1)
        (fun _ : Vec 2 => Real.exp ((lam • A) Y)) z) = fun _ => 0 := by
      funext Y
      rw [iteratedFDeriv_succ_const]
      rfl
    rw [he]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    positivity

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Pointwise time measurability and reserved fast continuity yield measurable clamped profiles. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem clamped_linear_profile_joint_measurable_from_window (p q : ℕ)
    (a b : ℝ) (hab : a ≤ b) (k : Fin 2)
    (f : ℝ → Vec 2 → Vec 2 → E)
    (hf : ∀ t ∈ Set.Icc a b, IsBoxSmooth p q (f t))
    (hm : ∀ l : E →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f (Set.projIcc a b hab t) X z)))
    (l : E →L[ℝ] ℝ) (X : Vec 2) :
    Measurable (fun tx : ℝ × ℝ =>
      ((l (f (Set.projIcc a b hab tx.1) X (tx.2 • basisVec k)) : ℝ) : ℂ)) := by
  have hm' : ∀ x : ℝ, Measurable (fun t =>
      ((l (f (Set.projIcc a b hab t) X (x • basisVec k)) : ℝ) : ℂ)) := by
    intro x
    exact Complex.ofRealCLM.continuous.measurable.comp (hm l X _)
  have hh := profile_iteratedDeriv_joint_measurable
    (fun t x => ((l (f (Set.projIcc a b hab t) X (x • basisVec k)) : ℝ) : ℂ))
    hm' q (fun t => clamped_linear_profile_fast_reserve p q a b hab k f hf l t X)
    0 (Nat.zero_le q)
  simpa only [iteratedDeriv_zero] using hh

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Exponential normalization preserves the original rectangular spatial reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exponential_normalization_box_reserve (p q : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f) :
    IsBoxSmooth p q (fun X z => (Real.exp (A X))⁻¹ • f X z) := by
  have he : (fun X z => (Real.exp (A X))⁻¹ • f X z) =
      fun X z => Real.exp ((-A) X) • f X z := by
    funext X z
    rw [neg_apply, Real.exp_neg]
  rw [he]
  exact isBoxSmooth_bilinear
    (isBoxSmooth_slow_field p q _ (Real.contDiff_exp.comp (-A).contDiff)) hf
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Strong time regularity of the actual Fourier response with all right-hand-side integrability discharged. -/

theorem profileModeResponse_rhs_memLp_top (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a b : ℝ) (hab : a ≤ b) (M : ℝ) (hM : 0 ≤ M)
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, |g t| ≤ M)
    (hfm : Measurable (Function.uncurry f)) (C : ℝ)
    (hfb : ∀ t ∈ uIcc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖f t x‖ ≤ C) (n : ℤ) :
    MemLp (fun t => (-(‖profileFourierFrequency n‖ ^ 2) * g t) • profileModeResponse g f a t n +
      unitProfileFourierCoeff (f t) n) ⊤ (volume.restrict (Icc a b)) := by
  have hg : MemLp g ⊤ (volume.restrict (Icc a b)) :=
    MemLp.of_bound hgm.restrict M (Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs] using hgb t)
  apply scalarModeRhs_memLp_top _ g _ _ hg
    (profileModeResponse_time_memLp_top g f a b hab M hM hgm hgb hfm C hfb n)
  apply unitProfileFourierCoeff_time_memLp_top f hfm a b C _ n
  intro t ht x hx
  exact hfb t (by simpa only [uIcc_of_le hab] using ht) x hx

theorem profileModeResponse_strongTime_actual (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a b : ℝ) (hab : a ≤ b) (M : ℝ) (hM : 0 ≤ M)
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, |g t| ≤ M)
    (hfm : Measurable (Function.uncurry f)) (C : ℝ)
    (hfb : ∀ t ∈ uIcc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖f t x‖ ≤ C) (n : ℤ) :
    StrongTimeRegularity a b (fun t => profileModeResponse g f a t n)
      (fun t => (-(‖profileFourierFrequency n‖ ^ 2) * g t) • profileModeResponse g f a t n +
        unitProfileFourierCoeff (f t) n) := by
  have hr := profileModeResponse_rhs_memLp_top g f a b hab M hM hgm hgb hfm C hfb n
  have hi := hr.integrable (by simp : (1 : ENNReal) ≤ ⊤)
  apply profileModeResponse_strongTime g f a b hab M hM hgm hgb hfm C hfb n
  apply IntegrableOn.intervalIntegrable
  simpa only [uIcc_of_le hab, IntegrableOn] using hi

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Rectangular lift reserves retain the fast order and spend only the tested slow input order. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_box_reserve (n p q : ℕ) (c : LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (hf : ContDiff ℝ ((p + n : ℕ) : ℕ∞) (f t))
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      IsBoxSmooth p q (fun X z => c m α t X z v u)) :
    IsBoxSmooth p q (liftApply n c f t) := by
  apply isBoxSmooth_pi p q
  intro v
  unfold liftApply
  apply IsBoxSmooth.sum
  intro m hm
  apply IsBoxSmooth.sum
  intro α _
  apply IsBoxSmooth.sum
  intro u _
  have hmn : m ≤ n := by have hh := Finset.mem_range.mp hm; omega
  have hslow := isBoxSmooth_slow_field p q (fun X => orderedDerivative α (f t) X u)
    (AVRegularity.contDiff_orderedDerivative_comp hmn α hf u)
  exact isBoxSmooth_bilinear (hc m hmn α v u) hslow
    (ContinuousLinearMap.id ℝ (h u →L[ℝ] h v))

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Uniform Fourier majorants give joint continuity of every supported classical response jet on the time strip. -/

theorem profileCellResponse_iteratedDeriv_joint_continuousOn
    (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (a b κ M : ℝ)
    (hab : a ≤ b) (hκ : 0 < κ) (hi : IntegrableOn g (Icc a b))
    (hg : ∀ s ∈ Icc a b, κ ≤ g s) (hM : 0 ≤ M)
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, |g t| ≤ M)
    (hfm : Measurable (Function.uncurry f)) (q : ℕ) (C : ℕ → ℝ)
    (hC : ∀ j ≤ q, 0 ≤ C j) (hf : ∀ s ∈ Icc a b, ContDiff ℝ q (f s))
    (hp : ∀ s ∈ Icc a b, Function.Periodic (f s) 1)
    (hj : ∀ j ≤ q, ∀ s ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (f s) x‖ ≤ C j)
    (j : ℕ) (hjq : j ≤ q) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv j (profileCellResponse g f a p.1) p.2)
      (Icc a b ×ˢ (Set.univ : Set ℝ)) := by
  have hz (s : ℝ) (hs : s ∈ Icc a b) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      ‖f s y‖ ≤ C 0 := by
    simpa using hj 0 (Nat.zero_le q) s hs y hy
  have hb (l : ℕ) (hl : l ≤ q) (n : ℤ) (t : ℝ) (ht : t ∈ Icc a b) :
      ‖profileFourierFrequency n ^ l * profileModeResponse g f a t n‖ ≤
        profileJetMajorant (C l / κ) (C 0 * (b - a)) n :=
    profileModeResponse_uniform_jet_bound g f a b κ hab hκ hi hg l (C l) (C 0)
      (hC l hl) (hC 0 (Nat.zero_le q))
      (fun s hs => (hf s hs).of_le (by exact_mod_cast hl)) hp (hj l hl) hz n t ht
  have hc (n : ℤ) : ContinuousOn (fun t => profileModeResponse g f a t n) (Icc a b) := by
    have ha := (profileModeResponse_solves g f a b hab M hM hgm hgb hfm (C 0)
      (by simpa only [uIcc_of_le hab] using hz) n).2
    simpa only [uIcc_of_le hab] using ha.continuousOn
  have hc' (n : ℤ) : ContinuousOn (fun p : ℝ × ℝ =>
      fourier n (p.2 : AddCircle (1 : ℝ)) *
        (profileFourierFrequency n ^ j * profileModeResponse g f a p.1 n))
      (Icc a b ×ˢ (Set.univ : Set ℝ)) := by
    apply ((((fourier n).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))).comp
      continuous_snd).continuousOn).mul
    exact continuousOn_const.mul ((hc n).comp continuous_fst.continuousOn (fun _ hp => hp.1))
  have hs := continuousOn_tsum hc' (profileJetMajorant_summable (C j / κ) (C 0 * (b - a)))
    (fun n p hp => by
      simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
      simpa only [norm_mul] using hb j hjq n p.1 hp.1)
  apply hs.congr
  intro p hp
  have hsum (l : ℕ) (hl : l ≤ j) :
      Summable (fun n => profileFourierFrequency n ^ l * profileModeResponse g f a p.1 n) :=
    (profileJetMajorant_summable _ _).of_norm_bounded
      (fun n => hb l (hl.trans hjq) n p.1 hp.1)
  change iteratedDeriv j (profileFourierSeries (profileModeResponse g f a p.1)) p.2 = _
  rw [profileFourierSeries_iteratedDeriv j _ hsum]
  rfl

/-! Uniform Fourier majorants transfer finite-mode time continuity to every supported classical jet. -/

theorem profileCellResponse_iteratedDeriv_time_continuousOn
    (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (a b κ M : ℝ)
    (hab : a ≤ b) (hκ : 0 < κ) (hi : IntegrableOn g (Icc a b))
    (hg : ∀ s ∈ Icc a b, κ ≤ g s) (hM : 0 ≤ M)
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, |g t| ≤ M)
    (hfm : Measurable (Function.uncurry f)) (q : ℕ) (C : ℕ → ℝ)
    (hC : ∀ j ≤ q, 0 ≤ C j) (hf : ∀ s ∈ Icc a b, ContDiff ℝ q (f s))
    (hp : ∀ s ∈ Icc a b, Function.Periodic (f s) 1)
    (hj : ∀ j ≤ q, ∀ s ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (f s) x‖ ≤ C j)
    (j : ℕ) (hjq : j ≤ q) (x : ℝ) :
    ContinuousOn (fun t => iteratedDeriv j (profileCellResponse g f a t) x) (Icc a b) := by
  have hz (s : ℝ) (hs : s ∈ Icc a b) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      ‖f s y‖ ≤ C 0 := by
    simpa using hj 0 (Nat.zero_le q) s hs y hy
  have hb (l : ℕ) (hl : l ≤ q) (n : ℤ) (t : ℝ) (ht : t ∈ Icc a b) :
      ‖profileFourierFrequency n ^ l * profileModeResponse g f a t n‖ ≤
        profileJetMajorant (C l / κ) (C 0 * (b - a)) n :=
    profileModeResponse_uniform_jet_bound g f a b κ hab hκ hi hg l (C l) (C 0)
      (hC l hl) (hC 0 (Nat.zero_le q))
      (fun s hs => (hf s hs).of_le (by exact_mod_cast hl)) hp (hj l hl) hz n t ht
  have hc (n : ℤ) : ContinuousOn (fun t => profileModeResponse g f a t n) (Icc a b) := by
    have ha := (profileModeResponse_solves g f a b hab M hM hgm hgb hfm (C 0)
      (by simpa only [uIcc_of_le hab] using hz) n).2
    simpa only [uIcc_of_le hab] using ha.continuousOn
  have hs := boundedTimeSeries_continuousOn
    (fun n t => fourier n (x : AddCircle (1 : ℝ)) *
      (profileFourierFrequency n ^ j * profileModeResponse g f a t n))
    (profileJetMajorant (C j / κ) (C 0 * (b - a)))
    (profileJetMajorant_summable _ _) a b
    (fun n => continuousOn_const.mul (continuousOn_const.mul (hc n)))
    (fun n t ht => by
      simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
      simpa only [norm_mul] using hb j hjq n t ht)
  apply hs.congr
  intro t ht
  have hsum (l : ℕ) (hl : l ≤ j) :
      Summable (fun n => profileFourierFrequency n ^ l * profileModeResponse g f a t n) :=
    (profileJetMajorant_summable _ _).of_norm_bounded
      (fun n => hb l (hl.trans hjq) n t ht)
  change iteratedDeriv j (profileFourierSeries (profileModeResponse g f a t)) x = _
  rw [profileFourierSeries_iteratedDeriv j _ hsum]
  rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! A selected output component of a lift needs rectangular reserves only in its own coefficient row. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_component_box_reserve (n p q : ℕ) (c : LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (v : ι)
    (hf : ContDiff ℝ ((p + n : ℕ) : ℕ∞) (f t))
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      IsBoxSmooth p q (fun X z => c m α t X z v u)) :
    IsBoxSmooth p q (fun X z => liftApply n c f t X z v) := by
  unfold liftApply
  apply IsBoxSmooth.sum
  intro m hm
  apply IsBoxSmooth.sum
  intro α _
  apply IsBoxSmooth.sum
  intro u _
  have hmn : m ≤ n := by have hh := Finset.mem_range.mp hm; omega
  exact isBoxSmooth_bilinear (hc m hmn α u)
    (isBoxSmooth_slow_field p q _ (AVRegularity.contDiff_orderedDerivative_comp hmn α hf u))
    (ContinuousLinearMap.id ℝ (h u →L[ℝ] h v))

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Every reserved ordered slow jet is measurable in time by repeated difference quotients. -/

variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem orderedDerivative_parameter_measurable (f : T → Vec 2 → E) (q : ℕ)
    (hm : ∀ x, Measurable (fun t => f t x))
    (hf : ∀ t, ContDiff ℝ (q : ℕ∞) (f t))
    (m : ℕ) (hmq : m ≤ q) (α : DerivativeWord2 m) (x : Vec 2) :
    Measurable (fun t => orderedDerivative α (f t) x) := by
  induction m generalizing x with
  | zero => simpa [orderedDerivative] using hm x
  | succ m ih =>
    have hα : α = Fin.snoc (Fin.init α) (α (Fin.last m)) := (Fin.snoc_init_self α).symm
    have he (t : T) : orderedDerivative α (f t) = fun y =>
        fderiv ℝ (orderedDerivative (Fin.init α) (f t)) y (basisVec (α (Fin.last m))) := by
      conv_lhs => rw [hα]
      exact orderedDerivative_append_direction (Fin.init α) (α (Fin.last m)) (f t)
    simp only [he]
    apply fderiv_apply_parameter_measurable
    · intro y
      exact ih (by omega) (Fin.init α) y
    · intro t
      exact (orderedDerivative_contDiff (Fin.init α) 1 (f t)
        ((hf t).of_le (by exact_mod_cast (show 1 + m ≤ q by omega)))).differentiable one_ne_zero

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The cross operators retain rectangular reserves with their exact slow/fast costs. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB1_box_reserve (p q : ℕ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth (p + 1) (q + 1) f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (hv : ∀ k, IsBoxSmooth p q (fun (_ : Vec 2) z => v t z k)) :
    IsBoxSmooth p q (cellB1 η G v t f) := by
  unfold cellB1
  apply IsBoxSmooth.sub
  · apply IsBoxSmooth.sum
    intro k _
    exact isBoxSmooth_bilinear ((hv k).const_smul (Real.sqrt η))
      ((hf.slowPartial k).mono le_rfl (by omega))
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  · apply IsBoxSmooth.const_smul
    apply IsBoxSmooth.sum
    intro i _
    apply IsBoxSmooth.sum
    intro j _
    apply IsBoxSmooth.add
    · exact isBoxSmooth_bilinear ((hG i j).mono (by omega) le_rfl)
        ((hf.slowPartial j).fastPartial i)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
    · exact (isBoxSmooth_bilinear (hG i j) (hf.fastPartial j)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)).slowPartial i

theorem cellB2_box_reserve (p q : ℕ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth (p + 2) q f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j)) :
    IsBoxSmooth p q (cellB2 η G t f) := by
  unfold cellB2
  apply IsBoxSmooth.neg
  apply IsBoxSmooth.const_smul
  apply IsBoxSmooth.sum
  intro i _
  apply IsBoxSmooth.sum
  intro j _
  have hslow : IsBoxSmooth (p + 1) q (slowPartial j f) :=
    (hf.mono (by omega) le_rfl).slowPartial j
  exact (isBoxSmooth_bilinear (hG i j) hslow
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)).slowPartial i

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Left-term actions retain rectangular regularity and spend only the differentiated variable. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem LeftTerm.apply_box (c : LeftTerm E F) (p q : ℕ)
    (hc : IsBoxSmooth p q c.coeff) (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsBoxSmooth p q (c.apply f) := by
  have hjet := Sampling.contDiff_orderedDerivative p c.word f (hf.of_le (by simp))
  exact isBoxSmooth_bilinear hc (isBoxSmooth_slow_field p q _ hjet)
    (ContinuousLinearMap.apply ℝ F : E →L[ℝ] (E →L[ℝ] F) →L[ℝ] F).flip

theorem LeftTerm.fastDerivative_box (c : LeftTerm E F) (p q : ℕ)
    (hc : IsBoxSmooth p (q + 1) c.coeff) (k : Fin 2) :
    IsBoxSmooth p q (c.fastDerivative k).coeff := hc.fastPartial k

theorem LeftTerm.slowCoefficientDerivative_box (c : LeftTerm E F) (p q : ℕ)
    (hc : IsBoxSmooth (p + 1) q c.coeff) (k : Fin 2) :
    IsBoxSmooth p q (c.slowCoefficientDerivative k).coeff := hc.slowPartial k

theorem LeftTerm.smul_box (c : LeftTerm E F) (p q : ℕ)
    (hc : IsBoxSmooth p q c.coeff) (a : ℝ) :
    IsBoxSmooth p q (c.smul a).coeff :=
  hc.clm_comp (a • ContinuousLinearMap.id ℝ (E →L[ℝ] F))

theorem leftTermsApply_box (l : List (LeftTerm E F)) (p q : ℕ)
    (hc : ∀ c ∈ l, IsBoxSmooth p q c.coeff) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : IsBoxSmooth p q (leftTermsApply l f) :=
  isBoxSmooth_list_sum l p q (fun c => c.apply f) (fun c h => c.apply_box p q (hc c h) f hf)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Continuous periodic representatives are fixed pointwise by their cell class. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem periodicContinuous_zero_of_cell_ae (f : Vec 2 → E) (hf : Continuous f)
    (hper : AVenhance.IsZ2Periodic f)
    (he : f =ᵐ[volume.restrict AVenhance.unitCube] 0) : f = 0 := by
  have hopen : IsOpen AVenhance.unitCube := by
    exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hcell : Set.EqOn f 0 AVenhance.unitCube :=
    Measure.eqOn_open_of_ae_eq he hopen hf.continuousOn continuous_const.continuousOn
  have hcl : Set.EqOn f 0 (closure AVenhance.unitCube) :=
    hcell.closure hf continuous_const
  funext x
  let y : Vec 2 := fun i => Int.fract (x i)
  let n : Fin 2 → ℤ := fun i => Int.floor (x i)
  have hy : y ∈ closure AVenhance.unitCube := by
    rw [AVenhance.unitCube, closure_pi_set]
    intro i hi
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have heq : y + AVenhance.latticeShift n = x := by
    funext i
    simp only [Pi.add_apply, y, n, AVenhance.latticeShift, Int.fract]
    ring
  have hp := hper n y
  rw [heq] at hp
  exact hp.trans (hcl hy)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite permutation averaging makes left coefficients symmetric without changing smooth actions. -/

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def wordSymmetrize {m : ℕ} (c : DerivativeWord2 m → E) (α : DerivativeWord2 m) : E :=
  (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin m), c (α ∘ σ)

theorem wordSymmetrize_comp_perm {m : ℕ} (c : DerivativeWord2 m → E)
    (α : DerivativeWord2 m) (τ : Equiv.Perm (Fin m)) :
    wordSymmetrize c (α ∘ τ) = wordSymmetrize c α := by
  unfold wordSymmetrize
  congr 1
  have he := Equiv.sum_comp (Equiv.mulLeft τ) (fun σ : Equiv.Perm (Fin m) => c (α ∘ σ))
  simpa only [Equiv.coe_mulLeft, Equiv.Perm.coe_mul, Function.comp_def] using he

def wordPermutationEquiv {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    DerivativeWord2 m ≃ DerivativeWord2 m where
  toFun α := α ∘ σ
  invFun α := α ∘ σ.symm
  left_inv α := by funext i; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  right_inv α := by funext i; simp only [Function.comp_apply, Equiv.symm_apply_apply]
end

/-! A smooth coefficient word acts smoothly on a smooth coarse vector field. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem coefficient_word_action_contDiff (p m : ℕ) (α : DerivativeWord2 m)
    (c : LiftCoeff ι h) (t : ℝ) (z : Vec 2)
    (hc : ∀ v u, ContDiff ℝ (p : ℕ∞) (fun X => c m α t X z v u))
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (p : ℕ∞) (fun X v => ∑ u, c m α t X z v u (orderedDerivative α f X u)) := by
  have hjet := Sampling.contDiff_orderedDerivative p α f (hf.of_le (by simp))
  apply contDiff_pi.mpr
  intro v
  apply ContDiff.sum
  intro u hu
  exact (hc v u).clm_apply
    ((ContinuousLinearMap.proj u : (∀ i, h i) →L[ℝ] h u).contDiff.comp hjet)
end

/-! Group a finite left term by its tested order and ordered word. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def LeftTerm.coeffAt (c : LeftTerm E F) (m : ℕ) (α : DerivativeWord2 m) :
    Vec 2 → Vec 2 → E →L[ℝ] F := by
  classical
  exact if hm : c.order = m then if (hm ▸ c.word) = α then c.coeff else fun _ _ => 0
    else fun _ _ => 0

theorem LeftTerm.coeffAt_self (c : LeftTerm E F) : c.coeffAt c.order c.word = c.coeff := by
  simp only [LeftTerm.coeffAt, dite_true, ite_true]

theorem LeftTerm.coeffAt_ne_order (c : LeftTerm E F) (m : ℕ) (α : DerivativeWord2 m)
    (hm : c.order ≠ m) : c.coeffAt m α = fun _ _ => 0 := by
  simp only [LeftTerm.coeffAt, dite_eq_right hm]

theorem LeftTerm.coeffAt_box (c : LeftTerm E F) (p q : ℕ)
    (hc : IsBoxSmooth p q c.coeff) (m : ℕ) (α : DerivativeWord2 m) :
    IsBoxSmooth p q (c.coeffAt m α) := by
  classical
  unfold LeftTerm.coeffAt
  split_ifs
  · exact hc
  · exact IsBoxSmooth.zero
  · exact IsBoxSmooth.zero

theorem LeftTerm.coeffAt_order_sum (c : LeftTerm E F) (n : ℕ) (hn : c.order ≤ n)
    (f : Vec 2 → E) (X z : Vec 2) :
    (∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m,
      c.coeffAt m α X z (orderedDerivative α f X)) = c.apply f X z := by
  classical
  rw [Finset.sum_eq_single c.order]
  · rw [Finset.sum_eq_single c.word]
    · rw [c.coeffAt_self]
      rfl
    · intro α _ hα
      simp only [LeftTerm.coeffAt, dite_true, ite_eq_right (Ne.symm hα), zero_apply]
    · simp
  · intro m _ hm
    simp only [c.coeffAt_ne_order m _ (Ne.symm hm), zero_apply, Finset.sum_const_zero]
  · intro hc
    exact (hc (Finset.mem_range.mpr (by omega))).elim
end

/-! Finite term-list actions preserve their literal sum algebra. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem leftTermsApply_cons (c : LeftTerm E F) (l : List (LeftTerm E F)) (f : Vec 2 → E) :
    leftTermsApply (c :: l) f = fun X z => c.apply f X z + leftTermsApply l f X z := rfl

theorem leftTermsApply_nil (f : Vec 2 → E) :
    leftTermsApply ([] : List (LeftTerm E F)) f = fun _ _ => 0 := rfl

theorem leftTermsApply_append (l l' : List (LeftTerm E F)) (f : Vec 2 → E) :
    leftTermsApply (l ++ l') f = fun X z => leftTermsApply l f X z + leftTermsApply l' f X z := by
  funext X z
  simp only [leftTermsApply, List.map_append, List.sum_append]

theorem leftTermsApply_map_smul (l : List (LeftTerm E F)) (a : ℝ) (f : Vec 2 → E) :
    leftTermsApply (l.map (fun c => c.smul a)) f = fun X z => a • leftTermsApply l f X z := by
  funext X z
  simp only [leftTermsApply, List.map_map, Function.comp_def, LeftTerm.smul_apply, List.smul_sum]

def LeftTerm.slowDerivativeTerms (c : LeftTerm E F) (k : Fin 2) : List (LeftTerm E F) :=
  [c.slowCoefficientDerivative k, c.slowInputDerivative k]

theorem leftTermsApply_slowDerivativeTerms (c : LeftTerm E F) (k : Fin 2) (f : Vec 2 → E) :
    leftTermsApply (c.slowDerivativeTerms k) f = fun X z =>
      (c.slowCoefficientDerivative k).apply f X z + (c.slowInputDerivative k).apply f X z := by
  funext X z
  simp only [leftTermsApply, LeftTerm.slowDerivativeTerms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
end

end AVRegularity.CycleComparison.Lift
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Constituent linear maps and scalar fields act on finite left terms. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def LeftTerm.postcompose (c : LeftTerm E F) (T : F →L[ℝ] G) : LeftTerm E G :=
  ⟨c.order, c.word, fun X z => T.comp (c.coeff X z)⟩

def LeftTerm.fieldSmul (c : LeftTerm E F) (a : Vec 2 → Vec 2 → ℝ) : LeftTerm E F :=
  ⟨c.order, c.word, fun X z => a X z • c.coeff X z⟩

theorem LeftTerm.postcompose_apply (c : LeftTerm E F) (T : F →L[ℝ] G)
    (f : Vec 2 → E) : (c.postcompose T).apply f = fun X z => T (c.apply f X z) := rfl

theorem LeftTerm.fieldSmul_apply (c : LeftTerm E F) (a : Vec 2 → Vec 2 → ℝ)
    (f : Vec 2 → E) : (c.fieldSmul a).apply f = fun X z => a X z • c.apply f X z := rfl

theorem LeftTerm.postcompose_box (c : LeftTerm E F) (T : F →L[ℝ] G) (p q : ℕ)
    (hc : IsBoxSmooth p q c.coeff) : IsBoxSmooth p q (c.postcompose T).coeff :=
  hc.clm_comp (ContinuousLinearMap.compL ℝ E F G T)

theorem LeftTerm.fieldSmul_box (c : LeftTerm E F) (a : Vec 2 → Vec 2 → ℝ) (p q : ℕ)
    (hc : IsBoxSmooth p q c.coeff) (ha : IsBoxSmooth p q a) :
    IsBoxSmooth p q (c.fieldSmul a).coeff :=
  isBoxSmooth_bilinear ha hc (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] F))
end

/-! Finite left terms produce genuine operator coefficient arrays with the same action. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def leftTermsCoefficient (l : List (LeftTerm E F)) (m : ℕ) (α : DerivativeWord2 m) :
    Vec 2 → Vec 2 → E →L[ℝ] F := fun X z => (l.map (fun c => c.coeffAt m α X z)).sum

theorem leftTermsCoefficient_cons (c : LeftTerm E F) (l : List (LeftTerm E F))
    (m : ℕ) (α : DerivativeWord2 m) :
    leftTermsCoefficient (c :: l) m α = fun X z => c.coeffAt m α X z + leftTermsCoefficient l m α X z := rfl

theorem leftTermsCoefficient_box (l : List (LeftTerm E F)) (p q : ℕ)
    (hl : ∀ c ∈ l, IsBoxSmooth p q c.coeff) (m : ℕ) (α : DerivativeWord2 m) :
    IsBoxSmooth p q (leftTermsCoefficient l m α) :=
  isBoxSmooth_list_sum l p q (fun c => c.coeffAt m α) (fun c hc => c.coeffAt_box p q (hl c hc) m α)

theorem leftTermsCoefficient_action (l : List (LeftTerm E F)) (n : ℕ)
    (hl : ∀ c ∈ l, c.order ≤ n) (f : Vec 2 → E) (X z : Vec 2) :
    (∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m,
      leftTermsCoefficient l m α X z (orderedDerivative α f X)) = leftTermsApply l f X z := by
  induction l with
  | nil => simp [leftTermsCoefficient, leftTermsApply]
  | cons c l ih =>
    have hc := hl c List.mem_cons_self
    have hl' : ∀ d ∈ l, d.order ≤ n := fun d hd => hl d (List.mem_cons_of_mem c hd)
    simp only [leftTermsCoefficient_cons, add_apply, Finset.sum_add_distrib]
    rw [c.coeffAt_order_sum n hc f X z, ih hl', leftTermsApply_cons]
end

/-! Variable left linear maps compose with finite differential coefficients without altering input order. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def LeftTerm.fieldPostcompose (c : LeftTerm E F) (T : Vec 2 → Vec 2 → F →L[ℝ] G) :
    LeftTerm E G := ⟨c.order, c.word, fun X z => (T X z).comp (c.coeff X z)⟩

theorem LeftTerm.fieldPostcompose_apply (c : LeftTerm E F) (T : Vec 2 → Vec 2 → F →L[ℝ] G)
    (f : Vec 2 → E) :
    (c.fieldPostcompose T).apply f = fun X z => T X z (c.apply f X z) := rfl

theorem leftTermsApply_map_fieldPostcompose (l : List (LeftTerm E F))
    (T : Vec 2 → Vec 2 → F →L[ℝ] G) (f : Vec 2 → E) :
    leftTermsApply (l.map (fun c => c.fieldPostcompose T)) f =
      fun X z => T X z (leftTermsApply l f X z) := by
  funext X z
  induction l with
  | nil => simp [leftTermsApply]
  | cons c l ih =>
    simp only [List.map_cons, leftTermsApply_cons, LeftTerm.fieldPostcompose_apply, map_add, ih]
end

end AVRegularity.CycleComparison.Lift
end
end
