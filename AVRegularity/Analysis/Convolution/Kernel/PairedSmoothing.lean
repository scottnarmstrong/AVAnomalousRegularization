-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Analysis.Convolution.Kernel.PairedGeometry
import AVRegularity.Analysis.Convolution.Kernel.Commutation.Torus
public import AVRegularity.Analysis.Convolution.Kernel.Commutation.TorusBridge
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization Polynomial
open scoped FourierTransform
namespace AVRegularity.Analysis.Convolution

/-! Literal source kernel moment cancellation through order 2n−1.
The characteristic normalization is exp(−2π i t Lz), source frequency 2πtL.
The convolution/binomial identity, double-zero power jets and coordinate coefficient
extraction are proved here; no Fourier-defined convolution operator is introduced. -/

/-- Finite Leibniz: a smooth scalar function with a double zero has powers
whose derivatives vanish below twice the power. -/
theorem iteratedDeriv_pow_double_zero (f : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hzero : f 0 = 0) (hfirst : deriv f 0 = 0)
    (n : ℕ) : ∀ m : ℕ, m < 2 * n → iteratedDeriv m (fun x => f x ^ n) 0 = 0 := by
  induction n with
  | zero => intro m hm; omega
  | succ n ih =>
    intro m hm
    have hid : (fun x => f x ^ (n + 1)) = f * (fun x => f x ^ n) := by
      funext x
      exact pow_succ' _ _
    rw [hid, iteratedDeriv_mul (hf.of_le (by simp)).contDiffAt
      ((hf.pow n).of_le (by simp)).contDiffAt]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    by_cases hsmall : k < 2
    · have hz : iteratedDeriv k f 0 = 0 := by
        have hcases : k = 0 ∨ k = 1 := by omega
        rcases hcases with rfl | rfl
        · simpa only [iteratedDeriv_zero] using hzero
        · simpa only [iteratedDeriv_one] using hfirst
      rw [hz, mul_zero, zero_mul]
    · rw [ih (m - k) (by omega), mul_zero]

theorem integral_linear_mul_even (q : Vec 2 → ℝ) (L : Vec 2 →L[ℝ] ℝ)
    (he : reflection q = q) : ∫ z, L z * q z = 0 := by
  have he' (z : Vec 2) : q (-z) = q z := congrFun he z
  have hi := integral_neg_eq_self (μ := volume) (fun z : Vec 2 => L z * q z)
  simp_rw [map_neg, he', neg_mul, integral_neg] at hi
  linarith

theorem projectionFourier_deriv_zero_even {q : Vec 2 → ℝ}
    (hc : HasCompactSupport q) (hq : Continuous q) (he : reflection q = q)
    (L : Vec 2 →L[ℝ] ℝ) : deriv (projectionFourier q L) 0 = 0 := by
  have h := projectionFourier_iteratedDeriv hc hq L 1
  simpa only [iteratedDeriv_one, pow_one, integral_linear_mul_even q L he,
    Complex.ofReal_zero, mul_zero] using h

 theorem scalar_binomial_regularizer (a : ℂ) (n : ℕ) :
    ∑ l ∈ Finset.Icc 1 n,
      ((-1 : ℂ) ^ (l + 1) * (n.choose l : ℂ)) * a ^ l = 1 - (1 - a) ^ n := by
  have hb : (1 - a)^n = ∑ l ∈ Finset.range (n+1),
      ((-1 : ℂ)^l * (n.choose l : ℂ)) * a^l := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro l _
    rw [one_pow, mul_one, ← neg_one_mul a, mul_pow]
    ring
  have hi : Finset.Icc 1 n = Finset.Ico 1 (n+1) :=
    (Finset.Ico_succ_right_eq_Icc 1 n).symm
  rw [hb, hi,
    Finset.sum_Ico_eq_sub (fun l => ((-1 : ℂ)^(l+1)*(n.choose l : ℂ))*a^l)
      (Nat.succ_le_succ (Nat.zero_le n))]
  simp only [Finset.sum_range_one, Nat.zero_add, pow_one, Nat.choose_zero_right,
    Nat.cast_one, mul_one, pow_zero]
  rw [Finset.sum_congr rfl (fun l _ => show
    ((-1 : ℂ)^(l+1)*(n.choose l : ℂ))*a^l = -(((-1 : ℂ)^l*(n.choose l : ℂ))*a^l) by
      rw [pow_succ]; ring), Finset.sum_neg_distrib]
  ring

theorem projectionFourier_kernelConvolution {q p : Vec 2 → ℝ}
    (hq : Integrable q) (hp : Integrable p) (L : Vec 2 →L[ℝ] ℝ) (t : ℝ) :
    projectionFourier (kernelConvolution q p) L t = projectionFourier q L t * projectionFourier p L t := by
  have hconv := hq.ofReal.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hp.ofReal
  have hchar : Continuous fun x : Vec 2 × Vec 2 => (𝐞 (-L x.1 * t) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (((L.continuous.comp continuous_fst).neg).mul continuous_const))
  have hd := hconv.bdd_mul hchar.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x : Vec 2 × Vec 2 => (Circle.norm_coe (𝐞 (-L x.1 * t))).le)
  calc
    projectionFourier (kernelConvolution q p) L t =
        ∫ u : Vec 2, ∫ z : Vec 2, (𝐞 (-L u * t) : ℂ) * ((q z : ℂ) * (p (u - z) : ℂ)) := by
      have hi (u : Vec 2) : (kernelConvolution q p u : ℂ) =
          ∫ z : Vec 2, (q z : ℂ) * (p (u - z) : ℂ) := by
        change ((∫ z : Vec 2, q z * p (u - z) : ℝ) : ℂ) = _
        rw [← integral_complex_ofReal]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => Complex.ofReal_mul _ _
      change (∫ u : Vec 2, (𝐞 (-L u * t) : ℂ) * (kernelConvolution q p u : ℂ)) = _
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        change (𝐞 (-L u * t) : ℂ) * (kernelConvolution q p u : ℂ) = _
        exact (congrArg (fun c : ℂ => (𝐞 (-L u * t) : ℂ) * c) (hi u)).trans
          (integral_const_mul (𝐞 (-L u * t) : ℂ)
            (fun z : Vec 2 => (q z : ℂ) * (p (u - z) : ℂ))).symm
    _ = ∫ z : Vec 2, ∫ u : Vec 2,
        (𝐞 (-L u * t) : ℂ) * ((q z : ℂ) * (p (u - z) : ℂ)) := integral_integral_swap hd
    _ = ∫ z : Vec 2, ∫ w : Vec 2,
        (𝐞 (-L (w + z) * t) : ℂ) * ((q z : ℂ) * (p w : ℂ)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        have h := integral_add_right_eq_self (μ := volume)
          (fun u : Vec 2 => (𝐞 (-L u * t) : ℂ) * ((q z : ℂ) * (p (u - z) : ℂ))) z
        simpa only [add_sub_cancel_right] using h.symm
    _ = projectionFourier q L t * projectionFourier p L t := by
      unfold projectionFourier
      simp_rw [map_add, neg_add, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
      have hprod (z w : Vec 2) :
          ((𝐞 (-L w * t) : ℂ) * (𝐞 (-L z * t) : ℂ)) * ((q z : ℂ) * (p w : ℂ)) =
          ((𝐞 (-L z * t) : ℂ) * (q z : ℂ)) * ((𝐞 (-L w * t) : ℂ) * (p w : ℂ)) := by ring
      simp_rw [hprod, integral_const_mul]
      exact integral_mul_const _ _

theorem projectionFourier_integrable {q : Vec 2 → ℝ} (hq : Integrable q)
    (L : Vec 2 →L[ℝ] ℝ) (t : ℝ) :
    Integrable (fun z : Vec 2 => (𝐞 (-L z*t) : ℂ)*(q z : ℂ)) := by
  apply hq.ofReal.bdd_mul
  · exact (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (L.continuous.neg.mul continuous_const))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => (Circle.norm_coe (𝐞 (-L z*t))).le

theorem projectionFourier_positiveConvolutionPower {q : Vec 2 → ℝ}
    (hq : Integrable q) (L : Vec 2 →L[ℝ] ℝ) (t : ℝ) (m : ℕ) :
    projectionFourier (positiveConvolutionPower q m) L t = projectionFourier q L t ^ (m+1) := by
  induction m with
  | zero => exact (pow_one _).symm
  | succ m ih =>
    rw [positiveConvolutionPower, projectionFourier_kernelConvolution hq
      (integrable_positiveConvolutionPower hq m), ih]
    exact (pow_succ' _ (m+1)).symm

theorem projectionFourier_momentKernel {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀)
    (n : ℕ+) (L : Vec 2 →L[ℝ] ℝ) (t : ℝ) :
    projectionFourier (momentKernel φ₀ n) L t =
      1 - (1 - projectionFourier (kernelConvolution (scaledTemplate φ₀ n)
        (reflection (scaledTemplate φ₀ n))) L t) ^ (n : ℕ) := by
  let q := kernelConvolution (scaledTemplate φ₀ n) (reflection (scaledTemplate φ₀ n))
  have hq : Integrable q := integrable_kernelConvolution
    (integrable_scaledTemplate hφ₀ n) (integrable_reflection (integrable_scaledTemplate hφ₀ n))
  rw [← scalar_binomial_regularizer (projectionFourier q L t) (n : ℕ)]
  unfold projectionFourier momentKernel
  have hpoint (z : Vec 2) :
      (𝐞 (-L z*t) : ℂ) *
        ((∑ l ∈ Finset.Icc 1 (n:ℕ),
          ((-1:ℝ)^(l+1)*((n:ℕ).choose l:ℝ)) • positiveConvolutionPower q (l-1) z : ℝ) : ℂ) =
      ∑ l ∈ Finset.Icc 1 (n:ℕ),
        ((-1:ℂ)^(l+1)*((n:ℕ).choose l:ℂ)) *
          ((𝐞 (-L z*t) : ℂ)*(positiveConvolutionPower q (l-1) z:ℂ)) := by
    simp only [smul_eq_mul]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp only [Finset.sum_apply, Pi.smul_apply]
  change (∫ z : Vec 2, (𝐞 (-L z*t):ℂ)*
    ((∑ l ∈ Finset.Icc 1 (n:ℕ),
      ((-1:ℝ)^(l+1)*((n:ℕ).choose l:ℝ)) • positiveConvolutionPower q (l-1) z : ℝ):ℂ)) = _
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro l hl
    rw [integral_const_mul]
    congr 1
    change projectionFourier (positiveConvolutionPower q (l-1)) L t = _
    rw [projectionFourier_positiveConvolutionPower hq, Nat.sub_add_cancel (Finset.mem_Icc.mp hl).1]
    rfl
  · intro l hl
    exact (projectionFourier_integrable (integrable_positiveConvolutionPower hq (l-1)) L t).const_mul _

/-- Every projected moment below twice the source order cancels for the literal kernel. -/
theorem integral_projection_pow_momentKernel {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hmass : ∫ z, φ₀ z = 1) (n : ℕ+) (L : Vec 2 →L[ℝ] ℝ)
    {m : ℕ} (hm : 0 < m) (hsmall : m < 2*(n:ℕ)) :
    ∫ z, (L z)^m * momentKernel φ₀ n z = 0 := by
  let p := scaledTemplate φ₀ n
  let q := kernelConvolution p (reflection p)
  have hip : Integrable p := integrable_scaledTemplate (hd.continuous.integrable_of_hasCompactSupport hc) n
  have hcp : HasCompactSupport p := hasCompactSupport_scaledTemplate hc n
  have hdp : ContDiff ℝ (⊤ : ℕ∞) p := contDiff_scaledTemplate hd n
  have hcq : HasCompactSupport q := hcp.convolution (ContinuousLinearMap.mul ℝ ℝ)
    (hasCompactSupport_reflection hcp)
  have hdq : ContDiff ℝ (⊤ : ℕ∞) q := hcp.contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℝ) hdp (integrable_reflection hip).locallyIntegrable
  have hmassq : ∫ z, q z = 1 := by
    rw [integral_autocorrelation hip, integral_scaledTemplate hmass n, one_pow]
  have heq : reflection q = q := reflection_autocorrelation p
  have hF := projectionFourier_contDiff hcq hdq.continuous L
  have hz : (fun t => (1:ℂ) - projectionFourier q L t) 0 = 0 := by
    change (1:ℂ) - projectionFourier q L 0 = 0
    rw [projectionFourier_zero, hmassq, Complex.ofReal_one, sub_self]
  have hdz : deriv (fun t => (1:ℂ) - projectionFourier q L t) 0 = 0 := by
    rw [deriv_const_sub, projectionFourier_deriv_zero_even hcq hdq.continuous heq L, neg_zero]
  have hj := iteratedDeriv_pow_double_zero _ (contDiff_const.sub hF) hz hdz (n:ℕ) m hsmall
  have hpoly : projectionFourier (momentKernel φ₀ n) L =
      fun t => (1:ℂ) - (1 - projectionFourier q L t)^(n:ℕ) := by
    funext t
    exact projectionFourier_momentKernel (hd.continuous.integrable_of_hasCompactSupport hc) n L t
  have hjk : iteratedDeriv m (projectionFourier (momentKernel φ₀ n) L) 0 = 0 := by
    rw [hpoly, iteratedDeriv_const_sub hm, iteratedDeriv_neg, hj, neg_zero]
  rw [projectionFourier_iteratedDeriv (hasCompactSupport_momentKernel hc n)
    (contDiff_momentKernel hc hd n).continuous L m] at hjk
  have hcoef : (-(2 * (Real.pi : ℂ) * Complex.I)) ^ m ≠ 0 := by
    apply pow_ne_zero
    simp only [ne_eq, neg_eq_zero, mul_eq_zero, Complex.I_ne_zero, or_false]
    norm_num [Real.pi_ne_zero]
  have hreal := (mul_eq_zero.mp hjk).resolve_left hcoef
  exact_mod_cast hreal

theorem integral_coordinate_monomial_of_projection {q : Vec 2 → ℝ}
    (hc : HasCompactSupport q) (hq : Continuous q) (m : ℕ)
    (hproj : ∀ L : Vec 2 →L[ℝ] ℝ, ∫ z, (L z)^m * q z = 0)
    (k : ℕ) (hk : k ≤ m) : ∫ z, z 0 ^ k * z 1 ^ (m-k) * q z = 0 := by
  let a (l : ℕ) := ∫ z : Vec 2, z 0 ^ l * z 1 ^ (m-l) * q z
  let P : ℝ[X] := ∑ l ∈ Finset.range (m+1), Polynomial.monomial l ((m.choose l:ℝ)*a l)
  have hi (l : ℕ) : Integrable (fun z : Vec 2 => z 0 ^ l * z 1 ^ (m-l) * q z) :=
    (((continuous_apply 0).pow l).mul ((continuous_apply 1).pow (m-l))).mul hq
      |>.integrable_of_hasCompactSupport hc.mul_left
  have hPeval (r : ℝ) : P.eval r = ∫ z : Vec 2, (r*z 0+z 1)^m * q z := by
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    rw [show (fun z : Vec 2 => (r*z 0+z 1)^m * q z) =
      fun z => ∑ l ∈ Finset.range (m+1), (m.choose l:ℝ)*r^l*(z 0^l*z 1^(m-l)*q z) by
      funext z
      rw [add_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      rw [mul_pow]
      ring]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro l _
      rw [integral_const_mul]
      change ((m.choose l:ℝ)*a l)*r^l = ((m.choose l:ℝ)*r^l)*a l
      ring
    · intro l _
      exact (hi l).const_mul _
  have hP : P = 0 := Polynomial.funext fun r => by
    rw [Polynomial.eval_zero, hPeval]
    exact hproj (r • ContinuousLinearMap.proj (0 : Fin 2) + ContinuousLinearMap.proj (1 : Fin 2))
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff k) hP
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hcoeff
  have hs : (∑ l ∈ Finset.range (m+1), if l=k then (m.choose l:ℝ)*a l else 0) =
      (m.choose k:ℝ)*a k := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hne
      simp [hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
  rw [hs] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left (by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hk)))

/-- Coordinate multiindex cancellation through order `2n-1` for the source kernel. -/
theorem integral_multiindex_momentKernel {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hmass : ∫ z, φ₀ z = 1) (n : ℕ+) (α : Fin 2 → ℕ)
    (hpos : 0 < ∑ i, α i) (hsmall : ∑ i, α i < 2*(n:ℕ)) :
    ∫ z, (∏ i : Fin 2, z i ^ α i) * momentKernel φ₀ n z = 0 := by
  simp only [Fin.sum_univ_two] at hpos hsmall
  have h := integral_coordinate_monomial_of_projection
    (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n).continuous
    (α 0 + α 1) (fun L => integral_projection_pow_momentKernel hc hd hmass n L hpos hsmall)
    (α 0) (Nat.le_add_right _ _)
  simpa only [Fin.prod_univ_two, Nat.add_sub_cancel_left] using h

end AVRegularity.Analysis.Convolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Analysis.Convolution

/-! Exact factorial split into lower orders and a shifted derivative family. -/

variable {μ : Measure (Vec 2)}
theorem factorial_weight_add_le (ρ : ℝ) (hρ : 0 ≤ ρ) (K j : ℕ) :
    ρ^(2*(K+j))/((K+j).factorial : ℝ)^2 ≤
      (ρ^(2*K)/(K.factorial : ℝ)^2) * (ρ^(2*j)/(j.factorial : ℝ)^2) := by
  have hfac : (K.factorial : ℝ) * (j.factorial : ℝ) ≤ ((K+j).factorial : ℝ) := by
    have h := Nat.le_of_dvd (Nat.factorial_pos (K+j))
      (Nat.factorial_mul_factorial_dvd_factorial (Nat.le_add_right K j))
    exact_mod_cast (by simpa only [Nat.add_sub_cancel_left] using h)
  have hsq : ((K.factorial : ℝ)*(j.factorial : ℝ))^2 ≤ ((K+j).factorial : ℝ)^2 := by
    simpa only [pow_two] using mul_self_le_mul_self (by positivity) hfac
  rw [Nat.mul_add, pow_add, ← mul_div_mul_comm, ← mul_pow]
  exact div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hρ _) (pow_nonneg hρ _)) (by positivity) hsq

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

theorem factorialNormSq_order_le {N : ℕ} {μ : Measure (Vec 2)} (D : JetL2 μ N E)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (j : Fin (N+1)) :
    ρ^(2*j.val)/(j.val.factorial : ℝ)^2 * derivativeNormSq D j ≤ factorialNormSq ρ D := by
  have hn : ∀ k : Fin (N+1), 0 ≤ ρ^(2*k.val)/(k.val.factorial : ℝ)^2 * derivativeNormSq D k :=
    fun k => mul_nonneg (by positivity) (derivativeNormSq_nonneg D k)
  exact Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ j)

variable [InnerProductSpace ℝ E]

theorem factorialNormSq_split_le {K L : ℕ} {μ : Measure (Vec 2)} (D : JetL2 μ (L+K) E)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    factorialNormSq ρ D ≤ ((L+K+1 : ℕ) : ℝ) *
      (factorialNormSq ρ (truncateJet (Nat.le_add_left K L) D) +
        (ρ^(2*K)/(K.factorial : ℝ)^2) *
          ∑ w : DerivativeWord2 K, factorialNormSq ρ (derivativeJet w D)) := by
  have hlo : 0 ≤ factorialNormSq ρ (truncateJet (Nat.le_add_left K L) D) :=
    factorialNormSq_nonneg ρ _
  have hhi : 0 ≤ (ρ^(2*K)/(K.factorial : ℝ)^2) *
      ∑ w : DerivativeWord2 K, factorialNormSq ρ (derivativeJet w D) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
      factorialNormSq_nonneg ρ _)
  unfold factorialNormSq at ⊢
  calc
    (∑ j : Fin (L+K+1), ρ^(2*j.val)/(j.val.factorial : ℝ)^2 * derivativeNormSq D j) ≤
        ∑ _j : Fin (L+K+1),
          (factorialNormSq ρ (truncateJet (Nat.le_add_left K L) D) +
            (ρ^(2*K)/(K.factorial : ℝ)^2) *
              ∑ w : DerivativeWord2 K, factorialNormSq ρ (derivativeJet w D)) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j.val ≤ K
      · let jl : Fin (K+1) := ⟨j.val, Nat.lt_succ_of_le hj⟩
        have h := factorialNormSq_order_le (truncateJet (Nat.le_add_left K L) D) ρ hρ jl
        have heq : derivativeNormSq (truncateJet (Nat.le_add_left K L) D) jl = derivativeNormSq D j := rfl
        rw [heq] at h
        exact h.trans (le_add_of_nonneg_right hhi)
      · have hk : K ≤ j.val := Nat.le_of_lt (Nat.lt_of_not_ge hj)
        let jt : Fin (L+1) := ⟨j.val-K, by omega⟩
        have heq : shiftedJetOrder jt = j := Fin.ext (by dsimp only [shiftedJetOrder, jt]; omega)
        have hw := factorial_weight_add_le ρ hρ K jt.val
        have hjv : K+jt.val = j.val := by dsimp only [jt]; omega
        rw [hjv] at hw
        have ht : ρ^(2*jt.val)/(jt.val.factorial : ℝ)^2 * derivativeNormSq D j ≤
            ∑ w : DerivativeWord2 K, factorialNormSq ρ (derivativeJet w D) := by
          rw [derivativeArray_factorialNormSq]
          rw [← heq]
          have hn : ∀ k : Fin (L+1), 0 ≤ ρ^(2*k.val)/(k.val.factorial : ℝ)^2 *
              derivativeNormSq D (shiftedJetOrder k) :=
            fun k => mul_nonneg (by positivity) (derivativeNormSq_nonneg D _)
          exact Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ jt)
        have htop : 0 ≤ ρ^(2*K)/(K.factorial : ℝ)^2 := by positivity
        have hmul := mul_le_mul_of_nonneg_left ht htop
        rw [← mul_assoc] at hmul
        have hh := (mul_le_mul_of_nonneg_right hw (derivativeNormSq_nonneg D j)).trans hmul
        exact hh.trans (le_add_of_nonneg_left hlo)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rfl

end AVRegularity.Analysis.Convolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.Analysis.Convolution

/-! Moment-kernel averages on the ordered weak Sobolev carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Identity pullback removes the redundant restriction to all of the plane. -/
def univToPlane : ComponentL2 (volume.restrict (Set.univ : Set (Vec 2))) E →ₗᵢ[ℝ]
    Lp E 2 (volume : Measure (Vec 2)) :=
  Lp.compMeasurePreservingₗᵢ ℝ id (by
    constructor
    · exact measurable_id
    · simp only [Measure.map_id, Measure.restrict_univ])

/-- Identity pullback inserts the redundant all-plane restriction. -/
def planeToUniv : Lp E 2 (volume : Measure (Vec 2)) →ₗᵢ[ℝ]
    ComponentL2 (volume.restrict (Set.univ : Set (Vec 2))) E :=
  Lp.compMeasurePreservingₗᵢ ℝ id (by
    constructor
    · exact measurable_id
    · simp only [Measure.map_id, Measure.restrict_univ])

omit [BorelSpace E] [CompleteSpace E] in
theorem univToPlane_ae (f : ComponentL2 (volume.restrict (Set.univ : Set (Vec 2))) E) :
    univToPlane f =ᵐ[volume] f := Lp.coeFn_compMeasurePreserving _ _

omit [BorelSpace E] [CompleteSpace E] in
theorem planeToUniv_ae (f : Lp E 2 (volume : Measure (Vec 2))) :
    planeToUniv f =ᵐ[volume] f := by
  have h : planeToUniv f =ᵐ[volume.restrict Set.univ] f :=
    Lp.coeFn_compMeasurePreserving _ _
  simpa only [Measure.restrict_univ] using h

omit [BorelSpace E] [CompleteSpace E] in
theorem planeToUniv_univToPlane (f : ComponentL2 (volume.restrict (Set.univ : Set (Vec 2))) E) :
    planeToUniv (univToPlane f) = f := by
  apply Lp.ext
  simpa only [Measure.restrict_univ] using
    (planeToUniv_ae (univToPlane f)).trans (univToPlane_ae f)

omit [BorelSpace E] [CompleteSpace E] in
theorem univToPlane_planeToUniv (f : Lp E 2 (volume : Measure (Vec 2))) :
    univToPlane (planeToUniv f) = f := by
  apply Lp.ext
  exact (univToPlane_ae (planeToUniv f)).trans (planeToUniv_ae f)

/-- A moment-kernel average on one plane Sobolev component. -/
def planeComponentAverage (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    (κ : Vec 2 → ℝ) (hκ : Integrable κ) :
    ComponentL2 (volume.restrict (Set.univ : Set (Vec 2))) E →L[ℝ]
      ComponentL2 (volume.restrict (Set.univ : Set (Vec 2))) E :=
  planeToUniv.toContinuousLinearMap.comp
    ((averagingOperator (E := E) (μ := volume) ρ hρ κ hκ).comp
      univToPlane.toContinuousLinearMap)

omit [BorelSpace E] in
theorem planeComponentAverage_hasWeakPartialDeriv {i : Fin 2}
    {f g : ComponentL2 (volume.restrict (Set.univ : Set (Vec 2))) E}
    (h : ∀ e : E, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (f x)) (fun x => inner ℝ e (g x)))
    (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) :
    ∀ e : E, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (planeComponentAverage ρ hρ κ hκ f x))
      (fun x => inner ℝ e (planeComponentAverage ρ hρ κ hκ g x)) := by
  have hin : ∀ e : E, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (univToPlane f x))
      (fun x => inner ℝ e (univToPlane g x)) := by
    intro e
    apply hasWeakPartialDerivOn_congr_ae _ _ (h e)
    · simpa only [Measure.restrict_univ, Function.comp_def] using
        (univToPlane_ae f).symm.fun_comp (inner ℝ e)
    · simpa only [Measure.restrict_univ, Function.comp_def] using
        (univToPlane_ae g).symm.fun_comp (inner ℝ e)
  intro e
  change HasWeakPartialDerivOn Set.univ i
    (fun x => inner ℝ e (planeToUniv (averagingOperator ρ hρ κ hκ (univToPlane f)) x))
    (fun x => inner ℝ e (planeToUniv (averagingOperator ρ hρ κ hκ (univToPlane g)) x))
  apply hasWeakPartialDerivOn_congr_ae _ _
    (averagingOperator_hasWeakPartialDeriv hin ρ hρ hκ e)
  · simpa only [Measure.restrict_univ, Function.comp_def] using
      (planeToUniv_ae (averagingOperator ρ hρ κ hκ (univToPlane f))).symm.fun_comp (inner ℝ e)
  · simpa only [Measure.restrict_univ, Function.comp_def] using
      (planeToUniv_ae (averagingOperator ρ hρ κ hκ (univToPlane g))).symm.fun_comp (inner ℝ e)

/-- Average every ordered derivative component on the plane. -/
def planeJetAverage {K : ℕ} (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    (κ : Vec 2 → ℝ) (hκ : Integrable κ)
    (D : JetL2 (volume.restrict (Set.univ : Set (Vec 2))) K E) :
    JetL2 (volume.restrict (Set.univ : Set (Vec 2))) K E :=
  WithLp.toLp 2 (fun a => planeComponentAverage ρ hρ κ hκ (D a))

theorem planeJetAverage_mem_graph {K : ℕ} (f : PlaneHk (Set.univ : Set (Vec 2)) K E)
    (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ) {κ : Vec 2 → ℝ} (hκ : Integrable κ) :
    planeJetAverage ρ hρ κ hκ f.val ∈ planeHkGraph (E := E) Set.univ K := by
  rw [mem_planeHkGraph_iff]
  intro j w i e
  exact planeComponentAverage_hasWeakPartialDeriv
    (fun e => f.toFunction.hasWeakJet j w i e) ρ hρ hκ e

/-- Average every periodic ordered derivative component through the torus isometry. -/
def periodicComponentAverage (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    (κ : Vec 2 → ℝ) (hκ : Integrable κ) :
    ComponentL2 (volume.restrict AVenhance.unitCube) E →L[ℝ] ComponentL2 (volume.restrict AVenhance.unitCube) E :=
  torusToCell.toContinuousLinearMap.comp
    ((averagingOperator (torusQuotient.comp ρ) (continuous_torusQuotient.comp hρ) κ hκ).comp
      cellToTorus.toContinuousLinearMap)

omit [BorelSpace E] [CompleteSpace E] in
theorem cellToTorus_global_ae {K : ℕ}
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) (a : JetIndex2 K) :
    (fun x => cellToTorus (D a) (torusQuotient x)) =ᵐ[volume]
      periodicJetRepresentative D a :=
  ae_torusQuotient (cellToTorus_ae (D a))

omit [BorelSpace E] in
theorem periodicComponentAverage_global_ae {K : ℕ}
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) (a : JetIndex2 K)
    (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ) {κ : Vec 2 → ℝ} (hκ : Integrable κ) :
    (fun x => cellToTorus (periodicComponentAverage ρ hρ κ hκ (D a)) (torusQuotient x)) =ᵐ[volume]
      (fun x => averagingOperator (torusQuotient.comp ρ)
        (continuous_torusQuotient.comp hρ) κ hκ (cellToTorus (D a)) (torusQuotient x)) := by
  change (fun x => cellToTorus (torusToCell
    (averagingOperator (torusQuotient.comp ρ) (continuous_torusQuotient.comp hρ)
      κ hκ (cellToTorus (D a)))) (torusQuotient x)) =ᵐ[volume] _
  rw [cellToTorus_torusToCell]

/-- Average every ordered derivative component on the normalized torus. -/
def periodicJetAverage {K : ℕ} (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    (κ : Vec 2 → ℝ) (hκ : Integrable κ)
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) :
    JetL2 (volume.restrict AVenhance.unitCube) K E :=
  WithLp.toLp 2 (fun a => periodicComponentAverage ρ hρ κ hκ (D a))

theorem periodicJetAverage_mem_graph {K : ℕ} (f : TorusHk K E)
    (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ) {κ : Vec 2 → ℝ} (hκ : Integrable κ) :
    periodicJetAverage ρ hρ κ hκ f.val ∈ torusHkGraph (E := E) K := by
  rw [mem_torusHkGraph_iff]
  refine ⟨periodicJetRepresentative_periodic _, periodicJetRepresentative_memL2 _, ?_⟩
  intro j w i e
  have hin (a : JetIndex2 K) := cellToTorus_global_ae f.val a
  have hw : ∀ e : E, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (cellToTorus (f.val (lowerIndex2 j w)) (torusQuotient x)))
      (fun x => inner ℝ e (cellToTorus (f.val (nextIndex2 j w i)) (torusQuotient x))) := by
    intro e
    apply hasWeakPartialDerivOn_congr_ae _ _ (f.toFunction.hasPeriodicWeakJet.2.2 j w i e)
    · simpa only [Measure.restrict_univ, Function.comp_def, TorusHk.toFunction] using
        (hin (lowerIndex2 j w)).symm.fun_comp (inner ℝ e)
    · simpa only [Measure.restrict_univ, Function.comp_def, TorusHk.toFunction] using
        (hin (nextIndex2 j w i)).symm.fun_comp (inner ℝ e)
  have havg := averagingOperator_hasWeakPartialDeriv_torus hw ρ hρ hκ e
  have hout (a : JetIndex2 K) :=
    (periodicComponentAverage_global_ae f.val a ρ hρ hκ).symm.trans
      (cellToTorus_global_ae (periodicJetAverage ρ hρ κ hκ f.val) a)
  apply hasWeakPartialDerivOn_congr_ae _ _ havg
  · simpa only [Measure.restrict_univ, Function.comp_def] using
      (hout (lowerIndex2 j w)).fun_comp (inner ℝ e)
  · simpa only [Measure.restrict_univ, Function.comp_def] using
      (hout (nextIndex2 j w i)).fun_comp (inner ℝ e)

/-- Literal plane convolution, promoted to its exact ordered weak graph. -/
def planeWeakAverage {K : ℕ} (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    (κ : Vec 2 → ℝ) (hκ : Integrable κ)
    (f : PlaneHk (Set.univ : Set (Vec 2)) K E) : PlaneHk (Set.univ : Set (Vec 2)) K E :=
  ⟨planeJetAverage ρ hρ κ hκ f.val, planeJetAverage_mem_graph f ρ hρ hκ⟩

/-- Literal torus convolution, promoted to its exact periodic weak graph. -/
def periodicWeakAverage {K : ℕ} (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    (κ : Vec 2 → ℝ) (hκ : Integrable κ) (f : TorusHk K E) : TorusHk K E :=
  ⟨periodicJetAverage ρ hρ κ hκ f.val, periodicJetAverage_mem_graph f ρ hρ hκ⟩

omit [BorelSpace E] in
theorem periodicComponentAverage_momentKernel_norm (ρ : Vec 2 →+ Vec 2)
    (hρ : Continuous ρ) {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1) (n : ℕ+)
    (f : ComponentL2 (volume.restrict AVenhance.unitCube) E) :
    ‖periodicComponentAverage ρ hρ (momentKernel φ₀ n)
      (integrable_momentKernel hφ₀ n) f‖ ≤ ‖f‖ := by
  change ‖torusToCell (averagingOperator (torusQuotient.comp ρ)
    (continuous_torusQuotient.comp hρ) (momentKernel φ₀ n)
    (integrable_momentKernel hφ₀ n) (cellToTorus f))‖ ≤ _
  rw [torusToCell.norm_map]
  calc
    _ ≤ 1 * ‖cellToTorus f‖ := ContinuousLinearMap.le_of_opNorm_le _
      (averagingOperator_momentKernel_contraction (torusQuotient.comp ρ)
        (continuous_torusQuotient.comp hρ) hφ₀ hnonneg hmass n) _
    _ = ‖f‖ := by rw [one_mul, cellToTorus.norm_map]

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem factorialNormSq_le_of_component_norm_le {K : ℕ} {U : Set (Vec 2)}
    (r : ℝ) (D F : JetL2 (volume.restrict U) K E)
    (h : ∀ a, ‖D a‖ ≤ ‖F a‖) : factorialNormSq r D ≤ factorialNormSq r F := by
  unfold factorialNormSq derivativeNormSq
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (by
    simpa only [factorialWeight] using factorialWeight_nonneg r j.val)
  apply Finset.sum_le_sum
  intro w _
  simpa only [pow_two] using
    mul_self_le_mul_self (norm_nonneg (D ⟨j, w⟩)) (h ⟨j, w⟩)

theorem periodicWeakAverage_momentKernel_factorialNormSq {K : ℕ}
    (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (hnonneg : ∀ z, 0 ≤ φ₀ z)
    (hmass : ∫ z, φ₀ z = 1) (n : ℕ+) (r : ℝ)
    (f : TorusHk K E) :
    factorialNormSq r (periodicWeakAverage ρ hρ (momentKernel φ₀ n)
      (integrable_momentKernel hφ₀ n) f).val ≤ factorialNormSq r f.val := by
  apply factorialNormSq_le_of_component_norm_le r
  intro a
  exact periodicComponentAverage_momentKernel_norm ρ hρ hφ₀ hnonneg hmass n (f.val a)

/-- Paired moment smoothing on the normalized torus. -/
def pairedTorusMomentSmoothing {K : ℕ} (r : ℝ) (H₁ H₂ : Vec 2 →L[ℝ] Vec 2)
    {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (n : ℕ+)
    (f : TorusHk K E) : TorusHk K E :=
  periodicWeakAverage (displacement r H₁) (continuous_displacement r H₁)
    (momentKernel φ₀ n) (integrable_momentKernel hφ₀ n)
    (periodicWeakAverage (displacement r H₂) (continuous_displacement r H₂)
      (momentKernel φ₀ n) (integrable_momentKernel hφ₀ n) f)

end AVRegularity.Analysis.Convolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Analysis.Convolution

/-! Named single and paired smoothers on the ordered weak-jet carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The single directional moment-kernel smoother on the plane Sobolev carrier. -/
def planeMomentSmoothing {K : ℕ} (r : ℝ) (H : Vec 2 →L[ℝ] Vec 2)
    {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (n : ℕ+)
    (f : PlaneHk (Set.univ : Set (Vec 2)) K E) : PlaneHk (Set.univ : Set (Vec 2)) K E :=
  planeWeakAverage (displacement r H) (continuous_displacement r H)
    (momentKernel φ₀ n) (integrable_momentKernel hφ₀ n) f

/-- The single directional moment-kernel smoother on the torus Sobolev carrier. -/
def torusMomentSmoothing {K : ℕ} (r : ℝ) (H : Vec 2 →L[ℝ] Vec 2)
    {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (n : ℕ+)
    (f : TorusHk K E) : TorusHk K E :=
  periodicWeakAverage (displacement r H) (continuous_displacement r H)
    (momentKernel φ₀ n) (integrable_momentKernel hφ₀ n) f

@[simp] theorem planeMomentSmoothing_component {K : ℕ} (r : ℝ) (H : Vec 2 →L[ℝ] Vec 2)
    {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (n : ℕ+)
    (f : PlaneHk (Set.univ : Set (Vec 2)) K E) (a : JetIndex2 K) :
    (planeMomentSmoothing r H hφ₀ n f).val a =
      planeComponentAverage (displacement r H) (continuous_displacement r H)
        (momentKernel φ₀ n) (integrable_momentKernel hφ₀ n) (f.val a) := rfl

@[simp] theorem torusMomentSmoothing_component {K : ℕ} (r : ℝ) (H : Vec 2 →L[ℝ] Vec 2)
    {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (n : ℕ+)
    (f : TorusHk K E) (a : JetIndex2 K) :
    (torusMomentSmoothing r H hφ₀ n f).val a =
      periodicComponentAverage (displacement r H) (continuous_displacement r H)
        (momentKernel φ₀ n) (integrable_momentKernel hφ₀ n) (f.val a) := rfl

end AVRegularity.Analysis.Convolution
end
