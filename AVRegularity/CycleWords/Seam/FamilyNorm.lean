-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Assembly.SeamNorms
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit

@[expose] public noncomputable section

section
open MeasureTheory Filter Asymptotics Complex
open scoped ENNReal SchwartzMap FourierTransform ComplexConjugate
namespace AVRegularity.CycleWords.Seam

/-! # A one-dimensional reproducing kernel and its Poisson summation

`Bump1` is a smooth even bump on `ℝ`, `1` on `[-π/2, π/2]` and `0` outside `(-3π/4, 3π/4)`.
Its kernel `kernelOneDimComplex = 𝓕⁻ ψ`, `ψ(s) = Bump1 (2π s)`, is a Schwartz function with real values
(`K1c_eq_ofReal`, `kernelOneDim = re ∘ kernelOneDimComplex`), and

* inversion (`K1c_inversion`): `∫ e^{-iσt} k(t) dt = ν₁(σ)` for every `σ`;
* Poisson summation (`K1c_poisson`): `∑_m e^{iθ(x+m)} k(x+m) = ν₁(θ)` for every `x` and
  `|θ| ≤ π`, since the Fourier coefficients `ν₁(2πn - θ)`, `n ≠ 0`, vanish
  (`|2πn - θ| ≥ π > 3π/4`);
* the lattice sums `∑_m |f(x+m)|` of a Schwartz function are bounded uniformly in `x`
  (`schwartz_lattice_le`). -/

/-- The one-dimensional bump. -/
def Bump1 : ContDiffBump (0 : ℝ) where
  rIn := Real.pi / 2
  rOut := 3 * Real.pi / 4
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith [Real.pi_pos]

theorem Bump1_neg (t : ℝ) : Bump1 (-t) = Bump1 t := Bump1.neg t

theorem Bump1_rIn : Bump1.rIn = Real.pi / 2 := rfl

theorem Bump1_rOut : Bump1.rOut = 3 * Real.pi / 4 := rfl

theorem Bump1_one {t : ℝ} (ht : |t| ≤ Real.pi / 2) : Bump1 t = 1 :=
  Bump1.one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, Bump1_rIn]
    exact ht)

theorem Bump1_zero {t : ℝ} (ht : 3 * Real.pi / 4 ≤ |t|) : Bump1 t = 0 :=
  Bump1.zero_of_le_dist (by
    rw [Real.dist_eq, sub_zero, Bump1_rOut]
    exact ht)

theorem Bump1_contDiff : ContDiff ℝ (⊤ : ℕ∞) (Bump1 : ℝ → ℝ) := Bump1.contDiff

theorem two_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity

theorem Psi_hasCompactSupport :
    HasCompactSupport (fun s : ℝ => ((Bump1 (2 * Real.pi * s) : ℝ) : ℂ)) :=
  (Bump1.hasCompactSupport.comp_homeomorph
    (Homeomorph.mulLeft₀ (2 * Real.pi) two_pi_ne)).comp_left Complex.ofReal_zero

theorem Psi_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => ((Bump1 (2 * Real.pi * s) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (Bump1_contDiff.comp (contDiff_const.mul contDiff_id))

/-- The scaled bump `s ↦ ν₁(2πs)` as a complex Schwartz function. -/
def scaledBumpSchwartz : 𝓢(ℝ, ℂ) := Psi_hasCompactSupport.toSchwartzMap Psi_contDiff

theorem Psi_apply (s : ℝ) : scaledBumpSchwartz s = ((Bump1 (2 * Real.pi * s) : ℝ) : ℂ) := rfl

theorem Psi_neg (s : ℝ) : scaledBumpSchwartz (-s) = scaledBumpSchwartz s := by
  simp only [Psi_apply, mul_neg, Bump1_neg]

/-- The one-dimensional kernel `𝓕⁻ ψ`. -/
def kernelOneDimComplex : 𝓢(ℝ, ℂ) := 𝓕⁻ scaledBumpSchwartz

theorem K1c_apply (t : ℝ) :
    kernelOneDimComplex t = ∫ s : ℝ, Complex.exp (↑(-2 * Real.pi * s * -t) * Complex.I) • scaledBumpSchwartz s := by
  rw [kernelOneDimComplex, congrFun (SchwartzMap.fourierInv_coe scaledBumpSchwartz) t, Real.fourierInv_eq_fourier_neg,
    Real.fourier_real_eq_integral_exp_smul]

theorem K1c_conj (t : ℝ) : conj (kernelOneDimComplex t) = kernelOneDimComplex t := by
  rw [K1c_apply, ← integral_conj]
  rw [← integral_neg_eq_self (fun s : ℝ =>
    Complex.exp (↑(-2 * Real.pi * s * -t) * Complex.I) • scaledBumpSchwartz s)]
  congr 1
  funext s
  rw [Psi_neg, smul_eq_mul, smul_eq_mul, map_mul, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, Psi_apply, Complex.conj_ofReal]
  congr 2
  push_cast
  ring

/-- The kernel is real. -/
def kernelOneDim (t : ℝ) : ℝ := (kernelOneDimComplex t).re

theorem K1c_eq_ofReal (t : ℝ) : kernelOneDimComplex t = (kernelOneDim t : ℂ) :=
  (Complex.conj_eq_iff_re.1 (K1c_conj t)).symm

theorem K1_continuous : Continuous kernelOneDim := Complex.continuous_re.comp kernelOneDimComplex.continuous

theorem K1_integrable : Integrable kernelOneDim := kernelOneDimComplex.integrable.re

theorem K1c_fourier : 𝓕 (kernelOneDimComplex : ℝ → ℂ) = (scaledBumpSchwartz : ℝ → ℂ) := by
  funext w
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) => f w) (FourierInvPair.fourier_fourierInv_eq (E := 𝓢(ℝ, ℂ)) (F := 𝓢(ℝ, ℂ)) scaledBumpSchwartz)
  rw [congrFun (SchwartzMap.fourier_coe (𝓕⁻ scaledBumpSchwartz)) w] at h
  exact h

/-- **Inversion**: `∫ e^{-iσt} k(t) dt = ν₁(σ)`. -/
theorem K1c_inversion (σ : ℝ) :
    ∫ t : ℝ, Complex.exp (↑(-σ * t) * Complex.I) * kernelOneDimComplex t = (Bump1 σ : ℂ) := by
  have h := congrFun K1c_fourier (σ / (2 * Real.pi))
  rw [Real.fourier_real_eq_integral_exp_smul, Psi_apply] at h
  have e1 : ∀ v : ℝ, (-2 * Real.pi * v * (σ / (2 * Real.pi)) : ℝ) = -σ * v := by
    intro v
    field_simp
  have e2 : 2 * Real.pi * (σ / (2 * Real.pi)) = σ := by
    field_simp
  simp only [e1, e2, smul_eq_mul] at h
  exact h

/-- The Fourier coefficients of the modulated kernel. -/
theorem K1c_modulated_fourier (θ : ℝ) (n : ℝ) :
    𝓕 (fun t : ℝ => Complex.exp (↑(θ * t) * Complex.I) * kernelOneDimComplex t) n =
      (Bump1 (2 * Real.pi * n - θ) : ℂ) := by
  have h := congrFun K1c_fourier (n - θ / (2 * Real.pi))
  rw [Real.fourier_real_eq_integral_exp_smul, Psi_apply] at h
  rw [Real.fourier_real_eq_integral_exp_smul]
  have e : ∀ v : ℝ, Complex.exp (↑(-2 * Real.pi * v * n) * Complex.I) •
      (Complex.exp (↑(θ * v) * Complex.I) * kernelOneDimComplex v) =
      Complex.exp (↑(-2 * Real.pi * v * (n - θ / (2 * Real.pi))) * Complex.I) • kernelOneDimComplex v := by
    intro v
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [integral_congr_ae (Eventually.of_forall e), h]
  congr 2
  field_simp

/-- **Poisson summation for the modulated kernel.** -/
theorem K1c_poisson {θ : ℝ} (hθ : |θ| ≤ Real.pi) (x : ℝ) :
    ∑' m : ℤ, Complex.exp (↑(θ * (x + m)) * Complex.I) * kernelOneDimComplex (x + m) = (Bump1 θ : ℂ) := by
  set f : ℝ → ℂ := fun t => Complex.exp (↑(θ * t) * Complex.I) * kernelOneDimComplex t with hfd
  have hc : Continuous f := by
    rw [hfd]
    fun_prop
  have hnorm : ∀ t, ‖f t‖ = ‖kernelOneDimComplex t‖ := by
    intro t
    rw [hfd, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hf : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
    have hk := kernelOneDimComplex.isBigO_cocompact_rpow (-2)
    simp only [Real.norm_eq_abs] at hk
    refine isBigO_norm_left.1 ?_
    simp only [hnorm]
    exact isBigO_norm_left.2 hk
  have hzero : ∀ n : ℤ, n ≠ 0 → 𝓕 f n = 0 := by
    intro n hn
    rw [hfd, K1c_modulated_fourier, Bump1_zero, Complex.ofReal_zero]
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn
    have h2 : |2 * Real.pi * n| = 2 * Real.pi * |(n : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have h3 := abs_sub_abs_le_abs_sub (2 * Real.pi * n) θ
    nlinarith [Real.pi_pos]
  have hsum : Summable fun n : ℤ => 𝓕 f n :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => hzero n (by simpa using hn)
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc (by norm_num) hf hsum x
  have hR : ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle) = (Bump1 θ : ℂ) := by
    rw [tsum_eq_single 0 fun n hn => by rw [hzero n hn, zero_mul], fourier_zero, mul_one, hfd,
      Int.cast_zero, K1c_modulated_fourier, mul_zero, zero_sub, Bump1_neg]
  show ∑' m : ℤ, f (x + m) = _
  rw [hP, hR]

/-- **The lattice sums of a Schwartz function are bounded uniformly.** -/
theorem schwartz_lattice_le (f : 𝓢(ℝ, ℂ)) :
    ∃ S : ℝ≥0∞, S < ⊤ ∧ ∀ x : ℝ, ∑' m : ℤ, ‖f (x + m)‖ₑ ≤ S := by
  set g : C(ℝ, ℂ) := ⟨f, f.continuous⟩ with hgd
  have hg : g =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
    have hk := f.isBigO_cocompact_rpow (-2)
    simp only [Real.norm_eq_abs] at hk
    exact hk
  set K : TopologicalSpace.Compacts ℝ := ⟨Set.Icc 0 1, isCompact_Icc⟩ with hKd
  have hs : Summable fun n : ℤ => ‖(g.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ :=
    summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
      ((isBigO_norm_restrict_cocompact g (by norm_num : (0 : ℝ) < 2) hg K).comp_tendsto
        Int.tendsto_coe_cofinite)
  refine ⟨ENNReal.ofReal (∑' n : ℤ, ‖(g.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖),
    ENNReal.ofReal_lt_top, fun x => ?_⟩
  rw [ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) hs]
  set s := Int.fract x with hsd
  have hsK : s ∈ (K : Set ℝ) := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hx : ∀ m : ℤ, x + m = s + ((⌊x⌋ + m : ℤ) : ℝ) := by
    intro m
    rw [hsd, Int.cast_add, ← add_assoc, Int.fract_add_floor]
  calc ∑' m : ℤ, ‖f (x + m)‖ₑ = ∑' m : ℤ, ‖f (s + ((⌊x⌋ + m : ℤ) : ℝ))‖ₑ := by
        simp only [hx]
    _ = ∑' n : ℤ, ‖f (s + n)‖ₑ := (Equiv.addLeft ⌊x⌋).tsum_eq (fun n : ℤ => ‖f (s + n)‖ₑ)
    _ ≤ _ := ENNReal.tsum_le_tsum fun n => by
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        have h := ContinuousMap.norm_coe_le_norm
          ((g.comp (ContinuousMap.addRight (n : ℝ))).restrict K) ⟨s, hsK⟩
        have heq : ((g.comp (ContinuousMap.addRight (n : ℝ))).restrict K) ⟨s, hsK⟩ =
            f (s + n) := rfl
        rw [heq] at h
        exact h

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Filter Complex Homogenization
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The product reproducing kernel on the plane

`productCutoff θ = ν₁(θ₀)ν₁(θ₁)` and `productKernel x = k(x₀)k(x₁)` (`k = kernelOneDim`). From the one-dimensional facts:

* `K_inversion`: `∫ e^{iθ·u} K(u) du = ν(θ)` for every `θ`;
* `K_poisson`: `∑_{k ∈ ℤ²} e^{iθ·(x+k)} K(x+k) = ν(θ)` for every `x` and `θ` in the closed cube
  `|θᵢ| ≤ π`;
* `K_lattice_le`: `∑_k |K(x+k)| ≤ S` uniformly in `x`. -/

/-- The product cutoff. -/
def productCutoff (θ : Vec 2) : ℝ := Bump1 (θ 0) * Bump1 (θ 1)

/-- The product kernel. -/
def productKernel (x : Vec 2) : ℝ := kernelOneDim (x 0) * kernelOneDim (x 1)

/-- The lattice translate `x + k`. -/
def Shift (x : Vec 2) (k : Fin 2 → ℤ) : Vec 2 := x + fun i => (k i : ℝ)

theorem vecDot_two (θ x : Vec 2) : vecDot θ x = θ 0 * x 0 + θ 1 * x 1 := by
  simp [vecDot, Fin.sum_univ_two]

theorem Nu_neg (θ : Vec 2) : productCutoff (-θ) = productCutoff θ := by
  simp only [productCutoff, Pi.neg_apply, Bump1_neg]

theorem K_continuous : Continuous productKernel := by
  unfold productKernel
  exact (K1_continuous.comp (continuous_apply 0)).mul (K1_continuous.comp (continuous_apply 1))

theorem K_integrable : Integrable productKernel := by
  have h := Integrable.fintype_prod (f := fun _ : Fin 2 => kernelOneDim) (μ := fun _ => volume)
    (fun _ => K1_integrable)
  simp only [Fin.prod_univ_two] at h
  exact h

/-- The complex exponential of a sum of two real phases. -/
theorem exp_add_two (a b : ℝ) :
    Complex.exp (↑(a + b) * Complex.I) =
      Complex.exp (↑a * Complex.I) * Complex.exp (↑b * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Inversion on the plane.** -/
theorem K_inversion (θ : Vec 2) :
    ∫ u : Vec 2, Complex.exp (↑(vecDot θ u) * Complex.I) * (productKernel u : ℂ) = (productCutoff θ : ℂ) := by
  have h1 : ∀ i : Fin 2, ∫ t : ℝ, Complex.exp (↑(θ i * t) * Complex.I) * kernelOneDimComplex t =
      (Bump1 (θ i) : ℂ) := by
    intro i
    have h := K1c_inversion (-θ i)
    simp only [neg_neg, Bump1_neg] at h
    exact h
  have he : ∀ u : Vec 2, Complex.exp (↑(vecDot θ u) * Complex.I) * (productKernel u : ℂ) =
      ∏ i : Fin 2, (fun (i : Fin 2) (t : ℝ) => Complex.exp (↑(θ i * t) * Complex.I) * kernelOneDimComplex t)
        i (u i) := by
    intro u
    simp only [Fin.prod_univ_two, K1c_eq_ofReal, vecDot_two, exp_add_two, productKernel,
      Complex.ofReal_mul]
    ring
  have hprod := integral_fin_nat_prod_volume_eq_prod (𝕜 := ℂ) (E := fun _ : Fin 2 => ℝ)
    (fun (i : Fin 2) (t : ℝ) => Complex.exp (↑(θ i * t) * Complex.I) * kernelOneDimComplex t)
  rw [Fin.prod_univ_two, h1, h1] at hprod
  simp only [he]
  rw [productCutoff, Complex.ofReal_mul]
  exact hprod

/-- Summability of a lattice family from a finite sum of norms. -/
theorem summable_of_tsum_enorm {ι : Type*} {f : ι → ℂ} (h : ∑' m, ‖f m‖ₑ < ⊤) :
    Summable fun m => ‖f m‖ := by
  have h' : ∑' m, (‖f m‖₊ : ℝ≥0∞) ≠ ⊤ := by
    simpa only [enorm_eq_nnnorm] using h.ne
  exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h')

/-- The one-dimensional constant of the lattice sums of the kernel. -/
def kernelLatticeConst : ℝ≥0∞ := Classical.choose (schwartz_lattice_le kernelOneDimComplex)

theorem S1_lt_top : kernelLatticeConst < ⊤ := (Classical.choose_spec (schwartz_lattice_le kernelOneDimComplex)).1

theorem S1_le (x : ℝ) : ∑' m : ℤ, ‖kernelOneDimComplex (x + m)‖ₑ ≤ kernelLatticeConst :=
  (Classical.choose_spec (schwartz_lattice_le kernelOneDimComplex)).2 x

theorem lattice_summable (x : ℝ) (θ : ℝ) :
    Summable fun m : ℤ => ‖Complex.exp (↑(θ * (x + m)) * Complex.I) * kernelOneDimComplex (x + m)‖ := by
  have h : ∑' m : ℤ, ‖Complex.exp (↑(θ * (x + m)) * Complex.I) * kernelOneDimComplex (x + m)‖ₑ < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) ((S1_le x).trans_lt S1_lt_top)
    congr 1
    funext m
    rw [enorm_mul, ← ofReal_norm (Complex.exp _), Complex.norm_exp_ofReal_mul_I,
      ENNReal.ofReal_one, one_mul]
  exact summable_of_tsum_enorm h

/-- The lattice sum over `ℤ²` of a product, as a product of lattice sums over `ℤ`. -/
theorem tsum_fin_two {f g : ℤ → ℂ} (hf : Summable fun m => ‖f m‖)
    (hg : Summable fun m => ‖g m‖) :
    ∑' k : Fin 2 → ℤ, f (k 0) * g (k 1) = (∑' m, f m) * ∑' m, g m := by
  rw [tsum_mul_tsum_of_summable_norm hf hg]
  exact ((finTwoArrowEquiv ℤ).tsum_eq (fun z : ℤ × ℤ => f z.1 * g z.2))

theorem summable_fin_two {f g : ℤ → ℂ} (hf : Summable fun m => ‖f m‖)
    (hg : Summable fun m => ‖g m‖) :
    Summable fun k : Fin 2 → ℤ => f (k 0) * g (k 1) := by
  have h := summable_mul_of_summable_norm hf hg
  exact (finTwoArrowEquiv ℤ).summable_iff.2 h

/-- **Poisson summation on the plane.** -/
theorem K_poisson {θ : Vec 2} (hθ : ∀ i, |θ i| ≤ Real.pi) (x : Vec 2) :
    ∑' k : Fin 2 → ℤ, Complex.exp (↑(vecDot θ (Shift x k)) * Complex.I) *
      (productKernel (Shift x k) : ℂ) = (productCutoff θ : ℂ) := by
  set f : Fin 2 → ℤ → ℂ := fun i m =>
    Complex.exp (↑(θ i * (x i + m)) * Complex.I) * kernelOneDimComplex (x i + m) with hfd
  have he : ∀ k : Fin 2 → ℤ, Complex.exp (↑(vecDot θ (Shift x k)) * Complex.I) *
      (productKernel (Shift x k) : ℂ) = f 0 (k 0) * f 1 (k 1) := by
    intro k
    simp only [hfd, Shift, vecDot_two, Pi.add_apply, exp_add_two, productKernel,
      Complex.ofReal_mul, K1c_eq_ofReal]
    ring
  simp only [he]
  rw [tsum_fin_two (lattice_summable (x 0) (θ 0)) (lattice_summable (x 1) (θ 1))]
  try simp only [hfd]
  rw [K1c_poisson (hθ 0), K1c_poisson (hθ 1), productCutoff, Complex.ofReal_mul]

theorem K_poisson_summable (θ : Vec 2) (x : Vec 2) :
    Summable fun k : Fin 2 → ℤ => Complex.exp (↑(vecDot θ (Shift x k)) * Complex.I) *
      (productKernel (Shift x k) : ℂ) := by
  set f : Fin 2 → ℤ → ℂ := fun i m =>
    Complex.exp (↑(θ i * (x i + m)) * Complex.I) * kernelOneDimComplex (x i + m) with hfd
  have he : (fun k : Fin 2 → ℤ => Complex.exp (↑(vecDot θ (Shift x k)) * Complex.I) *
      (productKernel (Shift x k) : ℂ)) = fun k => f 0 (k 0) * f 1 (k 1) := by
    funext k
    simp only [hfd, Shift, vecDot_two, Pi.add_apply, exp_add_two, productKernel,
      Complex.ofReal_mul, K1c_eq_ofReal]
    ring
  rw [he]
  exact summable_fin_two (lattice_summable (x 0) (θ 0)) (lattice_summable (x 1) (θ 1))

/-- **The lattice sums of the kernel are bounded uniformly.** -/
theorem K_lattice_le (x : Vec 2) : ∑' k : Fin 2 → ℤ, ‖productKernel (Shift x k)‖ₑ ≤ kernelLatticeConst * kernelLatticeConst := by
  have he : ∀ k : Fin 2 → ℤ, ‖productKernel (Shift x k)‖ₑ =
      ‖kernelOneDimComplex (x 0 + (k 0 : ℝ))‖ₑ * ‖kernelOneDimComplex (x 1 + (k 1 : ℝ))‖ₑ := by
    intro k
    rw [K1c_eq_ofReal, K1c_eq_ofReal, ← enorm_mul, ← Complex.ofReal_mul]
    simp only [productKernel, Shift, Pi.add_apply]
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  simp only [he]
  rw [← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [ENNReal.tsum_prod (f := fun (a b : ℤ) => ‖kernelOneDimComplex (x 0 + (a : ℝ))‖ₑ * ‖kernelOneDimComplex (x 1 + (b : ℝ))‖ₑ)]
  calc ∑' a : ℤ, ∑' b : ℤ, ‖kernelOneDimComplex (x 0 + (a : ℝ))‖ₑ * ‖kernelOneDimComplex (x 1 + (b : ℝ))‖ₑ
      = ∑' a : ℤ, ‖kernelOneDimComplex (x 0 + (a : ℝ))‖ₑ * ∑' b : ℤ, ‖kernelOneDimComplex (x 1 + (b : ℝ))‖ₑ := by
        congr 1
        funext a
        rw [ENNReal.tsum_mul_left]
    _ = (∑' a : ℤ, ‖kernelOneDimComplex (x 0 + (a : ℝ))‖ₑ) * ∑' b : ℤ, ‖kernelOneDimComplex (x 1 + (b : ℝ))‖ₑ := by
        rw [ENNReal.tsum_mul_right]
    _ ≤ kernelLatticeConst * kernelLatticeConst := mul_le_mul' (S1_le _) (S1_le _)

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Seam

/-! Multiplication of a plane carrier by a coefficient that grows like a weight `ρ`: if
`‖D^l C(x)‖ ≤ A_l ρ(x)` for `l ≤ K` and every jet of the carrier is in `L²` after multiplication by
`ρ`, the ordered Leibniz jet is again a plane carrier (the weak jet identities need only local
integrability). -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A Leibniz term is in `L²` when the coefficient growth is absorbed by the weighted jets. -/
theorem multiplicationTerm_memLp_weighted {K j : ℕ} (hj : j ≤ K)
    {C : Vec 2 → E →L[ℝ] F} (hC : ContDiff ℝ (K : ℕ) C) {D : RawJet2 K E}
    (hD : JetMemL2On Set.univ D) (ρ : Vec 2 → ℝ)
    (hρD : ∀ a, MemLp (fun x => ρ x * ‖D a x‖) 2 volume) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l * ρ x)
    (m : PositionMask j) (w : DerivativeWord2 j) :
    MemLp (multiplicationTerm hj C D m w) 2 volume := by
  let l : Fin (K + 1) := ⟨maskLeftLength j m,
    Nat.lt_succ_of_le ((maskLeftLength_le j m).trans hj)⟩
  have hCl : ContDiff ℝ (l.val : ℕ) C :=
    hC.of_le (by exact_mod_cast (Nat.le_of_lt_succ l.isLt))
  have hcont : Continuous
      (orderedCoefficientDerivative C l.val (maskWordEquiv 2 j m w).1) :=
    (orderedCoefficientDerivative_contDiff C l.val 0
      (by simpa only [Nat.add_zero] using hCl) (maskWordEquiv 2 j m w).1).continuous
  have hDm : MemLp (D (maskJetIndex hj m w)) 2 volume := by
    simpa only [Measure.restrict_univ] using hD (maskJetIndex hj m w)
  apply ((hρD (maskJetIndex hj m w)).const_mul (|A l|)).of_le
  · exact (ContinuousLinearMap.apply ℝ F).flip.aestronglyMeasurable_comp₂
      hcont.aestronglyMeasurable hDm.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    change ‖orderedCoefficientDerivative C l.val (maskWordEquiv 2 j m w).1 x
      (D (maskJetIndex hj m w) x)‖ ≤ ‖|A l| * (ρ x * ‖D (maskJetIndex hj m w) x‖)‖
    have h1 := (orderedCoefficientDerivative C l.val (maskWordEquiv 2 j m w).1 x).le_opNorm
      (D (maskJetIndex hj m w) x)
    have h2 := (orderedCoefficientDerivative_norm_le_array C l.val
      (maskWordEquiv 2 j m w).1 x).trans (hb l x)
    have h3 : A l * ρ x ≤ |A l| * |ρ x| := by
      rw [← abs_mul]
      exact le_abs_self _
    calc _ ≤ ‖orderedCoefficientDerivative C l.val (maskWordEquiv 2 j m w).1 x‖ *
          ‖D (maskJetIndex hj m w) x‖ := h1
      _ ≤ (|A l| * |ρ x|) * ‖D (maskJetIndex hj m w) x‖ :=
          mul_le_mul_of_nonneg_right (h2.trans h3) (norm_nonneg _)
      _ = ‖|A l| * (ρ x * ‖D (maskJetIndex hj m w) x‖)‖ := by
          rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
          ring

theorem multiplicationRawJet_memL2_weighted {K : ℕ}
    {C : Vec 2 → E →L[ℝ] F} (hC : ContDiff ℝ (K : ℕ) C) {D : RawJet2 K E}
    (hD : JetMemL2On Set.univ D) (ρ : Vec 2 → ℝ)
    (hρD : ∀ a, MemLp (fun x => ρ x * ‖D a x‖) 2 volume) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l * ρ x) :
    JetMemL2On Set.univ (multiplicationRawJet C D) := by
  intro a
  rw [Measure.restrict_univ]
  exact memLp_finsetSum Finset.univ (fun m _hm =>
    multiplicationTerm_memLp_weighted (Nat.le_of_lt_succ a.1.isLt) hC hD ρ hρD hb m a.2)

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- **Weighted coefficient multiplication of a plane carrier.** -/
def PlaneHk.mulCoefficientWeighted {K : ℕ} (w : PlaneHk Set.univ K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C) (ρ : Vec 2 → ℝ)
    (hρw : ∀ a, MemLp (fun x => ρ x * ‖w.toFunction.jet a x‖) 2 volume)
    {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l * ρ x) :
    PlaneHk Set.univ K F :=
  (show PlaneHkFunction Set.univ K F from
    ⟨multiplicationRawJet C w.toFunction.jet,
      multiplicationRawJet_memL2_weighted hC w.toFunction.memL2 ρ hρw hb,
      multiplicationRawJet_hasOrderedWeakJetOn hC w.toFunction.hasWeakJet
        (jet_scalar_locallyIntegrable w.toFunction.memL2)⟩).toHk

theorem PlaneHk.mulCoefficientWeighted_jet_ae {K : ℕ} (w : PlaneHk Set.univ K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C) (ρ : Vec 2 → ℝ)
    (hρw : ∀ a, MemLp (fun x => ρ x * ‖w.toFunction.jet a x‖) 2 volume)
    {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l * ρ x) (a : JetIndex2 K) :
    (PlaneHk.mulCoefficientWeighted w C hC ρ hρw hb).toFunction.jet a =ᵐ[volume]
      multiplicationRawJet C w.toFunction.jet a := by
  have h := (show PlaneHkFunction Set.univ K F from
    ⟨multiplicationRawJet C w.toFunction.jet,
      multiplicationRawJet_memL2_weighted hC w.toFunction.memL2 ρ hρw hb,
      multiplicationRawJet_hasOrderedWeakJetOn hC w.toFunction.hasWeakJet
        (jet_scalar_locallyIntegrable w.toFunction.memL2)⟩).toHk_toFunction_ae a
  simpa only [Measure.restrict_univ, PlaneHk.mulCoefficientWeighted] using h
end

/-! The partial derivative of a native plane carrier: `∂_k : PlaneHk (K+1) → PlaneHk K`, whose
ordered jets are those of the carrier with `k` prefixed to the word (ordered weak jets append the
newest derivative at the end, so a prefixed first derivative needs no commutation of weak
derivatives). -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The jet index with `k` prefixed. -/
def prefixIndex2 {K : ℕ} (k : Fin 2) (a : JetIndex2 K) : JetIndex2 (K + 1) :=
  ⟨⟨a.1.val + 1, Nat.succ_lt_succ a.1.isLt⟩, Fin.cons k a.2⟩

/-- The raw jet of the `k`-th partial derivative. -/
def partialRawJet {K : ℕ} (k : Fin 2) (D : RawJet2 (K + 1) E) : RawJet2 K E :=
  fun a => D (prefixIndex2 k a)

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem partialRawJet_memL2 {K : ℕ} (k : Fin 2) {D : RawJet2 (K + 1) E}
    (hD : JetMemL2On Set.univ D) : JetMemL2On Set.univ (partialRawJet k D) :=
  fun a => hD (prefixIndex2 k a)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem partialRawJet_hasWeakJet {K : ℕ} (k : Fin 2) {D : RawJet2 (K + 1) E}
    (hD : HasOrderedWeakJetOn Set.univ D) :
    HasOrderedWeakJetOn Set.univ (partialRawJet k D) := by
  intro j w i e
  have h := hD ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ (Fin.cons k w) i e
  have hlow : lowerIndex2 (K := K + 1) ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ (Fin.cons k w) =
      prefixIndex2 k (lowerIndex2 j w) := rfl
  have hnext : nextIndex2 (K := K + 1) ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ (Fin.cons k w) i =
      prefixIndex2 k (nextIndex2 j w i) := by
    unfold nextIndex2 nextIndex prefixIndex2
    congr 1
    exact (Fin.cons_snoc_eq_snoc_cons k w i).symm
  rw [hlow, hnext] at h
  exact h

/-- **The partial derivative `∂_k` of a plane carrier.** -/
def planeHkPartial {K : ℕ} (k : Fin 2) (U : PlaneHk Set.univ (K + 1) E) :
    PlaneHk Set.univ K E :=
  (show PlaneHkFunction Set.univ K E from
    ⟨partialRawJet k U.toFunction.jet, partialRawJet_memL2 k U.toFunction.memL2,
      partialRawJet_hasWeakJet k U.toFunction.hasWeakJet⟩).toHk

theorem planeHkPartial_jet_ae {K : ℕ} (k : Fin 2) (U : PlaneHk Set.univ (K + 1) E)
    (a : JetIndex2 K) :
    (planeHkPartial k U).toFunction.jet a =ᵐ[volume] U.toFunction.jet (prefixIndex2 k a) := by
  have h := (show PlaneHkFunction Set.univ K E from
    ⟨partialRawJet k U.toFunction.jet, partialRawJet_memL2 k U.toFunction.memL2,
      partialRawJet_hasWeakJet k U.toFunction.hasWeakJet⟩).toHk_toFunction_ae a
  simpa only [Measure.restrict_univ, planeHkPartial, partialRawJet] using h
end

end AVRegularity.CycleWords.Seam
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped FourierTransform SchwartzMap Topology
namespace AVRegularity.CycleWords.Seam

/-! Flatness of a scalar multiplier at zero forces cancellation of its kernel moments. -/

/-- The double Fourier transform of a Schwartz function is its reflection. -/
theorem cutoff_schwartz_fourier_fourier {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : 𝓢(V, ℂ)) (x : V) : (𝓕 (𝓕 f)) x = f (-x) := by
  have hh := congrArg (fun F : 𝓢(V, ℂ) => F (-x))
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(V, ℂ)) f)
  change (𝓕 (𝓕 f)) (- -x) = f (-x) at hh
  simpa only [neg_neg] using hh

/-- Every positive-order Fourier moment vanishes when the multiplier is locally constant. -/
theorem cutoff_schwartz_fourier_moment_zero {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : 𝓢(V, ℂ)) (c : ℂ) (hc : (f : V → ℂ) =ᶠ[𝓝 0] fun _ => c)
    {n : ℕ} (hn : n ≠ 0) (w : Fin n → V) :
    (∫ x : V, (∏ i, inner ℝ x (w i)) • (𝓕 f) x) = 0 := by
  let F : 𝓢(V, ℂ) := 𝓕 f
  have hflat : (𝓕 (F : V → ℂ)) =ᶠ[𝓝 0] fun _ => c := by
    have hneg : Filter.Tendsto (fun x : V => -x) (𝓝 0) (𝓝 0) := by
      simpa only [neg_zero] using continuous_neg.continuousAt.tendsto (x := (0 : V))
    filter_upwards [hc.comp_tendsto hneg] with x hx
    exact (cutoff_schwartz_fourier_fourier f x).trans hx
  have hz : iteratedFDeriv ℝ n (𝓕 (F : V → ℂ)) 0 = 0 := by
    have hh := (hflat.iteratedFDeriv ℝ n).self_of_nhds
    simpa only [iteratedFDeriv_const_of_ne hn, Pi.zero_apply] using hh
  have hd := Real.iteratedFDeriv_fourier (f := (F : V → ℂ)) (N := (⊤ : ℕ∞))
    (fun a _ => F.integrable_pow_mul volume a)
    F.continuous.aestronglyMeasurable (n := n) (by simp)
  have hi : Integrable (fun x : V =>
      VectorFourier.fourierPowSMulRight (innerSL ℝ) (F : V → ℂ) x n) := by
    apply Integrable.mono'
      ((F.integrable_pow_mul volume n).const_mul ((2 * Real.pi * ‖innerSL ℝ (E := V)‖) ^ n))
    · exact (F.continuous.fourierPowSMulRight (innerSL ℝ) n).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        simpa only [mul_assoc] using
          VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ) (F : V → ℂ) x n
  have hh := congrArg (fun D => D 0 w) hd
  rw [hz, zero_apply] at hh
  rw [Real.fourier_continuousMultilinearMap_apply hi] at hh
  change 0 = (∫ x : V, 𝐞 (-inner ℝ x 0) •
    VectorFourier.fourierPowSMulRight (innerSL ℝ) (F : V → ℂ) x n w) at hh
  simp only [inner_zero_right, neg_zero, Real.fourierChar.map_zero_eq_one, one_smul,
    VectorFourier.fourierPowSMulRight_apply] at hh
  rw [integral_smul] at hh
  exact (smul_eq_zero.mp hh.symm).resolve_left
    (pow_ne_zero _ (by simp only [ne_eq, neg_eq_zero, mul_eq_zero,
      Complex.I_ne_zero, or_false]; norm_num [Real.pi_ne_zero]))

theorem cutoff_coordinate_product_norm_le {n : ℕ} (w : DerivativeWord2 n) (x : Vec 2) :
    ‖∏ i, x (w i)‖ ≤ ‖x‖ ^ n := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _ : Fin n, ‖x‖ := Finset.prod_le_prod₀
      (fun _ _ => norm_nonneg _) (fun i _ => norm_le_pi_norm x (w i))
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Coordinate monomials multiplying a Schwartz function are integrable. -/
theorem cutoff_schwartz_coordinate_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : 𝓢(Vec 2, E)) {n : ℕ} (w : DerivativeWord2 n) :
    Integrable (fun x => (∏ i, x (w i)) • F x) := by
  apply Integrable.mono' (F.integrable_pow_mul volume n)
  · exact ((continuous_finsetProd _ fun i _ => continuous_apply (w i)).smul
      F.continuous).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (cutoff_coordinate_product_norm_le w x) (norm_nonneg _)

/-- Flatness near zero cancels every positive-order coordinate moment of the literal kernel. -/
theorem cutoffKernel_coordinate_moment_zero (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    (hflat : ∃ ε : ℝ, 0 < ε ∧ ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ ε → m ξ = 1)
    {n : ℕ} (hn : n ≠ 0) (w : DerivativeWord2 n) :
    (∫ x : Vec 2, (∏ i, x (w i)) * cutoffKernel m x) = 0 := by
  let f := seamHilbertCutoffSchwartz m R hm hs
  obtain ⟨ε, hε, hεm⟩ := hflat
  have hc : Continuous fun θ : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo =>
      Real.sqrt (vecDot (WithLp.ofLp θ) (WithLp.ofLp θ)) := by
    unfold vecDot
    fun_prop
  have hzero : Real.sqrt (vecDot (WithLp.ofLp (0 : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo))
      (WithLp.ofLp (0 : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo))) = 0 := by simp [vecDot]
  have hf : (f : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo → ℂ) =ᶠ[𝓝 0] fun _ => 1 := by
    have he := hc.continuousAt.preimage_mem_nhds
      (show Set.Iio ε ∈ 𝓝 (Real.sqrt (vecDot (WithLp.ofLp (0 : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo))
        (WithLp.ofLp (0 : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo)))) by rw [hzero]; exact Iio_mem_nhds hε)
    filter_upwards [he] with θ hθ
    change (m (WithLp.ofLp θ) : ℂ) = 1
    rw [hεm _ hθ.le, Complex.ofReal_one]
  have hb := cutoff_schwartz_fourier_moment_zero f 1 hf hn (fun i => AVRegularity.CoupledEnergyPlane.Fourier.coordinateVector (w i))
  have hi (θ : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo) (i : Fin 2) :
      inner ℝ θ (AVRegularity.CoupledEnergyPlane.Fourier.coordinateVector i) = WithLp.ofLp θ i := by
    simp [AVRegularity.CoupledEnergyPlane.Fourier.coordinateVector, PiLp.inner_apply]
  simp_rw [hi] at hb
  let a : ℝ := -(2 * Real.pi)⁻¹
  have ha : a ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero))
  have hscale := Measure.integral_comp_smul (volume : Measure AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo)
    (fun θ : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo => (∏ i, WithLp.ofLp (a⁻¹ • θ) (w i)) • (𝓕 f) θ) a
  have hdim : Module.finrank ℝ AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo = 2 := by simp [AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo]
  rw [hdim] at hscale
  have hp (θ : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo) : (∏ i, WithLp.ofLp (a⁻¹ • θ) (w i)) =
      a⁻¹ ^ n * ∏ i, WithLp.ofLp θ (w i) := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hl (θ : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo) : (∏ i, WithLp.ofLp (a⁻¹ • (a • θ)) (w i)) =
      ∏ i, WithLp.ofLp θ (w i) := by rw [inv_smul_smul₀ ha]
  simp_rw [hl, hp, mul_smul] at hscale
  rw [integral_smul, hb, smul_zero, smul_zero] at hscale
  have hphysical : (∫ x : Vec 2, (∏ i, x (w i)) • seamComplexCutoffSchwartz m R hm hs x) = 0 := by
    rw [← (PiLp.volume_preserving_ofLp (Fin 2)).integral_comp
      AVRegularity.CoupledEnergyPlane.Fourier.coordinateHilbertEquiv.toHomeomorph.measurableEmbedding
      (fun x : Vec 2 => (∏ i, x (w i)) • seamComplexCutoffSchwartz m R hm hs x)]
    exact hscale
  have hRe := integral_re (cutoff_schwartz_coordinate_integrable
    (seamComplexCutoffSchwartz m R hm hs) w)
  change (∫ x : Vec 2, ((∏ i, x (w i)) • seamComplexCutoffSchwartz m R hm hs x).re) =
    (∫ x : Vec 2, (∏ i, x (w i)) • seamComplexCutoffSchwartz m R hm hs x).re at hRe
  rw [hphysical, Complex.zero_re] at hRe
  simp only [Complex.smul_re, smul_eq_mul] at hRe
  rw [← seamRealCutoffSchwartz_eq m R hm hs]
  change (∫ x : Vec 2, (∏ i, x (w i)) *
    ((2 * Real.pi)⁻¹ ^ 2 * (seamComplexCutoffSchwartz m R hm hs x).re)) = 0
  simp_rw [mul_left_comm (∏ i, _)]
  rw [integral_const_mul, hRe, mul_zero]

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords.Seam

/-! Integration by parts between two plane carriers along an ordered word:
`⟨D_α W, T⟩ = (-1)^a ⟨W, ∂_{α_1}(∂_{α_2}(⋯ ∂_{α_a} T))⟩` in `L²(ℝ², E)`, one weak partial at a
time (`hilbert_weakPartial_inner`). The nested partials are `planeHkWordPartial α T`; ordered weak
jets append the newest derivative, so no commutation of weak derivatives is used. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A stored jet of a plane carrier as an `L²` class on the plane. -/
def planeJetL2 {K : ℕ} (U : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    Lp E 2 (volume : Measure (Vec 2)) :=
  univToPlane (U.val a)

theorem planeJetL2_ae {K : ℕ} (U : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (planeJetL2 U a : Vec 2 → E) =ᵐ[volume] U.toFunction.jet a :=
  univToPlane_ae (U.val a)

/-- The nested partials `∂_{α_1}(∂_{α_2}(⋯ ∂_{α_a} T))`. -/
def planeHkWordPartial {n : ℕ} : {a : ℕ} → DerivativeWord2 a →
    PlaneHk Set.univ (n + a) E → PlaneHk Set.univ n E
  | 0, _, T => T
  | a + 1, α, T => planeHkWordPartial (Fin.init α) (planeHkPartial (α (Fin.last a)) T)

/-- The weak partial of a stored jet, through `L²` classes. -/
theorem planeJetL2_weakPartial {K : ℕ} (U : PlaneHk Set.univ K E) (j : Fin K)
    (w : DerivativeWord2 j.val) (i : Fin 2) (e : E) :
    HasWeakPartialDerivOn Set.univ i (fun x => inner ℝ e (planeJetL2 U (lowerIndex2 j w) x))
      (fun x => inner ℝ e (planeJetL2 U (nextIndex2 j w i) x)) := by
  have h := U.toFunction.hasWeakJet j w i e
  apply hasWeakPartialDerivOn_congr_ae _ _ h
  · rw [Measure.restrict_univ]
    filter_upwards [planeJetL2_ae U (lowerIndex2 j w)] with x hx
    rw [hx]
  · rw [Measure.restrict_univ]
    filter_upwards [planeJetL2_ae U (nextIndex2 j w i)] with x hx
    rw [hx]

/-- The value of `∂_i T` is the first jet of `T` in direction `i`. -/
theorem planeJetL2_partial_value {K : ℕ} (T : PlaneHk Set.univ (K + 1) E) (i : Fin 2) :
    planeJetL2 (planeHkPartial i T) (valueIndex2 K) =
      planeJetL2 T (nextIndex2 (K := K + 1) ⟨0, Nat.succ_pos K⟩ Fin.elim0 i) := by
  have hidx : prefixIndex2 i (valueIndex2 K) =
      nextIndex2 (K := K + 1) ⟨0, Nat.succ_pos K⟩ Fin.elim0 i := by
    unfold prefixIndex2 valueIndex2 valueIndex nextIndex2 nextIndex
    congr 1
    funext q
    obtain rfl : q = 0 := Fin.fin_one_eq_zero q
    rfl
  apply Lp.ext
  refine (planeJetL2_ae _ _).trans ((planeHkPartial_jet_ae i T (valueIndex2 K)).trans ?_)
  rw [hidx]
  exact (planeJetL2_ae T _).symm

/-- **Integration by parts along a word.** -/
theorem planeHk_ibp [FiniteDimensional ℝ E] {K : ℕ} (W : PlaneHk Set.univ K E) :
    ∀ (a : ℕ) (ha : a ≤ K) (α : DerivativeWord2 a) {n : ℕ} (T : PlaneHk Set.univ (n + a) E),
      inner ℝ (planeJetL2 W ⟨⟨a, Nat.lt_succ_of_le ha⟩, α⟩) (planeJetL2 T (valueIndex2 (n + a))) =
        (-1) ^ a * inner ℝ (planeJetL2 W (valueIndex2 K))
          (planeJetL2 (planeHkWordPartial α T) (valueIndex2 n))
  | 0, _, α, n, T => by
      have hα : α = Fin.elim0 := funext fun q => q.elim0
      subst hα
      simp only [pow_zero, one_mul]
      rfl
  | a + 1, ha, α, n, T => by
      have hu := planeJetL2_weakPartial W ⟨a, by omega⟩ (Fin.init α) (α (Fin.last a))
      have hv := planeJetL2_weakPartial T ⟨0, by omega⟩ Fin.elim0 (α (Fin.last a))
      have hstep := hilbert_weakPartial_inner (α (Fin.last a))
        (planeJetL2 W (lowerIndex2 ⟨a, by omega⟩ (Fin.init α)))
        (planeJetL2 W (nextIndex2 ⟨a, by omega⟩ (Fin.init α) (α (Fin.last a))))
        (planeJetL2 T (lowerIndex2 (K := n + a + 1) ⟨0, by omega⟩ Fin.elim0))
        (planeJetL2 T (nextIndex2 (K := n + a + 1) ⟨0, by omega⟩ Fin.elim0 (α (Fin.last a))))
        hu hv
      have hW : nextIndex2 (K := K) ⟨a, by omega⟩ (Fin.init α) (α (Fin.last a)) =
          ⟨⟨a + 1, Nat.lt_succ_of_le ha⟩, α⟩ := by
        unfold nextIndex2 nextIndex
        congr 1
        exact Fin.snoc_init_self α
      have hT : lowerIndex2 (K := n + a + 1) ⟨0, by omega⟩ Fin.elim0 = valueIndex2 (n + (a + 1)) :=
        rfl
      rw [hW, hT] at hstep
      rw [hstep, ← planeJetL2_partial_value T (α (Fin.last a))]
      have ih := planeHk_ibp W a (by omega) (Fin.init α) (planeHkPartial (α (Fin.last a)) T)
      have hlow : lowerIndex2 (K := K) ⟨a, by omega⟩ (Fin.init α) =
          ⟨⟨a, Nat.lt_succ_of_le (by omega)⟩, Fin.init α⟩ := rfl
      have ih' : inner ℝ (planeJetL2 W ⟨⟨a, Nat.lt_succ_of_le (by omega)⟩, Fin.init α⟩)
          (planeJetL2 (planeHkPartial (α (Fin.last a)) T) (valueIndex2 (n.add a))) =
          (-1) ^ a * inner ℝ (planeJetL2 W (valueIndex2 K))
            (planeJetL2 (planeHkWordPartial (Fin.init α) (planeHkPartial (α (Fin.last a)) T))
              (valueIndex2 n)) := ih
      rw [hlow, ih']
      simp only [planeHkWordPartial, pow_succ]
      ring

/-- The raw jet of the nested partials (no proofs; see `planeHkWordPartial_jet_ae`). -/
def wordPartialRawJet {n : ℕ} : {a : ℕ} → DerivativeWord2 a → RawJet2 (n + a) E → RawJet2 n E
  | 0, _, D => D
  | a + 1, α, D => wordPartialRawJet (Fin.init α) (partialRawJet (α (Fin.last a)) D)

theorem planeHkWordPartial_jet_ae {n : ℕ} :
    ∀ {a : ℕ} (α : DerivativeWord2 a) (T : PlaneHk Set.univ (n + a) E) (b : JetIndex2 n),
      (planeHkWordPartial α T).toFunction.jet b =ᵐ[volume]
        wordPartialRawJet α T.toFunction.jet b
  | 0, _, _, _ => Filter.EventuallyEq.rfl
  | a + 1, α, T, b => by
      have ih := planeHkWordPartial_jet_ae (Fin.init α) (planeHkPartial (α (Fin.last a)) T) b
      refine ih.trans ?_
      -- push the a.e. identification of `∂_k T` through the remaining partials
      have key : ∀ {m : ℕ} {c : ℕ} (β : DerivativeWord2 c) (D D' : RawJet2 (m + c) E),
          (∀ q, D q =ᵐ[volume] D' q) → ∀ q, wordPartialRawJet β D q =ᵐ[volume]
            wordPartialRawJet β D' q := by
        intro m c
        induction c generalizing m with
        | zero => intro β D D' h q; exact h q
        | succ c ihc =>
          intro β D D' h q
          exact ihc (Fin.init β) _ _ (fun q' => h _) q
      exact key (Fin.init α) _ _ (fun q => planeHkPartial_jet_ae (α (Fin.last a)) T q) b

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
open AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleWords.Seam

/-! Vector plane carriers through orthonormal coordinates. The scalar adjoint chains are run on the
coordinates `⟨b_e, φ⟩` of a vector test; the vector adjoint is reassembled as `∑_e ψ_e b_e`. Every
jet of the assembly is the sum of the injected scalar jets, and `L²` pairings split over the
coordinates (Parseval). -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
theorem univToPlane_compLpL (L : E →L[ℝ] F)
    (f : ComponentL2 (volume.restrict (Set.univ : Set (Vec 2))) E) :
    univToPlane (L.compLpL 2 (volume.restrict Set.univ) f) =
      L.compLpL 2 volume (univToPlane f) := by
  apply Lp.ext
  have h1 := univToPlane_ae (L.compLpL 2 (volume.restrict Set.univ) f)
  have h2 := (ae_restrict_iff' MeasurableSet.univ).mp
    (L.coeFn_compLpL (μ := volume.restrict Set.univ) f)
  filter_upwards [h1, h2, L.coeFn_compLpL (univToPlane f), univToPlane_ae f]
    with z hz1 hz2 hz3 hz4
  rw [hz1, hz2 (Set.mem_univ z), hz3, hz4]

theorem planeJetL2_mapPlaneHk {K : ℕ} (L : E →L[ℝ] F) (u : PlaneHk Set.univ K E)
    (a : JetIndex2 K) :
    planeJetL2 (mapPlaneHk L u) a = L.compLpL 2 volume (planeJetL2 u a) := by
  unfold planeJetL2
  rw [mapPlaneHk_component, univToPlane_compLpL]

theorem planeJetL2_sum {n : Type*} [Fintype n] {K : ℕ} (u : n → PlaneHk Set.univ K E)
    (a : JetIndex2 K) :
    planeJetL2 (∑ e, u e) a = ∑ e, planeJetL2 (u e) a := by
  unfold planeJetL2
  rw [planeHk_sum_component, map_sum]

/-- The coordinate of a vector carrier along `e`. -/
def planeHkCoord (e : E) {K : ℕ} (u : PlaneHk Set.univ K E) : PlaneHk Set.univ K ℝ :=
  mapPlaneHk (InnerProductSpace.toDual ℝ E e) u

/-- The vector carrier with coordinates `ψ` in the orthonormal basis `b`. -/
def planeHkAssemble {n : Type*} [Fintype n] (b : OrthonormalBasis n ℝ E) {K : ℕ}
    (ψ : n → PlaneHk Set.univ K ℝ) : PlaneHk Set.univ K E :=
  ∑ e, mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight (b e)) (ψ e)

theorem planeJetL2_coord (e : E) {K : ℕ} (u : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    planeJetL2 (planeHkCoord e u) a = planeFiberCoordinateCLM e (planeJetL2 u a) :=
  planeJetL2_mapPlaneHk _ u a

theorem planeJetL2_assemble {n : Type*} [Fintype n] (b : OrthonormalBasis n ℝ E) {K : ℕ}
    (ψ : n → PlaneHk Set.univ K ℝ) (a : JetIndex2 K) :
    planeJetL2 (planeHkAssemble b ψ) a =
      ∑ e, planeFiberInjectionCLM (b e) (planeJetL2 (ψ e) a) := by
  unfold planeHkAssemble
  rw [planeJetL2_sum]
  exact Finset.sum_congr rfl fun e _ => planeJetL2_mapPlaneHk _ (ψ e) a

omit [MeasurableSpace E] [BorelSpace E] in
/-- An `L²` field is the sum of its injected coordinates. -/
theorem planeFiber_decompose {n : Type*} [Fintype n] (b : OrthonormalBasis n ℝ E)
    (w : Lp E 2 (volume : Measure (Vec 2))) :
    ∑ e, planeFiberInjectionCLM (b e) (planeFiberCoordinateCLM (b e) w) = w := by
  apply Lp.ext
  have hc : ∀ e, planeFiberInjectionCLM (b e) (planeFiberCoordinateCLM (b e) w) =ᵐ[volume]
      fun z => inner ℝ (b e) (w z) • b e := by
    intro e
    filter_upwards [((ContinuousLinearMap.id ℝ ℝ).smulRight (b e)).coeFn_compLpL
      (planeFiberCoordinateCLM (b e) w),
      (InnerProductSpace.toDual ℝ E (b e)).coeFn_compLpL w] with z h1 h2
    change planeFiberInjectionCLM (b e) (planeFiberCoordinateCLM (b e) w) z =
      planeFiberCoordinateCLM (b e) w z • b e at h1
    change planeFiberCoordinateCLM (b e) w z = inner ℝ (b e) (w z) at h2
    rw [h1, h2]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun e => planeFiberInjectionCLM (b e) (planeFiberCoordinateCLM (b e) w)),
    ae_all_iff.mpr hc] with z hs hz
  rw [hs, Finset.sum_apply]
  simp only [hz]
  exact b.sum_repr' (w z)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Parseval** for `L²` fields: the pairing is the sum of the coordinate pairings. -/
theorem inner_eq_sum_planeFiberCoordinate {n : Type*} [Fintype n]
    (b : OrthonormalBasis n ℝ E) (u w : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ u w = ∑ e, inner ℝ (planeFiberCoordinateCLM (b e) u)
      (planeFiberCoordinateCLM (b e) w) := by
  conv_lhs => rw [← planeFiber_decompose b w]
  rw [inner_sum]
  exact Finset.sum_congr rfl fun e _ => (planeFiberCoordinate_pair (b e) u _).symm

omit [MeasurableSpace E] [BorelSpace E] in
/-- Pairing against an assembled field splits over the coordinates. -/
theorem inner_assemble {n : Type*} [Fintype n] (b : OrthonormalBasis n ℝ E)
    (u : Lp E 2 (volume : Measure (Vec 2))) (φ : n → Lp ℝ 2 (volume : Measure (Vec 2))) :
    inner ℝ u (∑ e, planeFiberInjectionCLM (b e) (φ e)) =
      ∑ e, inner ℝ (planeFiberCoordinateCLM (b e) u) (φ e) := by
  rw [inner_sum]
  exact Finset.sum_congr rfl fun e _ => (planeFiberCoordinate_pair (b e) u _).symm

end AVRegularity.CycleWords.Seam
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! Homogeneity and compact-test dual bounds for the seam cutoff complement. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

/-- The weighted jet norm is homogeneous in the whole jet array. -/
theorem cutoff_weightedJetNorm_const_smul (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r c : ℝ)
    (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v) :
    weightedJetNorm π p j s r (fun v a w z => c • J v a w z) =
      ENNReal.ofReal |c| * weightedJetNorm π p j s r J := by
  have hw (v : ι) (a : ℕ) (z : Vec 2) :
      Real.sqrt (∑ w, ‖c • J v a w z‖ ^ 2) =
        |c| * Real.sqrt (∑ w, ‖J v a w z‖ ^ 2) := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg |c|), Real.sqrt_sq (abs_nonneg c)]
  have he (v : ι) (a : ℕ) :
      eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
        Real.sqrt (∑ w, ‖c • J v a w z‖ ^ 2)) 2 volume =
      ENNReal.ofReal |c| * eLpNorm (fun z =>
        (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
          Real.sqrt (∑ w, ‖J v a w z‖ ^ 2)) 2 volume := by
    simp_rw [hw]
    rw [show (fun z : Vec 2 => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
        (|c| * Real.sqrt (∑ w, ‖J v a w z‖ ^ 2))) =
      |c| • (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
        Real.sqrt (∑ w, ‖J v a w z‖ ^ 2)) by
          funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring]
    rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_abs]
  unfold weightedJetNorm
  simp_rw [he, mul_pow]
  have hsum (a : ℕ) :
      (∑ v, ENNReal.ofReal ((π v)⁻¹) * (ENNReal.ofReal |c| ^ 2 *
        eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
          Real.sqrt (∑ w, ‖J v a w z‖ ^ 2)) 2 volume ^ 2)) =
      ENNReal.ofReal |c| ^ 2 * (∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
          Real.sqrt (∑ w, ‖J v a w z‖ ^ 2)) 2 volume ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  simp_rw [hsum, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Classical ordered derivatives commute with real scalar multiplication. -/
theorem cutoff_orderedDerivative_const_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℕ} (w : DerivativeWord2 a) (c : ℝ)
    (φ : Vec 2 → E) (hφ : ContDiff ℝ (a : ℕ∞) φ) :
    orderedDerivative w (fun z => c • φ z) = fun z => c • orderedDerivative w φ z := by
  exact orderedDerivative_clm_comp (c • ContinuousLinearMap.id ℝ E) w hφ

/-- A compact smooth test of norm at most `A` pairs at most `A` times the negative norm. -/
theorem cutoff_compact_test_pair_le (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ)
    (g φ : ∀ v, Vec 2 → h v)
    (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v) ∧ HasCompactSupport (φ v))
    (A : ℝ) (hA : 0 < A)
    (hb : weightedJetNorm π (-p) j s r
      (fun v _ w z => orderedDerivative w (φ v) z) ≤ ENNReal.ofReal A) :
    ENNReal.ofReal |∑ v, (π v)⁻¹ * ∫ z, inner ℝ (g v z) (φ v z)| ≤
      ENNReal.ofReal A * Assembly.negJetNorm π p j s r g := by
  let ψ := fun v z => A⁻¹ • φ v z
  have hψ (v : ι) : ContDiff ℝ (⊤ : ℕ∞) (ψ v) ∧ HasCompactSupport (ψ v) :=
    ⟨(hφ v).1.const_smul _, (hφ v).2.smul_left⟩
  have hn : weightedJetNorm π (-p) j s r
      (fun v _ w z => orderedDerivative w (ψ v) z) ≤ 1 := by
    have hd (v : ι) (a : ℕ) (w : DerivativeWord2 a) :
        orderedDerivative w (ψ v) = fun z => A⁻¹ • orderedDerivative w (φ v) z :=
      cutoff_orderedDerivative_const_smul w A⁻¹ (φ v) ((hφ v).1.of_le (by simp))
    simp_rw [hd]
    rw [cutoff_weightedJetNorm_const_smul, abs_of_pos (inv_pos.mpr hA)]
    calc
      _ ≤ ENNReal.ofReal A⁻¹ * ENNReal.ofReal A := mul_le_mul' le_rfl hb
      _ = 1 := by rw [← ENNReal.ofReal_mul (inv_pos.mpr hA).le,
        inv_mul_cancel₀ hA.ne', ENNReal.ofReal_one]
  have htest : ENNReal.ofReal |∑ v, (π v)⁻¹ * ∫ z, inner ℝ (g v z) (ψ v z)| ≤
      Assembly.negJetNorm π p j s r g := by
    unfold Assembly.negJetNorm
    exact le_iSup_of_le ψ (le_iSup_of_le hψ (le_iSup_of_le hn le_rfl))
  have hp : (∑ v, (π v)⁻¹ * ∫ z, inner ℝ (g v z) (ψ v z)) =
      A⁻¹ * (∑ v, (π v)⁻¹ * ∫ z, inner ℝ (g v z) (φ v z)) := by
    simp only [ψ, inner_smul_right, integral_const_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hp, abs_mul, abs_of_pos (inv_pos.mpr hA),
    ENNReal.ofReal_mul (inv_pos.mpr hA).le] at htest
  calc
    _ = ENNReal.ofReal A * (ENNReal.ofReal A⁻¹ *
        ENNReal.ofReal |∑ v, (π v)⁻¹ * ∫ z, inner ℝ (g v z) (φ v z)|) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hA.le, mul_inv_cancel₀ hA.ne',
        ENNReal.ofReal_one, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl htest
end

/-! Weighted finite-family Minkowski estimates used to sum the transport chain rule. -/

/-- The inverse-mass Hilbert sum of component norms. -/
def familyNorm {ι : Type*} [Fintype ι] (c X : ι → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ v, c v * X v ^ 2) ^ (1 / 2 : ℝ)

theorem familyNorm_mono {ι : Type*} [Fintype ι] (c : ι → ℝ≥0∞) {X Y : ι → ℝ≥0∞}
    (h : ∀ v, X v ≤ Y v) : familyNorm c X ≤ familyNorm c Y := by
  unfold familyNorm
  gcongr with v
  exact h v

theorem familyNorm_mul {ι : Type*} [Fintype ι] (c X : ι → ℝ≥0∞) (A : ℝ≥0∞) :
    familyNorm c (fun v => A * X v) = A * familyNorm c X := by
  unfold familyNorm
  have he (v : ι) : c v * (A * X v) ^ 2 = A ^ 2 * (c v * X v ^ 2) := by ring
  simp only [he, ← Finset.mul_sum]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

theorem familyNorm_sum_le {ι α : Type*} [Fintype ι] (c : ι → ℝ≥0∞)
    (s : Finset α) (X : α → ι → ℝ≥0∞) :
    familyNorm c (fun v => ∑ a ∈ s, X a v) ≤ ∑ a ∈ s, familyNorm c (X a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [familyNorm]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (Assembly.ennreal_weighted_l2_add_le c _ _ _ (fun _ => le_rfl)).trans
      (add_le_add le_rfl ih)

theorem familyNorm_eLpNorm_majorant {ι α : Type*} [Fintype ι]
    (c : ι → ℝ≥0∞) (s : Finset α) (A : α → ℝ) (hA : ∀ a ∈ s, 0 ≤ A a)
    (f : ι → Vec 2 → ℝ) (hf : ∀ v, AEStronglyMeasurable (f v) volume)
    (F : α → ι → Vec 2 → ℝ)
    (hb : ∀ v z, |f v z| ≤ ∑ a ∈ s, A a * F a v z) :
    familyNorm c (fun v => eLpNorm (f v) 2 volume) ≤
      ∑ a ∈ s, ENNReal.ofReal (A a) * familyNorm c (fun v => eLpNorm (F a v) 2 volume) := by
  have hcomp (v : ι) : eLpNorm (f v) 2 volume ≤
      ∑ a ∈ s, ENNReal.ofReal (A a) * eLpNorm (F a v) 2 volume := by
    calc eLpNorm (f v) 2 volume ≤ eLpNorm (fun z => ∑ a ∈ s, A a * F a v z) 2 volume := by
          apply eLpNorm_mono_real (hf v)
          intro z
          exact hb v z
         _ = eLpNorm (∑ a ∈ s, A a • F a v) 2 volume := by
          congr 1
          funext z
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
         _ ≤ ∑ a ∈ s, eLpNorm (A a • F a v) 2 volume := eLpNorm_sum_le (by norm_num)
         _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hA a ha)]
  exact (familyNorm_mono c hcomp).trans
    ((familyNorm_sum_le c s (fun a v => ENNReal.ofReal (A a) * eLpNorm (F a v) 2 volume)).trans
      (le_of_eq (by simp only [familyNorm_mul])))

/-- The Euclidean size of the complete ordered word array. -/
def wordSize {E : Type*} [NormedAddCommGroup E] (a : ℕ)
    (J : DerivativeWord2 a → E) : ℝ := Real.sqrt (∑ w, ‖J w‖ ^ 2)

theorem norm_le_wordSize {E : Type*} [NormedAddCommGroup E] {a : ℕ}
    (J : DerivativeWord2 a → E) (w : DerivativeWord2 a) : ‖J w‖ ≤ wordSize a J := by
  unfold wordSize
  exact (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).mpr
    (Finset.single_le_sum (f := fun v => ‖J v‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ w))

theorem wordSize_le_card_mul {E : Type*} [NormedAddCommGroup E] {a : ℕ}
    (J : DerivativeWord2 a → E) {A : ℝ} (hA : 0 ≤ A) (hb : ∀ w, ‖J w‖ ≤ A) :
    wordSize a J ≤ (2 : ℝ) ^ a * A := by
  have hcard : (1 : ℝ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
  have hs : (∑ w, ‖J w‖ ^ 2) ≤ 2 ^ a * A ^ 2 := by
    calc _ ≤ ∑ _ : DerivativeWord2 a, A ^ 2 :=
          Finset.sum_le_sum fun w _ => pow_le_pow_left₀ (norm_nonneg _) (hb w) 2
         _ = _ := by simp [DerivativeWord2, DerivativeWord]
  apply (Real.sqrt_le_left (mul_nonneg (zero_le_one.trans hcard) hA)).mpr
  apply hs.trans
  nlinarith only [mul_nonneg (sq_nonneg A) (sub_nonneg.mpr hcard), hcard,
    mul_nonneg (sq_nonneg A) (sq_nonneg ((2 : ℝ) ^ a - 1))]

end AVRegularity.CycleWords.Seam
end
