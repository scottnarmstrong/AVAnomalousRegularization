-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Torus.JointContinuityMain
import AVRegularity.Applications.Tubes.Periodic
public import AVRegularity.Applications.Tubes.Trace
public import AVenhance.Statements.Section3.SigmaMat
import Homogenization.Ambient.BlockMatrix
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

@[expose] public section
noncomputable section

section
open Homogenization AVenhance
namespace AVRegularity.Applications

/-! # Assembling the `C^s(𝕋²)` bound

Step 4 of the proof of Proposition 3.2 of the paper: short increments from the microscopic lemma
at distances below `R/8`, comparison with the finite solution at all larger distances. -/

theorem exists_shift_lt {y z : Vec 2} {m : ℝ} (h : torusDist y z < m) :
    ∃ n : Fin 2 → ℤ, eNorm (y - (z + latticeShift n)) < m := by
  obtain ⟨n, hn⟩ := exists_lt_of_ciInf_lt (f := fun n : Fin 2 → ℤ =>
    Real.sqrt (vecNormSq (y - z - latticeShift n))) h
  refine ⟨n, ?_⟩
  have : y - (z + latticeShift n) = y - z - latticeShift n := by abel
  rw [this]
  exact hn

theorem holder_combine {s a' R G SF D : ℝ} {W Vt : Vec 2 → ℝ} (hs0 : 0 < s) (hsa : s ≤ a')
    (hs1 : s ≤ 1) (hR0 : 0 < R) (hR1 : R ≤ 1) (hG : 0 ≤ G) (hD : 0 ≤ D)
    (hWp : IsZ2Periodic W) (hVt : CsNormLe s Vt SF) (hD' : ∀ x, |W x - Vt x| ≤ D)
    (hshort : ∀ z y, eNorm (y - z) < R / 8 →
      |W z - W y| ≤ G * (eNorm (y - z) / (R / 2)) ^ a') :
    CsNormLe s W (SF + 17 * D * R ^ (-s) + 4 * G * R ^ (-s)) := by
  intro x y z hd
  have hdpos : 0 < torusDist y z := lt_of_le_of_ne (torusDist_nonneg _ _) (Ne.symm hd)
  have hV := hVt x y z hd
  have hRsp : 0 < R ^ s := Real.rpow_pos_of_pos hR0 s
  have hRs : R ^ (-s) = (R ^ s)⁻¹ := Real.rpow_neg hR0.le s
  have hRs1 : 1 ≤ R ^ (-s) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hR0 hR1 (by linarith)
  have hdp : 0 < torusDist y z ^ s := Real.rpow_pos_of_pos hdpos s
  have hamp : |W x| ≤ |Vt x| + D := by
    have := abs_sub_abs_le_abs_sub (W x) (Vt x)
    have := hD' x
    linarith [abs_nonneg (W x - Vt x), abs_sub_abs_le_abs_sub (W x) (Vt x)]
  have hH0 : 0 ≤ |Vt y - Vt z| / torusDist y z ^ s := by positivity
  have hDR : D ≤ D * R ^ (-s) := le_mul_of_one_le_right hD hRs1
  by_cases hlarge : R / 8 ≤ torusDist y z
  · have hdiff : |W y - W z| ≤ |Vt y - Vt z| + 2 * D := by
      have e : W y - W z = (W y - Vt y) + (Vt y - Vt z) - (W z - Vt z) := by ring
      rw [e]
      calc _ ≤ |(W y - Vt y) + (Vt y - Vt z)| + |W z - Vt z| := abs_sub _ _
        _ ≤ |W y - Vt y| + |Vt y - Vt z| + |W z - Vt z| := by
            gcongr; exact abs_add_le _ _
        _ ≤ _ := by linarith [hD' y, hD' z]
    have hinv : 1 / torusDist y z ^ s ≤ 8 * R ^ (-s) := by
      have h1 : (R / 8) ^ s ≤ torusDist y z ^ s := Real.rpow_le_rpow (by positivity) hlarge hs0.le
      have h2 : (8 : ℝ) ^ s ≤ 8 := by
        calc (8 : ℝ) ^ s ≤ (8 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
          _ = 8 := Real.rpow_one 8
      have h3 : (R / 8) ^ s = R ^ s / 8 ^ s := Real.div_rpow hR0.le (by norm_num) s
      rw [div_le_iff₀ hdp, hRs]
      have h4 : R ^ s / 8 ≤ (R / 8) ^ s := by
        rw [h3]; exact div_le_div_of_nonneg_left hRsp.le (by positivity) h2
      have h5 : 1 ≤ 8 * (R ^ s)⁻¹ * torusDist y z ^ s := by
        have : 8 * (R ^ s)⁻¹ * (R ^ s / 8) = 1 := by field_simp
        calc (1 : ℝ) = 8 * (R ^ s)⁻¹ * (R ^ s / 8) := this.symm
          _ ≤ 8 * (R ^ s)⁻¹ * torusDist y z ^ s :=
              mul_le_mul_of_nonneg_left (h4.trans h1) (by positivity)
      exact h5
    have h6 : |W y - W z| / torusDist y z ^ s ≤
        |Vt y - Vt z| / torusDist y z ^ s + 2 * D * (8 * R ^ (-s)) := by
      rw [div_le_iff₀ hdp]
      have : (|Vt y - Vt z| / torusDist y z ^ s + 2 * D * (8 * R ^ (-s))) * torusDist y z ^ s =
          |Vt y - Vt z| + 2 * D * ((8 * R ^ (-s)) * torusDist y z ^ s) := by field_simp
      rw [this]
      have h7 : 1 ≤ 8 * R ^ (-s) * torusDist y z ^ s := by
        rwa [div_le_iff₀ hdp] at hinv
        |> fun h => by simpa [mul_comm] using h
      nlinarith [mul_le_mul_of_nonneg_left h7 (by linarith : 0 ≤ 2 * D)]
    nlinarith
  · push Not at hlarge
    obtain ⟨n, hn⟩ := exists_shift_lt (y := y) (z := z)
      (m := min (2 * torusDist y z) (R / 8))
      (lt_min (by linarith) hlarge)
    have hn1 := (lt_min_iff.1 hn).1
    have hn2 := (lt_min_iff.1 hn).2
    have hper : W (z + latticeShift n) = W z := hWp n z
    have hdle : torusDist y z ≤ eNorm (y - (z + latticeShift n)) := by
      have := torusDist_le_shift y z n
      have e : y - z - latticeShift n = y - (z + latticeShift n) := by abel
      rwa [e] at this
    set e := eNorm (y - (z + latticeShift n)) with he
    have hepos : 0 < e := lt_of_lt_of_le hdpos hdle
    have hsh := hshort (z + latticeShift n) y hn2
    rw [hper] at hsh
    have hb0 : 0 < e / (R / 2) := by positivity
    have hb1 : e / (R / 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h1 : (e / (R / 2)) ^ a' ≤ (e / (R / 2)) ^ s :=
      Real.rpow_le_rpow_of_exponent_ge hb0 hb1 hsa
    have h2 : e / (R / 2) ≤ (4 / R) * torusDist y z := by
      rw [div_le_iff₀ (by positivity)]
      have : 4 / R * torusDist y z * (R / 2) = 2 * torusDist y z := by field_simp; ring
      rw [this]; exact hn1.le
    have h3 : (e / (R / 2)) ^ s ≤ (4 / R) ^ s * torusDist y z ^ s := by
      rw [← Real.mul_rpow (by positivity) hdpos.le]
      exact Real.rpow_le_rpow hb0.le h2 hs0.le
    have h4 : (4 / R) ^ s ≤ 4 * R ^ (-s) := by
      rw [Real.div_rpow (by norm_num) hR0.le, hRs]
      have : (4 : ℝ) ^ s ≤ 4 := by
        calc (4 : ℝ) ^ s ≤ (4 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
          _ = 4 := Real.rpow_one 4
      calc 4 ^ s / R ^ s = 4 ^ s * (R ^ s)⁻¹ := div_eq_mul_inv _ _
        _ ≤ 4 * (R ^ s)⁻¹ := mul_le_mul_of_nonneg_right this (by positivity)
    have h5 : |W y - W z| ≤ G * ((4 / R) ^ s * torusDist y z ^ s) := by
      have e1 : |W y - W z| = |W z - W y| := abs_sub_comm _ _
      rw [e1]
      exact hsh.trans (mul_le_mul_of_nonneg_left (h1.trans h3) hG)
    have h6 : |W y - W z| / torusDist y z ^ s ≤ 4 * G * R ^ (-s) := by
      rw [div_le_iff₀ hdp]
      calc _ ≤ G * ((4 / R) ^ s * torusDist y z ^ s) := h5
        _ ≤ G * ((4 * R ^ (-s)) * torusDist y z ^ s) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hdp.le) hG
        _ = 4 * G * R ^ (-s) * torusDist y z ^ s := by ring
    nlinarith

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization Set AVenhance
open scoped Convolution
namespace AVRegularity.Applications

/-! # The skew transfer identity

For `Ψ ∈ C¹(ℝ²)`, `g` with weak gradient `Dg` on `B` and `ψ ∈ C^∞_c(B)`,
`∫ (σ∇Ψ·∇g) ψ = ∫ Ψ σ∇g·∇ψ`.
Proved for smooth `Ψ` from the definition of the weak gradient and the symmetry of the Hessian,
then for `C¹` `Ψ` by uniform `C¹` approximation on the support of `ψ`. -/

theorem sigma_dot (a b : Vec 2) :
    vecDot (sigmaMat.mulVec a) b = -(a 1 * b 0) + a 0 * b 1 := by
  simp [sigmaMat, Matrix.mulVec, dotProduct, vecDot, Fin.sum_univ_two]

/-- Partial derivative `∂ᵢ f`. -/
def pd (i : Fin 2) (f : Vec 2 → ℝ) (x : Vec 2) : ℝ := fderiv ℝ f x (basisVec i)

theorem pd_contDiff {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (pd i f) :=
  contDiff_fderiv_apply_of_smooth hf _

theorem pd_comm {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 2) (x : Vec 2) :
    pd i (pd j f) x = pd j (pd i f) x := by
  have hsym := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have h1 : ∀ k : Fin 2, fderiv ℝ (fun y => fderiv ℝ f y (basisVec k)) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (basisVec k) := by
    intro k
    have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
      ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)) x
    exact (hd.hasFDerivAt.clm_apply (hasFDerivAt_const (basisVec k) x)).fderiv
      |> fun h => by simpa using h
  unfold pd
  rw [h1 j, h1 i]
  exact (hsym (basisVec j) (basisVec i)).symm

theorem pd_mul {f g : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) : pd i (fun y => f y * g y) x = f x * pd i g x + pd i f x * g x := by
  have hf' : DifferentiableAt ℝ f x := (hf.differentiable (by simp)) x
  have hg' : DifferentiableAt ℝ g x := (hg.differentiable (by simp)) x
  unfold pd
  have := (hf'.hasFDerivAt.mul hg'.hasFDerivAt).fderiv
  rw [show (fun y => f y * g y) = f * g from rfl, this]
  simp
  ring

theorem isSpTest_mul_left {B : Set (Vec 2)} {a ψ : Vec 2 → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hψ : IsSpTest B ψ) : IsSpTest B (fun y => a y * ψ y) :=
  ⟨ha.mul hψ.1, hψ.2.1.mul_left, (tsupport_mul_subset_right).trans hψ.2.2⟩

theorem isSpTest_pd {B : Set (Vec 2)} {ψ : Vec 2 → ℝ} (hψ : IsSpTest B ψ) (i : Fin 2) :
    IsSpTest B (pd i ψ) :=
  ⟨pd_contDiff hψ.1 i, hasCompactSupport_fderiv_apply hψ.2.1 _,
    (tsupport_fderiv_apply_subset ψ _).trans hψ.2.2⟩

theorem integrable_mul_cont_of_integrableOn {B : Set (Vec 2)} {f g : Vec 2 → ℝ}
    (hf : IntegrableOn f B) (hg : Continuous g) (hcs : HasCompactSupport g) :
    IntegrableOn (fun y => f y * g y) B := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hcs
  exact hf.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)

theorem skew_transfer_smooth {B : Set (Vec 2)} {Ψ g ψ : Vec 2 → ℝ} {Dg : Vec 2 → Vec 2}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hg : HasWeakGradientOn B g Dg) (hgI : IntegrableOn g B)
    (hDI : ∀ i, IntegrableOn (fun y => Dg y i) B) (hψ : IsSpTest B ψ) :
    ∫ y in B, vecDot (sigmaMat.mulVec (spGrad Ψ y)) (Dg y) * ψ y =
      ∫ y in B, Ψ y * vecDot (sigmaMat.mulVec (Dg y)) (spGrad ψ y) := by
  have W : ∀ (i : Fin 2) (ζ : Vec 2 → ℝ), IsSpTest B ζ →
      ∫ y in B, g y * pd i ζ y = -∫ y in B, Dg y i * ζ y := fun i ζ hζ =>
    hg i ζ hζ.1 hζ.2.1 hζ.2.2
  have hpdΨ := fun i => pd_contDiff hΨ i
  have tA := isSpTest_mul_left (hpdΨ 1) hψ
  have tB := isSpTest_mul_left (hpdΨ 0) hψ
  have tC := isSpTest_mul_left hΨ (isSpTest_pd hψ 0)
  have tD := isSpTest_mul_left hΨ (isSpTest_pd hψ 1)
  have cont : ∀ {ζ : Vec 2 → ℝ}, IsSpTest B ζ → Continuous ζ := fun h => h.1.continuous
  have iDg : ∀ (i : Fin 2) {ζ : Vec 2 → ℝ}, IsSpTest B ζ →
      IntegrableOn (fun y => Dg y i * ζ y) B := fun i ζ h =>
    integrable_mul_cont_of_integrableOn (hDI i) (cont h) h.2.1
  have iG : ∀ (i : Fin 2) {ζ : Vec 2 → ℝ}, IsSpTest B ζ →
      IntegrableOn (fun y => g y * pd i ζ y) B := fun i ζ h =>
    integrable_mul_cont_of_integrableOn hgI (cont (isSpTest_pd h i)) (isSpTest_pd h i).2.1
  have eL : ∫ y in B, vecDot (sigmaMat.mulVec (spGrad Ψ y)) (Dg y) * ψ y =
      ∫ y in B, (g y * pd 0 (fun z => pd 1 Ψ z * ψ z) y -
        g y * pd 1 (fun z => pd 0 Ψ z * ψ z) y) := by
    rw [integral_sub (iG 0 tA) (iG 1 tB), W 0 _ tA, W 1 _ tB]
    have i0 : IntegrableOn (fun y => -(Dg y 0 * (pd 1 Ψ y * ψ y))) B := (iDg 0 tA).neg
    have e : ∫ y in B, vecDot (sigmaMat.mulVec (spGrad Ψ y)) (Dg y) * ψ y =
        ∫ y in B, (-(Dg y 0 * (pd 1 Ψ y * ψ y)) + Dg y 1 * (pd 0 Ψ y * ψ y)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [sigma_dot, spGrad, pd]
      ring
    rw [e, integral_add i0 (iDg 1 tB), integral_neg]
    ring
  have eR : ∫ y in B, Ψ y * vecDot (sigmaMat.mulVec (Dg y)) (spGrad ψ y) =
      ∫ y in B, (g y * pd 1 (fun z => Ψ z * pd 0 ψ z) y -
        g y * pd 0 (fun z => Ψ z * pd 1 ψ z) y) := by
    rw [integral_sub (iG 1 tC) (iG 0 tD), W 1 _ tC, W 0 _ tD]
    have i0 : IntegrableOn (fun y => -(Dg y 1 * (Ψ y * pd 0 ψ y))) B := (iDg 1 tC).neg
    have e : ∫ y in B, Ψ y * vecDot (sigmaMat.mulVec (Dg y)) (spGrad ψ y) =
        ∫ y in B, (-(Dg y 1 * (Ψ y * pd 0 ψ y)) + Dg y 0 * (Ψ y * pd 1 ψ y)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [sigma_dot, spGrad, pd]
      ring
    rw [e, integral_add i0 (iDg 0 tD), integral_neg]
    ring
  rw [eL, eR]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h1 := pd_mul (hpdΨ 1) hψ.1 0 y
  have h2 := pd_mul (hpdΨ 0) hψ.1 1 y
  have h3 := pd_mul hΨ (pd_contDiff hψ.1 0) 1 y
  have h4 := pd_mul hΨ (pd_contDiff hψ.1 1) 0 y
  have c1 := pd_comm hΨ 0 1 y
  have c2 := pd_comm hψ.1 0 1 y
  show g y * pd 0 (fun z => pd 1 Ψ z * ψ z) y - g y * pd 1 (fun z => pd 0 Ψ z * ψ z) y =
    g y * pd 1 (fun z => Ψ z * pd 0 ψ z) y - g y * pd 0 (fun z => Ψ z * pd 1 ψ z) y
  rw [h1, h2, h3, h4, c1, ← c2]
  ring

/-- Derivative of a mollification on `ℝ²`: the derivative falls on `φ`. -/
theorem fderiv_normed_conv_apply_vec {φ : Vec 2 → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcs : HasCompactSupport φ) (ρ : ContDiffBump (0 : Vec 2)) (x v : Vec 2) :
    fderiv ℝ (ρ.normed (volume : Measure (Vec 2)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ)
        x v =
      (ρ.normed (volume : Measure (Vec 2)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun a => fderiv ℝ φ a v) x := by
  have hρ : Continuous (ρ.normed (volume : Measure (Vec 2))) := ρ.continuous_normed
  have hli := hρ.locallyIntegrable (μ := (volume : Measure (Vec 2)))
  have h := hcs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hli hφ x
  rw [h.fderiv, convolution_precompR_apply _ hli
    (hcs.fderiv (𝕜 := ℝ)) (hφ.continuous_fderiv one_ne_zero)]

/-- Smooth approximation of a `C¹` compactly supported function on `ℝ²` in `C¹`. -/
theorem exists_smooth_approx_vec {φ : Vec 2 → ℝ} (hφ : ContDiff ℝ 1 φ) (hcs : HasCompactSupport φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ (∀ x, |ψ x - φ x| ≤ ε) ∧
      ∀ x i, |pd i ψ x - pd i φ x| ≤ ε := by
  have hvol : ∀ v : Vec 2, ∃ δ > 0, ∀ ρ : ContDiffBump (0 : Vec 2), ρ.rOut < δ → ∀ x,
      |(ρ.normed (volume : Measure (Vec 2)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun a => fderiv ℝ φ a v) x - fderiv ℝ φ x v| ≤ ε := fun v =>
    normed_conv_approx (hφ.continuous_fderiv one_ne_zero |>.clm_apply continuous_const)
      (hasCompactSupport_fderiv_apply hcs v) hε
  obtain ⟨δ0, hδ0, h0⟩ := normed_conv_approx (μ := (volume : Measure (Vec 2)))
    hφ.continuous hcs hε
  obtain ⟨δ1, hδ1, h1⟩ := hvol (basisVec 0)
  obtain ⟨δ2, hδ2, h2⟩ := hvol (basisVec 1)
  set δ := min δ0 (min δ1 δ2) with hδdef
  have hδpos : 0 < δ := lt_min hδ0 (lt_min hδ1 hδ2)
  set ρ0 : ℝ := δ / 2 with hρ0
  have hρ0pos : 0 < ρ0 := by positivity
  let ρ : ContDiffBump (0 : Vec 2) :=
    { rIn := ρ0 / 2, rOut := ρ0, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hρδ : ρ.rOut < δ := by show ρ0 < δ; linarith
  have hli : LocallyIntegrable (ρ.normed (volume : Measure (Vec 2))) volume :=
    (ρ.continuous_normed (μ := (volume : Measure (Vec 2)))).locallyIntegrable
  refine ⟨ρ.normed (volume : Measure (Vec 2)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ,
    ?_, ?_, ?_⟩
  · exact (ρ.hasCompactSupport_normed (μ := (volume : Measure (Vec 2)))).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (ρ.contDiff_normed (μ := (volume : Measure (Vec 2)))
        (n := (⊤ : ℕ∞))) (hφ.continuous.locallyIntegrable)
  · intro x
    exact h0 ρ (lt_of_lt_of_le hρδ (min_le_left _ _)) x
  · intro x i
    unfold pd
    rw [fderiv_normed_conv_apply_vec hφ hcs]
    fin_cases i
    · exact h1 ρ (lt_of_lt_of_le hρδ ((min_le_right _ _).trans (min_le_left _ _))) x
    · exact h2 ρ (lt_of_lt_of_le hρδ ((min_le_right _ _).trans (min_le_right _ _))) x

/-- The (linear in `(P, p₀, p₁)`) integrand of the skew transfer. -/
def skewF (Dg : Vec 2 → Vec 2) (ψ : Vec 2 → ℝ) (P p0 p1 : Vec 2 → ℝ) (y : Vec 2) : ℝ :=
  Dg y 0 * (-(p1 y * ψ y) - P y * pd 1 ψ y) + Dg y 1 * (p0 y * ψ y + P y * pd 0 ψ y)

theorem skewF_eq (Dg : Vec 2 → Vec 2) (ψ Ψ : Vec 2 → ℝ) (y : Vec 2) :
    vecDot (sigmaMat.mulVec (spGrad Ψ y)) (Dg y) * ψ y -
        Ψ y * vecDot (sigmaMat.mulVec (Dg y)) (spGrad ψ y) =
      skewF Dg ψ Ψ (pd 0 Ψ) (pd 1 Ψ) y := by
  simp only [sigma_dot, spGrad, pd, skewF]
  ring

theorem exists_cutoff (K : Set (Vec 2)) (hK : IsCompact K) :
    ∃ (χ : Vec 2 → ℝ) (R : ℝ), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      K ⊆ Metric.ball (0 : Vec 2) R ∧ ∀ x ∈ Metric.ball (0 : Vec 2) R, χ x = 1 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Vec 2)
  let b : ContDiffBump (0 : Vec 2) :=
    { rIn := |R| + 1, rOut := |R| + 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  refine ⟨b, |R| + 1, b.contDiff, b.hasCompactSupport, ?_, fun x hx => ?_⟩
  · intro y hy
    have := hR hy
    rw [Metric.mem_closedBall] at this
    rw [Metric.mem_ball]
    linarith [le_abs_self R]
  · exact b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)

theorem integrable_skewF {B : Set (Vec 2)} {Dg : Vec 2 → Vec 2} {ψ P p0 p1 : Vec 2 → ℝ}
    (hDI : ∀ i, IntegrableOn (fun y => Dg y i) B) (hψ : IsSpTest B ψ) (hP : Continuous P)
    (h0 : Continuous p0) (h1 : Continuous p1) : IntegrableOn (skewF Dg ψ P p0 p1) B := by
  have c0 : Continuous fun y => -(p1 y * ψ y) - P y * pd 1 ψ y :=
    (h1.mul hψ.1.continuous).neg.sub (hP.mul (pd_contDiff hψ.1 1).continuous)
  have c1 : Continuous fun y => p0 y * ψ y + P y * pd 0 ψ y :=
    (h0.mul hψ.1.continuous).add (hP.mul (pd_contDiff hψ.1 0).continuous)
  have s0 : HasCompactSupport fun y => -(p1 y * ψ y) - P y * pd 1 ψ y :=
    (hψ.2.1.mul_left (f := p1)).neg.sub ((isSpTest_pd hψ 1).2.1.mul_left (f := P))
  have s1 : HasCompactSupport fun y => p0 y * ψ y + P y * pd 0 ψ y :=
    (hψ.2.1.mul_left (f := p0)).add ((isSpTest_pd hψ 0).2.1.mul_left (f := P))
  exact (integrable_mul_cont_of_integrableOn (hDI 0) c0 s0).add
    (integrable_mul_cont_of_integrableOn (hDI 1) c1 s1)

theorem pd_continuous {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 2) : Continuous (pd i f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem skewF_integral_eq {B : Set (Vec 2)} {Ψ ψ : Vec 2 → ℝ} {Dg : Vec 2 → Vec 2}
    (hΨ : ContDiff ℝ 1 Ψ) (hDI : ∀ i, IntegrableOn (fun y => Dg y i) B) (hψ : IsSpTest B ψ) :
    ∫ y in B, skewF Dg ψ Ψ (pd 0 Ψ) (pd 1 Ψ) y =
      (∫ y in B, vecDot (sigmaMat.mulVec (spGrad Ψ y)) (Dg y) * ψ y) -
        ∫ y in B, Ψ y * vecDot (sigmaMat.mulVec (Dg y)) (spGrad ψ y) := by
  have iL : IntegrableOn (fun y => vecDot (sigmaMat.mulVec (spGrad Ψ y)) (Dg y) * ψ y) B := by
    refine (integrable_skewF (P := fun _ => 0) (p0 := pd 0 Ψ) (p1 := pd 1 Ψ) hDI hψ
      continuous_const (pd_continuous hΨ 0) (pd_continuous hΨ 1)).congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [sigma_dot, spGrad, pd, skewF]
    ring
  have iR : IntegrableOn (fun y => Ψ y * vecDot (sigmaMat.mulVec (Dg y)) (spGrad ψ y)) B := by
    refine (integrable_skewF (P := Ψ) (p0 := fun _ => 0) (p1 := fun _ => 0) hDI hψ
      hΨ.continuous continuous_const continuous_const).neg.congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [sigma_dot, spGrad, pd, skewF, Pi.neg_apply]
    ring
  rw [← integral_sub iL iR]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact (skewF_eq Dg ψ Ψ y).symm

theorem skew_transfer {B : Set (Vec 2)} {Ψ g ψ : Vec 2 → ℝ} {Dg : Vec 2 → Vec 2}
    (hΨ : ContDiff ℝ 1 Ψ) (hg : HasWeakGradientOn B g Dg) (hgI : IntegrableOn g B)
    (hDI : ∀ i, IntegrableOn (fun y => Dg y i) B) (hψ : IsSpTest B ψ) :
    ∫ y in B, vecDot (sigmaMat.mulVec (spGrad Ψ y)) (Dg y) * ψ y =
      ∫ y in B, Ψ y * vecDot (sigmaMat.mulVec (Dg y)) (spGrad ψ y) := by
  obtain ⟨χ, R, hχ, hχcs, hKR, hχ1⟩ := exists_cutoff (tsupport ψ) hψ.2.1
  set Ψ' : Vec 2 → ℝ := fun y => χ y * Ψ y with hΨ'
  have hχ1' : ContDiff ℝ 1 χ := hχ.of_le (by exact_mod_cast le_top)
  have hΨ'c1 : ContDiff ℝ 1 Ψ' := hχ1'.mul hΨ
  have hΨ'cs : HasCompactSupport Ψ' := hχcs.mul_right
  have hag : ∀ y ∈ tsupport ψ, Ψ' =ᶠ[nhds y] Ψ := by
    intro y hy
    filter_upwards [Metric.isOpen_ball.mem_nhds (hKR hy)] with z hz
    simp [hΨ', hχ1 z hz]
  have hFeq : ∀ y, skewF Dg ψ Ψ (pd 0 Ψ) (pd 1 Ψ) y = skewF Dg ψ Ψ' (pd 0 Ψ') (pd 1 Ψ') y := by
    intro y
    by_cases hy : y ∈ tsupport ψ
    · have h := (hag y hy).fderiv_eq (𝕜 := ℝ)
      have h2 : Ψ' y = Ψ y := (hag y hy).eq_of_nhds
      simp only [skewF, pd, h, h2]
    · have h0 : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
      have h1 : pd 0 ψ y = 0 := by simp [pd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hy]
      have h2 : pd 1 ψ y = 0 := by simp [pd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hy]
      simp [skewF, h0, h1, h2]
  rw [← sub_eq_zero, ← skewF_integral_eq hΨ hDI hψ]
  simp only [hFeq]
  -- approximation of `Ψ'`
  set G : Vec 2 → ℝ := fun y => ‖Dg y 0‖ * (‖ψ y‖ + ‖pd 1 ψ y‖) + ‖Dg y 1‖ * (‖ψ y‖ + ‖pd 0 ψ y‖)
    with hG
  have hGint : IntegrableOn G B := by
    have c : ∀ i : Fin 2, IntegrableOn (fun y => ‖Dg y i‖ * (‖ψ y‖ + ‖pd (1 - i) ψ y‖)) B := by
      intro i
      refine integrable_mul_cont_of_integrableOn (hDI i).norm ?_ ?_
      · exact hψ.1.continuous.norm.add (pd_contDiff hψ.1 _).continuous.norm
      · exact hψ.2.1.norm.add (isSpTest_pd hψ _).2.1.norm
    exact (c 0).add (c 1)
  have hkey : ∀ ε : ℝ, 0 < ε → |∫ y in B, skewF Dg ψ Ψ' (pd 0 Ψ') (pd 1 Ψ') y| ≤
      ε * ∫ y in B, G y := by
    intro ε hε
    obtain ⟨Φ, hΦ, hΦ0, hΦ1⟩ := exists_smooth_approx_vec hΨ'c1 hΨ'cs hε
    have hΦ1' : ContDiff ℝ 1 Φ := hΦ.of_le (by exact_mod_cast le_top)
    have hz : ∫ y in B, skewF Dg ψ Φ (pd 0 Φ) (pd 1 Φ) y = 0 := by
      rw [skewF_integral_eq hΦ1' hDI hψ, skew_transfer_smooth hΦ hg hgI hDI hψ, sub_self]
    have i1 := integrable_skewF hDI hψ hΨ'c1.continuous (pd_continuous hΨ'c1 0)
      (pd_continuous hΨ'c1 1)
    have i2 := integrable_skewF hDI hψ hΦ1'.continuous (pd_continuous hΦ1' 0)
      (pd_continuous hΦ1' 1)
    have : ∫ y in B, skewF Dg ψ Ψ' (pd 0 Ψ') (pd 1 Ψ') y =
        ∫ y in B, (skewF Dg ψ Ψ' (pd 0 Ψ') (pd 1 Ψ') y - skewF Dg ψ Φ (pd 0 Φ) (pd 1 Φ) y) := by
      rw [integral_sub i1 i2, hz, sub_zero]
    rw [this, ← Real.norm_eq_abs]
    calc _ ≤ ∫ y in B, ε * G y := by
          refine norm_integral_le_of_norm_le (hGint.const_mul ε)
            (Filter.Eventually.of_forall fun y => ?_)
          have a0 := hΦ0 y
          have a1 := hΦ1 y 0
          have a2 := hΦ1 y 1
          rw [abs_sub_comm] at a0 a1 a2
          simp only [skewF, hG, Real.norm_eq_abs]
          have e : Dg y 0 * (-(pd 1 Ψ' y * ψ y) - Ψ' y * pd 1 ψ y) + Dg y 1 * (pd 0 Ψ' y * ψ y + Ψ' y * pd 0 ψ y) -
              (Dg y 0 * (-(pd 1 Φ y * ψ y) - Φ y * pd 1 ψ y) + Dg y 1 * (pd 0 Φ y * ψ y + Φ y * pd 0 ψ y)) =
              Dg y 0 * (-((pd 1 Ψ' y - pd 1 Φ y) * ψ y) - (Ψ' y - Φ y) * pd 1 ψ y) +
              Dg y 1 * ((pd 0 Ψ' y - pd 0 Φ y) * ψ y + (Ψ' y - Φ y) * pd 0 ψ y) := by ring
          rw [e]
          have t0 : |(Ψ' y - Φ y)| ≤ ε := a0
          have t1 : |(pd 0 Ψ' y - pd 0 Φ y)| ≤ ε := a1
          have t2 : |(pd 1 Ψ' y - pd 1 Φ y)| ≤ ε := a2
          have bnd : ∀ (D a b p q : ℝ), |a| ≤ ε → |b| ≤ ε →
              |D * (a * p + b * q)| ≤ ε * (|D| * (|p| + |q|)) := by
            intro D a b p q ha hb
            rw [abs_mul]
            have : |a * p + b * q| ≤ ε * (|p| + |q|) := by
              calc |a * p + b * q| ≤ |a * p| + |b * q| := abs_add_le _ _
                _ ≤ ε * |p| + ε * |q| := by
                  rw [abs_mul, abs_mul]
                  exact add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
                    (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
                _ = ε * (|p| + |q|) := by ring
            calc |D| * |a * p + b * q| ≤ |D| * (ε * (|p| + |q|)) :=
                  mul_le_mul_of_nonneg_left this (abs_nonneg _)
              _ = ε * (|D| * (|p| + |q|)) := by ring
          have u0 := bnd (Dg y 0) (-(pd 1 Ψ' y - pd 1 Φ y)) (-(Ψ' y - Φ y)) (ψ y) (pd 1 ψ y)
            (by rwa [abs_neg]) (by rwa [abs_neg])
          have u1 := bnd (Dg y 1) (pd 0 Ψ' y - pd 0 Φ y) (Ψ' y - Φ y) (ψ y) (pd 0 ψ y) t1 t0
          have r0 : Dg y 0 * (-((pd 1 Ψ' y - pd 1 Φ y) * ψ y) - (Ψ' y - Φ y) * pd 1 ψ y) =
              Dg y 0 * (-(pd 1 Ψ' y - pd 1 Φ y) * ψ y + -(Ψ' y - Φ y) * pd 1 ψ y) := by ring
          rw [r0]
          calc _ ≤ |Dg y 0 * (-(pd 1 Ψ' y - pd 1 Φ y) * ψ y + -(Ψ' y - Φ y) * pd 1 ψ y)| +
                |Dg y 1 * ((pd 0 Ψ' y - pd 0 Φ y) * ψ y + (Ψ' y - Φ y) * pd 0 ψ y)| :=
                abs_add_le _ _
            _ ≤ _ := by
              simp only [Real.norm_eq_abs] at *
              nlinarith [u0, u1]
      _ = ε * ∫ y in B, G y := integral_const_mul _ _
  have hM := setIntegral_nonneg_of_ae_restrict (μ := volume) (s := B)
    (f := G) (Filter.Eventually.of_forall fun y => by positivity)
  by_contra hne
  have hpos : 0 < |∫ y in B, skewF Dg ψ Ψ' (pd 0 Ψ') (pd 1 Ψ') y| := abs_pos.2 hne
  set I := |∫ y in B, skewF Dg ψ Ψ' (pd 0 Ψ') (pd 1 Ψ') y|
  set M := ∫ y in B, G y
  have h := hkey (I / (M + 1)) (by positivity)
  have h2 : I / (M + 1) * M < I := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

end AVRegularity.Applications
end

section
open MeasureTheory Set Filter Topology
open scoped Convolution
namespace AVRegularity.Applications

/-! # A function with bounded distributional derivative is a.e. within `M` of a constant

If `A ∈ L¹(-1,0)` and `∫ ζ' A = ∫ ζ G` for every `ζ ∈ C_c^∞(-1,0)` with `|G| ≤ M`, then
`|A - c₀| ≤ M` a.e. for some constant `c₀` (mollification in time, `L¹` Lebesgue points). Used for
the moving averages in the proof of Proposition 3.2 of the paper. -/

/-- The time bump of scale `1/(n+3)`. -/
def timeBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  { rIn := 1 / (2 * ((n : ℝ) + 3)), rOut := 1 / ((n : ℝ) + 3), rIn_pos := by positivity,
    rIn_lt_rOut := by
      have : (0 : ℝ) < (n : ℝ) + 3 := by positivity
      rw [div_lt_div_iff₀ (by positivity) this]; nlinarith }

theorem timeBump_rOut (n : ℕ) : (timeBump n).rOut = 1 / ((n : ℝ) + 3) := rfl

theorem tendsto_timeBump : Tendsto (fun n : ℕ => (timeBump n).rOut) atTop (𝓝 0) := by
  simp only [timeBump_rOut]
  have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 := (tendsto_add_atTop_iff_nat 2).2 this
  refine h2.congr fun n => ?_
  push_cast; ring_nf

/-- Derivative of the time mollification of an `L¹` function with bounded weak derivative. -/
theorem hasDerivAt_timeMollify {A G : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hA : IntegrableOn A (Ioo (-1 : ℝ) 0))
    (hG : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), |G τ| ≤ M)
    (hrel : ∀ ζ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Ioo (-1 : ℝ) 0 →
      ∫ τ in Ioo (-1 : ℝ) 0, deriv ζ τ * A τ = ∫ τ in Ioo (-1 : ℝ) 0, ζ τ * G τ)
    (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 + (timeBump n).rOut) (-(timeBump n).rOut)) :
    ∃ g, HasDerivAt (fun y => ((timeBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((Ioo (-1 : ℝ) 0).indicator A)) y) g x ∧ |g| ≤ M := by
  set f₀ : ℝ → ℝ := (timeBump n).normed volume with hf₀
  set Ā : ℝ → ℝ := (Ioo (-1 : ℝ) 0).indicator A with hĀ
  have hĀi : Integrable Ā := (integrable_indicator_iff measurableSet_Ioo).2 hA
  have hf₀c : ContDiff ℝ (⊤ : ℕ∞) f₀ := (timeBump n).contDiff_normed
  have hf₀cs : HasCompactSupport f₀ := (timeBump n).hasCompactSupport_normed
  have hd := hf₀cs.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hf₀c.of_le (by exact_mod_cast le_top)) hĀi.locallyIntegrable x
  refine ⟨_, hd, ?_⟩
  -- the test function `ζ s = f₀ (x - s)`
  set ζ : ℝ → ℝ := fun s => f₀ (x - s) with hζ
  have hζc : ContDiff ℝ (⊤ : ℕ∞) ζ := hf₀c.comp (contDiff_const.sub contDiff_id)
  have hζcs : HasCompactSupport ζ := hf₀cs.comp_homeomorph (Homeomorph.subLeft x)
  have hζts : tsupport ζ ⊆ Ioo (-1 : ℝ) 0 := by
    have h1 : tsupport ζ ⊆ (fun s => x - s) ⁻¹' tsupport f₀ := by
      refine closure_minimal ?_ ((isClosed_tsupport f₀).preimage (by fun_prop))
      intro s hs
      exact subset_closure hs
    intro s hs
    have h2 := h1 hs
    rw [mem_preimage, hf₀, ContDiffBump.tsupport_normed_eq, Metric.mem_closedBall,
      Real.dist_eq, sub_zero] at h2
    have h3 := abs_le.1 h2
    have := hx.1
    have := hx.2
    constructor <;> linarith [h3.1, h3.2]
  have hderζ : ∀ s, deriv ζ s = -deriv f₀ (x - s) := by
    intro s
    have hdf : DifferentiableAt ℝ f₀ (x - s) :=
      (hf₀c.differentiable (by simp)) _
    have := (hdf.hasDerivAt.comp s ((hasDerivAt_id s).const_sub x))
    exact this.deriv.trans (by simp)
  have hconv : (deriv f₀ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Ā) x =
      -∫ s in Ioo (-1 : ℝ) 0, deriv ζ s * A s := by
    rw [convolution_eq_swap]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    have h0 : ∀ s, deriv f₀ (x - s) * Ā s = -(deriv ζ s * Ā s) := fun s => by rw [hderζ]; ring
    simp only [h0, integral_neg]
    congr 1
    rw [hĀ]
    have : ∀ s, deriv ζ s * (Ioo (-1 : ℝ) 0).indicator A s =
        (Ioo (-1 : ℝ) 0).indicator (fun s => deriv ζ s * A s) s := fun s => by
      by_cases hs : s ∈ Ioo (-1 : ℝ) 0 <;> simp [hs]
    simp only [this]
    rw [integral_indicator measurableSet_Ioo]
  rw [hconv]
  have hrel' := hrel ζ hζc hζcs hζts
  rw [hrel']
  -- bound
  have hζ0 : ∀ s, 0 ≤ ζ s := fun s => (timeBump n).nonneg_normed _
  have hζint : ∫ s, ζ s = 1 := by
    have := integral_sub_left_eq_self (fun t => f₀ t) volume x
    simpa [hζ, hf₀] using this.trans (ContDiffBump.integral_normed (timeBump n))
  have hζI : Integrable ζ := hζc.continuous.integrable_of_hasCompactSupport hζcs
  rw [abs_neg]
  calc |∫ s in Ioo (-1 : ℝ) 0, ζ s * G s| ≤ ∫ s in Ioo (-1 : ℝ) 0, ζ s * M := by
        refine (abs_integral_le_integral_abs).trans ?_
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hζI.integrableOn.mul_const M) ?_
        filter_upwards [hG] with s hs
        rw [abs_mul, abs_of_nonneg (hζ0 s)]
        exact mul_le_mul_of_nonneg_left hs (hζ0 s)
    _ ≤ ∫ s, ζ s * M := by
        refine setIntegral_le_integral (hζI.mul_const M) (Eventually.of_forall fun s => ?_)
        exact mul_nonneg (hζ0 s) hM
    _ = M := by rw [integral_mul_const, hζint, one_mul]

theorem ae_near_const {A G : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hA : IntegrableOn A (Ioo (-1 : ℝ) 0))
    (hG : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), |G τ| ≤ M)
    (hrel : ∀ ζ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Ioo (-1 : ℝ) 0 →
      ∫ τ in Ioo (-1 : ℝ) 0, deriv ζ τ * A τ = ∫ τ in Ioo (-1 : ℝ) 0, ζ τ * G τ) :
    ∃ c0 : ℝ, ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), |A τ - c0| ≤ M := by
  set Ā : ℝ → ℝ := (Ioo (-1 : ℝ) 0).indicator A with hĀ
  have hĀi : Integrable Ā := (integrable_indicator_iff measurableSet_Ioo).2 hA
  set Aε : ℕ → ℝ → ℝ := fun n y =>
    ((timeBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Ā) y with hAε
  -- Lipschitz bound on the interior interval
  have hLip : ∀ n, ∀ x₁ ∈ Ioo (-1 + (timeBump n).rOut) (-(timeBump n).rOut),
      ∀ x₂ ∈ Ioo (-1 + (timeBump n).rOut) (-(timeBump n).rOut), |Aε n x₁ - Aε n x₂| ≤ M := by
    intro n x₁ hx₁ x₂ hx₂
    have hex : ∀ x : ℝ, ∃ g : ℝ, x ∈ Ioo (-1 + (timeBump n).rOut) (-(timeBump n).rOut) →
        (HasDerivAt (Aε n) g x ∧ |g| ≤ M) := by
      intro x
      by_cases hx : x ∈ Ioo (-1 + (timeBump n).rOut) (-(timeBump n).rOut)
      · obtain ⟨g, hg⟩ := hasDerivAt_timeMollify hM hA hG hrel n hx
        exact ⟨g, fun _ => hg⟩
      · exact ⟨0, fun h => absurd h hx⟩
    choose g hg using hex
    have hd : ∀ x ∈ Ioo (-1 + (timeBump n).rOut) (-(timeBump n).rOut),
        HasDerivWithinAt (Aε n) (g x) (Ioo (-1 + (timeBump n).rOut) (-(timeBump n).rOut)) x :=
      fun x hx => (hg x hx).1.hasDerivWithinAt
    have hb : ∀ x ∈ Ioo (-1 + (timeBump n).rOut) (-(timeBump n).rOut), ‖g x‖ ≤ M := fun x hx =>
      (hg x hx).2
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Ioo _ _) hx₂ hx₁
    have hdist : |x₁ - x₂| ≤ 1 := by
      have a1 := hx₁.1; have a2 := hx₁.2; have b1 := hx₂.1; have b2 := hx₂.2
      have := (timeBump n).rOut_pos
      rw [abs_le]; constructor <;> linarith
    calc |Aε n x₁ - Aε n x₂| = ‖Aε n x₁ - Aε n x₂‖ := (Real.norm_eq_abs _).symm
      _ ≤ M * ‖x₁ - x₂‖ := by
        exact this
      _ ≤ M * 1 := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hdist hM
      _ = M := mul_one _
  -- a.e. convergence
  have hconv : ∀ᵐ x ∂(volume : Measure ℝ), Tendsto (fun n => Aε n x) atTop (𝓝 (Ā x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K := 2) tendsto_timeBump
      (Eventually.of_forall fun n => by
        show 1 / ((n : ℝ) + 3) ≤ 2 * (1 / (2 * ((n : ℝ) + 3)))
        rw [show 2 * (1 / (2 * ((n : ℝ) + 3))) = 1 / ((n : ℝ) + 3) by field_simp])
      hĀi.locallyIntegrable
  have hconv' : ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 0)), Tendsto (fun n => Aε n x) atTop (𝓝 (A x)) := by
    filter_upwards [ae_restrict_of_ae hconv, ae_restrict_mem measurableSet_Ioo] with x hx hxm
    simpa [hĀ, hxm] using hx
  have hev : ∀ x ∈ Ioo (-1 : ℝ) 0, ∀ᶠ n in atTop,
      x ∈ Ioo (-1 + (timeBump n).rOut) (-(timeBump n).rOut) := by
    intro x hx
    have h0 := tendsto_timeBump.eventually (gt_mem_nhds (show (0 : ℝ) < min (x + 1) (-x) by
      exact lt_min (by linarith [hx.1]) (by linarith [hx.2])))
    filter_upwards [h0] with n hn
    have h1 := min_le_left (x + 1) (-x)
    have h2 := min_le_right (x + 1) (-x)
    constructor <;> linarith
  have hpair : ∀ x₁ x₂, x₁ ∈ Ioo (-1 : ℝ) 0 → x₂ ∈ Ioo (-1 : ℝ) 0 →
      Tendsto (fun n => Aε n x₁) atTop (𝓝 (A x₁)) → Tendsto (fun n => Aε n x₂) atTop (𝓝 (A x₂)) →
      |A x₁ - A x₂| ≤ M := by
    intro x₁ x₂ h₁ h₂ t₁ t₂
    have hlim := (t₁.sub t₂).abs
    refine le_of_tendsto hlim ?_
    filter_upwards [hev x₁ h₁, hev x₂ h₂] with n a b using hLip n x₁ a x₂ b
  -- choose the constant
  have hpos : (volume.restrict (Ioo (-1 : ℝ) 0)) ≠ 0 := by
    intro h
    have := congrArg (fun μ : Measure ℝ => μ univ) h
    simp at this
  have : (ae (volume.restrict (Ioo (-1 : ℝ) 0))).NeBot := ae_neBot.2 hpos
  obtain ⟨x₀, hx₀⟩ := (hconv'.and (ae_restrict_mem measurableSet_Ioo)).exists
  refine ⟨A x₀, ?_⟩
  filter_upwards [hconv', ae_restrict_mem measurableSet_Ioo] with x hx hxm
  exact hpair x x₀ hxm hx₀.2 hx hx₀.1

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization Set AVenhance
namespace AVRegularity.Applications

/-! # From the full relative drift to a skew matrix plus a divergence-free drift

If the full relative drift splits as `d' = d + w₁` with `w₁ = κ⁻¹ σ ∇_yΨ`, then by the skew
transfer identity (slice by slice, then integrating in time) a weak solution of
`∂τU - ΔU + d'·∇U = 0` solves `∂τU - div((I + K)∇U) + d·∇U = 0` with `K = κ⁻¹ Ψ σ`.
-/

/-- Fubini: an `L²(Q₁)` function has integrable slices on `B₁` for a.e. time. -/
theorem ae_slice_integrableOn {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 (volume.restrict (openCyl 0 1))) :
    ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), IntegrableOn (fun y => f (τ, y)) (euclidBall 0 1) := by
  have hfin : IsFiniteMeasure (volume.restrict (openCyl 0 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_openCyl_lt_top⟩
  have hint : Integrable f (volume.restrict (openCyl 0 1)) := hf.integrable one_le_two
  rw [volume_restrict_openCyl_eq_prod] at hint
  have h := hint.prod_right_ae
  simp only [Prod.fst_zero, Prod.snd_zero, zero_sub, one_pow] at h
  exact h

theorem fderiv_comp_spDil {c : Vec 2} {r : ℝ} {y : Vec 2} {f : Vec 2 → ℝ} (hf : DifferentiableAt ℝ f (spDil c r y)) (v : Vec 2) :
    fderiv ℝ (fun y => f (spDil c r y)) y v = fderiv ℝ f (spDil c r y) (r • v) := by
  have h1 : HasFDerivAt (fun y : Vec 2 => spDil c r y) (r • ContinuousLinearMap.id ℝ (Vec 2)) y := by
    have : (fun y : Vec 2 => spDil c r y) = fun y => c + (r • ContinuousLinearMap.id ℝ (Vec 2)) y := by
      funext y; simp [spDil]
    rw [this]
    exact ((r • ContinuousLinearMap.id ℝ (Vec 2)).hasFDerivAt).const_add c
  have := (hf.hasFDerivAt.comp y h1).fderiv
  simp only [Function.comp_def] at this
  rw [this]
  simp

section Abstract

variable {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2} {d d' w₁ : ℝ × Vec 2 → Vec 2}
  {Ψ : ℝ × Vec 2 → ℝ} {κ : ℝ}

theorem sigma_mulVec_smul (c : ℝ) (a : Vec 2) :
    (c • sigmaMat).mulVec a = c • sigmaMat.mulVec a := by
  rw [Matrix.smul_mulVec]

theorem integrable_T₁ {μ : Measure (ℝ × Vec 2)} (hDU : ∀ i : Fin 2, Integrable (fun p => DU p i) μ)
    (hΨc : Continuous Ψ) {BΨ : ℝ} (hΨB : ∀ p, |Ψ p| ≤ BΨ) {φ : ℝ × Vec 2 → ℝ}
    (hφ : IsSTTest (openCyl 0 1) φ) :
    Integrable (fun p => (Ψ p / κ) * vecDot (sigmaMat.mulVec (DU p)) (stSpaceGrad φ p)) μ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (by exact_mod_cast le_top)
  have hg : ∀ i : Fin 2, Continuous fun p => stSpaceGrad φ p i := fun i =>
    continuous_fderiv_apply_of_c1 hφ1 (0, basisVec i)
  have hgb : ∀ i : Fin 2, ∃ C, ∀ p, ‖stSpaceGrad φ p i‖ ≤ C := fun i =>
    bound_of_compactSupport (hg i) (hasCompactSupport_fderiv_apply hφ.2.1 _)
  obtain ⟨C0, hC0⟩ := hgb 0
  obtain ⟨C1, hC1⟩ := hgb 1
  have key : ∀ (i : Fin 2) (sgn : ℝ) (j : Fin 2) (C : ℝ),
      (∀ p, ‖stSpaceGrad φ p j‖ ≤ C) → Integrable (fun p => DU p i *
        (sgn * ((Ψ p / κ) * stSpaceGrad φ p j))) μ := by
    intro i sgn j C hC
    refine integrable_mul_bdd_cont (hDU i) (continuous_const.mul
      (((hΨc.div_const κ)).mul (hg j))) (C := |sgn| * ((BΨ / |κ|) * C)) fun p => ?_
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine mul_le_mul (div_le_div_of_nonneg_right (hΨB p) (abs_nonneg _)) (hC p)
      (norm_nonneg _) ((abs_nonneg _).trans (hΨB p) |> fun h => div_nonneg h (abs_nonneg _))
  have h0 := key 0 1 1 C1 hC1
  have h1 := key 1 (-1) 0 C0 hC0
  refine (h0.add h1).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [sigma_dot, Pi.add_apply, stSpaceGrad]
  ring

theorem integrable_T₂ {μ : Measure (ℝ × Vec 2)} (hDU : ∀ i : Fin 2, Integrable (fun p => DU p i) μ)
    (hw : Continuous w₁) {Bw : ℝ} (hwB : ∀ p, ‖w₁ p‖ ≤ Bw) {φ : ℝ × Vec 2 → ℝ}
    (hφ : IsSTTest (openCyl 0 1) φ) :
    Integrable (fun p => vecDot (w₁ p) (DU p) * φ p) μ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (by exact_mod_cast le_top)
  obtain ⟨Cφ, hCφ⟩ := bound_of_compactSupport hφ1.continuous hφ.2.1
  have key : ∀ i : Fin 2, Integrable (fun p => DU p i * (w₁ p i * φ p)) μ := by
    intro i
    refine integrable_mul_bdd_cont (hDU i) (((continuous_apply i).comp hw).mul hφ1.continuous)
      (C := Bw * Cφ) fun p => ?_
    rw [norm_mul]
    exact mul_le_mul ((norm_le_pi_norm _ i).trans (hwB p)) (hCφ p) (norm_nonneg _)
      ((norm_nonneg _).trans (hwB p))
  refine ((key 0).add (key 1)).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [vecDot, Fin.sum_univ_two, Pi.add_apply]
  ring

theorem slice_T_eq {κ : ℝ} {τ : ℝ}
    (hΨ1 : ContDiff ℝ 1 (fun y => Ψ (τ, y)))
    (hw₁ : ∀ y, w₁ (τ, y) = κ⁻¹ • sigmaMat.mulVec (spGrad (fun y => Ψ (τ, y)) y))
    (hgrad : HasWeakGradientOn (euclidBall 0 1) (fun y => U (τ, y)) (fun y => DU (τ, y)))
    (hU : IntegrableOn (fun y => U (τ, y)) (euclidBall 0 1))
    (hDI : ∀ i, IntegrableOn (fun y => DU (τ, y) i) (euclidBall 0 1)) {φ : ℝ × Vec 2 → ℝ}
    (hφ : IsSTTest (openCyl 0 1) φ) :
    ∫ y in euclidBall 0 1, (Ψ (τ, y) / κ) *
        vecDot (sigmaMat.mulVec (DU (τ, y))) (stSpaceGrad φ (τ, y)) =
      ∫ y in euclidBall 0 1, vecDot (w₁ (τ, y)) (DU (τ, y)) * φ (τ, y) := by
  have hψ : IsSpTest (euclidBall 0 1) (fun y => φ (τ, y)) :=
    isSpTest_slice (a := -1) (b := 0) (by rw [← openCyl_zero_one_eq]; exact hφ) τ
  have h := skew_transfer hΨ1 hgrad hU hDI hψ
  have e1 : ∀ y, vecDot (w₁ (τ, y)) (DU (τ, y)) * φ (τ, y) =
      κ⁻¹ * (vecDot (sigmaMat.mulVec (spGrad (fun y => Ψ (τ, y)) y)) (DU (τ, y)) * φ (τ, y)) := by
    intro y
    rw [hw₁ y, vecDot_smul_left]
    ring
  have e2 : ∀ y, (Ψ (τ, y) / κ) * vecDot (sigmaMat.mulVec (DU (τ, y))) (stSpaceGrad φ (τ, y)) =
      κ⁻¹ * (Ψ (τ, y) * vecDot (sigmaMat.mulVec (DU (τ, y)))
        (spGrad (fun y => φ (τ, y)) y)) := by
    intro y
    have : spGrad (fun y => φ (τ, y)) y = stSpaceGrad φ (τ, y) := by
      funext i
      simp only [spGrad, stSpaceGrad]
      exact fderiv_slice hφ.1 τ y (basisVec i)
    rw [this]
    ring
  simp only [e1, e2, integral_const_mul]
  rw [h]

theorem isSkewDriftWeak_of_skew {κ : ℝ}
    (hE : IsEnergyClassQ1 U DU) (hΨc : Continuous Ψ) {BΨ : ℝ} (hΨB : ∀ p, |Ψ p| ≤ BΨ)
    (hΨ1 : ∀ τ, ContDiff ℝ 1 (fun y => Ψ (τ, y)))
    (hd'c : Continuous d') {B' : ℝ} (hd'B : ∀ p, ‖d' p‖ ≤ B')
    (hdc : Continuous d) {B0 : ℝ} (hdB : ∀ p, ‖d p‖ ≤ B0)
    (hsplit : ∀ p, d' p = d p + w₁ p)
    (hw₁ : ∀ τ y, w₁ (τ, y) = κ⁻¹ • sigmaMat.mulVec (spGrad (fun y => Ψ (τ, y)) y))
    (hW : IsSkewDriftWeak 0 d' U DU) :
    IsSkewDriftWeak (fun p => (Ψ p / κ) • sigmaMat) d U DU := by
  intro φ hφ
  have hfin : IsFiniteMeasure (volume.restrict (openCyl 0 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_openCyl_lt_top⟩
  have hU : Integrable U (volume.restrict (openCyl 0 1)) := hE.1.integrable one_le_two
  have hDU : ∀ i : Fin 2, Integrable (fun p => DU p i) (volume.restrict (openCyl 0 1)) :=
    fun i => (hE.2.1 i).integrable one_le_two
  have hwc : Continuous w₁ := by
    have : w₁ = fun p => d' p - d p := funext fun p => by rw [hsplit p]; abel
    rw [this]; exact hd'c.sub hdc
  have hwB : ∀ p, ‖w₁ p‖ ≤ B' + B0 := fun p => by
    have : w₁ p = d' p - d p := by rw [hsplit p]; abel
    rw [this]; exact (norm_sub_le _ _).trans (add_le_add (hd'B p) (hdB p))
  have hH : Integrable (skewDriftIntegrand 0 d' U DU φ) (volume.restrict (openCyl 0 1)) :=
    integrable_skewDriftIntegrand_zero hU hDU hd'c hd'B hφ.1 hφ.2.1
  have hT₁ := integrable_T₁ (κ := κ) hDU hΨc hΨB hφ
  have hT₂ := integrable_T₂ hDU hwc hwB hφ
  -- the two terms have the same integral
  have hTeq : ∫ p in openCyl 0 1, (Ψ p / κ) * vecDot (sigmaMat.mulVec (DU p)) (stSpaceGrad φ p) =
      ∫ p in openCyl 0 1, vecDot (w₁ p) (DU p) * φ p := by
    have hQ := openCyl_zero_one_eq
    have hT₁' := hT₁
    have hT₂' := hT₂
    rw [hQ, volume_restrict_prod_eq] at hT₁' hT₂' ⊢
    rw [integral_prod _ hT₁', integral_prod _ hT₂']
    have hs1 := ae_slice_integrableOn hE.1
    have hs2 := fun i : Fin 2 => ae_slice_integrableOn (hE.2.1 i)
    have hs3 := hE.2.2.1
    have hs12 : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), ∀ i : Fin 2,
        IntegrableOn (fun y => DU (τ, y) i) (euclidBall 0 1) := by
      rw [ae_all_iff]; exact hs2
    refine integral_congr_ae ?_
    filter_upwards [hs1, hs12, hs3] with τ a b c
    exact slice_T_eq (hΨ1 τ) (hw₁ τ · ) c a b hφ
  change ∫ p in openCyl 0 1, (-(U p * stTimeDeriv φ p) + vecDot ((1 + (Ψ p / κ) • sigmaMat).mulVec (DU p))
      (stSpaceGrad φ p) + vecDot (d p) (DU p) * φ p) = 0
  have h0 : ∫ p in openCyl 0 1, skewDriftIntegrand 0 d' U DU φ p = 0 := hW φ hφ
  have hpt : ∀ p, (-(U p * stTimeDeriv φ p) + vecDot ((1 + (Ψ p / κ) • sigmaMat).mulVec (DU p))
      (stSpaceGrad φ p) + vecDot (d p) (DU p) * φ p) =
      skewDriftIntegrand 0 d' U DU φ p +
        ((Ψ p / κ) * vecDot (sigmaMat.mulVec (DU p)) (stSpaceGrad φ p) -
          vecDot (w₁ p) (DU p) * φ p) := by
    intro p
    simp only [skewDriftIntegrand, Pi.zero_apply, add_zero, Matrix.one_mulVec, hsplit p,
      Matrix.add_mulVec, sigma_mulVec_smul, vecDot_add_left, vecDot_smul_left,
      Matrix.one_mulVec]
    ring
  simp only [hpt]
  have hsub : Integrable (fun p => (Ψ p / κ) * vecDot (sigmaMat.mulVec (DU p)) (stSpaceGrad φ p) -
      vecDot (w₁ p) (DU p) * φ p) (volume.restrict (openCyl 0 1)) := hT₁.sub hT₂
  rw [integral_add hH hsub, integral_sub hT₁ hT₂, h0, hTeq]
  ring

end Abstract

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization Set AVRegularity.External.Campanato
namespace AVRegularity.Applications

/-! # The microscopic lemma applied with a skew matrix, about an arbitrary constant -/

/-- The root mean square about `c` over `Q₁`. -/
def rmsAbout (U : ℝ × Vec 2 → ℝ) (c : ℝ) : ℝ := Real.sqrt (⨍ p in openCyl 0 1, (U p - c) ^ 2)

theorem cylinderMean_sub_const {U : ℝ × Vec 2 → ℝ} (hU : MemLp U 2 (volume.restrict (openCyl 0 1)))
    (c : ℝ) : cylinderMean (fun p => U p - c) 0 1 = cylinderMean U 0 1 - c := by
  have hm : IsFiniteMeasure (volume.restrict (cylinder (0 : ℝ × Vec 2) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (cylinder_measure_ne_top 0 one_pos)⟩
  have hUi : Integrable U (volume.restrict (cylinder (0 : ℝ × Vec 2) 1)) := by
    rw [restrict_cylinder_eq_openCyl]
    have : IsFiniteMeasure (volume.restrict (openCyl 0 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact volume_openCyl_lt_top⟩
    exact hU.integrable one_le_two
  have hpos : 0 < (volume.real (cylinder (0 : ℝ × Vec 2) 1)) := cylinder_measureReal_pos 0 one_pos
  unfold cylinderMean
  rw [setAverage_eq, setAverage_eq, integral_sub hUi (integrable_const c), setIntegral_const,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]
  field_simp

theorem abs_cylinderMean_sub_le {U : ℝ × Vec 2 → ℝ} (hU : MemLp U 2 (volume.restrict (openCyl 0 1)))
    (c : ℝ) : |cylinderMean U 0 1 - c| ≤ rmsAbout U c := by
  have hfin : IsFiniteMeasure (volume.restrict (openCyl 0 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_openCyl_lt_top⟩
  have hUc : MemLp (fun p => U p - c) 2 (volume.restrict (openCyl 0 1)) :=
    hU.sub (memLp_const c)
  have := cylinderMean_abs_le hUc
  rwa [cylinderMean_sub_const hU c] at this

theorem camp_apply_K {a' η Ch : ℝ} (ha : 0 < a') (H : OcAt a' η Ch)
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2} {K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {d : ℝ × Vec 2 → Vec 2}
    (hK : ∀ i j : Fin 2, AEStronglyMeasurable (fun p => K p i j) (volume.restrict (openCyl 0 1)))
    (hd : ∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1)))
    (hskew : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (K p).transpose = -K p)
    (hbd : ∃ kK kd : ℝ, 0 ≤ kK ∧ 0 ≤ kd ∧ kK + kd ≤ η ∧
      ∀ᵐ p ∂(volume.restrict (openCyl 0 1)),
        (∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ kK ^ 2 * vecNormSq e) ∧
        vecNormSq (d p) ≤ kd ^ 2)
    (hdiv : IsDivFreeQ1 d) (hE : IsEnergyClassQ1 U DU) (hW : IsSkewDriftWeak K d U DU) :
    ∃ Ut : ℝ × Vec 2 → ℝ, ContinuousOn Ut (cylinder 0 (1 / 2)) ∧
      Tendsto (fun τ => ∫ y in euclidBall 0 (1 / 2), (U (τ, y) - Ut (0, y)) ^ 2)
        (𝓝[<] 0 ⊓ ae volume) (𝓝 0) ∧
      (∀ c : ℝ, ∀ z ∈ cylinder 0 (1 / 2), ∀ z' ∈ cylinder 0 (1 / 2),
        |Ut z - Ut z'| ≤ Ch * rmsAbout U c * parabolicHolderDistance z z' ^ a') ∧
      ∀ c : ℝ, ∀ z ∈ cylinder 0 (1 / 2), |Ut z - c| ≤ (Ch + 1) * rmsAbout U c := by
  obtain ⟨Ut, hcont, -, htr, hbound⟩ := H K d U DU hK hd hskew hbd hdiv hE hW
  have hz0 : ((0 : ℝ), (0 : Vec 2)) ∈ cylinder 0 (1 / 2) :=
    zero_mem_cylinder_of (by simp [euclidBall, vecNormSq, vecDot])
  have hw1 : ((-1 / 8 : ℝ), (0 : Vec 2)) ∈ cylinder 0 (1 / 2) := by
    refine ⟨?_, by simp [euclidBall, vecNormSq, vecDot]⟩
    simp only [Prod.fst_zero, mem_Ioc]
    constructor <;> norm_num
  have hne : (((0 : ℝ), (0 : Vec 2)) : ℝ × Vec 2) ≠ ((-1 / 8 : ℝ), (0 : Vec 2)) := by
    intro h
    have := congrArg Prod.fst h
    norm_num at this
  refine ⟨Ut, hcont, htr, ?_, ?_⟩
  · intro c z hz z' hz'
    by_cases h : z = z'
    · subst h
      simp [parabolicHolderDistance_self, Real.zero_rpow ha.ne']
    · have hpos := parabolicHolderDistance_pos h
      have := hbound c z hz z hz z' hz' h
      have h1 : |Ut z - Ut z'| / parabolicHolderDistance z z' ^ a' ≤ Ch * rmsAbout U c := by
        refine le_trans (le_add_of_nonneg_right (abs_nonneg (Ut z - cylinderMean U 0 1))) ?_
        simpa [rmsAbout] using this
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos _)] at h1
      exact h1
  · intro c z hz
    have h1 := hbound c z hz _ hz0 _ hw1 hne
    have h2 : |Ut z - cylinderMean U 0 1| ≤ Ch * rmsAbout U c := by
      refine le_trans (le_add_of_nonneg_left (div_nonneg (abs_nonneg (Ut (0, 0) - Ut (-1 / 8, 0)))
        (Real.rpow_nonneg (parabolicHolderDistance_nonneg' ((0 : ℝ), (0 : Vec 2))
          ((-1 / 8 : ℝ), (0 : Vec 2))) a'))) ?_
      simpa [rmsAbout] using h1
    have h3 := abs_cylinderMean_sub_le hE.1 c
    calc |Ut z - c| = |(Ut z - cylinderMean U 0 1) + (cylinderMean U 0 1 - c)| := by ring_nf
      _ ≤ |Ut z - cylinderMean U 0 1| + |cylinderMean U 0 1 - c| := abs_add_le _ _
      _ ≤ Ch * rmsAbout U c + rmsAbout U c := add_le_add h2 h3
      _ = (Ch + 1) * rmsAbout U c := by ring

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization Set
open scoped Convolution
namespace AVRegularity.Applications

/-! # The averaging kernel `χ` and product test functions `ζ(τ) χ(y)` -/

/-- A smooth bump on `ℝ²` (sup-norm balls of radii `1/4`, `1/2`). -/
def chiBump : ContDiffBump (0 : Vec 2) :=
  { rIn := 1 / 4, rOut := 1 / 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

/-- The averaging kernel: a smooth probability density supported in `B₁`. -/
def chi : Vec 2 → ℝ := chiBump.normed volume

theorem chi_smooth : ContDiff ℝ (⊤ : ℕ∞) chi := chiBump.contDiff_normed
theorem chi_cs : HasCompactSupport chi := chiBump.hasCompactSupport_normed
theorem chi_nonneg (y : Vec 2) : 0 ≤ chi y := chiBump.nonneg_normed y
theorem chi_integral : ∫ y, chi y = 1 := chiBump.integral_normed

theorem tsupport_chi : tsupport chi ⊆ euclidBall 0 1 := by
  rw [chi, ContDiffBump.tsupport_normed_eq]
  intro y hy
  have h : ‖y‖ ≤ 1 / 2 := by
    have : ‖y‖ ≤ chiBump.rOut := by simpa using hy
    exact this
  have := vecNormSq_le_two_norm_sq y
  have h2 : ‖y‖ ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  simp only [euclidBall, Set.mem_ofPred_eq, sub_zero]
  nlinarith

theorem chi_isSpTest : IsSpTest (euclidBall 0 1) chi := ⟨chi_smooth, chi_cs, tsupport_chi⟩

theorem chi_continuous : Continuous chi := chi_smooth.continuous

/-- The Laplacian `Δχ`. -/
def lapChi (y : Vec 2) : ℝ := pd 0 (pd 0 chi) y + pd 1 (pd 1 chi) y

theorem integral_pd_eq_zero {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f)
    (i : Fin 2) : ∫ y, pd i f y = 0 :=
  integral_fderiv_eq_zero_of_hasCompactSupport hf hcs (basisVec i)

theorem integral_lapChi : ∫ y, lapChi y = 0 := by
  have h0 := pd_contDiff chi_smooth 0
  have h1 := pd_contDiff chi_smooth 1
  have c0 : HasCompactSupport (pd 0 chi) := hasCompactSupport_fderiv_apply chi_cs _
  have c1 : HasCompactSupport (pd 1 chi) := hasCompactSupport_fderiv_apply chi_cs _
  have i0 : Integrable (pd 0 (pd 0 chi)) :=
    (pd_contDiff h0 0).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply c0 _)
  have i1 : Integrable (pd 1 (pd 1 chi)) :=
    (pd_contDiff h1 1).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply c1 _)
  unfold lapChi
  rw [integral_add i0 i1, integral_pd_eq_zero h0 c0, integral_pd_eq_zero h1 c1, add_zero]

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization Set AVRegularity.External.Campanato
namespace AVRegularity.Applications

/-! # One rescaled tube: representative, trace and bounds

From the rescaled problem `(K, d, U, DU)` along a `C¹` curve `Y` the microscopic lemma gives a
continuous profile `Wx = Ut(0, (· - Y t)/ρ)` which is the `L²` trace of `w` on `B_{ρ/4}(Y t)` and
satisfies amplitude and Hölder bounds about any constant `c`.
-/

theorem tube_core {a' η Ch : ℝ} (ha : 0 < a') (H : OcAt a' η Ch) (hCh : 0 ≤ Ch)
    {w : ℝ × Vec 2 → ℝ} {Dw : ℝ × Vec 2 → Vec 2} {Y Yd : ℝ → Vec 2} {t ρ κ B Rb : ℝ}
    (hκ : 0 < κ) (hρ : 0 < ρ) (hY1 : ContDiff ℝ 1 Y) (hYd : ∀ s, HasDerivAt Y (Yd s) s)
    (hYdB : ∀ s, ‖Yd s‖ ≤ B)
    (hE : IsEnergyClassQ1 (tubeU w Y t (ρ ^ 2 / κ) ρ) (tubeDU Dw Y t (ρ ^ 2 / κ) ρ))
    {K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {d : ℝ × Vec 2 → Vec 2}
    (hK : ∀ i j : Fin 2, AEStronglyMeasurable (fun p => K p i j) (volume.restrict (openCyl 0 1)))
    (hd : ∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1)))
    (hskew : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (K p).transpose = -K p)
    (hbd : ∃ kK kd : ℝ, 0 ≤ kK ∧ 0 ≤ kd ∧ kK + kd ≤ η ∧
      ∀ᵐ p ∂(volume.restrict (openCyl 0 1)),
        (∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ kK ^ 2 * vecNormSq e) ∧
        vecNormSq (d p) ≤ kd ^ 2)
    (hdiv : IsDivFreeQ1 d)
    (hW : IsSkewDriftWeak K d (tubeU w Y t (ρ ^ 2 / κ) ρ) (tubeDU Dw Y t (ρ ^ 2 / κ) ρ))
    (hRb : rmsAbout (tubeU w Y t (ρ ^ 2 / κ) ρ) 0 ≤ Rb) :
    ∃ Wx : Vec 2 → ℝ, ContinuousOn Wx (euclidBall (Y t) (ρ / 2)) ∧
      (∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
        IntegrableOn (fun y => (w (σ, y) - Wx y) ^ 2) (euclidBall (Y t) (ρ / 4))) ∧
      Tendsto (fun σ : ℝ => ∫ y in euclidBall (Y t) (ρ / 4), (w (σ, y) - Wx y) ^ 2)
        (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0) ∧
      (∀ z ∈ euclidBall (Y t) (ρ / 2), |Wx z| ≤ (Ch + 1) * Rb) ∧
      (∀ c : ℝ, |Wx (Y t) - c| ≤ (Ch + 1) * rmsAbout (tubeU w Y t (ρ ^ 2 / κ) ρ) c) ∧
      (∀ c : ℝ, ∀ z ∈ euclidBall (Y t) (ρ / 2), |Wx (Y t) - Wx z| ≤
        Ch * rmsAbout (tubeU w Y t (ρ ^ 2 / κ) ρ) c *
          (Real.sqrt (vecNormSq (Y t - z)) / ρ) ^ a') := by
  have hc : 0 < ρ ^ 2 / κ := by positivity
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hYdB 0)
  set U : ℝ × Vec 2 → ℝ := tubeU w Y t (ρ ^ 2 / κ) ρ with hU
  obtain ⟨Ut, hcont, htr, hhol, hamp⟩ := camp_apply_K ha H hK hd hskew hbd hdiv hE hW
  have hlip : ∀ s, ‖Y s - Y t‖ ≤ B * |s - t| := fun s => norm_sub_le_of_hasDerivAt hYd hYdB s t
  have hbd0 : ∀ z ∈ cylinder 0 (1 / 2), |Ut z| ≤ (Ch + 1) * rmsAbout U 0 := by
    intro z hz; simpa using hamp 0 z hz
  have hhol0 : ∀ z ∈ cylinder 0 (1 / 2), ∀ z' ∈ cylinder 0 (1 / 2),
      |Ut z - Ut z'| ≤ Ch * rmsAbout U 0 * parabolicHolderDistance z z' ^ a' := hhol 0
  obtain ⟨hint, htrace⟩ := trace_package (w := w) (Ut := Ut) (Y := Y) (t := t) (r := ρ)
    (c := ρ ^ 2 / κ) (M₁ := Ch * rmsAbout U 0) (M₀ := (Ch + 1) * rmsAbout U 0) (a' := a')
    (B := B) hc hρ ha hY1.continuous hB0 hlip hcont hhol0 hbd0 htr (ae_slice_memLp hE.1)
  have hprof : ∀ z ∈ euclidBall (Y t) (ρ / 2), spDilInv (Y t) ρ z ∈ euclidBall (0 : Vec 2) (1 / 2) := by
    intro z hz
    exact (mem_euclidBall_spDilInv hρ).2 (by rwa [← euclidBall_half_eq])
  have hspx : spDilInv (Y t) ρ (Y t) = 0 := by simp [spDilInv]
  have hrms0 : 0 ≤ rmsAbout U 0 := Real.sqrt_nonneg _
  refine ⟨tubeProfile Ut (Y t) ρ, ?_, hint, htrace, ?_, ?_, ?_⟩
  · exact hcont.comp (by unfold spDilInv; fun_prop : Continuous fun y : Vec 2 =>
      ((0 : ℝ), spDilInv (Y t) ρ y)).continuousOn
      (fun y hy => zero_mem_cylinder_of (hprof y hy))
  · intro z hz
    have h1 : |tubeProfile Ut (Y t) ρ z| ≤ (Ch + 1) * rmsAbout U 0 :=
      hbd0 _ (zero_mem_cylinder_of (hprof z hz))
    exact h1.trans (mul_le_mul_of_nonneg_left hRb (by linarith))
  · intro c
    have h2 : tubeProfile Ut (Y t) ρ (Y t) = Ut (0, 0) := by simp only [tubeProfile, hspx]
    rw [h2]
    exact hamp c _ (zero_mem_cylinder_of (by simp [euclidBall, vecNormSq, vecDot]))
  · intro c z hz
    have h0 : ((0 : Vec 2)) ∈ euclidBall (0 : Vec 2) (1 / 2) := by
      simp [euclidBall, vecNormSq, vecDot]
    have := holder_at_top (hhol c) h0 (hprof z hz)
    rw [zero_sub, vecNormSq_neg', sqrt_vecNormSq_spDilInv (Y t) z hρ] at this
    have h2 : tubeProfile Ut (Y t) ρ (Y t) = Ut (0, 0) := by simp only [tubeProfile, hspx]
    rw [h2]
    exact this

end AVRegularity.Applications
end
