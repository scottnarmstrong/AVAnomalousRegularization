-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Transverse.Link
import AVRegularity.Proofs.GenSem.ChainMetric
import AVRegularity.CycleReference.SingleModeFlux
public import AVRegularity.Proofs.GenSem.Transverse.Ops
public import AVRegularity.Proofs.GenSem.CoeffArr.FluxX
public import AVRegularity.Proofs.GenSem.GenArr.Arr
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

section
@[expose] public noncomputable section
open Homogenization AVRegularity
namespace AVRegularity.Providers.GenSem

/-! **The expression `cellInv (transPrim e)`.** `cellInvOf D e` is the scheduled
transverse inverse, from zero at the original start of the slot, of the transverse primitive of
the cell expression `e`: its flux is `transPrim e` in the transverse component and `0` in the
other, and its initial state is `0`. It is scheduled, from the seed and `solved`-invariant when `e`
is, and denotes `transverseInverseSem` of the transverse primitive of the denotation of `e`. -/

/-- The transverse inverse, from the original start of the slot and zero initial state, of the
transverse primitive of `e`. -/
def cellInvOf (D : OCData) {i : ℕ} {p : ℤ} (e : Gen .cell i p) : Gen .cell i p :=
  Gen.cellInv (fun j => if j = transverseIndex p then Gen.transPrim e
      else Gen.time (s := .cell) (i := i) (p := p) (.const 0))
    (D.slotStart i p) (Gen.time (s := .cell) (i := i) (p := p) (.const 0))

theorem isScheduled_cellInvOf (D : OCData) {i : ℕ} {p : ℤ} {e : Gen .cell i p}
    (he : Gen.IsScheduled D e) : Gen.IsScheduled D (cellInvOf D e) :=
  Gen.IsScheduled.cellInv fun j => by
    split_ifs
    · exact .transPrim he
    · exact .timeConst 0

theorem fromSeed_cellInvOf (D : OCData) {𝒮 : SeedExports} {i : ℕ} {p : ℤ} {e : Gen .cell i p}
    (he : Gen.FromSeed 𝒮 e) : Gen.FromSeed 𝒮 (cellInvOf D e) :=
  Gen.FromSeed.cellInv _ (fun j => by
    split_ifs
    · exact .transPrim he
    · exact .time _) (.time _)

theorem denotes_cellInvOf (D : OCData) (bw : ℝ) (j₀ : ℕ) {i : ℕ} {p : ℤ} {e : Gen .cell i p}
    {f : GenSort.Sem .cell} (hd : Gen.Denotes D bw j₀ e f) :
    Gen.Denotes D bw j₀ (cellInvOf D e)
      (transverseInverseSem D i p
        (fun j => if j = transverseIndex p then transversePrimitiveSem p f
          else GenSort.ofTime .cell (TimeLetter.eval D (.const 0)))
        (D.slotStart i p) (GenSort.ofTime .cell (TimeLetter.eval D (.const 0)))) :=
  Gen.Denotes.cellInv (D.slotStart i p) (fun j => by
    split_ifs
    · exact .transPrim hd
    · exact .time _) (.time _)

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity AVRegularity.Providers.Transverse
namespace AVRegularity.Providers.GenSem

/-! **Transverse Fourier calculus for the primitive.** The transverse primitive of a real
continuous periodic transverse function with summable transverse Fourier coefficients is the real
series with the amplitudes `primAmp`; its Fourier coefficients are `primAmp` and `∂_q` of it
recovers the function minus its transverse mean. -/

/-- A transverse series with Hermitian amplitudes is real. -/
theorem tser_conj_eq (q : Fin 2) {A : ℤ → ℂ} (hsym : ∀ h, A (-h) = starRingEnd ℂ (A h))
    (η : Vec 2) : starRingEnd ℂ (tser q A η) = tser q A η := by
  unfold tser
  rw [Complex.conj_tsum]
  have e : ∀ h : ℤ, starRingEnd ℂ (A h * modeExp q h η) = A (-h) * modeExp q (-h) η := by
    intro h
    rw [map_mul, hsym h, modeExp, modeExp, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast, Int.cast_neg]
    ring
  simp_rw [e]
  exact (Equiv.neg ℤ).tsum_eq (fun h => A h * modeExp q h η)

theorem modeExp_line (q : Fin 2) (k : ℤ) (s : ℝ) :
    modeExp q k (s • basisVec q) = Complex.exp ((2 * Real.pi * Complex.I * (k : ℂ)) * (s : ℂ)) := by
  simp [modeExp, basisVec_apply]

/-- The Fourier coefficient of the real transverse series with Hermitian summable amplitudes. -/
theorem phaseCoeff_tser_re (q : Fin 2) {A : ℤ → ℂ} (hA : Summable fun h => ‖A h‖)
    (hsym : ∀ h, A (-h) = starRingEnd ℂ (A h)) (h : ℤ) :
    phaseCoeff q (fun η => (tser q A η).re) h = A h := by
  have hreal : ∀ s : ℝ, (((tser q A (s • basisVec q)).re : ℝ) : ℂ) = tser q A (s • basisVec q) :=
    fun s => Complex.conj_eq_iff_re.mp (tser_conj_eq q hsym _)
  unfold phaseCoeff
  simp_rw [hreal, tser, ← tsum_mul_right, modeExp_line]
  rw [intervalIntegral.integral_of_le zero_le_one]
  set F : ℤ → ℝ → ℂ := fun k s => A k * Complex.exp ((2 * Real.pi * Complex.I * (k : ℂ)) * (s : ℂ)) *
    Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * (s : ℂ))) with hF
  have hFc : ∀ k, Continuous (F k) := fun k => by
    simp only [hF]; fun_prop
  have hFn : ∀ k s, ‖F k s‖ = ‖A k‖ := by
    intro k s
    simp only [hF, norm_mul, Complex.norm_exp]
    simp
  have hint : ∀ k, Integrable (F k) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun k =>
    ((hFc k).continuousOn.integrableOn_Icc (a := (0:ℝ)) (b := 1)).mono_set Set.Ioc_subset_Icc_self
  have hsum : Summable fun k => ∫ s in Set.Ioc (0 : ℝ) 1, ‖F k s‖ := by
    simp_rw [hFn]
    simpa [Measure.real] using hA
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  rw [tsum_eq_single h]
  · rw [← intervalIntegral.integral_of_le zero_le_one]
    simp only [hF]
    have : ∀ s : ℝ, A h * Complex.exp ((2 * Real.pi * Complex.I * (h : ℂ)) * (s : ℂ)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * (s : ℂ))) = A h := by
      intro s; rw [mul_assoc, ← Complex.exp_add]; simp
    simp_rw [this]
    simp
  · intro k hk
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have hk' : (2 * Real.pi * Complex.I * ((k - h : ℤ) : ℂ)) ≠ 0 := by
      have : ((k - h : ℤ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hk
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) this
    have e : ∀ s : ℝ, F k s = A k * Complex.exp ((2 * Real.pi * Complex.I * ((k - h : ℤ) : ℂ)) * (s : ℂ)) := by
      intro s
      simp only [hF]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hk']
    have h1 : Complex.exp ((2 * Real.pi * Complex.I * ((k - h : ℤ) : ℂ)) * ((1 : ℝ) : ℂ)) = 1 :=
      Complex.exp_eq_one_iff.mpr ⟨k - h, by push_cast; ring⟩
    rw [h1, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, zero_div, mul_zero]

theorem latticeShift_single' (q : Fin 2) :
    AVenhance.latticeShift (Pi.single q 1) = basisVec q := by
  funext i
  by_cases h : i = q
  · subst h; simp [AVenhance.latticeShift]
  · simp [AVenhance.latticeShift, h]

theorem line_periodic' {f : Vec 2 → ℝ} (hp : AVenhance.IsZ2Periodic f) (q : Fin 2)
    (s : ℝ) : f ((s + 1) • basisVec q) = f (s • basisVec q) := by
  have := hp (Pi.single q 1) (s • basisVec q)
  rw [latticeShift_single'] at this
  rw [← this, add_smul, one_smul]

/-- Fourier inversion for a continuous periodic transverse function with summable transverse
Fourier coefficients. -/
theorem hasSum_transverse_of_summable {q : Fin 2} {f : Vec 2 → ℝ} (hc : Continuous f)
    (hp : AVenhance.IsZ2Periodic f) (ht : IsTransverse q f)
    (hs : Summable fun h : ℤ => ‖phaseCoeff q f h‖) (η : Vec 2) :
    HasSum (fun h : ℤ => phaseCoeff q f h * modeExp q h η) (f η : ℂ) := by
  set g : ℝ → ℂ := fun s => ((f (s • basisVec q) : ℝ) : ℂ) with hg
  have hgc : Continuous g :=
    Complex.continuous_ofReal.comp (hc.comp (continuous_id.smul continuous_const))
  have hgp : Function.Periodic g 1 := fun s => by simp only [hg, line_periodic' hp q s]
  have hF : Continuous (AddCircle.liftIco (1 : ℝ) 0 g) :=
    AddCircle.liftIco_continuous (by simpa using (hgp 0).symm) hgc.continuousOn
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨AddCircle.liftIco (1 : ℝ) 0 g, hF⟩
  have hcoeff : ∀ n : ℤ, fourierCoeff F n = phaseCoeff q f n := by
    intro n
    change fourierCoeff (AddCircle.liftIco (1 : ℝ) 0 g) n = _
    rw [fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
    simp only [zero_add, sub_zero, div_one, one_smul, phaseCoeff, hg]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [smul_eq_mul]
    rw [fourier_coe_apply, mul_comm]
    congr 2
    push_cast
    ring
  have hsum : Summable (fourierCoeff F) := by
    refine Summable.of_norm ?_
    simpa [hcoeff] using hs
  have hpt := has_pointwise_sum_fourier_series_of_summable hsum ((η q : ℝ) : AddCircle (1 : ℝ))
  have hval : F ((η q : ℝ) : AddCircle (1 : ℝ)) = (f η : ℂ) := by
    have e1 : ((η q : ℝ) : AddCircle (1 : ℝ)) = ((Int.fract (η q) : ℝ) : AddCircle (1 : ℝ)) := by
      have : η q = Int.fract (η q) + ((⌊η q⌋ : ℤ) : ℝ) := (Int.fract_add_floor _).symm
      conv_lhs => rw [this]
      rw [AddCircle.coe_add]
      have : (((⌊η q⌋ : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨⌊η q⌋, by simp⟩
      rw [this, add_zero]
    change AddCircle.liftIco (1 : ℝ) 0 g _ = _
    rw [e1, AddCircle.liftIco_coe_apply (Set.mem_Ico.2 ⟨Int.fract_nonneg _, by rw [zero_add]; exact Int.fract_lt_one _⟩)]
    have : g (Int.fract (η q)) = g (η q) := by
      have := hgp.sub_int_mul_eq (x := η q) ⌊η q⌋
      rw [mul_one] at this
      exact this
    rw [this, hg]
    simp only
    rw [← ht η]
  rw [← hval]
  have e : (fun h : ℤ => phaseCoeff q f h * modeExp q h η) =
      fun i : ℤ => fourierCoeff F i • fourier i ((η q : ℝ) : AddCircle (1 : ℝ)) := by
    funext i
    rw [hcoeff, smul_eq_mul, fourier_coe_apply, modeExp]
    congr 2
    push_cast
    ring
  rw [e]
  exact hpt

/-- The Fourier amplitudes of the transverse primitive of `g`. -/
def primAmp (q : Fin 2) (g : Vec 2 → ℝ) (h : ℤ) : ℂ :=
  if h = 0 then 0 else (2 * Real.pi * Complex.I * (h : ℂ))⁻¹ * phaseCoeff q g h

theorem primAmp_sym (q : Fin 2) {g : Vec 2 → ℝ} (hg : Continuous g) (h : ℤ) :
    primAmp q g (-h) = starRingEnd ℂ (primAmp q g h) := by
  by_cases hh : h = 0
  · subst hh; simp [primAmp]
  · have hh' : -h ≠ 0 := neg_ne_zero.mpr hh
    simp only [primAmp, hh, hh', ite_false, map_mul, map_inv₀]
    rw [phaseCoeff_neg q g hg h]
    congr 2
    simp only [map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
    push_cast
    ring

theorem transversePrimitiveSem_eq (p : ℤ) (f : GenSort.Sem .cell) (t : ℝ) (ch : RealChain)
    (η : Vec 2) :
    transversePrimitiveSem p f t ch η =
      (tser (transverseIndex p) (primAmp (transverseIndex p) (f t ch)) η).re := rfl

end AVRegularity.Providers.GenSem
end

section
open MeasureTheory Set Homogenization AVRegularity AVRegularity.Providers.Transverse
namespace AVRegularity.Providers.GenSem

/-! **Parseval for transverse Fourier coefficients.** The transverse Fourier
coefficients of a continuous function are square summable (`summable_sq_phaseCoeff`). Hence the
amplitudes of its transverse primitive are summable (`summable_primAmp_of_continuous`), and so are
the transverse Fourier coefficients of a periodic `C¹` function
(`summable_phaseCoeff_of_contDiff`). -/

theorem phaseCoeff_eq_fourierCoeffOn (q : Fin 2) (f : Vec 2 → ℝ) (h : ℤ) :
    phaseCoeff q f h =
      fourierCoeffOn zero_lt_one (fun s : ℝ => ((f (s • basisVec q) : ℝ) : ℂ)) h := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul, phaseCoeff]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [smul_eq_mul]
  rw [fourier_coe_apply, mul_comm]
  congr 2
  push_cast
  ring

/-- **Parseval**: the transverse Fourier coefficients of a continuous function are square
summable. -/
theorem summable_sq_phaseCoeff (q : Fin 2) {f : Vec 2 → ℝ} (hc : Continuous f) :
    Summable fun h : ℤ => ‖phaseCoeff q f h‖ ^ 2 := by
  have hg : Continuous fun s : ℝ => ((f (s • basisVec q) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hc.comp (continuous_id.smul continuous_const))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg.continuousOn (s := Icc (0 : ℝ) 1))
  have hL2 : MemLp (fun s : ℝ => ((f (s • basisVec q) : ℝ) : ℂ)) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound hg.aestronglyMeasurable C
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => hC s (Ioc_subset_Icc_self hs))
  simpa only [phaseCoeff_eq_fourierCoeffOn] using
    (hasSum_sq_fourierCoeffOn zero_lt_one hL2).summable

theorem norm_primAmp_le_sq (q : Fin 2) (g : Vec 2 → ℝ) (h : ℤ) :
    ‖primAmp q g h‖ ≤ ‖phaseCoeff q g h‖ ^ 2 + 1 / (h : ℝ) ^ 2 := by
  by_cases hh : h = 0
  · simp only [primAmp, hh, ite_true, norm_zero]
    positivity
  · have h1 : (1 : ℝ) ≤ |(h : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
    have hpos : 0 < |(h : ℝ)| := by linarith
    simp only [primAmp, hh, ite_false, norm_mul, norm_inv, Complex.norm_I,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one,
      Complex.norm_intCast]
    set a := ‖phaseCoeff q g h‖
    have ha : 0 ≤ a := norm_nonneg _
    have e1 : (2 * Real.pi * |(h : ℝ)|)⁻¹ * a ≤ a * (1 / |(h : ℝ)|) := by
      rw [mul_comm, one_div]
      refine mul_le_mul_of_nonneg_left (inv_anti₀ hpos ?_) ha
      nlinarith [Real.pi_gt_three]
    have e2 : a * (1 / |(h : ℝ)|) ≤ a ^ 2 + 1 / (h : ℝ) ^ 2 := by
      have := two_mul_le_add_sq a (1 / |(h : ℝ)|)
      have hsq : (1 / |(h : ℝ)|) ^ 2 = 1 / (h : ℝ) ^ 2 := by rw [div_pow, sq_abs, one_pow]
      have hnn : 0 ≤ a * (1 / |(h : ℝ)|) := by positivity
      nlinarith
    linarith

/-- The amplitudes of the transverse primitive of a continuous function are summable. -/
theorem summable_primAmp_of_continuous (q : Fin 2) {g : Vec 2 → ℝ} (hc : Continuous g) :
    Summable fun h => ‖primAmp q g h‖ :=
  ((summable_sq_phaseCoeff q hc).add
      (Real.summable_one_div_int_pow.mpr one_lt_two)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (norm_primAmp_le_sq q g)

/-- The transverse Fourier coefficients of a periodic `C¹` function are summable. -/
theorem summable_phaseCoeff_of_contDiff (q : Fin 2) {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hp : AVenhance.IsZ2Periodic f) : Summable fun h : ℤ => ‖phaseCoeff q f h‖ := by
  have hc' : Continuous fun η => fderiv ℝ f η (basisVec q) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hP := summable_primAmp_of_continuous q hc'
  have hfin : Summable fun h : ℤ => if h = 0 then ‖phaseCoeff q f 0‖ else 0 :=
    summable_of_ne_finset_zero (s := {0}) fun h hh => by
      simp only [Finset.mem_singleton] at hh
      simp [hh]
  refine (hP.add hfin).of_nonneg_of_le (fun _ => norm_nonneg _) fun h => ?_
  by_cases hh : h = 0
  · subst hh
    simp
  · have hd := phaseCoeff_deriv (q := q) hf hp h
    have hc0 : (2 * Real.pi * Complex.I * (h : ℂ)) ≠ 0 := by
      have : (h : ℂ) ≠ 0 := by exact_mod_cast hh
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) this
    have e : primAmp q (fun η => fderiv ℝ f η (basisVec q)) h = phaseCoeff q f h := by
      simp only [primAmp, hh, ite_false]
      rw [hd, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    simp [e, hh]

/-- The Fourier coefficients of the transverse primitive of a continuous function (no summability
hypothesis). -/
theorem phaseCoeff_transversePrimitive' (p : ℤ) (f : GenSort.Sem .cell) (t : ℝ) (ch : RealChain)
    (hc : Continuous (f t ch)) (h : ℤ) :
    phaseCoeff (transverseIndex p) (transversePrimitiveSem p f t ch) h =
      primAmp (transverseIndex p) (f t ch) h := by
  have : transversePrimitiveSem p f t ch =
      fun η => (tser (transverseIndex p) (primAmp (transverseIndex p) (f t ch)) η).re :=
    funext fun η => transversePrimitiveSem_eq p f t ch η
  rw [this]
  exact phaseCoeff_tser_re _ (summable_primAmp_of_continuous _ hc) (primAmp_sym _ hc) h

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Uniform denotability over a family of base chains.** `UEnv Λ` is a `RepEnv` (only
`D bw j₀ i p ρ 𝒮` are used) together with an index type `Λ` of "times" carrying the physical time
`time l`, the base chain `base l` and the open set of offsets `U l`, and a window `W ⊆ Λ`.
`V.URep φ e` says that the cell expression `e` (scheduled, from the seed) denotes one function `f`
with `φ l X z = f (time l) ((base l).recenter (ρ X)) z` for all `l ∈ W` and offsets `X ∈ U l`, and
that every such `φ l X` is invariant under parallel shifts of the phase (carried semantically).
The closure lemmas are those of `RepEnv` with the quantifier over `l` inside. -/

section
/-- The data of a uniform representation problem over the index type `Λ`. -/
structure UEnv (Λ : Type) where
  /-- The fixed data (its time, base chain and offsets are not used). -/
  E : RepEnv
  /-- The physical time of an index. -/
  time : Λ → ℝ
  /-- The base chain of an index. -/
  base : Λ → RealChain
  /-- The admissible offsets of an index. -/
  U : Λ → Set (Vec 2)
  /-- The window of indices. -/
  W : Set Λ

namespace UEnv

variable {Λ : Type} {V : UEnv Λ}

/-- The fixed-time environment at the index `l`. -/
def envAt (V : UEnv Λ) (l : Λ) : RepEnv :=
  { V.E with t := V.time l, A := V.base l, U := V.U l }

/-- `φ` is represented by the cell expression `e` at all indices of the window. -/
def URep (V : UEnv Λ) (φ : Λ → Vec 2 → Vec 2 → ℝ) (e : Gen .cell V.E.i V.E.p) : Prop :=
  Gen.IsScheduled V.E.D e ∧ Gen.FromSeed V.E.𝒮 e ∧
    ∃ f : GenSort.Sem .cell, Gen.Denotes V.E.D V.E.bw V.E.j₀ e f ∧
      (∀ l ∈ V.W, ∀ X ∈ V.U l, ∀ z,
        φ l X z = f (V.time l) ((V.base l).recenter V.E.D (V.E.ρ • X)) z) ∧
      (∀ l ∈ V.W, ∀ X ∈ V.U l, ∀ z (s : ℝ),
        φ l X (z + s • basisVec (parIdx V.E.p)) = φ l X z)

/-- `φ` is represented by some cell expression. -/
def IsURep (V : UEnv Λ) (φ : Λ → Vec 2 → Vec 2 → ℝ) : Prop := ∃ e, V.URep φ e

theorem URep.congr {φ ψ : Λ → Vec 2 → Vec 2 → ℝ} {e : Gen .cell V.E.i V.E.p} (h : V.URep φ e)
    (hφψ : ∀ l ∈ V.W, ∀ X ∈ V.U l, ∀ z, ψ l X z = φ l X z) : V.URep ψ e := by
  obtain ⟨hs, hf, f, hd, hv, hi⟩ := h
  refine ⟨hs, hf, f, hd, fun l hl X hX z => (hφψ l hl X hX z).trans (hv l hl X hX z),
    fun l hl X hX z s => ?_⟩
  rw [hφψ l hl X hX, hφψ l hl X hX, hi l hl X hX z s]

theorem IsURep.congr {φ ψ : Λ → Vec 2 → Vec 2 → ℝ} (h : V.IsURep φ)
    (hφψ : ∀ l ∈ V.W, ∀ X ∈ V.U l, ∀ z, ψ l X z = φ l X z) : V.IsURep ψ := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, he.congr hφψ⟩

theorem URep.add {φ ψ : Λ → Vec 2 → Vec 2 → ℝ} {a b : Gen .cell V.E.i V.E.p} (ha : V.URep φ a)
    (hb : V.URep ψ b) : V.URep (fun l X z => φ l X z + ψ l X z) (Gen.add a b) := by
  obtain ⟨sa, fa, f, hf, hφ, ia⟩ := ha
  obtain ⟨sb, fb, g, hg, hψ, ib⟩ := hb
  refine ⟨.add sa sb, .add fa fb, GenSort.add .cell f g, .add hf hg, fun l hl X hX z => ?_,
    fun l hl X hX z s => ?_⟩
  · show φ l X z + ψ l X z = f (V.time l) _ z + g (V.time l) _ z
    rw [hφ l hl X hX z, hψ l hl X hX z]
  · show φ l X _ + ψ l X _ = φ l X z + ψ l X z
    rw [ia l hl X hX z s, ib l hl X hX z s]

theorem URep.mul {φ ψ : Λ → Vec 2 → Vec 2 → ℝ} {a b : Gen .cell V.E.i V.E.p} (ha : V.URep φ a)
    (hb : V.URep ψ b) : V.URep (fun l X z => φ l X z * ψ l X z) (Gen.mul a b) := by
  obtain ⟨sa, fa, f, hf, hφ, ia⟩ := ha
  obtain ⟨sb, fb, g, hg, hψ, ib⟩ := hb
  refine ⟨.mul sa sb, .mul fa fb, GenSort.mul .cell f g, .mul hf hg, fun l hl X hX z => ?_,
    fun l hl X hX z s => ?_⟩
  · show φ l X z * ψ l X z = f (V.time l) _ z * g (V.time l) _ z
    rw [hφ l hl X hX z, hψ l hl X hX z]
  · show φ l X _ * ψ l X _ = φ l X z * ψ l X z
    rw [ia l hl X hX z s, ib l hl X hX z s]

theorem urep_const (V : UEnv Λ) (c : ℝ) :
    V.URep (fun _ _ _ => c) (Gen.time (s := .cell) (i := V.E.i) (p := V.E.p) (.const c)) :=
  ⟨.timeConst c, .time _, GenSort.ofTime .cell (TimeLetter.eval V.E.D (.const c)), .time _,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem isURep_const (V : UEnv Λ) (c : ℝ) : V.IsURep (fun _ _ _ => c) := ⟨_, urep_const V c⟩

theorem IsURep.add {φ ψ : Λ → Vec 2 → Vec 2 → ℝ} (ha : V.IsURep φ) (hb : V.IsURep ψ) :
    V.IsURep (fun l X z => φ l X z + ψ l X z) := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  exact ⟨_, ha.add hb⟩

theorem IsURep.mul {φ ψ : Λ → Vec 2 → Vec 2 → ℝ} (ha : V.IsURep φ) (hb : V.IsURep ψ) :
    V.IsURep (fun l X z => φ l X z * ψ l X z) := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  exact ⟨_, ha.mul hb⟩

/-- Finite sums of represented functions are represented. -/
theorem IsURep.sum {ι : Type*} (s : Finset ι) {φ : ι → Λ → Vec 2 → Vec 2 → ℝ}
    (h : ∀ k ∈ s, V.IsURep (φ k)) : V.IsURep (fun l X z => ∑ k ∈ s, φ k l X z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isURep_const V 0
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self a s)).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact h1.congr fun l _ X _ z => by simp [Finset.sum_insert ha]

theorem IsURep.smul {φ : Λ → Vec 2 → Vec 2 → ℝ} (h : V.IsURep φ) (c : ℝ) :
    V.IsURep (fun l X z => c * φ l X z) :=
  (isURep_const V c).mul h

/-! ### Geometric letters and the drift -/

/-- The metric entries of the chain at the physical time `time l`. -/
theorem urep_metric (V : UEnv Λ) (a b : Fin 2) :
    V.URep (fun l X _ => ((V.base l).recenter V.E.D (V.E.ρ • X)).famMetric V.E.D (V.time l) a b)
      (Gen.restrict (Gen.geo (i := V.E.i) (p := V.E.p) .own (.metric a b))) :=
  ⟨.restrict (.geoOwn _), .restrict (.geo _ _), GeoLetter.eval V.E.D V.E.i .own (.metric a b),
    .restrict (.geo _ _), fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- The unnormalized pulse drift at the lift time `lt l`, when `time l = ℓ_i² * lt l`,
`ℓ_i² ≠ 0` and `√(κ_i/κ_{i-1}) ≠ 0`. -/
theorem urep_pulseDrift (V : UEnv Λ) (lt : Λ → ℝ)
    (hc : ∀ l, V.time l = V.E.D.cellScaleSq V.E.i * lt l) (hc0 : V.E.D.cellScaleSq V.E.i ≠ 0)
    (hn : Real.sqrt (V.E.D.kap V.E.i / V.E.D.kap (V.E.i - 1)) ≠ 0) (k : Fin 2) :
    V.IsURep (fun l _ z => ocPulseCellDrift V.E.D.α V.E.D.q V.E.D.Λ V.E.D.ζ V.E.i
      (V.E.D.kap V.E.i) V.E.p (lt l) z k) := by
  have h1 : V.URep (fun l _ z => Real.sqrt (V.E.D.kap V.E.i / V.E.D.kap (V.E.i - 1)) *
      ocPulseCellDrift V.E.D.α V.E.D.q V.E.D.Λ V.E.D.ζ V.E.i (V.E.D.kap V.E.i) V.E.p
        (V.time l / V.E.D.cellScaleSq V.E.i) z k) (Gen.drift (i := V.E.i) (p := V.E.p) k) :=
    ⟨.drift k, .drift k, driftSem V.E.D V.E.i V.E.p k, .drift k, fun _ _ _ _ _ => rfl,
      fun l _ X _ z s => driftSem_phase V.E.D V.E.i V.E.p k (V.time l)
        ((V.base l).recenter V.E.D (V.E.ρ • X)) z s⟩
  have h2 := (urep_const V (Real.sqrt (V.E.D.kap V.E.i / V.E.D.kap (V.E.i - 1)))⁻¹).mul h1
  refine ⟨_, h2.congr fun l _ X _ z => ?_⟩
  have hτ : V.time l / V.E.D.cellScaleSq V.E.i = lt l := by
    rw [hc l]; field_simp
  simp only [hτ]
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-! ### Fast derivatives and invariance -/

/-- Fast derivatives of a function invariant along `b` are invariant along `b`. -/
theorem fastPartial_invariant {φ : Vec 2 → Vec 2 → ℝ} (j : Fin 2) (b : Vec 2) (X : Vec 2)
    (hinv : ∀ z (s : ℝ), φ X (z + s • b) = φ X z) (z : Vec 2) (s : ℝ) :
    fastPartial j φ X (z + s • b) = fastPartial j φ X z := by
  have h : (fun z' => φ X z') = fun z' => φ X (z' + s • b) := funext fun z' => (hinv z' s).symm
  have e1 := congrArg (fun F : Vec 2 → ℝ => fderiv ℝ F z) h
  rw [fderiv_comp_add_right] at e1
  show fderiv ℝ (fun z' => φ X z') (z + s • b) (basisVec j) =
    fderiv ℝ (fun z' => φ X z') z (basisVec j)
  rw [← e1]

theorem URep.dInternal {φ : Λ → Vec 2 → Vec 2 → ℝ} {e : Gen .cell V.E.i V.E.p} (h : V.URep φ e) :
    V.URep (fun l => fastPartial (transverseIndex V.E.p) (φ l)) (Gen.dInternal e) := by
  obtain ⟨hs, hf, f, hd, hv, hi⟩ := h
  refine ⟨.dInternal hs, .dInternal hf, _, .dInternal hd, fun l hl X hX z => ?_,
    fun l hl X hX z s => fastPartial_invariant _ _ X (hi l hl X hX) z s⟩
  have : (fun z' => φ l X z') = f (V.time l) ((V.base l).recenter V.E.D (V.E.ρ • X)) :=
    funext (hv l hl X hX)
  simp only [fastPartial, this]

theorem urep_fastPartial_of_invariant {φ : Λ → Vec 2 → Vec 2 → ℝ} (j : Fin 2)
    (hinv : ∀ l ∈ V.W, ∀ X ∈ V.U l, ∀ z (s : ℝ), φ l X (z + s • basisVec j) = φ l X z) :
    V.URep (fun l => fastPartial j (φ l))
      (Gen.time (s := .cell) (i := V.E.i) (p := V.E.p) (.const 0)) :=
  (urep_const V 0).congr fun l hl X hX z =>
    RepEnv.fastPartial_eq_zero_of_invariant j X (hinv l hl X hX) z

/-- Every represented function is invariant under parallel shifts of the phase. -/
theorem URep.invariant {φ : Λ → Vec 2 → Vec 2 → ℝ} {e : Gen .cell V.E.i V.E.p}
    (h : V.URep φ e) :
    ∀ l ∈ V.W, ∀ X ∈ V.U l, ∀ z (s : ℝ), φ l X (z + s • basisVec (parIdx V.E.p)) = φ l X z :=
  h.2.2.choose_spec.2.2

theorem IsURep.invariant {φ : Λ → Vec 2 → Vec 2 → ℝ} (h : V.IsURep φ) :
    ∀ l ∈ V.W, ∀ X ∈ V.U l, ∀ z (s : ℝ), φ l X (z + s • basisVec (parIdx V.E.p)) = φ l X z := by
  obtain ⟨e, he⟩ := h
  exact he.invariant

theorem fin2_cases (p : ℤ) (j : Fin 2) : j = transverseIndex p ∨ j = parIdx p := by
  have h := parIdx_ne_transverseIndex p
  revert h j
  unfold parIdx transverseIndex
  split_ifs <;> decide

/-- The fast derivative in any direction of a represented function is represented. -/
theorem IsURep.fastPartial {φ : Λ → Vec 2 → Vec 2 → ℝ} (h : V.IsURep φ) (j : Fin 2) :
    V.IsURep (fun l => fastPartial j (φ l)) := by
  rcases fin2_cases V.E.p j with hj | hj
  · subst hj
    obtain ⟨e, he⟩ := h
    exact ⟨_, he.dInternal⟩
  · subst hj
    exact ⟨_, urep_fastPartial_of_invariant _ h.invariant⟩

/-! ### Slow derivatives -/

/-- `slowPartial j φ` is represented by `ρ * dSlowCell j e`. -/
theorem URep.slowPartial (hζ : IsFastProfile V.E.D.ζ) (hρ : V.E.ρ ≠ 0)
    (hU : ∀ l ∈ V.W, IsOpen (V.U l))
    {φ : Λ → Vec 2 → Vec 2 → ℝ} {e : Gen .cell V.E.i V.E.p} (h : V.URep φ e)
    (hd : ∀ l ∈ V.W, ∀ X ∈ V.U l, ∀ z, DifferentiableAt ℝ (fun X' => φ l X' z) X)
    (j : Fin 2) :
    V.URep (fun l => AVRegularity.slowPartial j (φ l))
      (Gen.mul (Gen.time (s := .cell) (i := V.E.i) (p := V.E.p) (.const V.E.ρ))
        (Gen.dSlowCell j e)) := by
  obtain ⟨hs, hf, f, hdn, hv, hi⟩ := h
  refine ⟨.mul (.timeConst _) (.dSlowCell j hs), .mul (.time _) (.dSlowCell j hf),
    GenSort.mul .cell (GenSort.ofTime .cell (TimeLetter.eval V.E.D (.const V.E.ρ))) _,
    .mul (.time _) (.dSlowCell j hdn), fun l hl X hX z => ?_, fun l hl X hX z s => ?_⟩
  · show AVRegularity.slowPartial j (φ l) X z = V.E.ρ * fderiv ℝ (fun h : Vec 2 =>
      f (V.time l) (((V.base l).recenter V.E.D (V.E.ρ • X)).recenter V.E.D h) z) 0 (basisVec j)
    have h := RepEnv.fderiv_recenter_eq (E := V.envAt l) hζ hρ (hU l hl) f (hv l hl)
      (hd l hl) j hX z
    rw [show (fderiv ℝ (fun h : Vec 2 => f (V.time l)
        (((V.base l).recenter V.E.D (V.E.ρ • X)).recenter V.E.D h) z) 0) (basisVec j) =
        V.E.ρ⁻¹ * AVRegularity.slowPartial j (φ l) X z from h,
      ← mul_assoc, mul_inv_cancel₀ hρ, one_mul]
  · show fderiv ℝ (fun X' => φ l X' (z + s • basisVec (parIdx V.E.p))) X (basisVec j) =
      fderiv ℝ (fun X' => φ l X' z) X (basisVec j)
    have hev : (fun X' => φ l X' (z + s • basisVec (parIdx V.E.p))) =ᶠ[nhds X]
        fun X' => φ l X' z := by
      filter_upwards [(hU l hl).mem_nhds hX] with X' hX'
      exact hi l hl X' hX' z s
    rw [hev.fderiv_eq]

/-! ### The mean -/

/-- The cell mean as a (z-independent) cell function. -/
theorem URep.meanCell {φ : Λ → Vec 2 → Vec 2 → ℝ} {e : Gen .cell V.E.i V.E.p} (h : V.URep φ e) :
    V.URep (fun l X _ => fieldCellMean (φ l X)) (Gen.famCell (Gen.mean e)) := by
  obtain ⟨hs, hf, f, hd, hv, hi⟩ := h
  refine ⟨.famCell (.mean hs), .famCell (.mean hf), _, .famCell (.mean hd),
    fun l hl X hX _ => ?_, fun _ _ _ _ _ _ => rfl⟩
  have : φ l X = f (V.time l) ((V.base l).recenter V.E.D (V.E.ρ • X)) := funext (hv l hl X hX)
  simp only [fieldCellMean, this]
  rfl

end UEnv
end

/-! **Time-uniform denotability of coefficient arrays.** `V.URepArr A` for a time-indexed
array `A : Λ → CArr`: every entry `(m, α)` is time-uniformly represented. Closure under the array
operations (sums, constants, `slowArr`, `fastArr`, `mulArr`, `meanArr`, `iterSlow`, `compArr`),
with the smoothness side conditions of the slow derivative. -/

section
namespace UEnv

variable {Λ : Type} {V : UEnv Λ}

/-- Every entry of the time-indexed array is time-uniformly represented. -/
def URepArr (V : UEnv Λ) (A : Λ → CArr) : Prop := ∀ m α, V.IsURep (fun l => A l m α)

theorem URepArr.congr {A B : Λ → CArr} (h : V.URepArr A) (hAB : ∀ l ∈ V.W, B l = A l) :
    V.URepArr B := fun m α =>
  (h m α).congr fun l hl X _ z => by rw [hAB l hl]

theorem urepArr_zero (V : UEnv Λ) : V.URepArr (fun _ => 0) := fun _ _ =>
  (isURep_const V 0).congr fun _ _ _ _ _ => rfl

theorem URepArr.add {A B : Λ → CArr} (hA : V.URepArr A) (hB : V.URepArr B) :
    V.URepArr (fun l => A l + B l) := fun m α =>
  ((hA m α).add (hB m α)).congr fun _ _ _ _ _ => rfl

theorem URepArr.smul {A : Λ → CArr} (hA : V.URepArr A) (c : ℝ) :
    V.URepArr (fun l => c • A l) := fun m α =>
  ((hA m α).smul c).congr fun _ _ _ _ _ => rfl

theorem URepArr.neg {A : Λ → CArr} (hA : V.URepArr A) : V.URepArr (fun l => -A l) := fun m α =>
  ((hA m α).smul (-1)).congr fun _ _ _ _ _ => by simp

theorem URepArr.sub {A B : Λ → CArr} (hA : V.URepArr A) (hB : V.URepArr B) :
    V.URepArr (fun l => A l - B l) := fun m α =>
  ((hA m α).add ((hB m α).smul (-1))).congr fun _ _ _ _ _ => by
    simp only [Pi.sub_apply]; ring

theorem URepArr.sum {ι : Type*} (s : Finset ι) {A : ι → Λ → CArr}
    (h : ∀ k ∈ s, V.URepArr (A k)) : V.URepArr (fun l => ∑ k ∈ s, A k l) := fun m α =>
  (IsURep.sum s fun k hk => h k hk m α).congr fun l _ X _ z => by
    simp [Finset.sum_apply]

theorem URepArr.list_sum {A : ℕ → Λ → CArr} (L : List ℕ) (h : ∀ k ∈ L, V.URepArr (A k)) :
    V.URepArr (fun l => (L.map fun k => A k l).sum) := by
  induction L with
  | nil => simpa using urepArr_zero V
  | cons a L ih =>
    simpa using (h a (List.mem_cons_self)).add (ih fun k hk => h k (List.mem_cons_of_mem _ hk))

theorem isURep_slowExtra (j : Fin 2) {A : Λ → CArr} (hA : V.URepArr A) (m : ℕ)
    (β : DerivativeWord2 m) : V.IsURep (fun l => slowExtra j (A l) m β) := by
  cases m with
  | zero => exact (isURep_const V 0).congr fun _ _ _ _ _ => rfl
  | succ m =>
    by_cases hc : β (Fin.last m) = j
    · exact (hA m (Fin.init β)).congr fun l _ X _ z => by simp [slowExtra, hc]
    · exact (isURep_const V 0).congr fun l _ X _ z => by simp [slowExtra, hc]

/-- Slow arrays: `slowPartial` is `ρ * dSlowCell`, `slowExtra` is a shifted entry or `0`. -/
theorem URepArr.slowArr (hζ : IsFastProfile V.E.D.ζ) (hρ : V.E.ρ ≠ 0) (hU : ∀ l ∈ V.W, IsOpen (V.U l))
    {A : Λ → CArr} (hA : V.URepArr A) (hs : ∀ l ∈ V.W, ArrSlowSmooth 1 (A l)) (j : Fin 2) :
    V.URepArr (fun l => slowArr j (A l)) := by
  intro m β
  obtain ⟨e, he⟩ := hA m β
  have h1 : V.IsURep (fun l => AVRegularity.slowPartial j (A l m β)) :=
    ⟨_, he.slowPartial hζ hρ hU (fun l hl X _ z =>
      (hs l hl m β z).differentiable (by simp) X) j⟩
  exact (h1.add (isURep_slowExtra j hA m β)).congr fun _ _ _ _ _ => rfl

/-- Fast arrays in any direction. -/
theorem URepArr.fastArr {A : Λ → CArr} (hA : V.URepArr A)
    (j : Fin 2) :
    V.URepArr (fun l => fastArr j (A l)) := fun m α =>
  (hA m α).fastPartial j

theorem URepArr.mulArr {g : Λ → Vec 2 → Vec 2 → ℝ} (hg : V.IsURep g) {A : Λ → CArr}
    (hA : V.URepArr A) : V.URepArr (fun l => mulArr (g l) (A l)) := fun m α =>
  (hg.mul (hA m α)).congr fun _ _ _ _ _ => rfl

theorem URepArr.meanArr {A : Λ → CArr} (hA : V.URepArr A) :
    V.URepArr (fun l => meanArr (A l)) := by
  intro m α
  obtain ⟨e, he⟩ := hA m α
  exact ⟨_, he.meanCell⟩

theorem URepArr.iterSlow (hζ : IsFastProfile V.E.D.ζ) (hρ : V.E.ρ ≠ 0) (hU : ∀ l ∈ V.W, IsOpen (V.U l)) :
    ∀ {n : ℕ} (α : DerivativeWord2 n) {B : Λ → CArr}, V.URepArr B →
      (∀ l ∈ V.W, ArrSlowSmooth n (B l)) → V.URepArr (fun l => iterSlow n α (B l))
  | 0, _, _, hB, _ => hB
  | n + 1, α, _, hB, hs =>
    URepArr.iterSlow hζ hρ hU (fun i => α i.succ)
      (hB.slowArr hζ hρ hU (fun l hl => (hs l hl).mono (by omega)) (α 0))
      (fun l hl => arrSlowSmooth_slowArr (r := n) _ (hs l hl))

/-- Composition `compArr J C B z0`: `C` and `B` represented, `B` independent of `z`, and `B` is
`C^J` in the slow variable. -/
theorem URepArr.compArr (hζ : IsFastProfile V.E.D.ζ) (hρ : V.E.ρ ≠ 0) (hU : ∀ l ∈ V.W, IsOpen (V.U l))
    (J : ℕ) {C B : Λ → CArr} (z0 : Vec 2) (hC : V.URepArr C) (hB : V.URepArr B)
    (hz : ∀ l ∈ V.W, RepEnv.ArrZConst (B l)) (hs : ∀ l ∈ V.W, ArrSlowSmooth J (B l)) :
    V.URepArr (fun l => compArr J (C l) (B l) z0) := by
  intro m' β
  have h : V.IsURep (fun l X z => ∑ m ∈ Finset.range (J + 1), ∑ α : DerivativeWord2 m,
      C l m α X z * AVRegularity.Providers.GenSem.iterSlow m α (B l) m' β X z) := by
    refine IsURep.sum _ fun m hm => IsURep.sum _ fun α _ => (hC m α).mul ?_
    exact URepArr.iterSlow hζ hρ hU α hB (fun l hl => (hs l hl).mono
      (by simpa [Nat.lt_succ_iff] using hm)) m' β
  exact h.congr fun l hl X _ z => by
    simp only [GenSem.compArr, (RepEnv.arrZConst_iterSlow _ (hz l hl)) _ _ X z z0]

end UEnv
end

/-! **The recursion arrays of the lift are time-uniformly represented.** From the
representability of the metric, the drift, the source edges and of the lower coefficients
(`CoeffRepBelow`), the arrays `ℬ₁`, `ℬ₂`, `𝒮_j`, `A_n^{(hh)}`, and the cell source `GenSem.srcArr` are
time-uniformly represented (`URepArr`), with the smoothness side conditions of the coefficient
arrays. -/

section
namespace UEnv

variable {V : UEnv (RealChain × ℝ)}

/-- The standing hypotheses of the closure lemmas. -/
structure Ok (V : UEnv (RealChain × ℝ)) : Prop where
  /-- The fast profile. -/
  hζ : IsFastProfile V.E.D.ζ
  /-- The scale is nonzero. -/
  hρ : V.E.ρ ≠ 0
  /-- The offsets form open sets. -/
  hU : ∀ l ∈ V.W, IsOpen (V.U l)

/-! ### The cell operators `ℬ₁`, `ℬ₂` -/

theorem URepArr.cellB1Arr (hV : V.Ok) {η : ℝ} {G : RealChain → ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ}
    {vel : RealChain → ℝ → Vec 2 → Vec 2} (hGr : ∀ i j, V.IsURep (fun l X _ => G l.1 l.2 X i j))
    (hvr : ∀ k, V.IsURep (fun l _ z => vel l.1 l.2 z k)) {B : RealChain × ℝ → CArr}
    (hB : V.URepArr B) (hB2 : ∀ l ∈ V.W, ArrSmooth 2 (B l))
    (hG1 : ∀ l ∈ V.W, ∀ i j,
      ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => G l.1 l.2 p.1 i j)) :
    V.URepArr (fun l => GenSem.cellB1Arr η (G l.1) (vel l.1) l.2 (B l)) := by
  unfold GenSem.cellB1Arr
  have hsl : ∀ j, V.URepArr (fun l => GenSem.slowArr j (B l)) := fun j =>
    hB.slowArr hV.hζ hV.hρ hV.hU (fun l hl => (hB2 l hl).slow.mono (by omega)) j
  refine URepArr.add (URepArr.sum _ fun k _ => URepArr.mulArr ((hvr k).smul (Real.sqrt η)) (hsl k))
    (URepArr.smul (URepArr.sum _ fun i _ => URepArr.sum _ fun j _ =>
      URepArr.add (URepArr.mulArr (hGr i j) ((hsl j).fastArr i)) ?_) _)
  refine (URepArr.mulArr (hGr i j) (hB.fastArr j)).slowArr hV.hζ hV.hρ hV.hU
    (fun l hl => ?_) i
  exact (arrSmooth_mulArr (hG1 l hl i j) (arrSmooth_fastArr (r := 1) j (hB2 l hl))).slow

theorem URepArr.cellB2Arr (hV : V.Ok) {η : ℝ} {G : RealChain → ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ}
    (hGr : ∀ i j, V.IsURep (fun l X _ => G l.1 l.2 X i j)) {B : RealChain × ℝ → CArr}
    (hB : V.URepArr B) (hB2 : ∀ l ∈ V.W, ArrSmooth 2 (B l))
    (hG1 : ∀ l ∈ V.W, ∀ i j,
      ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => G l.1 l.2 p.1 i j)) :
    V.URepArr (fun l => GenSem.cellB2Arr η (G l.1) l.2 (B l)) := by
  unfold GenSem.cellB2Arr
  have hsl : ∀ j, V.URepArr (fun l => GenSem.slowArr j (B l)) := fun j =>
    hB.slowArr hV.hζ hV.hρ hV.hU (fun l hl => (hB2 l hl).slow.mono (by omega)) j
  refine URepArr.smul (URepArr.sum _ fun i _ => URepArr.sum _ fun j _ => ?_) _
  refine (URepArr.mulArr (hGr i j) (hsl j)).slowArr hV.hζ hV.hρ hV.hU (fun l hl => ?_) i
  exact (arrSmooth_mulArr (hG1 l hl i j) (arrSmooth_slowArr (r := 1) j (hB2 l hl))).slow

/-! ### Graded arrays -/

/-- A graded array indexed by `l` all of whose grades are uniformly represented. -/
def URepG (V : UEnv (RealChain × ℝ)) (P : RealChain × ℝ → ℕ → CArr) : Prop :=
  ∀ p, V.URepArr (fun l => P l p)

theorem URepG.zero (V : UEnv (RealChain × ℝ)) : V.URepG (fun _ => 0) := fun _ => urepArr_zero V

theorem URepG.add {P Q : RealChain × ℝ → ℕ → CArr} (hP : V.URepG P) (hQ : V.URepG Q) :
    V.URepG (fun l => P l + Q l) := fun p => (hP p).add (hQ p)

theorem URepG.smul {P : RealChain × ℝ → ℕ → CArr} (hP : V.URepG P) (c : ℝ) :
    V.URepG (fun l => c • P l) := fun p => (hP p).smul c

theorem URepG.sum {β : Type*} (s : Finset β) {P : β → RealChain × ℝ → ℕ → CArr}
    (h : ∀ k ∈ s, V.URepG (P k)) : V.URepG (fun l => ∑ k ∈ s, P k l) := fun p =>
  (URepArr.sum s fun k hk => h k hk p).congr fun l _ => by simp [Finset.sum_apply]

theorem URepG.mulG {g : RealChain × ℝ → Vec 2 → Vec 2 → ℝ} (hg : V.IsURep g)
    {P : RealChain × ℝ → ℕ → CArr}
    (hP : V.URepG P) : V.URepG (fun l => mulG (g l) (P l)) := fun p =>
  URepArr.mulArr hg (hP p)

theorem URepG.constG {A : RealChain × ℝ → CArr} (hA : V.URepArr A) :
    V.URepG (fun l => GenSem.constG (A l)) := by
  intro p
  by_cases hp : p = 0
  · subst hp; exact hA.congr fun l _ => by simp [GenSem.constG]
  · exact (urepArr_zero V).congr fun l _ => by simp [GenSem.constG, hp]

theorem URepG.dG (hV : V.Ok) {P : RealChain × ℝ → ℕ → CArr} (hP : V.URepG P)
    (hs : ∀ l ∈ V.W, GSmooth 1 (P l)) (s : ℝ) (i : Fin 2) :
    V.URepG (fun l => GenSem.dG s i (P l)) := by
  intro p
  cases p with
  | zero => exact (hP 0).fastArr i
  | succ p =>
    exact (((hP (p + 1)).fastArr i).add
      (((hP p).slowArr hV.hζ hV.hρ hV.hU (fun l hl => (hs l hl p).slow) i).smul s))

theorem URepG.dWordG (hV : V.Ok) (s : ℝ) :
    ∀ {m : ℕ} (α : DerivativeWord2 m) {P : RealChain × ℝ → ℕ → CArr}, V.URepG P →
      (∀ l ∈ V.W, GSmooth m (P l)) → V.URepG (fun l => GenSem.dWordG s m α (P l))
  | 0, _, _, hP, _ => hP
  | m + 1, α, _, hP, hs =>
    URepG.dWordG hV s (fun i => α i.succ)
      (URepG.dG hV hP (fun l hl p => (hs l hl p).mono (by omega)) s (α 0))
      (fun l hl => gSmooth_dG (r := m) s (α 0) (hs l hl))

/-! ### The source operator -/

variable {ι : Type} [Fintype ι] {Dm : ℕ}

theorem wordG_add (s : ℝ) (g h : Vec 2 → Vec 2 → ℝ) (m : ℕ) (α : DerivativeWord2 m) (A : CArr) :
    GenSem.wordG s (fun X z => g X z + h X z) m α A =
      GenSem.wordG s g m α A + GenSem.wordG s h m α A := by
  funext p m' β X z
  simp [GenSem.wordG, GenSem.mulG, GenSem.mulArr, add_mul]

theorem wordG_zero (s : ℝ) (m : ℕ) (α : DerivativeWord2 m) (A : CArr) :
    GenSem.wordG s (fun _ _ => 0) m α A = 0 := by
  funext p m' β X z
  simp [GenSem.wordG, GenSem.mulG, GenSem.mulArr]

/-- The flux array through the aggregate of the edge coefficients: the source flux only sees
`∑_γ (γ.map 1) * γ.coeff α t X z k`. -/
theorem fluxG_eq_agg (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (s t : ℝ) (k : Fin 2)
    (A : ι → CArr) (v : ι) :
    GenSem.fluxG edge s t k A v = ∑ u : ι, ∑ d : Finset.Icc 2 Dm,
      ∑ α : DerivativeWord2 (d.1 - 1), GenSem.wordG s (fun X z =>
        ((edge v u d).map fun γ => γ.map 1 * γ.coeff α t X z k).sum) (d.1 - 1) α (A u) := by
  unfold GenSem.fluxG
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun d _ => ?_
  generalize edge v u d = L
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact (Finset.sum_eq_zero fun α _ => wordG_zero _ _ _ _).symm
  | cons γ L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← wordG_add]
    congr 1
    funext X z
    rw [mul_comm]

theorem URepG.fluxG (hV : V.Ok) (edge : RealChain → ConstituentEdges Dm (fun _ : ι => ℝ))
    (s : ℝ) (k : Fin 2) {A : ι → RealChain × ℝ → CArr} (hA : ∀ u, V.URepArr (A u))
    (hAs : ∀ l ∈ V.W, ∀ u, ArrSmooth Dm (A u l))
    (hE : ∀ (v u : ι) (d : Finset.Icc 2 Dm) α k', V.IsURep (fun l X z =>
      ((edge l.1 v u d).map fun γ => γ.map 1 * γ.coeff α l.2 X z k').sum)) (v : ι) :
    V.URepG (fun l => GenSem.fluxG (edge l.1) s l.2 k (fun u => A u l) v) := by
  have h : V.URepG (fun l => ∑ u : ι, ∑ d : Finset.Icc 2 Dm,
      ∑ α : DerivativeWord2 (d.1 - 1), GenSem.wordG s (fun X z =>
        ((edge l.1 v u d).map fun γ => γ.map 1 * γ.coeff α l.2 X z k).sum) (d.1 - 1) α (A u l)) := by
    refine URepG.sum _ fun u _ => URepG.sum _ fun d _ => URepG.sum _ fun α _ => ?_
    have hd := Finset.mem_Icc.mp d.2
    refine URepG.mulG (hE v u d α k) ?_
    exact URepG.dWordG hV s α (URepG.constG (hA u)) fun l hl =>
      gSmooth_constG ((hAs l hl u).mono (by omega))
  intro p
  exact (h p).congr fun l _ => by dsimp only; rw [fluxG_eq_agg]

theorem URepG.sourceG (hV : V.Ok) (edge : RealChain → ConstituentEdges Dm (fun _ : ι => ℝ))
    (s : ℝ) {A : ι → RealChain × ℝ → CArr} (hA : ∀ u, V.URepArr (A u))
    (hAs : ∀ l ∈ V.W, ∀ u, ArrSmooth (1 + Dm) (A u l))
    (hE : ∀ (v u : ι) (d : Finset.Icc 2 Dm) α k', V.IsURep (fun l X z =>
      ((edge l.1 v u d).map fun γ => γ.map 1 * γ.coeff α l.2 X z k').sum))
    (hEs : ∀ l ∈ V.W, ∀ (v u : ι) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ),
      γ ∈ edge l.1 v u d → ∀ α k',
        ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => γ.coeff α l.2 p.1 p.2 k'))
    (v : ι) : V.URepG (fun l => GenSem.sourceG (edge l.1) s l.2 (fun u => A u l) v) := by
  unfold GenSem.sourceG
  refine URepG.sum _ fun k _ => URepG.dG hV
    (URepG.fluxG hV edge s k hA (fun l hl u => (hAs l hl u).mono (by omega)) hE v)
    (fun l hl => fluxG_gSmooth (edge l.1) s l.2 k (r := 1) (hAs l hl)
      (fun v u d γ hγ α => hEs l hl v u d γ hγ α k) v) s k

end UEnv
end

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity
namespace AVRegularity.Providers.GenSem

/-! **The pulse drift is continuous and has no transverse component.** -/

/-- The drift of an odd pulse has no component in the transverse direction. -/
theorem ocPulseCellDrift_transverse {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (m : ℕ) (ν : ℝ) {k : ℤ}
    (hk : Odd k) (t : ℝ) (z : Vec 2) :
    ocPulseCellDrift α q Λ ζ m ν k t z (transverseIndex k) = 0 := by
  have hk' : k % 4 = 1 ∨ k % 4 = 3 := by
    obtain ⟨j, rfl⟩ := hk
    omega
  unfold ocPulseCellDrift
  rcases hk' with h1 | h3
  · have e : transverseIndex k = 0 := by
      have : ¬ k % 4 = 3 := by omega
      simp [transverseIndex, this]
    rw [e]
    simp [CycleReference.ocShearVel_horizontal h1]
  · have e : transverseIndex k = 1 := by simp [transverseIndex, h3]
    rw [e]
    simp [CycleReference.ocShearVel_vertical h3]

end AVRegularity.Providers.GenSem
end
end
end
