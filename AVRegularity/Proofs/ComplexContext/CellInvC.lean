-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexContext.Inv
import AVRegularity.Proofs.Results.Construction.SuccessorFluxUnique
import AVRegularity.Proofs.ComplexContext.Restrict
public import AVRegularity.Proofs.ComplexCell.Mode
public import AVRegularity.Proofs.ComplexChain.Family
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Proofs.ComplexChain.Vel
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.PicardGroup

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the drift letter** (`drift`). The normalized cell drift of the pulse `p` of level
`i` is a time-only amplitude times `cos(2π η_q)` (the shear `𝐮_{i,p}(ε_i η)`, from its entire
extension `ocShearVelC`): `driftSem_eq`. Its modes are `a_c(t)/2` at `h = ±1` and zero otherwise,
constant in the chain parameters (`driftW`). The amplitude is at most `2π ε_i^{1+α}/√(κ_iκ_{i-1})`,
bounded uniformly by the band chain (`drift_scale_bound`), so the modes are at most
`π C_d` (`CellInv.drift`). -/

open AVRegularity.Providers.ComplexFlow

/-- The scaled complex shear is the shear at `0` times `cos(2π η_q)`. -/
theorem ocShearVelC_scaled {α q : ℝ} {Λ m : ℕ} {k : ℤ} (hε : ocEpsilon q Λ m ≠ 0) (η : Vec 2)
    (c : Fin 2) :
    ocShearVelC α q Λ m k (((ocEpsilon q Λ m : ℝ) : ℂ) • ofRealVec η) c =
      ocShearVelC α q Λ m k 0 c * Complex.cos (2 * Real.pi * (η (transverseIndex k) : ℂ)) := by
  have hf : ∀ a : Fin 2, (shearFreq q Λ m : ℂ) * (((ocEpsilon q Λ m : ℝ) : ℂ) * ofRealVec η a) =
      2 * Real.pi * (η a : ℂ) := by
    intro a
    have hεC : ((ocEpsilon q Λ m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hε
    simp only [ofRealVec, shearFreq]
    push_cast
    field_simp
  unfold ocShearVelC
  split_ifs with h1 h3
  · have hq : transverseIndex k = 0 := by simp [transverseIndex, show ¬ k % 4 = 3 by omega]
    rw [hq]
    fin_cases c <;> simp [hf]
  · have hq : transverseIndex k = 1 := by simp [transverseIndex, h3]
    rw [hq]
    fin_cases c <;> simp [hf]
  · simp

/-- The scaled real shear is the shear at `0` times `cos(2π η_q)`. -/
theorem ocShearVel_scaled {α q : ℝ} {Λ m : ℕ} {k : ℤ} (hε : ocEpsilon q Λ m ≠ 0) (η : Vec 2)
    (c : Fin 2) :
    ocShearVel α q Λ m k (ocEpsilon q Λ m • η) c =
      ocShearVel α q Λ m k 0 c * Real.cos (2 * Real.pi * η (transverseIndex k)) := by
  have h1 := ocShearVelC_scaled (α := α) (k := k) hε η c
  have e1 : ((ocEpsilon q Λ m : ℝ) : ℂ) • ofRealVec η = ofRealVec (ocEpsilon q Λ m • η) := by
    funext a; simp [ofRealVec]
  have e0 : (0 : CVec) = ofRealVec 0 := by funext a; simp [ofRealVec]
  rw [e1, ocShearVelC_ofRealVec, e0, ocShearVelC_ofRealVec] at h1
  have := congrArg Complex.re h1
  simp only [ofRealVec, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at this
  rw [this]
  congr 1
  rw [← Complex.cos_ofReal_re]
  congr 2
  push_cast
  ring

/-- The time-only amplitude of the drift component `c`. -/
def driftAmp (D : OCData) (i : ℕ) (p : ℤ) (c : Fin 2) (t : ℝ) : ℝ :=
  Real.sqrt (D.kap i / D.kap (i - 1)) * (ocEll D.q D.Λ i (D.kap i) ^ 2 / D.eps i *
    (ocPulse D.α D.q D.Λ D.ζ i p t * ocShearVel D.α D.q D.Λ i p 0 c))

/-- **The drift is its amplitude times `cos(2π η_q)`.** -/
theorem driftSem_eq {D : OCData} (hΛ : 1 ≤ D.Λ) (hκ : ∀ m, 0 < D.kap m) (i : ℕ) (p : ℤ)
    (c : Fin 2) (t : ℝ) (ch : RealChain) (η : Vec 2) :
    driftSem D i p c t ch η = driftAmp D i p c t * Real.cos (2 * Real.pi * η (transverseIndex p)) := by
  have hε : 0 < D.eps i := Construction.Stream.ocEpsilon_pos hΛ
  have hell : ocEll D.q D.Λ i (D.kap i) ^ 2 = D.cellScaleSq i := by
    unfold ocEll OCData.cellScaleSq
    rw [div_pow, Real.sq_sqrt (hκ i).le]; rfl
  have hcs : D.cellScaleSq i ≠ 0 := by
    unfold OCData.cellScaleSq; exact div_ne_zero (pow_ne_zero 2 hε.ne') (hκ i).ne'
  unfold driftSem ocPulseCellDrift driftAmp
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hell, mul_div_cancel₀ t hcs]
  rw [ocShearVel_scaled (show ocEpsilon D.q D.Λ i ≠ 0 from hε.ne') η c,
    show D.eps i = ocEpsilon D.q D.Λ i from rfl]
  ring

/-- The modes of the drift. -/
def driftW (D : OCData) (i : ℕ) (p : ℤ) (c : Fin 2) (h : ℤ) : Ext :=
  fun _ _ t _ => if h = 1 ∨ h = -1 then ((driftAmp D i p c t / 2 : ℝ) : ℂ) else 0

/-- The amplitude is bounded by the scale bound of the drift. -/
theorem abs_driftAmp_le {D : OCData} (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hκ : ∀ m, 0 < D.kap m)
    {i : ℕ} {p : ℤ} (hp : Odd p) {Cd : ℝ}
    (hCd : D.eps i ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap i * D.kap (i - 1))) (c : Fin 2) (t : ℝ) :
    |driftAmp D i p c t| ≤ 2 * Real.pi * Cd := by
  have hε : 0 < D.eps i := Construction.Stream.ocEpsilon_pos hΛ
  have hki := hκ i
  have hki1 := hκ (i - 1)
  have hp1 := CycleReference.ocPulse_range (α := D.α) (q := D.q) (Λ := D.Λ) (m := i) hζ p t
  have hu := ocShearVel_bound D.α D.q D.Λ i hp 0 c
  have hell : ocEll D.q D.Λ i (D.kap i) ^ 2 = D.eps i ^ 2 / D.kap i := by
    unfold ocEll; rw [div_pow, Real.sq_sqrt hki.le]; rfl
  have hA : |2 * Real.pi * ocEpsilon D.q D.Λ i ^ (1 + D.α) * (ocEpsilon D.q D.Λ i)⁻¹| =
      2 * Real.pi * D.eps i ^ (1 + D.α) / D.eps i := by
    rw [abs_of_nonneg (by have := Real.pi_pos; positivity)]; rfl
  have hsq : Real.sqrt (D.kap i / D.kap (i - 1)) * (1 / D.kap i) =
      1 / Real.sqrt (D.kap i * D.kap (i - 1)) := by
    rw [Real.sqrt_div hki.le, Real.sqrt_mul hki.le]
    have h1 : 0 < Real.sqrt (D.kap i) := Real.sqrt_pos.mpr hki
    have h2 : 0 < Real.sqrt (D.kap (i - 1)) := Real.sqrt_pos.mpr hki1
    field_simp
    rw [Real.sq_sqrt hki.le]
  have hS : 0 < Real.sqrt (D.kap i * D.kap (i - 1)) := Real.sqrt_pos.mpr (mul_pos hki hki1)
  unfold driftAmp
  rw [hell, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (by positivity : 0 ≤ D.eps i ^ 2 / D.kap i / D.eps i),
    abs_of_nonneg hp1.1]
  calc Real.sqrt (D.kap i / D.kap (i - 1)) * (D.eps i ^ 2 / D.kap i / D.eps i *
        (ocPulse D.α D.q D.Λ D.ζ i p t * |ocShearVel D.α D.q D.Λ i p 0 c|))
      ≤ Real.sqrt (D.kap i / D.kap (i - 1)) * (D.eps i ^ 2 / D.kap i / D.eps i *
        (1 * (2 * Real.pi * D.eps i ^ (1 + D.α) / D.eps i))) := by
        gcongr
        · exact hp1.2
        · rw [← hA]; exact hu
    _ = 2 * Real.pi * D.eps i ^ (1 + D.α) *
          (Real.sqrt (D.kap i / D.kap (i - 1)) * (1 / D.kap i)) := by
        field_simp
    _ = 2 * Real.pi * (D.eps i ^ (1 + D.α) / Real.sqrt (D.kap i * D.kap (i - 1))) := by
        rw [hsq]; ring
    _ ≤ 2 * Real.pi * Cd := by
        gcongr
        rw [div_le_iff₀ hS]; exact hCd

section Drift

variable {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}

/-- **The drift letter.** -/
theorem CellInv.drift (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hκ : ∀ m, 0 < D.kap m)
    (hp : Odd p) {Cd : ℝ} (hCd : D.eps i ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap i * D.kap (i - 1)))
    (c : Fin 2) :
    CellInv D b j₀ i p (driftSem D i p c) (driftW D i p c)
      (fun _ h _ => if h = 1 ∨ h = -1 then ENNReal.ofReal (Real.pi * Cd) else 0) where
  hol h dd n t ht := differentiableOn_const _
  meas h dd n x hx := by
    have hc : Continuous (driftAmp D i p c) := by
      unfold driftAmp
      exact continuous_const.mul (continuous_const.mul
        ((ComplexFlow.continuous_ocPulse D hζ i p).mul continuous_const))
    unfold driftW
    split_ifs
    · exact (Complex.continuous_ofReal.comp ((hc.div_const 2).comp
        continuous_subtype_val)).measurable
    · exact measurable_const
  indep h dd n t x z := rfl
  agree ch t ht hch η := by
    rw [driftSem_eq hΛ hκ i p c t ch η]
    have hsupp : ∀ h ∉ ({1, -1} : Finset ℤ), driftW D i p c h ch.data ch.children.length t
        (ch.paramsC 0) * emode h (η (transverseIndex p)) = 0 := by
      intro h hh
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
      simp [driftW, hh.1, hh.2]
    have hval : (((driftAmp D i p c t * Real.cos (2 * Real.pi * η (transverseIndex p)) : ℝ)) : ℂ) =
        ∑ h ∈ ({1, -1} : Finset ℤ), driftW D i p c h ch.data ch.children.length t
          (ch.paramsC 0) * emode h (η (transverseIndex p)) := by
      rw [Finset.sum_pair (by norm_num)]
      simp only [driftW, emode, true_or, or_true, ↓reduceIte]
      push_cast
      rw [Complex.cos]
      have e1 : (2 * (Real.pi : ℂ) * (η (transverseIndex p) : ℂ)) * Complex.I =
          2 * Real.pi * Complex.I * 1 * (η (transverseIndex p) : ℂ) := by ring
      have e2 : -(2 * (Real.pi : ℂ) * (η (transverseIndex p) : ℂ)) * Complex.I =
          2 * Real.pi * Complex.I * -1 * (η (transverseIndex p) : ℂ) := by ring
      rw [e1, e2]
      ring
    rw [hval]
    exact hasSum_sum_of_ne_finset_zero hsupp
  child h dd n t ht x hx k v hv := rfl
  decay dd n x hx := by
    obtain ⟨Cd', hCd'⟩ : ∃ C : ℝ, ∀ t, |driftAmp D i p c t| ≤ C :=
      ⟨_, abs_driftAmp_le hΛ hζ hκ hp hCd c⟩
    refine ⟨univ, univ_mem, max Cd' 0 * Real.exp (2 * Real.pi), 1, one_pos,
      fun h t _ y _ => ?_⟩
    unfold driftW
    split_ifs with hh
    · have h1 : |(h : ℝ)| = 1 := by
        rcases hh with h' | h' <;> subst h' <;> simp
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
      rw [mul_assoc, ← Real.exp_add]
      simp only [mul_one, add_neg_cancel, Real.exp_zero, mul_one]
      have := hCd' t
      have : |driftAmp D i p c t| ≤ max Cd' 0 := this.trans (le_max_left _ _)
      linarith [abs_nonneg (driftAmp D i p c t)]
    · rw [norm_zero]; positivity
  mode mres hm0 hm2 h t ht dd n hdd x hx := by
    unfold driftW
    split_ifs with hh
    · rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_div, abs_two]
      have := abs_driftAmp_le hΛ hζ hκ hp hCd c t
      linarith
    · simp

end Drift

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Set Filter Topology Metric Homogenization ComplexConjugate
open scoped ENNReal Interval
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the transverse cell inverse** (`cellInv`). The scheduled inverse is solved
from the start `t₀ = inf J_𝗉` with zero initial state. Its modes are the complex Duhamel amplitudes
`W_h(t) = (2πih/ℓ²) ∫_{t₀}^t exp(-(4π²h²/ℓ²) ∫_s^t 𝒢_qq) F̂_{q,h}(s) ds` of the flux modes, with the
complex extension of the metric entry `𝒢_qq` of the family (`MetricExt`: holomorphic, measurable in
time, `Re 𝒢_qq ≥ 9/10`). They are holomorphic in the parameters (parametric integrals of measurable
families, `differentiableOn_intervalIntegral_of_meas`), continuous in time (`continuousOn_modeWC`),
conjugate symmetric at real parameters (so the real part in `transverseInverseSem` drops), and
bounded by `(4/3)(2π|h|)⁻¹` times the supremum of the flux modes over the history:
`CellInv.cellInv`. -/

open AVRegularity.Providers.ComplexFlow AVRegularity.Providers.Transverse
  AVRegularity.Providers.ComplexCell

variable {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}

/-- **The complex extension of the metric entry `𝒢_qq`** over the slot `p` of level `i`. -/
structure MetricExt (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (G : Ext) : Prop where
  hol : ∀ dd n, ∀ u ∈ ocPulseWindow D.α D.q D.Λ i p,
    DifferentiableOn ℂ (G dd n u) (carrierC D b dd n 2)
  meas : ∀ dd n, ∀ x ∈ carrierC D b dd n 2,
    Measurable fun u : ocPulseWindow D.α D.q D.Λ i p => G dd n u x
  indep : ∀ dd n u, FinalIndep (G dd n u)
  child : ∀ dd n, ∀ u ∈ ocPulseWindow D.α D.q D.Λ i p,
    ChildSymm dd (G dd n u) (carrierC D b dd n 2)
  re : ∀ dd n, ∀ u ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ x ∈ carrierC D b dd n 2,
    9 / 10 ≤ (G dd n u x).re
  bd : ∀ dd n, ∀ u ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ x ∈ carrierC D b dd n 2,
    ‖G dd n u x‖ ≤ 2
  agree : ∀ (ch : RealChain), ∀ u ∈ ocPulseWindow D.α D.q D.Λ i p,
    IsAdmissibleChain D b j₀ i p ch → G ch.data ch.children.length u (ch.paramsC 0) =
      ((ch.famMetric D u (transverseIndex p) (transverseIndex p) : ℝ) : ℂ)

/-- The output window starts at the recorded start of the slot. -/
theorem slotStart_le {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) : D.slotStart i p ≤ t :=
  ht.1

theorem history_subset {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    Icc (D.slotStart i p) t ⊆ ocPulseWindow D.α D.q D.Λ i p :=
  fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩

theorem measurableSet_window : MeasurableSet (ocPulseWindow D.α D.q D.Λ i p) := measurableSet_Icc

/-- The modes of the transverse inverse. -/
def invW (D : OCData) (i : ℕ) (p : ℤ) (G : Ext) (Wf : ℤ → Ext) (h : ℤ) : Ext :=
  fun dd n t x => modeWC (D.cellScaleSq i) (fun u => G dd n u x) (fun s => Wf h dd n s x)
    (D.slotStart i p) h t

section Inverse

variable {fF : Fin 2 → GenSort.Sem .cell} {Wf : ℤ → Ext} {Bf : ℝ → ℤ → ℝ → ℝ≥0∞} {G : Ext}

/-- Integrability of the metric entry along the history. -/
theorem MetricExt.intervalIntegrable (hG : MetricExt D b j₀ i p G) {dd : ChainData} {n : ℕ}
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n 2) {s t : ℝ}
    (hs : s ∈ ocPulseWindow D.α D.q D.Λ i p) (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    IntervalIntegrable (fun u => G dd n u x) volume s t := by
  have hsub : Ι s t ⊆ ocPulseWindow D.α D.q D.Λ i p :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound (by simp [Real.volume_Ioc, uIoc])
    (aestronglyMeasurable_of_window measurableSet_window hsub (hG.meas dd n x hx)) 2 ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  exact hG.bd dd n u (hsub hu) x hx

/-- The flux modes are integrable along the history. -/
theorem CellInv.intervalIntegrable_mode {f : GenSort.Sem .cell} {W : ℤ → Ext}
    {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hW : CellInv D b j₀ i p f W B) {dd : ChainData} {n : ℕ}
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n 2) (h : ℤ) {s t : ℝ}
    (hs : s ∈ ocPulseWindow D.α D.q D.Λ i p) (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    IntervalIntegrable (fun s => W h dd n s x) volume s t := by
  obtain ⟨U, hU, M, w, hw, hM⟩ := hW.decay dd n x hx
  have hsub : Ι s t ⊆ ocPulseWindow D.α D.q D.Λ i p :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound (by simp [Real.volume_Ioc, uIoc])
    (aestronglyMeasurable_of_window measurableSet_window hsub (hW.meas h dd n x hx)) M ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  refine (hM h u (hsub hu) x (mem_of_mem_nhds hU)).trans ?_
  have hM0 := decay_const_nonneg (hM 0 u (hsub hu) x (mem_of_mem_nhds hU))
  exact mul_le_of_le_one_right hM0 (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))

/-- The kernel is continuous along the history. -/
theorem MetricExt.continuousOn_kernel (hG : MetricExt D b j₀ i p G) {dd : ChainData} {n : ℕ}
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n 2) (c : ℝ) (h : ℤ) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    ContinuousOn (fun s => modeKC c (fun u => G dd n u x) h t s) (uIcc (D.slotStart i p) t) := by
  have ht₀ : D.slotStart i p ∈ ocPulseWindow D.α D.q D.Λ i p :=
    history_subset ht ⟨le_rfl, slotStart_le ht⟩
  have hI := (intervalIntegrable_iff' (f := fun u => G dd n u x) (μ := volume)).1
    (hG.intervalIntegrable hx ht₀ ht)
  unfold modeKC
  exact (continuousOn_const.mul (intervalIntegral.continuousOn_primitive_interval_left hI)).cexp

/-- The modes of the inverse vanish at `h = 0`. -/
theorem invW_zero (G : Ext) (Wf : ℤ → Ext) (dd : ChainData) (n : ℕ) (t : ℝ) (x : ChainParamsC n) :
    invW D i p G Wf 0 dd n t x = 0 := by
  simp [invW, modeWC, modeCoup]

/-- **The modes of the inverse are holomorphic.** -/
theorem invW_hol (hc : 0 < D.cellScaleSq i) (hW : CellInv D b j₀ i p (fF (transverseIndex p)) Wf Bf)
    (hG : MetricExt D b j₀ i p G) (h : ℤ) (dd : ChainData) (n : ℕ) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    DifferentiableOn ℂ (invW D i p G Wf h dd n t) (carrierC D b dd n 2) := by
  have hU := isOpen_carrierC D b dd n 2
  have ht₀ : D.slotStart i p ∈ ocPulseWindow D.α D.q D.Λ i p :=
    history_subset ht ⟨le_rfl, slotStart_le ht⟩
  have hsJ : ∀ s ∈ uIcc (D.slotStart i p) t, s ∈ ocPulseWindow D.α D.q D.Λ i p := fun s hs =>
    history_subset ht (by rwa [uIcc_of_le (slotStart_le ht)] at hs)
  have hK : ∀ s ∈ uIcc (D.slotStart i p) t, DifferentiableOn ℂ
      (fun x => modeKC (D.cellScaleSq i) (fun u => G dd n u x) h t s) (carrierC D b dd n 2) := by
    intro s hs
    have hs' := hsJ s hs
    have hint : DifferentiableOn ℂ (fun x => ∫ u in s..t, G dd n u x) (carrierC D b dd n 2) :=
      differentiableOn_intervalIntegral_of_meas hU
        (fun u hu => hG.hol dd n u (uIcc_subset_Icc hs' ht hu))
        (fun x hx => aestronglyMeasurable_of_window measurableSet_window
          (uIoc_subset_uIcc.trans (uIcc_subset_Icc hs' ht)) (hG.meas dd n x hx))
        (fun x hx => ⟨_, hU.mem_nhds hx, 2, fun u hu y hy =>
          hG.bd dd n u (uIcc_subset_Icc hs' ht hu) y hy⟩)
    exact (hint.const_mul _).cexp
  unfold invW
  refine (differentiableOn_intervalIntegral_of_meas hU
    (fun s hs => (hK s hs).mul (hW.hol h dd n s (hsJ s hs))) (fun x hx => ?_)
    (fun x hx => ?_)).const_mul _
  · refine AEStronglyMeasurable.mul ?_ (aestronglyMeasurable_of_window measurableSet_window
      (uIoc_subset_uIcc.trans (uIcc_subset_Icc ht₀ ht)) (hW.meas h dd n x hx))
    exact ((hG.continuousOn_kernel hx _ h ht).mono uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · obtain ⟨U, hUn, M, w, hw, hM⟩ := hW.decay dd n x hx
    refine ⟨U ∩ carrierC D b dd n 2, inter_mem hUn (hU.mem_nhds hx), M, fun s hs y hy => ?_⟩
    have hs' := hsJ s hs
    have hst : s ≤ t := by rw [uIcc_of_le (slotStart_le ht)] at hs; exact hs.2
    have hM0 := decay_const_nonneg (hM 0 s hs' y hy.1)
    simp only [Pi.mul_apply]
    rw [norm_mul]
    calc ‖modeKC (D.cellScaleSq i) (fun u => G dd n u y) h t s‖ * ‖Wf h dd n s y‖ ≤ 1 * M := by
          refine mul_le_mul (norm_modeKC_le_one hc (by norm_num : (0 : ℝ) ≤ 9 / 10) h hst
            (hG.intervalIntegrable hy.2 hs' ht) fun u hu => hG.re dd n u
              (uIcc_subset_Icc hs' ht (by rwa [uIcc_of_le hst])) y hy.2)
            ((hM h s hs' y hy.1).trans (mul_le_of_le_one_right hM0
              (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))))
            (norm_nonneg _) zero_le_one
      _ = M := one_mul M

/-- **The modes of the inverse decay** locally uniformly and uniformly in time. -/
theorem invW_decay (hc : 0 < D.cellScaleSq i)
    (hW : CellInv D b j₀ i p (fF (transverseIndex p)) Wf Bf) (hG : MetricExt D b j₀ i p G)
    (dd : ChainData) (n : ℕ) {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n 2) :
    ∃ U ∈ 𝓝 x, ∃ M w : ℝ, 0 < w ∧ ∀ (h : ℤ), ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ y ∈ U,
      ‖invW D i p G Wf h dd n t y‖ ≤ M * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|)) := by
  obtain ⟨U, hUn, M, w, hw, hM⟩ := hW.decay dd n x hx
  refine ⟨U ∩ carrierC D b dd n 2, inter_mem hUn ((isOpen_carrierC D b dd n 2).mem_nhds hx), M,
    w, hw, fun h t ht y hy => ?_⟩
  have hM0 := decay_const_nonneg (hM 0 t ht y hy.1)
  by_cases h0 : h = 0
  · subst h0; rw [invW_zero, norm_zero]; positivity
  have ht₀ : D.slotStart i p ∈ ocPulseWindow D.α D.q D.Λ i p :=
    history_subset ht ⟨le_rfl, slotStart_le ht⟩
  have hb := norm_modeWC_le' hc (by norm_num : (0 : ℝ) < 9 / 10) h0 (slotStart_le ht)
    (hG.intervalIntegrable hy.2 ht₀ ht) (fun u hu => hG.re dd n u (history_subset ht hu) y hy.2)
    (M := M * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|)))
    (F := fun s => Wf h dd n s y) (fun s hs => hM h s (history_subset ht hs) y hy.1)
  refine hb.trans ?_
  have hh : (1 : ℝ) ≤ |(h : ℝ)| := by exact_mod_cast Int.one_le_abs h0
  have hden : 1 ≤ 2 * Real.pi * |(h : ℝ)| * (9 / 10) := by
    have := Real.pi_gt_three; nlinarith
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ M * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|)) := by positivity
  nlinarith

/-- **The transverse cell inverse** of a scheduled flux. -/
theorem CellInv.cellInv (hΛ : 1 ≤ D.Λ) (hb : 0 < b) (hc : 0 < D.cellScaleSq i)
    (hW : CellInv D b j₀ i p (fF (transverseIndex p)) Wf Bf) (hG : MetricExt D b j₀ i p G) :
    CellInv D b j₀ i p
      (transverseInverseSem D i p fF (D.slotStart i p)
        (GenSort.ofTime .cell (TimeLetter.eval D (.const 0))))
      (invW D i p G Wf)
      (fun mres h t => ENNReal.ofReal (4 / 3) * modeGain h *
        ⨆ s ∈ Icc (D.slotStart i p) t, Bf mres h s) where
  hol h dd n t ht := invW_hol hc hW hG h dd n ht
  meas h dd n x hx := by
    have hτ : 0 < ocTau D.α D.q D.Λ i := Construction.Stream.ocTau_pos hΛ
    have ht01 : D.slotStart i p ≤ ((p : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i := by
      unfold OCData.slotStart; nlinarith
    have hJ0 : D.slotStart i p ∈ ocPulseWindow D.α D.q D.Λ i p := ⟨le_rfl, ht01⟩
    have hJ1 : ((p : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i ∈ ocPulseWindow D.α D.q D.Λ i p :=
      ⟨ht01, le_rfl⟩
    obtain ⟨U, hUn, M, w, hw, hM⟩ := hW.decay dd n x hx
    have hFb : ∃ M', ∀ s ∈ Icc (D.slotStart i p) (((p : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i),
        ‖Wf h dd n s x‖ ≤ M' := by
      refine ⟨M, fun s hs => (hM h s hs x (mem_of_mem_nhds hUn)).trans ?_⟩
      have hM0 := decay_const_nonneg (hM 0 s hs x (mem_of_mem_nhds hUn))
      exact mul_le_of_le_one_right hM0 (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
    have hcont := continuousOn_modeWC (c := D.cellScaleSq i) (hG.intervalIntegrable hx hJ0 hJ1)
      (hW.intervalIntegrable_mode hx h hJ0 hJ1) hFb h ht01
    exact (continuousOn_iff_continuous_domRestrict.mp hcont).measurable
  indep h dd n t x z := by
    unfold invW
    simp only [hG.indep dd n _ x z, hW.indep h dd n _ x z]
  agree ch t ht hch η := by
    set q := transverseIndex p
    set c := D.cellScaleSq i
    have hx := GenSem.paramsC_mem_carrierC hΛ hb hch 0
    set A : ℤ → ℂ := fun h => invW D i p G Wf h ch.data ch.children.length t (ch.paramsC 0) with hA
    have hAW : ∀ h, A h = modeWC c (fun u => ((ch.famMetric D u q q : ℝ) : ℂ))
        (fun s => Wf h ch.data ch.children.length s (ch.paramsC 0)) (D.slotStart i p) h t :=
      fun h => modeWC_congr h (slotStart_le ht) (fun u hu => hG.agree ch u (history_subset ht hu) hch)
        (fun s _ => rfl)
    have hAeq : ∀ h, A h = modeWC c (fun u => ((ch.famMetric D u q q : ℝ) : ℂ))
        (fun s => phaseCoeff q (fF q s ch) h) (D.slotStart i p) h t := fun h =>
      (hAW h).trans (modeWC_congr h (slotStart_le ht) (fun _ _ => rfl)
        (fun s hs => (hW.phaseCoeff_eq hΛ hb hch (history_subset ht hs) h).symm))
    obtain ⟨U, hUn, M, w, hw, hM⟩ := invW_decay hc hW hG ch.data ch.children.length hx
    have hs : Summable fun h => A h * emode h (η q) := by
      refine Summable.of_norm_bounded (summable_exp_rate hw M) fun h => ?_
      rw [norm_mul, norm_emode, mul_one]
      exact hM h t ht _ (mem_of_mem_nhds hUn)
    have hcs : ∀ h, A (-h) = conj (A h) := by
      intro h
      have e1 : A (-h) = modeWC c (fun u => ((ch.famMetric D u q q : ℝ) : ℂ))
          (fun s => conj (Wf h ch.data ch.children.length s (ch.paramsC 0))) (D.slotStart i p)
          (-h) t :=
        (hAW (-h)).trans (modeWC_congr (-h) (slotStart_le ht) (fun _ _ => rfl)
          (fun s hs => hW.conj_symm hΛ hb hch (history_subset ht hs) h))
      rw [e1, hAW h]
      exact modeWC_neg_conj (ar := fun u => (ch.famMetric D u) q q) (fun _ => rfl) _ h t
    have hsem : transverseInverseSem D i p fF (D.slotStart i p)
        (GenSort.ofTime .cell (TimeLetter.eval D (.const 0))) t ch η =
          (∑' h, A h * emode h (η q)).re := by
      unfold transverseInverseSem
      congr 1
      refine tsum_congr fun h => ?_
      have hz : phaseCoeff q (GenSort.ofTime .cell (TimeLetter.eval D (.const 0))
          (D.slotStart i p) ch) h = 0 := phaseCoeff_zero q h
      rw [hz, mul_zero, zero_add, hAeq, modeWC_ofReal]
      simp only [modeW, modeK, modeCoup, modeRate, modeKernel, emode, c, q]
    rw [hsem, ofReal_re_of_conj hs.hasSum hcs]
    exact hs.hasSum
  child h dd n t ht x hx k v hv := by
    unfold invW
    exact modeWC_congr h (slotStart_le ht) (fun u hu => hG.child dd n u (history_subset ht hu) x hx k v hv)
      (fun s hs => hW.child h dd n s (history_subset ht hs) x hx k v hv)
  decay dd n x hx := invW_decay hc hW hG dd n hx
  mode mres hm0 hm2 h t ht dd n hdd x hx := by
    by_cases h0 : h = 0
    · subst h0; rw [invW_zero]; simp
    have hx2 := carrierC_mono hb.le hm2 hx
    set Bs := ⨆ s ∈ Icc (D.slotStart i p) t, Bf mres h s with hBs
    have hgain : modeGain h = ENNReal.ofReal (2 * Real.pi * |(h : ℝ)|)⁻¹ := by
      have hpos : 0 < 2 * Real.pi * |(h : ℝ)| := by
        have : (h : ℝ) ≠ 0 := by exact_mod_cast h0
        positivity
      unfold modeGain modeMul
      simp only [h0, ↓reduceIte]
      rw [ENNReal.ofReal_inv_of_pos hpos]
    by_cases htop : Bs = ⊤
    · rw [htop, hgain, ENNReal.mul_top]
      · exact le_top
      · have hpos : 0 < (2 * Real.pi * |(h : ℝ)|)⁻¹ := by
          have : (h : ℝ) ≠ 0 := by exact_mod_cast h0
          positivity
        exact mul_ne_zero (ENNReal.ofReal_pos.mpr (by norm_num)).ne' (ENNReal.ofReal_pos.mpr hpos).ne'
    have ht₀ : D.slotStart i p ∈ ocPulseWindow D.α D.q D.Λ i p :=
    history_subset ht ⟨le_rfl, slotStart_le ht⟩
    have hbd : ∀ s ∈ Icc (D.slotStart i p) t, ‖Wf h dd n s x‖ ≤ Bs.toReal := by
      intro s hs
      have h1 : ‖Wf h dd n s x‖ₑ ≤ Bs :=
        (hW.mode mres hm0 hm2 h s (history_subset ht hs) dd n hdd x hx).trans
          (le_iSup₂_of_le s hs le_rfl)
      rw [← ofReal_norm] at h1
      exact (ENNReal.ofReal_le_iff_le_toReal htop).mp h1
    have hb' := norm_modeWC_le' hc (by norm_num : (0 : ℝ) < 9 / 10) h0 (slotStart_le ht)
      (hG.intervalIntegrable hx2 ht₀ ht) (fun u hu => hG.re dd n u (history_subset ht hu) x hx2)
      (F := fun s => Wf h dd n s x) hbd
    have hB0 : 0 ≤ Bs.toReal := ENNReal.toReal_nonneg
    have hpos : 0 < 2 * Real.pi * |(h : ℝ)| := by
      have : (h : ℝ) ≠ 0 := by exact_mod_cast h0
      positivity
    rw [← ofReal_norm, hgain, ← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (hb'.trans ?_)
    rw [div_le_iff₀ (by positivity)]
    have : (4 / 3 * (2 * Real.pi * |(h : ℝ)|)⁻¹ * Bs.toReal) *
        (2 * Real.pi * |(h : ℝ)| * (9 / 10)) = 6 / 5 * Bs.toReal := by
      field_simp
      ring
    rw [this]
    linarith

end Inverse

end AVRegularity.Providers.ComplexContext
end
