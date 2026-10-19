-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexFlow.Bounds
import AVRegularity.Velocity.Jets.OCData
import AVRegularity.Applications.Construction.StreamTail
public import AVRegularity.Statements.Construction.IsOCStreamSeq
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.PicardGroup

@[expose] public noncomputable section

section
open Homogenization AVenhance
namespace AVRegularity.Providers.ComplexFlow

/-! **The complex shear profiles**: each profile `ψ_{m,k}` extends to an entire function on
`ℂ²`, given by the same formula, as in the proof of Proposition 6.5 of the paper. `psi0C`,
`ocShearC` are the entire extensions of `psi0`, `ocShear`;
`|sin z| ≤ e^{|Im z|}` (`norm_sin_le`) gives `|ψ_{m,k}(w)| ≤ ε_m^{1+α} e^{2π|Im w|₁/ε_m}`
(`norm_ocShearC_le`). -/

/-- `|sin z| ≤ e^{|Im z|}`. -/
theorem norm_sin_le (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have e : Complex.sin z = (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) *
      Complex.I / 2 := rfl
  rw [e, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  have h1 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h2 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h3 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have h4 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  calc ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ / 2
      ≤ (‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖) / 2 := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ Real.exp |z.im| := by rw [h1, h2]; linarith

/-- The entire extension of `ψ_{0,k}`. -/
def psi0C (k : ℤ) (w : CVec) : ℂ :=
  if k % 4 = 1 then Complex.sin (2 * Real.pi * w 0)
  else if k % 4 = 3 then Complex.sin (2 * Real.pi * w 1) else 0

/-- The entire extension of the shear profile `ψ_{m,k}(y) = ε_m^{1+α} ψ_{0,k}(y/ε_m)`. -/
def ocShearC (α q : ℝ) (Λ m : ℕ) (k : ℤ) (w : CVec) : ℂ :=
  ((ocEpsilon q Λ m ^ (1 + α) : ℝ) : ℂ) * psi0C k ((((ocEpsilon q Λ m)⁻¹ : ℝ) : ℂ) • w)

theorem differentiable_psi0C (k : ℤ) : Differentiable ℂ (psi0C k) := by
  unfold psi0C
  split_ifs
  · exact Complex.differentiable_sin.comp ((differentiable_const _).mul (differentiable_apply 0))
  · exact Complex.differentiable_sin.comp ((differentiable_const _).mul (differentiable_apply 1))
  · exact differentiable_const _

theorem differentiable_ocShearC (α q : ℝ) (Λ m : ℕ) (k : ℤ) :
    Differentiable ℂ (ocShearC α q Λ m k) :=
  (differentiable_const _).mul ((differentiable_psi0C k).comp
    ((differentiable_id (𝕜 := ℂ) (E := CVec)).const_smul
      ((((ocEpsilon q Λ m)⁻¹ : ℝ) : ℂ))))

theorem psi0C_ofRealVec (k : ℤ) (x : Vec 2) : psi0C k (ofRealVec x) = (psi0 k x : ℂ) := by
  unfold psi0C psi0
  split_ifs <;> simp [ofRealVec, Complex.ofReal_sin]

theorem ocShearC_ofRealVec (α q : ℝ) (Λ m : ℕ) (k : ℤ) (y : Vec 2) :
    ocShearC α q Λ m k (ofRealVec y) = (ocShear α q Λ m k y : ℂ) := by
  have e : (((ocEpsilon q Λ m)⁻¹ : ℝ) : ℂ) • ofRealVec y = ofRealVec ((ocEpsilon q Λ m)⁻¹ • y) := by
    funext a
    simp [ofRealVec]
  unfold ocShearC ocShear
  rw [e, psi0C_ofRealVec]
  push_cast
  rfl

theorem norm_psi0C_le (k : ℤ) (w : CVec) :
    ‖psi0C k w‖ ≤ Real.exp (2 * Real.pi * imL1 w) := by
  have hb : ∀ a : Fin 2, ‖Complex.sin (2 * Real.pi * w a)‖ ≤ Real.exp (2 * Real.pi * imL1 w) := by
    intro a
    refine (norm_sin_le _).trans (Real.exp_le_exp.mpr ?_)
    have h1 : (2 * (Real.pi : ℂ) * w a).im = 2 * Real.pi * (w a).im := by simp
    rw [h1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Finset.single_le_sum (f := fun a => |(w a).im|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ a)
  unfold psi0C
  split_ifs
  · exact hb 0
  · exact hb 1
  · simpa using (Real.exp_pos _).le

theorem norm_ocShearC_le (α q : ℝ) (Λ m : ℕ) (k : ℤ) (w : CVec) (hε : 0 < ocEpsilon q Λ m) :
    ‖ocShearC α q Λ m k w‖ ≤
      ocEpsilon q Λ m ^ (1 + α) * Real.exp (2 * Real.pi * (imL1 w / ocEpsilon q Λ m)) := by
  unfold ocShearC
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hε.le _)]
  refine mul_le_mul_of_nonneg_left ((norm_psi0C_le k _).trans (le_of_eq ?_))
    (Real.rpow_nonneg hε.le _)
  congr 2
  unfold imL1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, Complex.im_ofReal_mul, abs_mul,
    abs_of_pos (inv_pos.mpr hε), inv_mul_eq_div]

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Homogenization AVenhance
namespace AVRegularity.Providers.ComplexFlow

/-! **The complex stream increment**. For a complex velocity `b_{m-1}` on `S_{2rE}`
(`E = ε_{m-1}`, `r = 1/100`) with the Lipschitz constant `Γ`, `Γ τ_m'' ≤ 1/16`, the term
`T_k(t, z) = ŝ_{m,l_k}(t) ζ_{m,k}(t) ψ_{m,k}(Y_k(t, z))`, `Y_k(t, z) = X^ℂ_{m-1}(l_k τ_m'', z, t)`
(`thetaTerm`), uses the complex flow on the renewal window `|t - l_k τ_m''| ≤ τ_m''/2` only where
the slow envelope is nonzero (`env_support`), so that on the strip `S_{4re}` (`e = ε_m`):
* each term is jointly continuous and holomorphic in `z` (`continuousOn_thetaTerm`,
  `differentiableOn_thetaTerm`), bounded by `2 ζ_{m,k}(t) e^{1+α}` (`norm_thetaTerm_le`), and real
  at real points, where it is the term of the recursion `ocNextStream`
  (`thetaTerm_ofRealVec`);
* only the four terms `k ∈ [⌊t₀/τ_m⌋ - 1, ⌊t₀/τ_m⌋ + 2]` are nonzero near `t₀`
  (`thetaTerm_eq_zero_of`). -/

section
/-- The closed strip `S̄_{E/100}` of the flows of `b_{m-1}`. -/
def flowW (q : ℝ) (Λ m : ℕ) : ℝ := ocEpsilon q Λ (m - 1) / 100

/-- The renewal anchor `l_k τ_m''` of the term `k`. -/
def anchorK (α q : ℝ) (Λ m : ℕ) (k : ℤ) : ℝ := (ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m

/-- The time cutoff `ŝ_{m,l_k}(t) ζ_{m,k}(t)` of the term `k`. -/
def cutK (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (k : ℤ) (t : ℝ) : ℝ :=
  slowEnvelope α q Λ m (ocLabel α q Λ m k) t * ζ ((t - k * ocTau α q Λ m) / ocTau α q Λ m)

/-- **One term of the complex stream increment.** -/
def thetaTerm (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (bP : ℝ → CVec → CVec) (k : ℤ) (t : ℝ)
    (z : CVec) : ℂ :=
  (cutK α q Λ ζ m k t : ℂ) * ocShearC α q Λ m k (cflow bP (flowW q Λ m) (anchorK α q Λ m k) z t)

/-- **The complex stream increment** `Θ_m = ∑_k T_k`. -/
def thetaC (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (bP : ℝ → CVec → CVec) (t : ℝ) (z : CVec) :
    ℂ :=
  ∑' k : ℤ, thetaTerm α q Λ ζ m bP k t z

/-- **The scale facts of the level `m` used by the analytic step.** -/
structure VelScales (α q : ℝ) (Λ m : ℕ) (Γ : ℝ) : Prop where
  hΛ : 128 ≤ Λ
  hm : 1 ≤ m
  heE : 128 * ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1)
  hΓ : 0 ≤ Γ
  hwin : Γ * ocTauPP α q Λ m ≤ 1 / 16

variable {α q : ℝ} {Λ m : ℕ} {Γ V : ℝ} {ζ : ℝ → ℝ} {bP : ℝ → CVec → CVec}

namespace VelScales

theorem hΛ1 (h : VelScales α q Λ m Γ) : 1 ≤ Λ := by have := h.hΛ; omega

theorem he (h : VelScales α q Λ m Γ) : 0 < ocEpsilon q Λ m :=
  Construction.Stream.ocEpsilon_pos h.hΛ1

theorem hE (h : VelScales α q Λ m Γ) : 0 < ocEpsilon q Λ (m - 1) :=
  Construction.Stream.ocEpsilon_pos h.hΛ1

theorem hτ (h : VelScales α q Λ m Γ) : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos h.hΛ1

theorem hτP (h : VelScales α q Λ m Γ) : 0 < ocTauP α q Λ m := Velocity.Jets.ocTauP_pos h.hΛ1

theorem hτPP (h : VelScales α q Λ m Γ) : 0 < ocTauPP α q Λ m :=
  Construction.Stream.ocTauPP_pos h.hΛ1

end VelScales

/-! ### The renewal window of a term -/

/-- The renewal window `[l_k τ'' - τ''/2, l_k τ'' + τ''/2]`. -/
def winK (α q : ℝ) (Λ m : ℕ) (k : ℤ) : Set ℝ :=
  Icc (anchorK α q Λ m k - ocTauPP α q Λ m / 2) (anchorK α q Λ m k + ocTauPP α q Λ m / 2)

theorem flowWin_k (hs : VelScales α q Λ m Γ) (k : ℤ) :
    FlowWin (ocEpsilon q Λ (m - 1) / 50) (flowW q Λ m) Γ
      (anchorK α q Λ m k - ocTauPP α q Λ m / 2) (anchorK α q Λ m k + ocTauPP α q Λ m / 2) where
  hℓ' := by unfold flowW; have := hs.hE; positivity
  hℓℓ := by unfold flowW; have := hs.hE; linarith
  hab := by have := hs.hτPP; linarith
  hΓT := by
    have h : anchorK α q Λ m k + ocTauPP α q Λ m / 2 - (anchorK α q Λ m k - ocTauPP α q Λ m / 2) =
        ocTauPP α q Λ m := by ring
    rw [h]
    linarith [hs.hwin]

/-- The strip `S_{4re} = S_{e/25}` of the stream increment. -/
def strip4 (q : ℝ) (Λ m : ℕ) : Set CVec := strip (ocEpsilon q Λ m / 25)

theorem strip4_subset_U0 (hs : VelScales α q Λ m Γ) (k : ℤ) :
    strip4 q Λ m ⊆ U0 (flowW q Λ m) Γ (anchorK α q Λ m k - ocTauPP α q Λ m / 2)
      (anchorK α q Λ m k + ocTauPP α q Λ m / 2) := by
  intro z hz
  show imL1 z < (1 - Γ * (anchorK α q Λ m k + ocTauPP α q Λ m / 2 -
    (anchorK α q Λ m k - ocTauPP α q Λ m / 2))) * flowW q Λ m
  have h : anchorK α q Λ m k + ocTauPP α q Λ m / 2 - (anchorK α q Λ m k - ocTauPP α q Λ m / 2) =
      ocTauPP α q Λ m := by ring
  rw [h]
  have hz' : imL1 z < ocEpsilon q Λ m / 25 := hz
  have h1 : (15 / 16) * flowW q Λ m ≤ (1 - Γ * ocTauPP α q Λ m) * flowW q Λ m :=
    mul_le_mul_of_nonneg_right (by linarith [hs.hwin]) (by unfold flowW; have := hs.hE; positivity)
  have h2 : ocEpsilon q Λ m / 25 ≤ (15 / 16) * flowW q Λ m := by
    unfold flowW
    have := hs.heE
    have := hs.he
    linarith
  linarith

theorem isOpen_strip4 : IsOpen (strip4 q Λ m) := isOpen_strip _

/-- **Where the slow envelope is nonzero, the time is inside the renewal window.** -/
theorem env_support (hs : VelScales α q Λ m Γ) (k : ℤ) {t : ℝ}
    (h : slowEnvelope α q Λ m (ocLabel α q Λ m k) t ≠ 0) :
    t ∈ Icc (anchorK α q Λ m k - ocTauPP α q Λ m / 2 + ocTauP α q Λ m)
      (anchorK α q Λ m k + ocTauPP α q Λ m / 2 - ocTauP α q Λ m) := by
  unfold slowEnvelope at h
  have hτP := hs.hτP
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    refine h (mul_eq_zero_of_left (Real.smoothTransition.zero_of_nonpos ?_) _)
    rw [div_nonpos_iff]
    right
    refine ⟨?_, hτP.le⟩
    unfold anchorK at hlt
    linarith
  · by_contra hlt
    rw [not_le] at hlt
    refine h (mul_eq_zero_of_right _ (Real.smoothTransition.zero_of_nonpos ?_))
    rw [div_nonpos_iff]
    right
    refine ⟨?_, hτP.le⟩
    unfold anchorK at hlt
    linarith

theorem env_window (hs : VelScales α q Λ m Γ) (k : ℤ) {t : ℝ}
    (h : slowEnvelope α q Λ m (ocLabel α q Λ m k) t ≠ 0) : t ∈ winK α q Λ m k := by
  have h1 := env_support hs k h
  have := hs.hτP
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

/-- Away from the interior of the renewal window the slow envelope vanishes nearby. -/
theorem env_eventually_zero (hs : VelScales α q Λ m Γ) (k : ℤ) {t₀ : ℝ}
    (ht₀ : t₀ ∉ Ioo (anchorK α q Λ m k - ocTauPP α q Λ m / 2)
      (anchorK α q Λ m k + ocTauPP α q Λ m / 2)) :
    ∀ᶠ t in 𝓝 t₀, slowEnvelope α q Λ m (ocLabel α q Λ m k) t = 0 := by
  have hτP := hs.hτP
  have hC : t₀ ∉ Icc (anchorK α q Λ m k - ocTauPP α q Λ m / 2 + ocTauP α q Λ m)
      (anchorK α q Λ m k + ocTauPP α q Λ m / 2 - ocTauP α q Λ m) := fun hm =>
    ht₀ ⟨by linarith [hm.1], by linarith [hm.2]⟩
  filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hC] with t ht
  by_contra hne
  exact ht (env_support hs k hne)

theorem cutK_nonneg (hζ : IsFastProfile ζ) (k : ℤ) (t : ℝ) : 0 ≤ cutK α q Λ ζ m k t := by
  unfold cutK slowEnvelope
  exact mul_nonneg (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
    (hζ.2.2.2.1 _).1

theorem cutK_le (hζ : IsFastProfile ζ) (k : ℤ) (t : ℝ) :
    cutK α q Λ ζ m k t ≤ ζ ((t - k * ocTau α q Λ m) / ocTau α q Λ m) := by
  unfold cutK slowEnvelope
  have h1 := Real.smoothTransition.le_one
    ((t - ((ocLabel α q Λ m k : ℝ) - 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) / ocTauP α q Λ m)
  have h2 := Real.smoothTransition.le_one
    ((((ocLabel α q Λ m k : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m - t) / ocTauP α q Λ m)
  have h3 := Real.smoothTransition.nonneg
    ((t - ((ocLabel α q Λ m k : ℝ) - 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) / ocTauP α q Λ m)
  have h4 := Real.smoothTransition.nonneg
    ((((ocLabel α q Λ m k : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m - t) / ocTauP α q Λ m)
  have h5 := (hζ.2.2.2.1 ((t - k * ocTau α q Λ m) / ocTau α q Λ m)).1
  calc _ ≤ 1 * ζ ((t - k * ocTau α q Λ m) / ocTau α q Λ m) := by
        refine mul_le_mul_of_nonneg_right ?_ h5
        calc _ ≤ 1 * 1 := mul_le_mul h1 h2 h4 zero_le_one
          _ = 1 := one_mul 1
    _ = _ := one_mul _

theorem continuous_cutK (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) (k : ℤ) :
    Continuous (cutK α q Λ ζ m k) := by
  unfold cutK slowEnvelope
  have hτ := hs.hτ
  have hτP := hs.hτP
  refine ((Real.smoothTransition.continuous.comp ?_).mul
    (Real.smoothTransition.continuous.comp ?_)).mul (hζ.1.continuous.comp ?_) <;>
    · fun_prop (disch := positivity)

/-! ### The terms -/

theorem continuousOn_thetaTerm (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) (k : ℤ) :
    ContinuousOn (fun p : ℝ × CVec => thetaTerm α q Λ ζ m bP k p.1 p.2) (univ ×ˢ strip4 q Λ m) := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨t₀, z₀⟩ := p
  have hz₀ : z₀ ∈ strip4 q Λ m := hp.2
  by_cases ht₀ : t₀ ∈ Ioo (anchorK α q Λ m k - ocTauPP α q Λ m / 2)
      (anchorK α q Λ m k + ocTauPP α q Λ m / 2)
  · -- inside the window the flow is continuous
    have hw := flowWin_k hs k
    have hcf := continuousOn_cflow hv.toStripField hw
    have hmem : ∀ᶠ p : ℝ × CVec in 𝓝 (t₀, z₀), (anchorK α q Λ m k, p.2, p.1) ∈
        flowDom (flowW q Λ m) Γ (anchorK α q Λ m k - ocTauPP α q Λ m / 2)
          (anchorK α q Λ m k + ocTauPP α q Λ m / 2) := by
      filter_upwards [prod_mem_nhds (isOpen_Ioo.mem_nhds ht₀) (isOpen_strip4.mem_nhds hz₀)] with
        p hp
      refine ⟨⟨by have := hs.hτPP; linarith, by have := hs.hτPP; linarith⟩,
        U0_subset_Z0 (strip4_subset_U0 hs k hp.2), Ioo_subset_Icc_self hp.1⟩
    have hg : Continuous fun p : ℝ × CVec => (anchorK α q Λ m k, p.2, p.1) :=
      continuous_const.prodMk (continuous_snd.prodMk continuous_fst)
    have hY : ContinuousAt (fun p : ℝ × CVec =>
        cflow bP (flowW q Λ m) (anchorK α q Λ m k) p.2 p.1) (t₀, z₀) := by
      have hτPP := hs.hτPP
      have hdom : flowDom (flowW q Λ m) Γ (anchorK α q Λ m k - ocTauPP α q Λ m / 2)
          (anchorK α q Λ m k + ocTauPP α q Λ m / 2) ∈ 𝓝 (anchorK α q Λ m k, z₀, t₀) := by
        refine prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)) (prod_mem_nhds ?_
          (Icc_mem_nhds ht₀.1 ht₀.2))
        exact Filter.mem_of_superset (isOpen_U0.mem_nhds (strip4_subset_U0 hs k hz₀)) U0_subset_Z0
      have h1 : ContinuousAt (fun p : ℝ × CVec × ℝ => cflow bP (flowW q Λ m) p.1 p.2.1 p.2.2)
          (anchorK α q Λ m k, z₀, t₀) := hcf.continuousAt hdom
      exact ContinuousAt.comp (g := fun p : ℝ × CVec × ℝ => cflow bP (flowW q Λ m) p.1 p.2.1 p.2.2)
        (f := fun p : ℝ × CVec => (anchorK α q Λ m k, p.2, p.1)) h1 hg.continuousAt
    unfold thetaTerm
    exact (Complex.continuous_ofReal.comp
      ((continuous_cutK hζ hs k).comp continuous_fst)).continuousAt.mul
      (ContinuousAt.comp (g := ocShearC α q Λ m k)
        (f := fun p : ℝ × CVec => cflow bP (flowW q Λ m) (anchorK α q Λ m k) p.2 p.1)
        (differentiable_ocShearC α q Λ m k).continuous.continuousAt hY)
  · -- outside the window the term vanishes nearby
    refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    have h := env_eventually_zero hs k ht₀
    filter_upwards [(continuous_fst.tendsto (t₀, z₀)).eventually h] with p hp
    unfold thetaTerm cutK
    rw [hp, zero_mul, Complex.ofReal_zero, zero_mul]

theorem differentiableOn_thetaTerm (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hs : VelScales α q Λ m Γ) (k : ℤ) (t : ℝ) :
    DifferentiableOn ℂ (thetaTerm α q Λ ζ m bP k t) (strip4 q Λ m) := by
  by_cases h : slowEnvelope α q Λ m (ocLabel α q Λ m k) t = 0
  · have e : thetaTerm α q Λ ζ m bP k t = fun _ => 0 := by
      funext z
      unfold thetaTerm cutK
      rw [h, zero_mul, Complex.ofReal_zero, zero_mul]
    rw [e]
    exact differentiableOn_const _
  · have hw := flowWin_k hs k
    have htW := env_window hs k h
    have hY := differentiableOn_cflow hv hw htW (τ := anchorK α q Λ m k)
      ⟨by have := hs.hτPP; linarith, by have := hs.hτPP; linarith⟩
    unfold thetaTerm
    exact (differentiableOn_const _).mul
      ((differentiable_ocShearC α q Λ m k).comp_differentiableOn (hY.mono (strip4_subset_U0 hs k)))

theorem exp_le_two : Real.exp (2 * Real.pi * (16 / 375)) ≤ 2 := by
  have hπ : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
  have hlog := Real.log_two_gt_d9
  calc Real.exp (2 * Real.pi * (16 / 375)) ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
    _ = 2 := Real.exp_log (by norm_num)

/-- **The bound of a term on the strip `S_{4re}`.** -/
theorem norm_thetaTerm_le (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) (k : ℤ) (t : ℝ) {z : CVec}
    (hz : z ∈ strip4 q Λ m) :
    ‖thetaTerm α q Λ ζ m bP k t z‖ ≤
      ζ ((t - k * ocTau α q Λ m) / ocTau α q Λ m) * (2 * ocEpsilon q Λ m ^ (1 + α)) := by
  have he := hs.he
  have hζ0 := (hζ.2.2.2.1 ((t - k * ocTau α q Λ m) / ocTau α q Λ m)).1
  by_cases h : slowEnvelope α q Λ m (ocLabel α q Λ m k) t = 0
  · unfold thetaTerm cutK
    rw [h, zero_mul, Complex.ofReal_zero, zero_mul, norm_zero]
    exact mul_nonneg hζ0 (by positivity)
  · have hw := flowWin_k hs k
    have htW := env_window hs k h
    have hz0 : z ∈ Z0 (flowW q Λ m) Γ (anchorK α q Λ m k - ocTauPP α q Λ m / 2)
        (anchorK α q Λ m k + ocTauPP α q Λ m / 2) := U0_subset_Z0 (strip4_subset_U0 hs k hz)
    have hτW : anchorK α q Λ m k ∈ winK α q Λ m k :=
      ⟨by have := hs.hτPP; linarith, by have := hs.hτPP; linarith⟩
    have hIm := imL1_cflow_le hv.toStripField hw hz0 htW hτW
    have hT : anchorK α q Λ m k + ocTauPP α q Λ m / 2 - (anchorK α q Λ m k - ocTauPP α q Λ m / 2) =
        ocTauPP α q Λ m := by ring
    rw [hT] at hIm
    have hr : 15 / 16 ≤ 1 - Γ * ocTauPP α q Λ m := by linarith [hs.hwin]
    have hz' : imL1 z < ocEpsilon q Λ m / 25 := hz
    have hIm2 : imL1 (cflow bP (flowW q Λ m) (anchorK α q Λ m k) z t) / ocEpsilon q Λ m ≤
        16 / 375 := by
      rw [div_le_iff₀ he]
      calc imL1 (cflow bP (flowW q Λ m) (anchorK α q Λ m k) z t)
          ≤ imL1 z / (1 - Γ * ocTauPP α q Λ m) := hIm
        _ ≤ (ocEpsilon q Λ m / 25) / (15 / 16) :=
            div_le_div₀ (by positivity) hz'.le (by norm_num) hr
        _ = 16 / 375 * ocEpsilon q Λ m := by ring
    have hsh := norm_ocShearC_le α q Λ m k (cflow bP (flowW q Λ m) (anchorK α q Λ m k) z t) he
    have hexp : Real.exp (2 * Real.pi *
        (imL1 (cflow bP (flowW q Λ m) (anchorK α q Λ m k) z t) / ocEpsilon q Λ m)) ≤ 2 :=
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hIm2 (by positivity))).trans exp_le_two
    unfold thetaTerm
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutK_nonneg hζ k t)]
    calc cutK α q Λ ζ m k t * ‖ocShearC α q Λ m k (cflow bP (flowW q Λ m) (anchorK α q Λ m k) z t)‖
        ≤ ζ ((t - k * ocTau α q Λ m) / ocTau α q Λ m) * (ocEpsilon q Λ m ^ (1 + α) * 2) :=
          mul_le_mul (cutK_le hζ k t) (hsh.trans (mul_le_mul_of_nonneg_left hexp
            (Real.rpow_nonneg he.le _))) (norm_nonneg _) hζ0
      _ = _ := by ring

/-- **A term vanishes unless `|t/τ_m - k| < 2/3`.** -/
theorem thetaTerm_eq_zero_of (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) (k : ℤ) {t : ℝ}
    (hk : 2 / 3 ≤ |t / ocTau α q Λ m - k|) (z : CVec) : thetaTerm α q Λ ζ m bP k t z = 0 := by
  have hτ := hs.hτ
  have hζ0 : ζ ((t - k * ocTau α q Λ m) / ocTau α q Λ m) = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have h1 := hζ.2.2.1 hmem
    have e : (t - k * ocTau α q Λ m) / ocTau α q Λ m = t / ocTau α q Λ m - k := by
      field_simp
    rw [e] at h1
    have := abs_lt.mpr ⟨h1.1, h1.2⟩
    linarith
  unfold thetaTerm cutK
  rw [hζ0, mul_zero, Complex.ofReal_zero, zero_mul]
end

/-! **The complex stream increment as a locally finite sum**. On the strip `S_{4re}`:
* near `t₀` the increment is the sum of the four terms `k ∈ [⌊t₀/τ_m⌋ - 1, ⌊t₀/τ_m⌋ + 2]`
  (`thetaC_eq_sum`), hence jointly continuous (`continuousOn_thetaC`) and holomorphic in `z`
  (`differentiableOn_thetaC`);
* `|Θ_m| ≤ 2 ε_m^{1+α}`, by `∑_k ζ_{m,k} = 1` (`norm_thetaC_le`);
* at real points it is the increment `Φ_m - Φ_{m-1}` of the recursion `ocNextStream`,
  with the complex flow equal to the real inverse flow (`thetaC_ofRealVec`). -/

section
variable {α q : ℝ} {Λ m : ℕ} {Γ V : ℝ} {ζ : ℝ → ℝ} {bP : ℝ → CVec → CVec}

/-- The four indices of the terms that can be nonzero near `t₀`. -/
def idxK (α q : ℝ) (Λ m : ℕ) (t₀ : ℝ) : Finset ℤ :=
  Finset.Icc (⌊t₀ / ocTau α q Λ m⌋ - 1) (⌊t₀ / ocTau α q Λ m⌋ + 2)

theorem thetaTerm_eq_zero_of_not_mem (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) {t₀ t : ℝ}
    (ht : |t - t₀| < ocTau α q Λ m / 6) {k : ℤ} (hk : k ∉ idxK α q Λ m t₀) (z : CVec) :
    thetaTerm α q Λ ζ m bP k t z = 0 := by
  have hτ := hs.hτ
  refine thetaTerm_eq_zero_of hζ hs k ?_ z
  have hfl := Int.floor_le (t₀ / ocTau α q Λ m)
  have hfl2 := Int.lt_floor_add_one (t₀ / ocTau α q Λ m)
  have htt : |t / ocTau α q Λ m - t₀ / ocTau α q Λ m| < 1 / 6 := by
    rw [← sub_div, abs_div, abs_of_pos hτ, div_lt_iff₀ hτ]
    linarith
  rw [abs_lt] at htt
  simp only [idxK, Finset.mem_Icc, not_and_or, not_le] at hk
  rcases hk with hk | hk
  · have hk' : (k : ℝ) ≤ (⌊t₀ / ocTau α q Λ m⌋ : ℝ) - 2 := by
      have : k ≤ ⌊t₀ / ocTau α q Λ m⌋ - 2 := by omega
      exact_mod_cast this
    rw [abs_of_pos (by linarith)]
    linarith
  · have hk' : (⌊t₀ / ocTau α q Λ m⌋ : ℝ) + 3 ≤ (k : ℝ) := by
      have : ⌊t₀ / ocTau α q Λ m⌋ + 3 ≤ k := by omega
      exact_mod_cast this
    rw [abs_of_neg (by linarith)]
    linarith

/-- **Near `t₀` the increment is a sum of four terms.** -/
theorem thetaC_eq_sum (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) {t₀ t : ℝ}
    (ht : |t - t₀| < ocTau α q Λ m / 6) (z : CVec) :
    thetaC α q Λ ζ m bP t z = ∑ k ∈ idxK α q Λ m t₀, thetaTerm α q Λ ζ m bP k t z :=
  tsum_eq_sum fun _ hk => thetaTerm_eq_zero_of_not_mem hζ hs ht hk z

theorem continuousOn_thetaC (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) :
    ContinuousOn (fun p : ℝ × CVec => thetaC α q Λ ζ m bP p.1 p.2) (univ ×ˢ strip4 q Λ m) := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  have hnhds : univ ×ˢ strip4 q Λ m ∈ 𝓝 p := prod_mem_nhds univ_mem (isOpen_strip4.mem_nhds hp.2)
  have hsum : ContinuousAt (fun p' : ℝ × CVec =>
      ∑ k ∈ idxK α q Λ m p.1, thetaTerm α q Λ ζ m bP k p'.1 p'.2) p :=
    tendsto_finsetSum _ fun k _ => (continuousOn_thetaTerm hv hζ hs k).continuousAt hnhds
  refine hsum.congr ?_
  have hτ := hs.hτ
  have ht : ∀ᶠ p' : ℝ × CVec in 𝓝 p, |p'.1 - p.1| < ocTau α q Λ m / 6 := by
    have h := (continuous_fst.tendsto p).eventually
      (Metric.ball_mem_nhds p.1 (by positivity : (0 : ℝ) < ocTau α q Λ m / 6))
    filter_upwards [h] with p' hp'
    rwa [Real.dist_eq] at hp'
  filter_upwards [ht] with p' hp'
  exact (thetaC_eq_sum hζ hs hp' p'.2).symm

theorem differentiableOn_thetaC (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) (t : ℝ) :
    DifferentiableOn ℂ (thetaC α q Λ ζ m bP t) (strip4 q Λ m) := by
  have hτ := hs.hτ
  have e : thetaC α q Λ ζ m bP t = fun z => ∑ k ∈ idxK α q Λ m t, thetaTerm α q Λ ζ m bP k t z :=
    funext fun z => thetaC_eq_sum hζ hs (by rw [sub_self, abs_zero]; positivity) z
  rw [e]
  exact DifferentiableOn.fun_sum fun k _ => differentiableOn_thetaTerm hv hs k t

theorem summable_zeta (hζ : IsFastProfile ζ) (x : ℝ) : Summable fun k : ℤ => ζ (x - k) := by
  by_contra h
  have := hζ.2.2.2.2.1 x
  rw [tsum_eq_zero_of_not_summable h] at this
  exact zero_ne_one this

/-- **The bound of the complex stream increment** on `S_{4re}`. -/
theorem norm_thetaC_le (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) (t : ℝ) {z : CVec}
    (hz : z ∈ strip4 q Λ m) : ‖thetaC α q Λ ζ m bP t z‖ ≤ 2 * ocEpsilon q Λ m ^ (1 + α) := by
  have hτ := hs.hτ
  have he := hs.he
  rw [thetaC_eq_sum hζ hs (t₀ := t) (by rw [sub_self, abs_zero]; positivity) z]
  have hζe : ∀ k : ℤ, (t - k * ocTau α q Λ m) / ocTau α q Λ m = t / ocTau α q Λ m - k := by
    intro k
    field_simp
  have hsum : ∑ k ∈ idxK α q Λ m t, ζ ((t - k * ocTau α q Λ m) / ocTau α q Λ m) ≤ 1 := by
    simp only [hζe]
    rw [← hζ.2.2.2.2.1 (t / ocTau α q Λ m)]
    exact (summable_zeta hζ _).sum_le_tsum _ fun k _ => (hζ.2.2.2.1 _).1
  calc ‖∑ k ∈ idxK α q Λ m t, thetaTerm α q Λ ζ m bP k t z‖
      ≤ ∑ k ∈ idxK α q Λ m t, ‖thetaTerm α q Λ ζ m bP k t z‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ idxK α q Λ m t, ζ ((t - k * ocTau α q Λ m) / ocTau α q Λ m) *
          (2 * ocEpsilon q Λ m ^ (1 + α)) :=
        Finset.sum_le_sum fun k _ => norm_thetaTerm_le hv hζ hs k t hz
    _ = (∑ k ∈ idxK α q Λ m t, ζ ((t - k * ocTau α q Λ m) / ocTau α q Λ m)) *
          (2 * ocEpsilon q Λ m ^ (1 + α)) := by rw [Finset.sum_mul]
    _ ≤ 1 * (2 * ocEpsilon q Λ m ^ (1 + α)) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = _ := one_mul _

/-- **At real points a term is the term of the recursion `ocNextStream`.** -/
theorem thetaTerm_ofRealVec (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hs : VelScales α q Λ m Γ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (hagree : ∀ t y, bP t (ofRealVec y) = ofRealVec (streamVel φ t y)) (k : ℤ) (t : ℝ)
    (x : Vec 2) :
    thetaTerm α q Λ ζ m bP k t (ofRealVec x) =
      ((slowEnvelope α q Λ m (ocLabel α q Λ m k) t *
        ζ ((t - k * ocTau α q Λ m) / ocTau α q Λ m) *
        ocShear α q Λ m k (flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz t x
          ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m)) : ℝ) : ℂ) := by
  by_cases h : slowEnvelope α q Λ m (ocLabel α q Λ m k) t = 0
  · unfold thetaTerm cutK
    rw [h]
    simp
  · have hw := flowWin_k hs k
    have htW := env_window hs k h
    have hτW : anchorK α q Λ m k ∈ winK α q Λ m k :=
      ⟨by have := hs.hτPP; linarith, by have := hs.hτPP; linarith⟩
    have hx : ofRealVec x ∈ Z0 (flowW q Λ m) Γ (anchorK α q Λ m k - ocTauPP α q Λ m / 2)
        (anchorK α q Λ m k + ocTauPP α q Λ m / 2) := by
      show imL1 (ofRealVec x) ≤ _
      rw [imL1_ofRealVec]
      have hT : anchorK α q Λ m k + ocTauPP α q Λ m / 2 - (anchorK α q Λ m k - ocTauPP α q Λ m / 2) =
          ocTauPP α q Λ m := by ring
      rw [hT]
      exact mul_nonneg (by linarith [hs.hwin]) (by unfold flowW; have := hs.hE; positivity)
    have hX := flow_isFlow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
    have hXc : ∀ x s, Continuous fun σ =>
        flow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz σ x s :=
      fun x s => continuous_iff_continuousAt.mpr fun σ => (hX.2 x s σ).continuousAt
    have hcf := cflow_ofRealVec_eq hv.toStripField hw hφ.vel_continuous hagree hX hXc x hx htW
      (anchorK α q Λ m k) hτW
    unfold thetaTerm cutK
    rw [hcf, ocShearC_ofRealVec]
    unfold flowInv anchorK
    push_cast
    ring

/-- **At real points the complex increment is `Φ_m - Φ_{m-1}`.** -/
theorem thetaC_ofRealVec (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hs : VelScales α q Λ m Γ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (hagree : ∀ t y, bP t (ofRealVec y) = ofRealVec (streamVel φ t y)) (t : ℝ) (x : Vec 2) :
    thetaC α q Λ ζ m bP t (ofRealVec x) =
      ((ocNextStream α q Λ ζ m φ hφ t x - φ t x : ℝ) : ℂ) := by
  unfold thetaC ocNextStream
  simp only [thetaTerm_ofRealVec hv hs hφ hagree, add_sub_cancel_left]
  rw [Complex.ofReal_tsum]
end

/-! **One step of the analytic induction**. The complex velocity of the level `m` is
`b_m = b_{m-1} + σ∇Θ_m` (`velNext`, `σ∇F = (-∂₂F, ∂₁F)`, `rotGradC`). On the strip
`S_{2re} = S_{ε_m/50}` it is a holomorphic field (`velNext_holField`):
* jointly continuous, by the parametric Cauchy formula for `∇Θ_m`;
* `|·|₁`-Lipschitz with constant `Γ + 720000 a_m`: the second derivatives of `Θ_m` are at most
  `2ε_m^{1+α}/ρ²`, `ρ = ε_m/300`, by Cauchy's estimate on `S_{4re}` (`norm_fderiv_rotGrad_le`);
* real on real points, where it is `∇^⊥Φ_m` (`velNext_ofRealVec`), since the complex derivatives
  of `Θ_m` at real points are the real derivatives of `Φ_m - Φ_{m-1}`. -/

section
open AVRegularity.Providers.GenSem

/-- The rotated complex gradient `σ∇F = (-∂₂F, ∂₁F)`. -/
def rotGradC (F : CVec → ℂ) (z : CVec) : CVec :=
  ![-(fderiv ℂ F z (cbasis 1)), fderiv ℂ F z (cbasis 0)]

/-- **The complex velocity of the level `m`**: `b_m = b_{m-1} + σ∇Θ_m`. -/
def velNext (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (bP : ℝ → CVec → CVec) (t : ℝ) (z : CVec) :
    CVec :=
  bP t z + rotGradC (thetaC α q Λ ζ m bP t) z

variable {α q : ℝ} {Λ m : ℕ} {Γ V : ℝ} {ζ : ℝ → ℝ} {bP : ℝ → CVec → CVec}

/-- The strip `S_{2re} = S_{ε_m/50}` of the complex velocity of the level `m`. -/
def strip2 (q : ℝ) (Λ m : ℕ) : Set CVec := strip (ocEpsilon q Λ m / 50)

theorem strip2_subset_strip4 (hs : VelScales α q Λ m Γ) : strip2 q Λ m ⊆ strip4 q Λ m := by
  intro z hz
  show imL1 z < ocEpsilon q Λ m / 25
  have : imL1 z < ocEpsilon q Λ m / 50 := hz
  have := hs.he
  linarith

theorem strip2_subset_prev (hs : VelScales α q Λ m Γ) :
    strip2 q Λ m ⊆ strip (ocEpsilon q Λ (m - 1) / 50) := by
  intro z hz
  show imL1 z < ocEpsilon q Λ (m - 1) / 50
  have : imL1 z < ocEpsilon q Λ m / 50 := hz
  have := hs.heE
  have := hs.he
  linarith

theorem rotGradC_apply_zero (F : CVec → ℂ) (z : CVec) :
    rotGradC F z 0 = -(fderiv ℂ F z (cbasis 1)) := rfl

theorem rotGradC_apply_one (F : CVec → ℂ) (z : CVec) :
    rotGradC F z 1 = fderiv ℂ F z (cbasis 0) := rfl

/-- The gradient entries of `Θ_m` are jointly continuous. -/
theorem continuousAt_gradTheta (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) (w : CVec) {p : ℝ × CVec}
    (hp : p.2 ∈ strip4 q Λ m) :
    ContinuousAt (fun p : ℝ × CVec => fderiv ℂ (thetaC α q Λ ζ m bP p.1) p.2 w) p :=
  continuousAt_fderiv_apply_of_param isOpen_strip4 (continuousOn_thetaC hv hζ hs)
    (differentiableOn_thetaC hv hζ hs) w hp

theorem continuousOn_rotGrad (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) :
    ContinuousOn (fun p : ℝ × CVec => rotGradC (thetaC α q Λ ζ m bP p.1) p.2)
      (univ ×ˢ strip2 q Λ m) := by
  intro p hp
  have hp4 : p.2 ∈ strip4 q Λ m := strip2_subset_strip4 hs hp.2
  refine ContinuousAt.continuousWithinAt (continuousAt_pi.mpr fun i => ?_)
  fin_cases i
  · exact (continuousAt_gradTheta hv hζ hs (cbasis 1) hp4).neg
  · exact continuousAt_gradTheta hv hζ hs (cbasis 0) hp4

theorem differentiableOn_rotGrad (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) (t : ℝ) :
    DifferentiableOn ℂ (rotGradC (thetaC α q Λ ζ m bP t)) (strip4 q Λ m) := by
  have hd := differentiableOn_thetaC hv hζ hs t
  refine differentiableOn_pi.mpr fun i => ?_
  fin_cases i
  · exact (differentiableOn_fderiv_apply isOpen_strip4 hd (cbasis 1)).neg
  · exact differentiableOn_fderiv_apply isOpen_strip4 hd (cbasis 0)

/-- **The entries of the derivative of `σ∇Θ_m` on `S_{2re}`.** -/
theorem norm_fderiv_rotGrad_le (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) (t : ℝ) {y : CVec}
    (hy : y ∈ strip2 q Λ m) (i k : Fin 2) :
    ‖fderiv ℂ (rotGradC (thetaC α q Λ ζ m bP t)) y (cbasis k) i‖ ≤
      2 * ocEpsilon q Λ m ^ (1 + α) / (ocEpsilon q Λ m / 300) / (ocEpsilon q Λ m / 300) := by
  have he := hs.he
  have hρ : 0 < ocEpsilon q Λ m / 300 := by positivity
  have hd := differentiableOn_thetaC hv hζ hs t
  have hy4 : y ∈ strip4 q Λ m := strip2_subset_strip4 hs hy
  have hR : HasFDerivAt (rotGradC (thetaC α q Λ ζ m bP t))
      (fderiv ℂ (rotGradC (thetaC α q Λ ζ m bP t)) y) y :=
    ((differentiableOn_rotGrad hv hζ hs t).differentiableAt
      (isOpen_strip4.mem_nhds hy4)).hasFDerivAt
  have hcomp : fderiv ℂ (rotGradC (thetaC α q Λ ζ m bP t)) y (cbasis k) i =
      fderiv ℂ (fun z => rotGradC (thetaC α q Λ ζ m bP t) z i) y (cbasis k) := by
    have h2 : HasFDerivAt (fun z => rotGradC (thetaC α q Λ ζ m bP t) z i)
        ((ContinuousLinearMap.proj i : CVec →L[ℂ] ℂ).comp
          (fderiv ℂ (rotGradC (thetaC α q Λ ζ m bP t)) y)) y :=
      ((ContinuousLinearMap.proj i : CVec →L[ℂ] ℂ).hasFDerivAt).comp y hR
    rw [h2.fderiv]
    rfl
  rw [hcomp]
  have hK : ∀ z ∈ strip (ocEpsilon q Λ m / 25), ‖thetaC α q Λ ζ m bP t z‖ ≤
      2 * ocEpsilon q Λ m ^ (1 + α) := fun z hz => norm_thetaC_le hv hζ hs t hz
  have hyb : imL1 y ≤ ocEpsilon q Λ m / 25 - 6 * (ocEpsilon q Λ m / 300) := by
    have : imL1 y < ocEpsilon q Λ m / 50 := hy
    linarith
  have hbd : ∀ j : Fin 2, ‖fderiv ℂ (fun z => fderiv ℂ (thetaC α q Λ ζ m bP t) z (cbasis j)) y
      (cbasis k)‖ ≤ 2 * ocEpsilon q Λ m ^ (1 + α) / (ocEpsilon q Λ m / 300) /
        (ocEpsilon q Λ m / 300) := by
    intro j
    refine ((fderiv ℂ _ y).le_opNorm _).trans ?_
    rw [norm_cbasis, mul_one]
    exact norm_fderiv_fderiv_le_of_strip hρ hd hK (norm_cbasis j).le hyb
  fin_cases i
  · show ‖fderiv ℂ (fun z => -(fderiv ℂ (thetaC α q Λ ζ m bP t) z (cbasis 1))) y (cbasis k)‖ ≤ _
    rw [fderiv_fun_neg, neg_apply, norm_neg]
    exact hbd 1
  · exact hbd 0

/-- **The complex velocity of the level `m` is a holomorphic field** with the Lipschitz constant
`Γ'` as soon as `Γ + 720000 a_m ≤ Γ'`. -/
theorem velNext_holField (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) {φ' : ℝ → Vec 2 → ℝ} {Γ' V' : ℝ} (hΓ' : Γ + 4 * (2 * ocEpsilon q Λ m ^ (1 + α) / (ocEpsilon q Λ m / 300) /
      (ocEpsilon q Λ m / 300)) ≤ Γ')
    (hreal : ∀ t x, velNext α q Λ ζ m bP t (ofRealVec x) = ofRealVec (streamVel φ' t x))
    (hV' : ∀ t x, l1 (ofRealVec (streamVel φ' t x)) ≤ V') :
    HolField (velNext α q Λ ζ m bP) (ocEpsilon q Λ m / 50) Γ' V' where
  cont := by
    have h1 : ContinuousOn (fun p : ℝ × CVec => bP p.1 p.2) (univ ×ˢ strip2 q Λ m) :=
      hv.cont.mono (prod_mono subset_rfl (strip2_subset_prev hs))
    exact h1.add (continuousOn_rotGrad hv hζ hs)
  holo := fun t => ((hv.holo t).mono (strip2_subset_prev hs)).add
    ((differentiableOn_rotGrad hv hζ hs t).mono (strip2_subset_strip4 hs))
  lip := by
    intro t z hz w hw
    have hz' := strip2_subset_prev hs hz
    have hw' := strip2_subset_prev hs hw
    have h1 := hv.lip t z hz' w hw'
    have h2 := l1_sub_le_of_entry_le (isOpen_strip _) (convex_strip _)
      ((differentiableOn_rotGrad hv hζ hs t).mono (strip2_subset_strip4 hs))
      (fun y hy i k => norm_fderiv_rotGrad_le hv hζ hs t hy i k) hz hw
    have e : velNext α q Λ ζ m bP t z - velNext α q Λ ζ m bP t w =
        (bP t z - bP t w) + (rotGradC (thetaC α q Λ ζ m bP t) z -
          rotGradC (thetaC α q Λ ζ m bP t) w) := by
      unfold velNext
      abel
    rw [e]
    refine (l1_add_le _ _).trans ?_
    have hl := l1_nonneg (z - w)
    nlinarith
  real := fun t x => by
    rw [hreal]
    exact imL1_ofRealVec _
  bdd := fun t x => by
    rw [hreal]
    exact hV' t x
  hΓ := by
    have := hs.hΓ
    have he := hs.he
    have : 0 ≤ 4 * (2 * ocEpsilon q Λ m ^ (1 + α) / (ocEpsilon q Λ m / 300) /
        (ocEpsilon q Λ m / 300)) := by positivity
    linarith

theorem l1_ofRealVec_le (y : Vec 2) : l1 (ofRealVec y) ≤ 2 * ‖y‖ := by
  refine (l1_le_two_mul_norm _).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr fun a => ?_
  simp only [ofRealVec, Complex.norm_real]
  exact norm_le_pi_norm y a

/-- The velocity of an admissible stream is bounded. -/
theorem exists_streamVel_bound {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) :
    ∃ V : ℝ, ∀ t x, l1 (ofRealVec (streamVel φ t x)) ≤ V := by
  obtain ⟨C, -, hC⟩ := Infra.Flow.exists_global_iteratedFDeriv_bound
    (Infra.Construction.smoothPeriodic_streamVel hφ) 0
  refine ⟨2 * C, fun t x => (l1_ofRealVec_le _).trans ?_⟩
  have h := hC (t, x)
  rw [norm_iteratedFDeriv_zero] at h
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- **At real points the complex velocity of the level `m` is `∇^⊥ Φ_m`.** -/
theorem velNext_ofRealVec (hv : HolField bP (ocEpsilon q Λ (m - 1) / 50) Γ V)
    (hζ : IsFastProfile ζ) (hs : VelScales α q Λ m Γ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (hagree : ∀ t y, bP t (ofRealVec y) = ofRealVec (streamVel φ t y))
    (hφ' : IsAdmissibleStream (ocNextStream α q Λ ζ m φ hφ)) (t : ℝ) (x : Vec 2) :
    velNext α q Λ ζ m bP t (ofRealVec x) =
      ofRealVec (streamVel (ocNextStream α q Λ ζ m φ hφ) t x) := by
  have hx4 : ofRealVec x ∈ strip4 q Λ m := ofRealVec_mem_strip (by have := hs.he; positivity) x
  have hd1 : DifferentiableAt ℝ (φ t) x :=
    (hφ.1.differentiable (by simp)).comp (differentiable_const t |>.prodMk differentiable_id) x
  have hd2 : DifferentiableAt ℝ (ocNextStream α q Λ ζ m φ hφ t) x :=
    (hφ'.1.differentiable (by simp)).comp (differentiable_const t |>.prodMk differentiable_id) x
  have hgrad : ∀ j : Fin 2, fderiv ℂ (thetaC α q Λ ζ m bP t) (ofRealVec x) (cbasis j) =
      ((fderiv ℝ (ocNextStream α q Λ ζ m φ hφ t) x (basisVec j) -
        fderiv ℝ (φ t) x (basisVec j) : ℝ) : ℂ) := by
    intro j
    rw [← ofRealVec_basisVec j, fderiv_ofRealVec_eq isOpen_strip4
      (differentiableOn_thetaC hv hζ hs t)
      (f := fun y => ocNextStream α q Λ ζ m φ hφ t y - φ t y)
      (fun y => thetaC_ofRealVec hv hs hφ hagree t y) hx4 (basisVec j)]
    rw [fderiv_fun_sub hd2 hd1]
    rfl
  unfold velNext
  rw [hagree]
  have h0 : (ofRealVec (streamVel φ t x) + rotGradC (thetaC α q Λ ζ m bP t) (ofRealVec x)) 0 =
      ofRealVec (streamVel (ocNextStream α q Λ ζ m φ hφ) t x) 0 := by
    simp only [Pi.add_apply, ofRealVec, rotGradC_apply_zero, hgrad,
      Applications.streamVel_apply_zero]
    push_cast
    ring
  have h1 : (ofRealVec (streamVel φ t x) + rotGradC (thetaC α q Λ ζ m bP t) (ofRealVec x)) 1 =
      ofRealVec (streamVel (ocNextStream α q Λ ζ m φ hφ) t x) 1 := by
    simp only [Pi.add_apply, ofRealVec, rotGradC_apply_one, hgrad,
      Applications.streamVel_apply_one]
    push_cast
    ring
  funext a
  fin_cases a
  · exact h0
  · exact h1
end

/-! **The analytic bounds for the finite velocities**. The complex velocities `b^ℂ_m`
(`velC`: `b^ℂ_0 = 0`, `b^ℂ_m = b^ℂ_{m-1} + σ∇Θ_m`) of a stream sequence satisfying the recursion
(`IsOCStreamSeq`) are holomorphic fields on the strips `S_{2rε_m} = S_{ε_m/50}` with the
`|·|₁`-Lipschitz constants `A a_m`, `A = 2^21` (`velA`), real on real points where they are the
velocities `∇^⊥Φ_m` (`velC_spec`). The induction closes because the parent strain is small,
`A a_{m-1} τ_m'' ≤ 2^{21-25}` (so the complex flows of `b^ℂ_{m-1}` exist on the renewal windows),
and `a_{m-1} ≤ a_m/16`, so that `A a_{m-1} + 720000 a_m ≤ A a_m`. -/

/-- The constant `A` of the gradient bounds. -/
def velA : ℝ := 2 ^ 21

/-- **The complex velocities of the levels.** -/
def velC (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) : ℕ → ℝ → CVec → CVec
  | 0 => fun _ _ => 0
  | m + 1 => velNext α q Λ ζ (m + 1) (velC α q Λ ζ m)

theorem rpow_div_sq_eq {e p : ℝ} (he : 0 < e) :
    2 * e ^ p / (e / 300) / (e / 300) = 180000 * e ^ (p - 2) := by
  rw [Real.rpow_sub he, Real.rpow_two]
  field_simp
  ring

theorem streamVel_zero (t : ℝ) (x : Vec 2) : streamVel (fun _ _ => (0 : ℝ)) t x = 0 := by
  rw [Applications.streamVel_eq_mk]
  simp

theorem ofRealVec_zero : ofRealVec 0 = 0 := by
  funext a
  simp [ofRealVec]

/-- The base field `0`. -/
theorem holField_zero (ℓ Γ : ℝ) (hΓ : 0 ≤ Γ) :
    HolField (fun (_ : ℝ) (_ : CVec) => (0 : CVec)) ℓ Γ 0 where
  cont := continuousOn_const
  holo := fun _ => differentiableOn_const _
  lip := fun _ z _ w _ => by
    rw [sub_self, l1_zero]
    exact mul_nonneg hΓ (l1_nonneg _)
  real := fun _ _ => by simp [imL1]
  bdd := fun _ _ => by rw [l1_zero]
  hΓ := hΓ

/-- **The analytic bounds of the finite velocities.** -/
theorem velC_spec {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {Λ : ℕ} (hΛ : 128 ≤ Λ) {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsOCStreamSeq α q Λ ζ Φ) :
    ∀ m : ℕ, (∃ V, HolField (velC α q Λ ζ m) (ocEpsilon q Λ m / 50) (velA * ocA α q Λ m) V) ∧
      ∀ t x, velC α q Λ ζ m t (ofRealVec x) = ofRealVec (streamVel (Φ m) t x) := by
  have hq1 : 1 < q := hq.1
  have hA0 : (0 : ℝ) < velA := by unfold velA; positivity
  intro m
  induction m with
  | zero =>
    refine ⟨⟨0, holField_zero _ _ (mul_nonneg hA0.le ?_)⟩, fun t x => ?_⟩
    · unfold ocA
      exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos (by omega)).le _
    · rw [hΦ.1]
      show (0 : CVec) = ofRealVec (streamVel (fun _ _ => (0 : ℝ)) t x)
      rw [streamVel_zero, ofRealVec_zero]
  | succ m ih =>
    obtain ⟨⟨V, hv⟩, hagree⟩ := ih
    obtain ⟨hφ, hΦm⟩ := hΦ.2 (m + 1) (by omega)
    obtain ⟨hφ', -⟩ := hΦ.2 (m + 2) (by omega)
    simp only [Nat.add_sub_cancel] at hφ hΦm hφ'
    have hε := Construction.Stream.ocEpsilon_pos (q := q) (n := m + 1) (by omega : 1 ≤ Λ)
    have hεm := Construction.Stream.ocEpsilon_pos (q := q) (n := m) (by omega : 1 ≤ Λ)
    have hA : 0 ≤ ocA α q Λ m := by
      unfold ocA
      exact Real.rpow_nonneg hεm.le _
    -- the scale facts of the level `m + 1`
    have hs : VelScales α q Λ (m + 1) (velA * ocA α q Λ m) := by
      refine ⟨hΛ, by omega, ?_, mul_nonneg hA0.le hA, ?_⟩
      · have h := Scales.epsilon_ratio_lower (q := q) (Λ := Λ) (m := m + 1) hq1 hΛ (by omega)
        rw [Nat.add_sub_cancel, ge_iff_le, le_div_iff₀ hε] at h
        have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
        rw [Nat.add_sub_cancel]
        nlinarith
      · have h := (Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ
          (m := m + 1) (by omega)).2.2.2.2.1
        rw [Nat.add_sub_cancel] at h
        have hδ := AVRegularity.ocDelta_pos_of_admissible hα₀ hq
        have h1 : ocEpsilon q Λ m ^ (2 * ocDelta α q) ≤ 1 :=
          Real.rpow_le_one hεm.le (Scales.epsilon_basic hq1 hΛ).2.1 (by positivity)
        have h2 : (2 : ℝ) ^ (-25 : ℤ) = 1 / 2 ^ 25 := by norm_num
        unfold velA
        rw [h2] at h
        calc (2 : ℝ) ^ 21 * ocA α q Λ m * ocTauPP α q Λ (m + 1)
            = 2 ^ 21 * (ocA α q Λ m * ocTauPP α q Λ (m + 1)) := by ring
          _ ≤ 2 ^ 21 * (1 / 2 ^ 25 * 1) := by
              refine mul_le_mul_of_nonneg_left (h.trans ?_) (by positivity)
              exact mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 1 / 16 := by norm_num
    have hv' : HolField (velC α q Λ ζ m) (ocEpsilon q Λ (m + 1 - 1) / 50) (velA * ocA α q Λ m) V := by
      rw [Nat.add_sub_cancel]
      exact hv
    have hreal : ∀ t x, velC α q Λ ζ (m + 1) t (ofRealVec x) =
        ofRealVec (streamVel (Φ (m + 1)) t x) := by
      intro t x
      have h := velNext_ofRealVec hv' hζ hs hφ hagree (hΦm ▸ hφ') t x
      rw [hΦm]
      exact h
    obtain ⟨V', hV'⟩ := exists_streamVel_bound hφ'
    refine ⟨⟨V', velNext_holField hv' hζ hs ?_ hreal hV'⟩, hreal⟩
    -- the Lipschitz constant closes
    have h16 := Applications.ocA_succ_ge hα₁ hq1 hΛ m
    have e : 2 * ocEpsilon q Λ (m + 1) ^ (1 + α) / (ocEpsilon q Λ (m + 1) / 300) /
        (ocEpsilon q Λ (m + 1) / 300) = 180000 * ocA α q Λ (m + 1) := by
      rw [rpow_div_sq_eq hε]
      rfl
    rw [e]
    unfold velA
    nlinarith

end AVRegularity.Providers.ComplexFlow
end
