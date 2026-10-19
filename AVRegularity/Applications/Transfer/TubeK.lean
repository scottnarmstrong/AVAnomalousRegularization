-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Transfer.Core
import AVRegularity.Applications.Tubes.Periodic
public import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Applications.LocalEnergy.Mollifier
import AVRegularity.Applications.TorusEnergy.StreamFacts
import Homogenization.Ambient.BlockMatrix
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization Set
namespace AVRegularity.Applications

/-! # Product test functions `ζ(τ) χ(y)` -/

/-- The product test function. -/
def prodTest (ζ : ℝ → ℝ) (χ : Vec 2 → ℝ) : ℝ × Vec 2 → ℝ := fun p => ζ p.1 * χ p.2

theorem fderiv_prodTest {ζ : ℝ → ℝ} {χ : Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (p : ℝ × Vec 2) (v : ℝ × Vec 2) :
    fderiv ℝ (prodTest ζ χ) p v = deriv ζ p.1 * v.1 * χ p.2 + ζ p.1 * fderiv ℝ χ p.2 v.2 := by
  have hζd : DifferentiableAt ℝ ζ p.1 := (hζ.differentiable (by simp)) _
  have hχd : DifferentiableAt ℝ χ p.2 := (hχ.differentiable (by simp)) _
  have h1 : HasFDerivAt (fun p : ℝ × Vec 2 => ζ p.1)
      ((fderiv ℝ ζ p.1).comp (ContinuousLinearMap.fst ℝ ℝ (Vec 2))) p :=
    hζd.hasFDerivAt.comp p (ContinuousLinearMap.fst ℝ ℝ (Vec 2)).hasFDerivAt
  have h2 : HasFDerivAt (fun p : ℝ × Vec 2 => χ p.2)
      ((fderiv ℝ χ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (Vec 2))) p :=
    hχd.hasFDerivAt.comp p (ContinuousLinearMap.snd ℝ ℝ (Vec 2)).hasFDerivAt
  have := (h1.mul h2).fderiv
  have e0 : prodTest ζ χ = (fun p : ℝ × Vec 2 => ζ p.1) * (fun p : ℝ × Vec 2 => χ p.2) := rfl
  rw [e0, this]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul]
  have e : fderiv ℝ ζ p.1 v.1 = deriv ζ p.1 * v.1 := by
    have h := (fderiv ℝ ζ p.1).map_smul v.1 1
    rw [smul_eq_mul, mul_one] at h
    rw [h, smul_eq_mul, fderiv_apply_one_eq_deriv, mul_comm]
  rw [e]
  ring

theorem stTimeDeriv_prodTest {ζ : ℝ → ℝ} {χ : Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (p : ℝ × Vec 2) :
    stTimeDeriv (prodTest ζ χ) p = deriv ζ p.1 * χ p.2 := by
  unfold stTimeDeriv
  rw [fderiv_prodTest hζ hχ]
  simp

theorem stSpaceGrad_prodTest {ζ : ℝ → ℝ} {χ : Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (p : ℝ × Vec 2) (i : Fin 2) :
    stSpaceGrad (prodTest ζ χ) p i = ζ p.1 * pd i χ p.2 := by
  unfold stSpaceGrad
  rw [fderiv_prodTest hζ hχ]
  simp [pd]

theorem tsupport_prodTest_subset (ζ : ℝ → ℝ) (χ : Vec 2 → ℝ) :
    tsupport (prodTest ζ χ) ⊆ tsupport ζ ×ˢ tsupport χ := by
  refine closure_minimal ?_ ((isClosed_tsupport ζ).prod (isClosed_tsupport χ))
  intro p hp
  have h1 : ζ p.1 ≠ 0 := left_ne_zero_of_mul hp
  have h2 : χ p.2 ≠ 0 := right_ne_zero_of_mul hp
  exact ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩

theorem isSTTest_prodTest {ζ : ℝ → ℝ} {χ : Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζcs : HasCompactSupport ζ) (hζts : tsupport ζ ⊆ Ioo (-1 : ℝ) 0)
    (hχ : IsSpTest (euclidBall 0 1) χ) : IsSTTest (openCyl 0 1) (prodTest ζ χ) := by
  refine ⟨(hζ.comp contDiff_fst).mul (hχ.1.comp contDiff_snd), ?_, ?_⟩
  · exact IsCompact.of_isClosed_subset (hζcs.prod hχ.2.1) (isClosed_tsupport _)
      (tsupport_prodTest_subset ζ χ)
  · refine (tsupport_prodTest_subset ζ χ).trans ?_
    rw [openCyl_zero_one_eq]
    exact prod_mono hζts hχ.2.2

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization Set
namespace AVRegularity.Applications

/-! # Gluing local traces over all centres

Local continuous `L²`-traces `Wf x` on discs `B_{ρ/4}(x)` agree on overlaps (`traces_unique`), so
they glue to one continuous function `W`; if `w` is spatially periodic then so is `W`. -/

theorem glue_traces {w : ℝ × Vec 2 → ℝ} {t ρ M : ℝ} (hρ : 0 < ρ) {Wf : Vec 2 → Vec 2 → ℝ}
    (hcont : ∀ x, ContinuousOn (Wf x) (euclidBall x (ρ / 2)))
    (hint : ∀ x, ∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
      IntegrableOn (fun y => (w (σ, y) - Wf x y) ^ 2) (euclidBall x (ρ / 4)))
    (htr : ∀ x, Tendsto (fun σ : ℝ => ∫ y in euclidBall x (ρ / 4), (w (σ, y) - Wf x y) ^ 2)
      (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0))
    (hbd : ∀ x, ∀ z ∈ euclidBall x (ρ / 2), |Wf x z| ≤ M) :
    ∃ W : Vec 2 → ℝ, Continuous W ∧ (∀ x, ∀ y ∈ euclidBall x (ρ / 4), W y = Wf x y) ∧
      (∀ x, Tendsto (fun σ : ℝ => ∫ y in euclidBall x (ρ / 4), (w (σ, y) - W y) ^ 2)
        (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0)) ∧
      (∀ x, ∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
        IntegrableOn (fun y => (w (σ, y) - W y) ^ 2) (euclidBall x (ρ / 4))) := by
  have hρ4 : (0 : ℝ) ≤ ρ / 4 := by positivity
  have hsub4 : ∀ x : Vec 2, euclidBall x (ρ / 4) ⊆ euclidBall x (ρ / 2) := fun x =>
    euclidBall_mono x hρ4 (by linarith)
  have hagree : ∀ x x' : Vec 2, ∀ y ∈ euclidBall x (ρ / 4), y ∈ euclidBall x' (ρ / 4) →
      Wf x y = Wf x' y := by
    intro x x' y hy hy'
    have hVo : IsOpen (euclidBall x (ρ / 4) ∩ euclidBall x' (ρ / 4)) :=
      (isOpen_euclidBall _ _).inter (isOpen_euclidBall _ _)
    refine traces_unique (t := t) (w := w) (M := M) hVo
      (lt_of_le_of_lt (measure_mono inter_subset_left) (volume_euclidBall_lt_top _ _))
      inter_subset_left inter_subset_right
      ((hcont x).mono (inter_subset_left.trans (hsub4 x)))
      ((hcont x').mono (inter_subset_right.trans (hsub4 x')))
      (fun z hz => hbd x z (hsub4 x hz.1)) (fun z hz => hbd x' z (hsub4 x' hz.2))
      (hint x) (htr x) (hint x') (htr x') ⟨hy, hy'⟩
  classical
  let W : Vec 2 → ℝ := fun y =>
    if h : ∃ x, y ∈ euclidBall x (ρ / 4) then Wf h.choose y else 0
  have hW : ∀ x, ∀ y ∈ euclidBall x (ρ / 4), W y = Wf x y := by
    intro x y hy
    have h : ∃ x, y ∈ euclidBall x (ρ / 4) := ⟨x, hy⟩
    simp only [W, h, ↓reduceDIte]
    exact hagree _ x y h.choose_spec hy
  have hWcongr : ∀ x : Vec 2, ∀ σ : ℝ, ∫ y in euclidBall x (ρ / 4), (w (σ, y) - W y) ^ 2 =
      ∫ y in euclidBall x (ρ / 4), (w (σ, y) - Wf x y) ^ 2 := by
    intro x σ
    refine setIntegral_congr_fun (External.Campanato.euclidBall_measurable x _) fun y hy => ?_
    simp only [hW x y hy]
  refine ⟨W, ?_, hW, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun y => ?_
    have hyy : y ∈ euclidBall y (ρ / 4) := mem_euclidBall_self y (by positivity)
    have hat : ContinuousAt (Wf y) y :=
      (hcont y).continuousAt ((isOpen_euclidBall y (ρ / 2)).mem_nhds (hsub4 y hyy))
    have heq : W =ᶠ[𝓝 y] Wf y :=
      Filter.eventuallyEq_of_mem ((isOpen_euclidBall y (ρ / 4)).mem_nhds hyy)
        fun z hz => hW y z hz
    exact hat.congr heq.symm
  · intro x
    simp only [hWcongr x]
    exact htr x
  · intro x
    refine (hint x).mono fun σ h => ?_
    exact h.congr_fun (fun y hy => by simp only [hW x y hy])
      (External.Campanato.euclidBall_measurable x _)

theorem glue_traces_periodic {w : ℝ × Vec 2 → ℝ} {t ρ M : ℝ} (hρ : 0 < ρ)
    (hper : ∀ᶠ τ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
      ∀ y (n : Fin 2 → ℤ), w (τ, y + AVenhance.latticeShift n) = w (τ, y))
    {Wf : Vec 2 → Vec 2 → ℝ}
    (hcont : ∀ x, ContinuousOn (Wf x) (euclidBall x (ρ / 2)))
    (hint : ∀ x, ∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
      IntegrableOn (fun y => (w (σ, y) - Wf x y) ^ 2) (euclidBall x (ρ / 4)))
    (htr : ∀ x, Tendsto (fun σ : ℝ => ∫ y in euclidBall x (ρ / 4), (w (σ, y) - Wf x y) ^ 2)
      (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0))
    (hbd : ∀ x, ∀ z ∈ euclidBall x (ρ / 2), |Wf x z| ≤ M) :
    ∃ W : Vec 2 → ℝ, AVenhance.IsZ2Periodic W ∧ Continuous W ∧
      (∀ x, ∀ y ∈ euclidBall x (ρ / 4), W y = Wf x y) ∧
      (∀ x, Tendsto (fun σ : ℝ => ∫ y in euclidBall x (ρ / 4), (w (σ, y) - W y) ^ 2)
        (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0)) := by
  obtain ⟨W, hWc, hW, hW2, hW3⟩ := glue_traces hρ hcont hint htr hbd
  have hWb : ∀ u : Vec 2, |W u| ≤ M := by
    intro u
    have huu : u ∈ euclidBall u (ρ / 4) := mem_euclidBall_self u (by positivity)
    rw [hW u u huu]
    exact hbd u u (euclidBall_mono u (by positivity) (by linarith) huu)
  have hperW : ∀ (n : Fin 2 → ℤ) (x : Vec 2), W (x + AVenhance.latticeShift n) = W x := by
    intro n x
    set a := AVenhance.latticeShift n with ha
    have hcont' : Continuous fun y => W (y + a) := hWc.comp (continuous_id.add continuous_const)
    have key := traces_unique (t := t) (w := w) (W₁ := fun y => W (y + a)) (W₂ := W)
      (V := euclidBall x (ρ / 4)) (B₁ := euclidBall x (ρ / 4)) (B₂ := euclidBall x (ρ / 4))
      (M := M) (isOpen_euclidBall _ _)
      (volume_euclidBall_lt_top _ _) subset_rfl subset_rfl hcont'.continuousOn
      hWc.continuousOn (fun y _ => hWb _) (fun y _ => hWb _)
      ?_ ?_ (hW3 x) (hW2 x)
    · exact key (mem_euclidBall_self x (by positivity))
    · filter_upwards [hW3 (x + a), hper] with σ hσ hpσ
      have := integrableOn_ball_add a x (ρ / 4) hσ
      refine this.congr_fun (fun y _ => ?_) (External.Campanato.euclidBall_measurable x _)
      simp only [ha, hpσ]
    · have : ∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
          ∫ y in euclidBall (x + a) (ρ / 4), (w (σ, y) - W y) ^ 2 =
            ∫ y in euclidBall x (ρ / 4), (w (σ, y) - W (y + a)) ^ 2 := by
        filter_upwards [hper] with σ hpσ
        rw [← setIntegral_ball_add (fun y => (w (σ, y) - W y) ^ 2) a x (ρ / 4)]
        refine setIntegral_congr_fun (External.Campanato.euclidBall_measurable x _) fun y _ => ?_
        simp only [ha, hpσ]
      exact (hW2 (x + a)).congr' this
  exact ⟨W, fun n x => hperW n x, hWc, hW, hW2⟩

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization Set
namespace AVRegularity.Applications

/-! # Moving averages

In the rescaled frame, a solution `V` of `∂τV - ΔV + d·∇V = 0` (with `d` smooth in `y` and
divergence free) has averages `A(τ) = ∫ V(τ,y) χ(y) dy` with bounded distributional derivative
`A' = -∫ V (Δχ + d·∇χ)`; if the spatial oscillation of `V` is at most `O`, then
`|V - c₀| ≤ O + O (L₁ + kd L₂)` a.e. for a suitable constant `c₀`.
-/

/-- The integral of the weighted gradient identity on one slice. -/
theorem slice_identity {V : Vec 2 → ℝ} {DV : Vec 2 → Vec 2} {dτ : Vec 2 → Vec 2}
    (hgrad : HasWeakGradientOn (euclidBall 0 1) V DV)
    (hV : IntegrableOn V (euclidBall 0 1))
    (hDV : ∀ i, IntegrableOn (fun y => DV y i) (euclidBall 0 1))
    (hd : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun y => dτ y i))
    (hdiv : ∀ y, pd 0 (fun y => dτ y 0) y + pd 1 (fun y => dτ y 1) y = 0) :
    ∫ y in euclidBall 0 1, (vecDot (DV y) (spGrad chi y) + vecDot (dτ y) (DV y) * chi y) =
      -∫ y in euclidBall 0 1, V y * (lapChi y + vecDot (dτ y) (spGrad chi y)) := by
  have W : ∀ (i : Fin 2) (ζ : Vec 2 → ℝ), IsSpTest (euclidBall 0 1) ζ →
      ∫ y in euclidBall 0 1, V y * pd i ζ y = -∫ y in euclidBall 0 1, DV y i * ζ y :=
    fun i ζ hζ => hgrad i ζ hζ.1 hζ.2.1 hζ.2.2
  have tχ : ∀ i : Fin 2, IsSpTest (euclidBall 0 1) (pd i chi) := fun i => isSpTest_pd chi_isSpTest i
  have tdχ : ∀ i : Fin 2, IsSpTest (euclidBall 0 1) (fun y => dτ y i * chi y) :=
    fun i => isSpTest_mul_left (hd i) chi_isSpTest
  have iV : ∀ (i : Fin 2) {ζ : Vec 2 → ℝ}, IsSpTest (euclidBall 0 1) ζ →
      IntegrableOn (fun y => V y * pd i ζ y) (euclidBall 0 1) := fun i ζ h =>
    integrable_mul_cont_of_integrableOn hV (pd_contDiff h.1 i).continuous (isSpTest_pd h i).2.1
  have iD : ∀ (i : Fin 2) {ζ : Vec 2 → ℝ}, IsSpTest (euclidBall 0 1) ζ →
      IntegrableOn (fun y => DV y i * ζ y) (euclidBall 0 1) := fun i ζ h =>
    integrable_mul_cont_of_integrableOn (hDV i) h.1.continuous h.2.1
  -- first part
  have e1 : ∫ y in euclidBall 0 1, vecDot (DV y) (spGrad chi y) =
      -∫ y in euclidBall 0 1, V y * lapChi y := by
    have a0 := W 0 _ (tχ 0)
    have a1 := W 1 _ (tχ 1)
    have : ∫ y in euclidBall 0 1, V y * lapChi y =
        (∫ y in euclidBall 0 1, V y * pd 0 (pd 0 chi) y) +
          ∫ y in euclidBall 0 1, V y * pd 1 (pd 1 chi) y := by
      refine Eq.trans ?_ (integral_add (iV 0 (tχ 0)) (iV 1 (tχ 1)))
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [lapChi]; ring
    rw [this, a0, a1, ← neg_add, neg_neg]
    refine Eq.trans ?_ (integral_add (iD 0 (tχ 0)) (iD 1 (tχ 1)))
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [vecDot, spGrad, Fin.sum_univ_two, pd]
  -- second part
  have e2 : ∫ y in euclidBall 0 1, vecDot (dτ y) (DV y) * chi y =
      -∫ y in euclidBall 0 1, V y * vecDot (dτ y) (spGrad chi y) := by
    have a0 := W 0 _ (tdχ 0)
    have a1 := W 1 _ (tdχ 1)
    have hpt : ∀ y, pd 0 (fun y => dτ y 0 * chi y) y + pd 1 (fun y => dτ y 1 * chi y) y =
        vecDot (dτ y) (spGrad chi y) := by
      intro y
      rw [pd_mul (hd 0) chi_smooth, pd_mul (hd 1) chi_smooth]
      have := hdiv y
      simp only [vecDot, spGrad, Fin.sum_univ_two, pd] at this ⊢
      linear_combination (chi y) * this
    have : ∫ y in euclidBall 0 1, V y * vecDot (dτ y) (spGrad chi y) =
        (∫ y in euclidBall 0 1, V y * pd 0 (fun y => dτ y 0 * chi y) y) +
          ∫ y in euclidBall 0 1, V y * pd 1 (fun y => dτ y 1 * chi y) y := by
      refine Eq.trans ?_ (integral_add (iV 0 (tdχ 0)) (iV 1 (tdχ 1)))
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only
      rw [← mul_add, hpt]
    rw [this, a0, a1, ← neg_add, neg_neg]
    refine Eq.trans ?_ (integral_add (iD 0 (tdχ 0)) (iD 1 (tdχ 1)))
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [vecDot, Fin.sum_univ_two]
    ring
  have iA : IntegrableOn (fun y => vecDot (DV y) (spGrad chi y)) (euclidBall 0 1) := by
    have := (iD 0 (tχ 0)).add (iD 1 (tχ 1))
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [vecDot, spGrad, Fin.sum_univ_two, pd, Pi.add_apply]
  have iB : IntegrableOn (fun y => vecDot (dτ y) (DV y) * chi y) (euclidBall 0 1) := by
    have := (iD 0 (tdχ 0)).add (iD 1 (tdχ 1))
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [vecDot, Fin.sum_univ_two, Pi.add_apply]
    ring
  rw [integral_add iA iB, e1, e2]
  have iL : IntegrableOn (fun y => V y * lapChi y) (euclidBall 0 1) := by
    have := (iV 0 (tχ 0)).add (iV 1 (tχ 1))
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [lapChi, Pi.add_apply]; ring
  have hpt' : ∀ y, pd 0 (fun y => dτ y 0 * chi y) y + pd 1 (fun y => dτ y 1 * chi y) y =
      vecDot (dτ y) (spGrad chi y) := by
    intro y
    rw [pd_mul (hd 0) chi_smooth, pd_mul (hd 1) chi_smooth]
    have := hdiv y
    simp only [vecDot, spGrad, Fin.sum_univ_two, pd] at this ⊢
    linear_combination (chi y) * this
  have iM : IntegrableOn (fun y => V y * vecDot (dτ y) (spGrad chi y)) (euclidBall 0 1) := by
    have := (iV 0 (tdχ 0)).add (iV 1 (tdχ 1))
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    have := hpt' y
    simp only [Pi.add_apply]
    rw [← mul_add, this]
  have hsum : ∫ y in euclidBall 0 1, V y * (lapChi y + vecDot (dτ y) (spGrad chi y)) =
      (∫ y in euclidBall 0 1, V y * lapChi y) +
        ∫ y in euclidBall 0 1, V y * vecDot (dτ y) (spGrad chi y) :=
    Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => mul_add _ _ _))
      (integral_add iL iM)
  rw [hsum]
  ring

/-! # Slice bounds for the moving averages -/

/-- `L¹` norms of the kernel derivatives. -/
def chiL1 : ℝ := ∫ y, |lapChi y|

def chiL2 : ℝ := ∫ y, (|pd 0 chi y| + |pd 1 chi y|)

theorem chiL1_nonneg : 0 ≤ chiL1 := integral_nonneg fun _ => abs_nonneg _

theorem chiL2_nonneg : 0 ≤ chiL2 := integral_nonneg fun _ => by positivity

theorem continuous_lapChi : Continuous lapChi := by
  have h0 := pd_contDiff (pd_contDiff chi_smooth 0) 0
  have h1 := pd_contDiff (pd_contDiff chi_smooth 1) 1
  exact h0.continuous.add h1.continuous

theorem hasCompactSupport_lapChi : HasCompactSupport lapChi := by
  have c0 : HasCompactSupport (pd 0 chi) := hasCompactSupport_fderiv_apply chi_cs _
  have c1 : HasCompactSupport (pd 1 chi) := hasCompactSupport_fderiv_apply chi_cs _
  exact (hasCompactSupport_fderiv_apply c0 _).add (hasCompactSupport_fderiv_apply c1 _)

theorem integrable_chi_abs_parts :
    Integrable (fun y => |lapChi y|) ∧
      Integrable (fun y => |pd 0 chi y| + |pd 1 chi y|) := by
  have h0 := pd_contDiff chi_smooth 0
  have h1 := pd_contDiff chi_smooth 1
  have c0 : HasCompactSupport (pd 0 chi) := hasCompactSupport_fderiv_apply chi_cs _
  have c1 : HasCompactSupport (pd 1 chi) := hasCompactSupport_fderiv_apply chi_cs _
  refine ⟨?_, ?_⟩
  · exact (continuous_lapChi.abs).integrable_of_hasCompactSupport hasCompactSupport_lapChi.abs
  · exact ((h0.continuous.abs.add h1.continuous.abs)).integrable_of_hasCompactSupport
      (c0.abs.add c1.abs)

theorem setIntegral_chi_ball : ∫ y in euclidBall 0 1, chi y = 1 := by
  rw [setIntegral_eq_integral_of_tsupport (g := chi) tsupport_chi fun y hy =>
    image_eq_zero_of_notMem_tsupport hy]
  exact chi_integral

theorem integrableOn_chi (B : Set (Vec 2)) : IntegrableOn chi B :=
  (chi_continuous.integrable_of_hasCompactSupport chi_cs).integrableOn

/-- Oscillation of a slice about its `χ`-average. -/
theorem slice_dev_le {Vτ : Vec 2 → ℝ} {O : ℝ} (hV : IntegrableOn Vτ (euclidBall 0 1))
    (hosc : ∀ᵐ y ∂(volume.restrict (euclidBall 0 1)), ∀ᵐ y' ∂(volume.restrict (euclidBall 0 1)),
      |Vτ y - Vτ y'| ≤ O) :
    ∀ᵐ y ∂(volume.restrict (euclidBall 0 1)),
      |Vτ y - ∫ y' in euclidBall 0 1, Vτ y' * chi y'| ≤ O := by
  have iVχ : IntegrableOn (fun y' => Vτ y' * chi y') (euclidBall 0 1) :=
    integrable_mul_cont_of_integrableOn hV chi_continuous chi_cs
  filter_upwards [hosc] with y hy
  have h1 : Vτ y - ∫ y' in euclidBall 0 1, Vτ y' * chi y' =
      ∫ y' in euclidBall 0 1, (Vτ y - Vτ y') * chi y' := by
    rw [show (fun y' => (Vτ y - Vτ y') * chi y') = fun y' => Vτ y * chi y' - Vτ y' * chi y' from
      funext fun y' => by ring, integral_sub ((integrableOn_chi _).const_mul _) iVχ,
      integral_const_mul, setIntegral_chi_ball, mul_one]
  rw [h1]
  calc |∫ y' in euclidBall 0 1, (Vτ y - Vτ y') * chi y'|
      = ‖∫ y' in euclidBall 0 1, (Vτ y - Vτ y') * chi y'‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y' in euclidBall 0 1, O * chi y' := by
        refine norm_integral_le_of_norm_le ((integrableOn_chi _).const_mul O) ?_
        filter_upwards [hy] with y' hy'
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (chi_nonneg y')]
        exact mul_le_mul_of_nonneg_right hy' (chi_nonneg y')
    _ = O := by rw [integral_const_mul, setIntegral_chi_ball, mul_one]

theorem integral_lapChi_ball : ∫ y in euclidBall 0 1, lapChi y = 0 := by
  have hz : ∀ i : Fin 2, ∀ y, y ∉ tsupport chi → pd i (pd i chi) y = 0 := by
    intro i y hy
    have h1 : y ∉ tsupport (pd i chi) := fun h => hy ((tsupport_fderiv_apply_subset chi _) h)
    simp [pd, fderiv_of_notMem_tsupport (𝕜 := ℝ) h1]
  rw [setIntegral_eq_integral_of_tsupport (g := chi) tsupport_chi fun y hy => by
    simp [lapChi, hz 0 y hy, hz 1 y hy]]
  exact integral_lapChi

theorem integral_div_ball {dτ : Vec 2 → Vec 2} (hd : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun y => dτ y i))
    (hdiv : ∀ y, pd 0 (fun y => dτ y 0) y + pd 1 (fun y => dτ y 1) y = 0) :
    ∫ y in euclidBall 0 1, vecDot (dτ y) (spGrad chi y) = 0 := by
  have hpt : ∀ y, vecDot (dτ y) (spGrad chi y) =
      pd 0 (fun y => dτ y 0 * chi y) y + pd 1 (fun y => dτ y 1 * chi y) y := by
    intro y
    rw [pd_mul (hd 0) chi_smooth, pd_mul (hd 1) chi_smooth]
    have := hdiv y
    simp only [vecDot, spGrad, Fin.sum_univ_two, pd] at this ⊢
    linear_combination (-(chi y)) * this
  have c : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun y => dτ y i * chi y) := fun i => (hd i).mul chi_smooth
  have cs : ∀ i : Fin 2, HasCompactSupport (fun y => dτ y i * chi y) := fun i => chi_cs.mul_left
  have hz : ∀ y, y ∉ tsupport chi → vecDot (dτ y) (spGrad chi y) = 0 := by
    intro y hy
    simp [vecDot, spGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) hy]
  rw [setIntegral_eq_integral_of_tsupport (g := chi) tsupport_chi hz]
  simp only [hpt]
  have i0 : Integrable (pd 0 (fun y => dτ y 0 * chi y)) :=
    (pd_contDiff (c 0) 0).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply (cs 0) _)
  have i1 : Integrable (pd 1 (fun y => dτ y 1 * chi y)) :=
    (pd_contDiff (c 1) 1).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply (cs 1) _)
  rw [integral_add i0 i1, integral_pd_eq_zero (c 0) (cs 0), integral_pd_eq_zero (c 1) (cs 1),
    add_zero]

theorem continuous_div_term {dτ : Vec 2 → Vec 2}
    (hd : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun y => dτ y i)) :
    Continuous fun y => lapChi y + vecDot (dτ y) (spGrad chi y) := by
  have h0 := (pd_contDiff chi_smooth 0).continuous
  have h1 := (pd_contDiff chi_smooth 1).continuous
  refine continuous_lapChi.add ?_
  simp only [vecDot, spGrad, Fin.sum_univ_two]
  exact ((hd 0).continuous.mul h0).add ((hd 1).continuous.mul h1)

theorem hasCompactSupport_div_term {dτ : Vec 2 → Vec 2} :
    HasCompactSupport fun y => lapChi y + vecDot (dτ y) (spGrad chi y) := by
  refine hasCompactSupport_lapChi.add ?_
  have c0 : HasCompactSupport (pd 0 chi) := hasCompactSupport_fderiv_apply chi_cs _
  have c1 : HasCompactSupport (pd 1 chi) := hasCompactSupport_fderiv_apply chi_cs _
  simp only [vecDot, spGrad, Fin.sum_univ_two]
  exact (c0.mul_left).add (c1.mul_left)

theorem J_bound {Vτ : Vec 2 → ℝ} {dτ : Vec 2 → Vec 2} {O kd : ℝ} (hO : 0 ≤ O) (hkd : 0 ≤ kd)
    (hV : IntegrableOn Vτ (euclidBall 0 1))
    (hosc : ∀ᵐ y ∂(volume.restrict (euclidBall 0 1)), ∀ᵐ y' ∂(volume.restrict (euclidBall 0 1)),
      |Vτ y - Vτ y'| ≤ O)
    (hd : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun y => dτ y i))
    (hdiv : ∀ y, pd 0 (fun y => dτ y 0) y + pd 1 (fun y => dτ y 1) y = 0)
    (hdk : ∀ y ∈ euclidBall (0 : Vec 2) 1, ‖dτ y‖ ≤ kd) :
    |∫ y in euclidBall 0 1, Vτ y * (lapChi y + vecDot (dτ y) (spGrad chi y))| ≤
      O * (chiL1 + kd * chiL2) := by
  set a : ℝ := ∫ y' in euclidBall 0 1, Vτ y' * chi y' with ha
  set st : Vec 2 → ℝ := fun y => lapChi y + vecDot (dτ y) (spGrad chi y) with hst
  have hstc : Continuous st := continuous_div_term hd
  have hstcs : HasCompactSupport st := hasCompactSupport_div_term
  have hstI : IntegrableOn st (euclidBall 0 1) := (hstc.integrable_of_hasCompactSupport hstcs).integrableOn
  have hint0 : ∫ y in euclidBall 0 1, st y = 0 := by
    have iL : IntegrableOn lapChi (euclidBall 0 1) :=
      (continuous_lapChi.integrable_of_hasCompactSupport hasCompactSupport_lapChi).integrableOn
    have iD : IntegrableOn (fun y => vecDot (dτ y) (spGrad chi y)) (euclidBall 0 1) := by
      have := (hstI.sub iL)
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp [hst]
    simp only [hst]
    rw [integral_add iL iD, integral_lapChi_ball, integral_div_ball hd hdiv, add_zero]
  have hVst : IntegrableOn (fun y => Vτ y * st y) (euclidBall 0 1) :=
    integrable_mul_cont_of_integrableOn hV hstc hstcs
  have hsplit : ∫ y in euclidBall 0 1, Vτ y * st y =
      ∫ y in euclidBall 0 1, (Vτ y - a) * st y := by
    have : ∫ y in euclidBall 0 1, (Vτ y - a) * st y =
        (∫ y in euclidBall 0 1, Vτ y * st y) - a * ∫ y in euclidBall 0 1, st y := by
      rw [← integral_const_mul, ← integral_sub hVst (hstI.const_mul a)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    rw [this, hint0]; ring
  show |∫ y in euclidBall 0 1, Vτ y * st y| ≤ _
  rw [hsplit]
  obtain ⟨hl, hr⟩ := integrable_chi_abs_parts
  set g : Vec 2 → ℝ := fun y => O * (|lapChi y| + kd * (|pd 0 chi y| + |pd 1 chi y|)) with hg
  have hgI : IntegrableOn g (euclidBall 0 1) :=
    ((hl.add (hr.const_mul kd)).const_mul O).integrableOn
  have hdev := slice_dev_le hV hosc
  calc |∫ y in euclidBall 0 1, (Vτ y - a) * st y|
      = ‖∫ y in euclidBall 0 1, (Vτ y - a) * st y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y in euclidBall 0 1, g y := by
        refine norm_integral_le_of_norm_le hgI ?_
        filter_upwards [hdev, ae_restrict_mem (isOpen_euclidBall (0 : Vec 2) 1).measurableSet] with y hy hym
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        have hdy := hdk y hym
        have b0 : |dτ y 0| ≤ kd := (norm_le_pi_norm _ 0).trans hdy
        have b1 : |dτ y 1| ≤ kd := (norm_le_pi_norm _ 1).trans hdy
        have hstb : |st y| ≤ |lapChi y| + kd * (|pd 0 chi y| + |pd 1 chi y|) := by
          simp only [hst, vecDot, spGrad, Fin.sum_univ_two, pd]
          have e1 : |dτ y 0 * fderiv ℝ chi y (basisVec 0) + dτ y 1 * fderiv ℝ chi y (basisVec 1)| ≤
              kd * (|fderiv ℝ chi y (basisVec 0)| + |fderiv ℝ chi y (basisVec 1)|) := by
            calc _ ≤ |dτ y 0 * fderiv ℝ chi y (basisVec 0)| +
                  |dτ y 1 * fderiv ℝ chi y (basisVec 1)| := abs_add_le _ _
              _ ≤ kd * |fderiv ℝ chi y (basisVec 0)| + kd * |fderiv ℝ chi y (basisVec 1)| := by
                rw [abs_mul, abs_mul]
                exact add_le_add (mul_le_mul_of_nonneg_right b0 (abs_nonneg _))
                  (mul_le_mul_of_nonneg_right b1 (abs_nonneg _))
              _ = _ := by ring
          calc _ ≤ |lapChi y| + |dτ y 0 * fderiv ℝ chi y (basisVec 0) +
                dτ y 1 * fderiv ℝ chi y (basisVec 1)| := abs_add_le _ _
            _ ≤ _ := by linarith [e1]
        calc |Vτ y - a| * |st y| ≤ O * (|lapChi y| + kd * (|pd 0 chi y| + |pd 1 chi y|)) :=
              mul_le_mul hy hstb (abs_nonneg _) hO
          _ = g y := rfl
    _ ≤ O * (chiL1 + kd * chiL2) := by
        have e : ∫ y in euclidBall 0 1, g y =
            O * ((∫ y in euclidBall 0 1, |lapChi y|) +
              kd * ∫ y in euclidBall 0 1, (|pd 0 chi y| + |pd 1 chi y|)) := by
          simp only [hg]
          rw [integral_const_mul, integral_add hl.integrableOn (hr.const_mul kd).integrableOn,
            integral_const_mul]
        rw [e]
        have l1 : ∫ y in euclidBall 0 1, |lapChi y| ≤ chiL1 :=
          setIntegral_le_integral hl (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        have l2 : ∫ y in euclidBall 0 1, (|pd 0 chi y| + |pd 1 chi y|) ≤ chiL2 :=
          setIntegral_le_integral hr (Filter.Eventually.of_forall fun _ => by positivity)
        exact mul_le_mul_of_nonneg_left (add_le_add l1 (mul_le_mul_of_nonneg_left l2 hkd)) hO

/-! # The moving average is within `O + M` of a constant -/

theorem slice_integrable {DV : Vec 2 → Vec 2} {dτ : Vec 2 → Vec 2}
    (hDV : ∀ i, IntegrableOn (fun y => DV y i) (euclidBall 0 1))
    (hd : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun y => dτ y i)) :
    IntegrableOn (fun y => vecDot (DV y) (spGrad chi y) + vecDot (dτ y) (DV y) * chi y)
      (euclidBall 0 1) := by
  have iD : ∀ (i : Fin 2) {ζ : Vec 2 → ℝ}, IsSpTest (euclidBall 0 1) ζ →
      IntegrableOn (fun y => DV y i * ζ y) (euclidBall 0 1) := fun i ζ h =>
    integrable_mul_cont_of_integrableOn (hDV i) h.1.continuous h.2.1
  have tχ : ∀ i : Fin 2, IsSpTest (euclidBall 0 1) (pd i chi) := fun i => isSpTest_pd chi_isSpTest i
  have tdχ : ∀ i : Fin 2, IsSpTest (euclidBall 0 1) (fun y => dτ y i * chi y) :=
    fun i => isSpTest_mul_left (hd i) chi_isSpTest
  have iA : IntegrableOn (fun y => vecDot (DV y) (spGrad chi y)) (euclidBall 0 1) := by
    have := (iD 0 (tχ 0)).add (iD 1 (tχ 1))
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [vecDot, spGrad, Fin.sum_univ_two, pd, Pi.add_apply]
  have iB : IntegrableOn (fun y => vecDot (dτ y) (DV y) * chi y) (euclidBall 0 1) := by
    have := (iD 0 (tdχ 0)).add (iD 1 (tdχ 1))
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [vecDot, Fin.sum_univ_two, Pi.add_apply]
    ring
  exact iA.add iB

theorem mem_openCyl_of_slice {τ : ℝ} {y : Vec 2} (hτ : τ ∈ Ioo (-1 : ℝ) 0)
    (hy : y ∈ euclidBall (0 : Vec 2) 1) : (τ, y) ∈ openCyl 0 1 := by
  rw [openCyl_zero_one_eq]
  exact ⟨hτ, hy⟩

theorem avg_const {V : ℝ × Vec 2 → ℝ} {DV : ℝ × Vec 2 → Vec 2} {d : ℝ × Vec 2 → Vec 2}
    {kd O Bd : ℝ} (hkd : 0 ≤ kd) (hO : 0 ≤ O) (hE : IsEnergyClassQ1 V DV)
    (hW : IsSkewDriftWeak 0 d V DV) (hdc : Continuous d) (hdB : ∀ p, ‖d p‖ ≤ Bd)
    (hdsm : ∀ τ i, ContDiff ℝ (⊤ : ℕ∞) (fun y => d (τ, y) i))
    (hdiv : ∀ τ y, pd 0 (fun y => d (τ, y) 0) y + pd 1 (fun y => d (τ, y) 1) y = 0)
    (hdk : ∀ p ∈ openCyl 0 1, ‖d p‖ ≤ kd)
    (hosc : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      ∀ᵐ y ∂(volume.restrict (euclidBall 0 1)), ∀ᵐ y' ∂(volume.restrict (euclidBall 0 1)),
        |V (τ, y) - V (τ, y')| ≤ O) :
    ∃ c0 : ℝ, ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      ∀ᵐ y ∂(volume.restrict (euclidBall 0 1)),
        |V (τ, y) - c0| ≤ O + O * (chiL1 + kd * chiL2) := by
  set M : ℝ := O * (chiL1 + kd * chiL2) with hMdef
  have hM : 0 ≤ M := mul_nonneg hO (add_nonneg chiL1_nonneg (mul_nonneg hkd chiL2_nonneg))
  have hfin : IsFiniteMeasure (volume.restrict (openCyl 0 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_openCyl_lt_top⟩
  have hU : Integrable V (volume.restrict (openCyl 0 1)) := hE.1.integrable one_le_two
  have hDU : ∀ i : Fin 2, Integrable (fun p => DV p i) (volume.restrict (openCyl 0 1)) :=
    fun i => (hE.2.1 i).integrable one_le_two
  have hs_int := ae_slice_integrableOn hE.1
  have hs_DV : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), ∀ i : Fin 2,
      IntegrableOn (fun y => DV (τ, y) i) (euclidBall 0 1) := by
    rw [ae_all_iff]; exact fun i => ae_slice_integrableOn (hE.2.1 i)
  have hs_grad := hE.2.2.1
  set A : ℝ → ℝ := fun τ => ∫ y in euclidBall 0 1, V (τ, y) * chi y with hA
  set J : ℝ → ℝ := fun τ => ∫ y in euclidBall 0 1,
    V (τ, y) * (lapChi y + vecDot (d (τ, y)) (spGrad chi y)) with hJ
  have hQ := openCyl_zero_one_eq
  -- integrability of `A`
  have hFint : Integrable (fun p : ℝ × Vec 2 => V p * chi p.2)
      ((volume.restrict (Ioo (-1 : ℝ) 0)).prod (volume.restrict (euclidBall 0 1))) := by
    obtain ⟨Cχ, hCχ⟩ := chi_continuous.bounded_above_of_compact_support chi_cs
    have : Integrable (fun p : ℝ × Vec 2 => V p * chi p.2) (volume.restrict (openCyl 0 1)) :=
      integrable_mul_bdd_cont hU (chi_continuous.comp continuous_snd) (C := Cχ) fun p => hCχ p.2
    rwa [hQ, volume_restrict_prod_eq] at this
  have hAint : IntegrableOn A (Ioo (-1 : ℝ) 0) := hFint.integral_prod_left
  -- the bound on `J`
  have hJb : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), |-(J τ)| ≤ M := by
    filter_upwards [hs_int, hosc, ae_restrict_mem measurableSet_Ioo] with τ h1 h2 hτ
    rw [abs_neg]
    exact J_bound hO hkd h1 h2 (hdsm τ) (hdiv τ) (fun y hy => hdk _ (mem_openCyl_of_slice hτ hy))
  -- the weak relation
  have hrel : ∀ ζ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Ioo (-1 : ℝ) 0 →
      ∫ τ in Ioo (-1 : ℝ) 0, deriv ζ τ * A τ = ∫ τ in Ioo (-1 : ℝ) 0, ζ τ * (-(J τ)) := by
    intro ζ hζ hζcs hζts
    have hφ := isSTTest_prodTest hζ hζcs hζts chi_isSpTest
    have hint := integrable_skewDriftIntegrand_zero hU hDU hdc hdB hφ.1 hφ.2.1
    have h0 : ∫ p in openCyl 0 1, skewDriftIntegrand 0 d V DV (prodTest ζ chi) p = 0 :=
      hW _ hφ
    have hpt : ∀ τ y, skewDriftIntegrand 0 d V DV (prodTest ζ chi) (τ, y) =
        -(deriv ζ τ * (V (τ, y) * chi y)) + ζ τ *
          (vecDot (DV (τ, y)) (spGrad chi y) + vecDot (d (τ, y)) (DV (τ, y)) * chi y) := by
      intro τ y
      have hg : stSpaceGrad (prodTest ζ chi) (τ, y) = ζ τ • spGrad chi y := by
        funext i
        rw [stSpaceGrad_prodTest hζ chi_smooth]
        simp [spGrad, pd]
      simp only [skewDriftIntegrand, Pi.zero_apply, add_zero, Matrix.one_mulVec, hg,
        stTimeDeriv_prodTest hζ chi_smooth, vecDot_smul_right, prodTest]
      ring
    rw [hQ, volume_restrict_prod_eq] at h0 hint
    have hFub := integral_prod _ hint
    have hinner : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
        ∫ y in euclidBall 0 1, skewDriftIntegrand 0 d V DV (prodTest ζ chi) (τ, y) =
          -(deriv ζ τ * A τ) - ζ τ * J τ := by
      filter_upwards [hs_int, hs_DV, hs_grad] with τ h1 h2 h3
      have iVχ : IntegrableOn (fun y => V (τ, y) * chi y) (euclidBall 0 1) :=
        integrable_mul_cont_of_integrableOn h1 chi_continuous chi_cs
      have iW := slice_integrable (DV := fun y => DV (τ, y)) (dτ := fun y => d (τ, y)) h2 (hdsm τ)
      have hid := slice_identity (V := fun y => V (τ, y)) (DV := fun y => DV (τ, y))
        (dτ := fun y => d (τ, y)) h3 h1 h2 (hdsm τ) (hdiv τ)
      have n1 : IntegrableOn (fun y => -(deriv ζ τ * (V (τ, y) * chi y))) (euclidBall 0 1) :=
        (iVχ.const_mul (deriv ζ τ)).neg
      simp only [hpt]
      rw [integral_add n1 (iW.const_mul (ζ τ)), integral_neg,
        integral_const_mul, integral_const_mul, hid]
      simp only [hA, hJ]
      ring
    have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by exact_mod_cast le_top)
    have hdζ : Continuous (deriv ζ) := hζ1.continuous_deriv le_rfl
    have hdζb : ∃ C, ∀ τ, ‖deriv ζ τ‖ ≤ C := by
      have := hζcs.deriv
      exact hdζ.bounded_above_of_compact_support this
    obtain ⟨Cd, hCd⟩ := hdζb
    have iζA : IntegrableOn (fun τ => deriv ζ τ * A τ) (Ioo (-1 : ℝ) 0) := by
      have := hAint.mul_bdd hdζ.aestronglyMeasurable (Filter.Eventually.of_forall hCd)
      refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
      simp only; ring
    have hinnerI := hint.integral_prod_left
    have iζJ : IntegrableOn (fun τ => ζ τ * J τ) (Ioo (-1 : ℝ) 0) := by
      have := hinnerI.neg.sub iζA
      refine this.congr ?_
      filter_upwards [hinner] with τ hτ
      simp only [Pi.sub_apply, Pi.neg_apply]
      rw [hτ]; ring
    have h1 : ∫ τ in Ioo (-1 : ℝ) 0, (-(deriv ζ τ * A τ) - ζ τ * J τ) = 0 := by
      calc ∫ τ in Ioo (-1 : ℝ) 0, (-(deriv ζ τ * A τ) - ζ τ * J τ)
          = ∫ τ in Ioo (-1 : ℝ) 0, ∫ y in euclidBall 0 1,
              skewDriftIntegrand 0 d V DV (prodTest ζ chi) (τ, y) :=
            integral_congr_ae (hinner.mono fun τ hτ => hτ.symm)
        _ = 0 := by rw [← hFub]; exact h0
    have n2 : IntegrableOn (fun τ => -(deriv ζ τ * A τ)) (Ioo (-1 : ℝ) 0) := iζA.neg
    rw [integral_sub n2 iζJ, integral_neg] at h1
    have : ∫ τ in Ioo (-1 : ℝ) 0, ζ τ * (-(J τ)) = -∫ τ in Ioo (-1 : ℝ) 0, ζ τ * J τ := by
      rw [← integral_neg]; exact integral_congr_ae (Filter.Eventually.of_forall fun τ => by ring)
    rw [this]; linarith
  obtain ⟨c0, hc0⟩ := ae_near_const hM hAint hJb hrel
  refine ⟨c0, ?_⟩
  filter_upwards [hc0, hs_int, hosc] with τ h1 h2 h3
  filter_upwards [slice_dev_le h2 h3] with y hy
  calc |V (τ, y) - c0| = |(V (τ, y) - A τ) + (A τ - c0)| := by ring_nf
    _ ≤ |V (τ, y) - A τ| + |A τ - c0| := abs_add_le _ _
    _ ≤ O + M := add_le_add hy h1

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance Set
namespace AVRegularity.Applications

/-! # Time clamping of streams

The finite stream is smooth but only bounded on compact time windows. Replacing `φ(t)` by
`φ(clamp t)` (with `clamp` the projection onto the window) keeps all objects inside the window
unchanged and makes the velocities globally bounded, as required by the trajectory and tube
lemmas. -/

/-- Projection of a time onto `[a, b]`. -/
def clampT (a b t : ℝ) : ℝ := max a (min t b)

theorem continuous_clampT (a b : ℝ) : Continuous (clampT a b) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clampT_mem {a b : ℝ} (hab : a ≤ b) (t : ℝ) : clampT a b t ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem clampT_of_mem {a b t : ℝ} (ht : t ∈ Icc a b) : clampT a b t = t := by
  simp [clampT, min_eq_left ht.2, max_eq_right ht.1]

/-- The stream clamped to `[a, b]` in time. -/
def clampStream (a b : ℝ) (φ : ℝ → Vec 2 → ℝ) : ℝ → Vec 2 → ℝ := fun t => φ (clampT a b t)

theorem streamVel_clampStream (a b : ℝ) (φ : ℝ → Vec 2 → ℝ) (t : ℝ) :
    streamVel (clampStream a b φ) t = streamVel φ (clampT a b t) := rfl

theorem isFullStream_clamp {φ : ℝ → Vec 2 → ℝ} (h : IsFullStream φ) (a b : ℝ) :
    IsFullStream (clampStream a b φ) := by
  obtain ⟨hc, h1, hbc, ⟨B, hB⟩, hp⟩ := h
  refine ⟨?_, fun t => h1 _, ?_, ⟨B, fun t x => hB _ _⟩, fun t => hp _⟩
  · exact hc.comp (((continuous_clampT a b).comp continuous_fst).prodMk continuous_snd)
  · exact hbc.comp (((continuous_clampT a b).comp continuous_fst).prodMk continuous_snd)

/-- The clamped smooth stream: smooth slices, continuous bounded velocity. -/
theorem clamp_smooth_stream {φ : ℝ → Vec 2 → ℝ} (h : IsSmoothStream φ) {a b : ℝ} (hab : a ≤ b) :
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (clampStream a b φ t)) ∧
      Continuous (fun p : ℝ × Vec 2 => streamVel (clampStream a b φ) p.1 p.2) ∧
      (∃ B : ℝ, ∀ t x, ‖streamVel (clampStream a b φ) t x‖ ≤ B) ∧
      ∀ t, IsZ2Periodic (clampStream a b φ t) := by
  obtain ⟨hs, hp⟩ := h
  refine ⟨fun t => hs.comp (contDiff_const.prodMk contDiff_id), ?_, ?_, fun t => hp _⟩
  · exact (continuous_streamVel_smooth hs).comp
      (((continuous_clampT a b).comp continuous_fst).prodMk continuous_snd)
  · obtain ⟨C, hC⟩ := bounded_streamVel_smooth hs hp a b
    exact ⟨C, fun t x => hC _ (clampT_mem hab t) x⟩

/-- A local weak solution depends on the velocity only inside the domain. -/
theorem IsLocalWeakSolution.congr_vel {v v' : ℝ → Vec 2 → Vec 2} {κ : ℝ} {O : Set (ℝ × Vec 2)}
    (hO : IsOpen O) {u : ℝ × Vec 2 → ℝ} {Du : ℝ × Vec 2 → Vec 2}
    (h : IsLocalWeakSolution v κ O u Du) (hv : ∀ p ∈ O, v p.1 p.2 = v' p.1 p.2) :
    IsLocalWeakSolution v' κ O u Du := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun φ hφ => ?_⟩
  rw [← h4 φ hφ]
  refine setIntegral_congr_fun hO.measurableSet fun p hp => ?_
  simp only [hv p hp]

/-! # The relative drift along a trajectory of the finite velocity

For `b_L = σ∇φ_L` with smooth spatial slices, the relative drift
`d = (ρ/κ)(b_L(s, Y(s) + ρ y) - Ẏ(s))` is smooth in `y`, classically divergence free, and
bounded by `(ρ²/κ) D_L` on `Q₁` when `b_L(s,·)` is `D_L`-Lipschitz.
-/

section
theorem norm_le_eNorm (v : Vec 2) : ‖v‖ ≤ eNorm v := by
  refine (pi_norm_le_iff_of_nonneg (eNorm_nonneg v)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  unfold eNorm
  exact Real.abs_le_sqrt (sq_apply_le_vecNormSq v i)

section Finite

variable {φL : ℝ → Vec 2 → ℝ}

theorem streamVel_comp_smooth (hφ : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (φL t)) (t : ℝ) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => streamVel φL t x i) := by
  have h : ∀ j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => spaceGrad (φL t) x j) := fun j =>
    pd_contDiff (hφ t) j
  have e : (fun x => streamVel φL t x i) = fun x =>
      ![-(spaceGrad (φL t) x 1), spaceGrad (φL t) x 0] i := by
    funext x; rw [streamVel_apply]
  rw [e]
  fin_cases i
  · exact (h 1).neg
  · exact h 0

theorem streamVel_classical_div (hφ : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (φL t)) (t : ℝ) (x : Vec 2) :
    pd 0 (fun y => streamVel φL t y 0) x + pd 1 (fun y => streamVel φL t y 1) x = 0 := by
  have e0 : (fun y => streamVel φL t y 0) = fun y => -(pd 1 (φL t) y) := by
    funext y; rw [streamVel_apply]; rfl
  have e1 : (fun y => streamVel φL t y 1) = pd 0 (φL t) := by
    funext y; rw [streamVel_apply]; rfl
  have hd1 : DifferentiableAt ℝ (pd 1 (φL t)) x :=
    ((pd_contDiff (hφ t) 1).differentiable (by simp)) x
  rw [e0, e1]
  have : pd 0 (fun y => -(pd 1 (φL t) y)) x = -pd 0 (pd 1 (φL t)) x := by
    unfold pd
    rw [fderiv_fun_neg]; rfl
  rw [this, pd_comm (hφ t) 0 1 x]
  ring

theorem pd_affine {G : Vec 2 → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (a : Vec 2) (ρ k e : ℝ)
    (i : Fin 2) (y : Vec 2) :
    pd i (fun y => k * (G (a + ρ • y) - e)) y = k * (ρ * pd i G (a + ρ • y)) := by
  have hGd : DifferentiableAt ℝ G (a + ρ • y) := (hG.differentiable (by simp)) _
  have hf : DifferentiableAt ℝ (fun x => k * (G x - e)) (spDil a ρ y) :=
    (hGd.sub_const e).const_mul k
  unfold pd
  have h := fderiv_comp_spDil hf (basisVec i)
  have e1 : (fun y => k * (G (a + ρ • y) - e)) = fun y => (fun x => k * (G x - e)) (spDil a ρ y) :=
    rfl
  rw [e1, h]
  have h2 : fderiv ℝ (fun x => k * (G x - e)) (a + ρ • y) = k • fderiv ℝ G (a + ρ • y) := by
    rw [fderiv_const_mul (hGd.sub_const e), fderiv_sub_const]
  have h3 : spDil a ρ y = a + ρ • y := rfl
  rw [h3, h2]
  simp only [smul_apply, smul_eq_mul, map_smul]
  ring

variable {b : ℝ → Vec 2 → Vec 2} {Y Yd : ℝ → Vec 2} {t c ρ κ : ℝ}

theorem tubeDrift_apply (i : Fin 2) (τ : ℝ) (y : Vec 2) :
    tubeDrift b Y Yd t c ρ κ (τ, y) i =
      (ρ / κ) * (b (t + c * τ) (Y (t + c * τ) + ρ • y) i - Yd (t + c * τ) i) := by
  simp [tubeDrift]

theorem tubeDrift_smooth (hφ : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (φL t)) (τ : ℝ) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => tubeDrift (streamVel φL) Y Yd t c ρ κ (τ, y) i) := by
  simp only [tubeDrift_apply]
  refine contDiff_const.mul (ContDiff.sub ?_ contDiff_const)
  exact (streamVel_comp_smooth hφ _ i).comp (contDiff_const.add (contDiff_id.const_smul ρ))

theorem tubeDrift_classical_div (hφ : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (φL t)) (τ : ℝ) (y : Vec 2) :
    pd 0 (fun y => tubeDrift (streamVel φL) Y Yd t c ρ κ (τ, y) 0) y +
      pd 1 (fun y => tubeDrift (streamVel φL) Y Yd t c ρ κ (τ, y) 1) y = 0 := by
  simp only [tubeDrift_apply]
  rw [pd_affine (streamVel_comp_smooth hφ _ 0), pd_affine (streamVel_comp_smooth hφ _ 1)]
  have := streamVel_classical_div hφ (t + c * τ) (Y (t + c * τ) + ρ • y)
  linear_combination (ρ / κ * ρ) * this

theorem vecNormSq_tubeDrift_le {DL : ℝ}
    (hlip : ∀ s x y, eNorm (b s x - b s y) ≤ DL * eNorm (x - y))
    (hr : 0 < ρ) (hκ : 0 < κ) (hc : c = ρ ^ 2 / κ) (hYd : ∀ s, s ≤ t → Yd s = b s (Y s))
    {p : ℝ × Vec 2} (hp : p ∈ openCyl 0 1) :
    vecNormSq (tubeDrift b Y Yd t c ρ κ p) ≤ (ρ ^ 2 / κ * DL) ^ 2 := by
  rw [mem_openCyl_zero_one_iff] at hp
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
  have hc0 : 0 < c := by rw [hc]; positivity
  have hsle : t + c * p.1 ≤ t := by nlinarith
  have hy : vecNormSq p.2 ≤ 1 := by
    have : vecNormSq p.2 < 1 := by simpa [vecNormSq, vecDot] using hp3
    exact this.le
  unfold tubeDrift
  rw [vecNormSq_smul, hYd _ hsle]
  have h1 := hlip (t + c * p.1) (Y (t + c * p.1) + ρ • p.2) (Y (t + c * p.1))
  have h2 : vecNormSq (b (t + c * p.1) (Y (t + c * p.1) + ρ • p.2) -
      b (t + c * p.1) (Y (t + c * p.1))) ≤ (DL * ρ) ^ 2 := by
    have e : eNorm (Y (t + c * p.1) + ρ • p.2 - Y (t + c * p.1)) = ρ * eNorm p.2 := by
      rw [add_sub_cancel_left]
      unfold eNorm
      rw [vecNormSq_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.le]
    rw [e] at h1
    have h3 : eNorm p.2 ≤ 1 := by
      unfold eNorm; rw [Real.sqrt_le_one]; exact hy
    have h0 := eNorm_nonneg (b (t + c * p.1) (Y (t + c * p.1) + ρ • p.2) -
      b (t + c * p.1) (Y (t + c * p.1)))
    have h4 : eNorm (b (t + c * p.1) (Y (t + c * p.1) + ρ • p.2) -
        b (t + c * p.1) (Y (t + c * p.1))) ≤ |DL| * ρ := by
      refine h1.trans ?_
      calc DL * (ρ * eNorm p.2) ≤ |DL| * (ρ * 1) :=
            mul_le_mul (le_abs_self _) (mul_le_mul_of_nonneg_left h3 hr.le) (mul_nonneg hr.le (eNorm_nonneg _))
              (abs_nonneg _)
        _ = |DL| * ρ := by ring
    have h5 : vecNormSq (b (t + c * p.1) (Y (t + c * p.1) + ρ • p.2) -
        b (t + c * p.1) (Y (t + c * p.1))) =
        eNorm (b (t + c * p.1) (Y (t + c * p.1) + ρ • p.2) -
          b (t + c * p.1) (Y (t + c * p.1))) ^ 2 := by
      unfold eNorm; rw [Real.sq_sqrt (vecNormSq_nonneg _)]
    rw [h5]
    calc _ ≤ (|DL| * ρ) ^ 2 := pow_le_pow_left₀ h0 h4 2
      _ = (DL * ρ) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
  calc (ρ / κ) ^ 2 * vecNormSq _ ≤ (ρ / κ) ^ 2 * (DL * ρ) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = (ρ ^ 2 / κ * DL) ^ 2 := by ring

theorem norm_tubeDrift_le_lip {DL : ℝ} (hDL : 0 ≤ DL)
    (hlip : ∀ s x y, eNorm (b s x - b s y) ≤ DL * eNorm (x - y))
    (hr : 0 < ρ) (hκ : 0 < κ) (hc : c = ρ ^ 2 / κ) (hYd : ∀ s, s ≤ t → Yd s = b s (Y s))
    {p : ℝ × Vec 2} (hp : p ∈ openCyl 0 1) :
    ‖tubeDrift b Y Yd t c ρ κ p‖ ≤ ρ ^ 2 / κ * DL := by
  have h := vecNormSq_tubeDrift_le hlip hr hκ hc hYd hp
  have h0 : 0 ≤ ρ ^ 2 / κ * DL := by positivity
  refine (norm_le_eNorm _).trans ?_
  unfold eNorm
  rw [Real.sqrt_le_left h0]
  exact h

end Finite
end

/-! # The full solution in a finite-velocity tube: skew matrix plus drift

Along a trajectory of `b_L` the full rescaled solution solves the small-skew problem with
`K = κ⁻¹ (φ - φ_L)(·) σ` and the divergence free drift `d = (ρ/κ)(b_L - Ẏ)`. -/

section
theorem streamVel_sub {φ φL : ℝ → Vec 2 → ℝ} (hφ : ∀ t, ContDiff ℝ 1 (φ t))
    (hφL : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (φL t)) (t : ℝ) (x : Vec 2) :
    streamVel φ t x - streamVel φL t x =
      sigmaMat.mulVec (spaceGrad (fun y => φ t y - φL t y) x) := by
  have h1 : DifferentiableAt ℝ (φ t) x := ((hφ t).differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ (φL t) x := ((hφL t).differentiable (by simp)) x
  have : spaceGrad (fun y => φ t y - φL t y) x = spaceGrad (φ t) x - spaceGrad (φL t) x := by
    funext i
    simp [spaceGrad, fderiv_fun_sub h1 h2]
  rw [this, Matrix.mulVec_sub]
  rfl

theorem spGrad_comp_affine {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (a : Vec 2) (ρ : ℝ) (y : Vec 2) :
    spGrad (fun y => f (a + ρ • y)) y = ρ • spaceGrad f (a + ρ • y) := by
  have hd : DifferentiableAt ℝ f (spDil a ρ y) := (hf.differentiable (by simp)) _
  funext i
  have := fderiv_comp_spDil hd (basisVec i)
  simp only [spGrad, spaceGrad, Pi.smul_apply, smul_eq_mul]
  rw [show (fun y => f (a + ρ • y)) = fun y => f (spDil a ρ y) from rfl, this, map_smul,
    smul_eq_mul]
  rfl

section K

variable {φ φL : ℝ → Vec 2 → ℝ} {Y Yd : ℝ → Vec 2} {t c ρ κ : ℝ}

/-- The skew coefficient function `Ψ` in tube coordinates. -/
def tubePsi (φ φL : ℝ → Vec 2 → ℝ) (Y : ℝ → Vec 2) (t c ρ : ℝ) : ℝ × Vec 2 → ℝ :=
  fun p => φ (t + c * p.1) (Y (t + c * p.1) + ρ • p.2) -
    φL (t + c * p.1) (Y (t + c * p.1) + ρ • p.2)

theorem tube_skewData {O : Set (ℝ × Vec 2)} {w : ℝ × Vec 2 → ℝ} {Dw : ℝ × Vec 2 → Vec 2}
    (hφ : IsFullStream φ) (hφL1 : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (φL t))
    (hφLc : Continuous fun p : ℝ × Vec 2 => φL p.1 p.2)
    (hbLc : Continuous fun p : ℝ × Vec 2 => streamVel φL p.1 p.2)
    {B : ℝ} (hBb : ∀ s y, ‖streamVel φ s y‖ ≤ B) (hBL : ∀ s y, ‖streamVel φL s y‖ ≤ B)
    (hκ : 0 < κ) (hρ : 0 < ρ) (hO : IsOpen O)
    (hw : IsLocalWeakSolution (streamVel φ) κ O w Dw)
    (hY : ContDiff ℝ 1 Y) (hYd : ∀ s, HasDerivAt Y (Yd s) s) (hYdc : Continuous Yd)
    (hYdB : ∀ s, ‖Yd s‖ ≤ B) (hsub : closedTube Y t ρ κ ⊆ O) {ϑ : ℝ}
    (hψ : ∀ t x, |φ t x - φL t x| ≤ κ * ϑ)
    (hE : IsEnergyClassQ1 (tubeU w Y t (ρ ^ 2 / κ) ρ) (tubeDU Dw Y t (ρ ^ 2 / κ) ρ)) :
    IsSkewDriftWeak (fun p => (tubePsi φ φL Y t (ρ ^ 2 / κ) ρ p / κ) • sigmaMat)
      (tubeDrift (streamVel φL) Y Yd t (ρ ^ 2 / κ) ρ κ)
      (tubeU w Y t (ρ ^ 2 / κ) ρ) (tubeDU Dw Y t (ρ ^ 2 / κ) ρ) := by
  obtain ⟨hφc, hφ1, hbc, -, hφp⟩ := hφ
  have hW0 := tube_isSkewDriftWeak hκ hρ hO hw hbc hBb hY hYd hYdc hYdB hsub hE
  set c := ρ ^ 2 / κ with hc
  have hcont1 : Continuous fun p : ℝ × Vec 2 => t + c * p.1 :=
    continuous_const.add (continuous_const.mul continuous_fst)
  have hcont2 : Continuous fun p : ℝ × Vec 2 => Y (t + c * p.1) + ρ • p.2 :=
    (hY.continuous.comp hcont1).add (continuous_snd.const_smul ρ)
  have hcomp : Continuous fun p : ℝ × Vec 2 => (t + c * p.1, Y (t + c * p.1) + ρ • p.2) :=
    hcont1.prodMk hcont2
  refine isSkewDriftWeak_of_skew (Ψ := tubePsi φ φL Y t c ρ)
    (w₁ := fun p => tubeDrift (streamVel φ) Y Yd t c ρ κ p -
      tubeDrift (streamVel φL) Y Yd t c ρ κ p) (κ := κ) hE ?_ (BΨ := κ * ϑ) ?_ ?_
    (continuous_tubeDrift hbc hY.continuous hYdc) (B' := |ρ / κ| * (B + B))
    (norm_tubeDrift_le hBb hYdB) (continuous_tubeDrift hbLc hY.continuous hYdc)
    (B0 := |ρ / κ| * (B + B)) (norm_tubeDrift_le hBL hYdB) (fun p => by abel) ?_ hW0
  · exact (hφc.comp hcomp).sub (hφLc.comp hcomp)
  · intro p; exact hψ _ _
  · intro τ
    have h1 : ContDiff ℝ 1 (φ (t + c * τ)) := hφ1 _
    have h2 : ContDiff ℝ 1 (φL (t + c * τ)) := (hφL1 _).of_le (by exact_mod_cast le_top)
    have h3 : ContDiff ℝ 1 fun y : Vec 2 => Y (t + c * τ) + ρ • y :=
      contDiff_const.add (contDiff_id.const_smul ρ)
    exact (h1.sub h2).comp h3
  · intro τ y
    have h1 : ContDiff ℝ 1 (fun y => φ (t + c * τ) y - φL (t + c * τ) y) :=
      (hφ1 _).sub ((hφL1 _).of_le (by exact_mod_cast le_top))
    have e : spGrad (fun y => tubePsi φ φL Y t c ρ (τ, y)) y =
        ρ • spaceGrad (fun x => φ (t + c * τ) x - φL (t + c * τ) x)
          (Y (t + c * τ) + ρ • y) :=
      spGrad_comp_affine h1 (Y (t + c * τ)) ρ y
    rw [e, Matrix.mulVec_smul, ← streamVel_sub hφ1 hφL1]
    simp only [tubeDrift, ← smul_sub]
    have : (ρ / κ) • (streamVel φ (t + c * τ) (Y (t + c * τ) + ρ • y) - Yd (t + c * τ) -
        (streamVel φL (t + c * τ) (Y (t + c * τ) + ρ • y) - Yd (t + c * τ))) =
        (ρ / κ) • (streamVel φ (t + c * τ) (Y (t + c * τ) + ρ • y) -
          streamVel φL (t + c * τ) (Y (t + c * τ) + ρ • y)) := by
      congr 1; abel
    rw [this, smul_smul, inv_mul_eq_div]

end K
end

end AVRegularity.Applications
end
