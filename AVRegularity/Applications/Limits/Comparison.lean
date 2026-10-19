-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Limits.Equi
import AVRegularity.Applications.TorusEnergy.StreamComparison
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.OcGamma
import AVRegularity.Construction.Scales.Times
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open MeasureTheory Filter Topology Homogenization AVenhance Set
namespace AVRegularity.Applications

/-! # Passing to the limit in the pairing identities

Pointwise convergence on `(a, ∞) × ℝ²` plus uniform `C^s` bounds on windows gives convergence of
all pairings over the cube (dominated convergence), the spatial `C^s` bound and periodicity of the
limit, and the pairing identity for the limit with `κ = 0`. -/

section
theorem abs_integral_cube_le {g : Vec 2 → ℝ} {M : ℝ} (hg : ∀ x, |g x| ≤ M) :
    |∫ x in unitCube, g x| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict unitCube) (f := g) (C := M)
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hg x)
  have hm : (volume.restrict unitCube).real Set.univ = 1 := by
    simp [Measure.real, volume_unitCube]
  rw [hm, mul_one] at h
  simpa [Real.norm_eq_abs] using h

theorem tendsto_cube_integral {F : ℕ → Vec 2 → ℝ} {F' : Vec 2 → ℝ} {M : ℝ}
    (hm : ∀ i, AEStronglyMeasurable (F i) (volume.restrict unitCube))
    (hb : ∀ i x, |F i x| ≤ M) (hl : ∀ x, Tendsto (fun i => F i x) atTop (𝓝 (F' x))) :
    Tendsto (fun i => ∫ x in unitCube, F i x) atTop (𝓝 (∫ x in unitCube, F' x)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => M) hm (integrable_const M)
    (fun i => Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb i x)
    (Eventually.of_forall hl)

theorem exists_abs_le_periodic {ψ : Vec 2 → ℝ} (hc : Continuous ψ) (hp : IsZ2Periodic ψ) :
    ∃ C : ℝ, ∀ x, |ψ x| ≤ C := by
  obtain ⟨C, hC⟩ := bounded_periodic_window (F := fun p : ℝ × Vec 2 => ψ p.2)
    (hc.comp continuous_snd) (fun t n x => hp n x) 0 0
  exact ⟨C, fun x => hC 0 ⟨le_rfl, le_rfl⟩ x⟩

/-- The data of a locally uniformly convergent sequence with uniform `C^s` bounds. -/
structure LimData (a s : ℝ) (Kc : ℝ → ℝ → ℝ) (κ : ℕ → ℝ) (g : ℕ → ℝ → Vec 2 → ℝ)
    (θs : ℝ → Vec 2 → ℝ) : Prop where
  conv : ∀ t, a < t → ∀ x, Tendsto (fun i => g i t x) atTop (𝓝 (θs t x))
  cs : ∀ i t₀ T, 0 < t₀ → t₀ < T → ∀ t ∈ Icc (a + t₀) (a + T), CsNormLe s (g i t) (Kc t₀ T)
  per : ∀ i t, a < t → IsZ2Periodic (g i t)
  cont : ∀ i t, a < t → Continuous (g i t)
  jcont : ∀ i, ContinuousOn (fun p : ℝ × Vec 2 => g i p.1 p.2) (Set.Ioi a ×ˢ Set.univ)
  κlim : Tendsto κ atTop (𝓝 0)

theorem window_of_gt {a t : ℝ} (ht : a < t) :
    ∃ t₀ T : ℝ, 0 < t₀ ∧ t₀ < T ∧ t ∈ Icc (a + t₀) (a + T) :=
  ⟨(t - a) / 2, t - a + 1, by linarith, by linarith, by constructor <;> linarith⟩

namespace LimData

variable {a s : ℝ} {Kc : ℝ → ℝ → ℝ} {κ : ℕ → ℝ} {g : ℕ → ℝ → Vec 2 → ℝ} {θs : ℝ → Vec 2 → ℝ}

theorem tcont (h : LimData a s Kc κ g θs) (i : ℕ) (x : Vec 2) :
    ContinuousOn (fun t => g i t x) (Ioi a) := by
  have := (h.jcont i).comp (continuousOn_id.prodMk continuousOn_const : ContinuousOn
    (fun t : ℝ => (t, x)) (Ioi a)) (fun t ht => ⟨ht, trivial⟩)
  exact this

theorem theta_cs (h : LimData a s Kc κ g θs) {t₀ T : ℝ} (h0 : 0 < t₀) (h1 : t₀ < T)
    {t : ℝ} (ht : t ∈ Icc (a + t₀) (a + T)) : CsNormLe s (θs t) (Kc t₀ T) := by
  have hta : a < t := by linarith [ht.1]
  intro x y z hyz
  have hconv : ∀ x, Tendsto (fun i => g i t x) atTop (𝓝 (θs t x)) := h.conv t hta
  have hlim : Tendsto (fun i => |g i t x| + |g i t y - g i t z| / torusDist y z ^ s) atTop
      (𝓝 (|θs t x| + |θs t y - θs t z| / torusDist y z ^ s)) :=
    (hconv x).abs.add ((((hconv y).sub (hconv z)).abs).div_const _)
  exact le_of_tendsto hlim (Eventually.of_forall fun i => h.cs i t₀ T h0 h1 t ht x y z hyz)

theorem theta_per (h : LimData a s Kc κ g θs) {t : ℝ} (ht : a < t) : IsZ2Periodic (θs t) := by
  intro n x
  exact tendsto_nhds_unique (h.conv t ht (x + latticeShift n))
    ((h.conv t ht x).congr fun i => (h.per i t ht n x).symm)

theorem theta_cont (h : LimData a s Kc κ g θs) (hs : 0 < s) {t : ℝ} (ht : a < t) :
    Continuous (θs t) := by
  obtain ⟨t₀, T, h0, h1, hw⟩ := window_of_gt ht
  exact continuous_of_csNormLe hs (h.theta_cs h0 h1 hw)

theorem bound (h : LimData a s Kc κ g θs) {t₀ T : ℝ} (h0 : 0 < t₀) (h1 : t₀ < T) (i : ℕ)
    {t : ℝ} (ht : t ∈ Icc (a + t₀) (a + T)) (x : Vec 2) : |g i t x| ≤ Kc t₀ T :=
  csNormLe_abs_le_lim (h.cs i t₀ T h0 h1 t ht) x

theorem tendsto_pairing (h : LimData a s Kc κ g θs) {ψ : Vec 2 → ℝ}
    (hψ : Continuous ψ) (hψp : IsZ2Periodic ψ) {t : ℝ} (ht : a < t) :
    Tendsto (fun i => pairing (g i) ψ t) atTop (𝓝 (pairing θs ψ t)) := by
  obtain ⟨t₀, T, h0, h1, hw⟩ := window_of_gt ht
  obtain ⟨C, hC⟩ := exists_abs_le_periodic hψ hψp
  have hK : 0 ≤ Kc t₀ T := csNormLe_K_nonneg (h.cs 0 t₀ T h0 h1 t hw)
  refine tendsto_cube_integral (M := Kc t₀ T * C)
    (fun i => ((h.cont i t ht).mul hψ).aestronglyMeasurable) (fun i x => ?_)
    (fun x => (h.conv t ht x).mul_const _)
  rw [abs_mul]
  exact mul_le_mul (h.bound h0 h1 i hw x) (hC x) (abs_nonneg _) hK

theorem tendsto_incK (h : LimData a s Kc κ g θs) {b : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b)
    {κbar : ℝ} (hκb : ∀ i, |κ i| ≤ κbar) {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψp : IsZ2Periodic ψ) {t : ℝ} (ht : a < t) :
    Tendsto (fun i => incK b (κ i) ψ (g i) t) atTop (𝓝 (incK b 0 ψ θs t)) := by
  obtain ⟨t₀, T, h0, h1, hw⟩ := window_of_gt ht
  obtain ⟨B, hB0, hB⟩ := hb.bounded
  obtain ⟨C, hC0, hC⟩ := exists_bound_periodic_grad hψ hψp
  have hK : 0 ≤ Kc t₀ T := csNormLe_K_nonneg (h.cs 0 t₀ T h0 h1 t hw)
  have hdc : Continuous fun x => vecDot (b t x) (spaceGrad ψ x) := by
    have hbi : ∀ j : Fin 2, Continuous fun x => b t x j := fun j =>
      (continuous_apply j).comp (hb.slice_continuous t)
    have hg : ∀ j : Fin 2, Continuous fun x => spaceGrad ψ x j :=
      continuous_spaceGrad_apply (contDiff_one_of_top hψ)
    simp only [vecDot, Fin.sum_univ_two]
    exact ((hbi 0).mul (hg 0)).add ((hbi 1).mul (hg 1))
  have hlc : Continuous (lapl ψ) := continuous_lapl hψ
  refine tendsto_cube_integral (M := Kc t₀ T * (2 * B * C + κbar * C))
    (fun i => ((h.cont i t ht).mul (hdc.add (continuous_const.mul hlc))).aestronglyMeasurable)
    (fun i x => ?_) (fun x => ?_)
  · rw [abs_mul]
    have hbd := drift_bound hB (κ i) hC t x
    have hk : |κ i| * C ≤ κbar * C := mul_le_mul_of_nonneg_right (hκb i) hC0
    exact mul_le_mul (h.bound h0 h1 i hw x) (hbd.trans (by linarith)) (abs_nonneg _) hK
  · exact (h.conv t ht x).mul (tendsto_const_nhds.add (h.κlim.mul_const _))
      |>.congr' (Eventually.of_forall fun i => rfl) |> fun hh => by simpa using hh

theorem theta_l2 (h : LimData a s Kc κ g θs) {F : ℝ}
    (hF : ∀ i t, a < t → l2NormSq (g i t) ≤ F ^ 2) {t : ℝ} (ht : a < t) :
    l2NormSq (θs t) ≤ F ^ 2 := by
  obtain ⟨t₀, T, h0, h1, hw⟩ := window_of_gt ht
  have hK : 0 ≤ Kc t₀ T := csNormLe_K_nonneg (h.cs 0 t₀ T h0 h1 t hw)
  have hlim : Tendsto (fun i => ∫ x in unitCube, g i t x ^ 2) atTop
      (𝓝 (∫ x in unitCube, θs t x ^ 2)) := by
    refine tendsto_cube_integral (M := Kc t₀ T ^ 2)
      (fun i => ((h.cont i t ht).pow 2).aestronglyMeasurable) (fun i x => ?_)
      (fun x => (h.conv t ht x).pow 2)
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (h.bound h0 h1 i hw x) 2
  exact le_of_tendsto' hlim (fun i => hF i t ht)

/-- The pairing identity passes to the limit, with `κ = 0`. -/
theorem incIdent_limit (h : LimData a s Kc κ g θs) {b : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b)
    {κbar : ℝ} (hκb : ∀ i, |κ i| ≤ κbar)
    (hinc : ∀ i, IncIdent b (κ i) (g i) (Ioi a))
    (hint : ∀ i, ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ → ∀ σ τ : ℝ, a < σ →
      σ ≤ τ → IntervalIntegrable (incK b (κ i) ψ (g i)) volume σ τ) :
    IncIdent b 0 θs (Ioi a) := by
  intro ψ hψ hψp σ hσ τ hτ hστ
  have hσa : a < σ := hσ
  have hτa : a < τ := hτ
  obtain ⟨B, hB0, hB⟩ := hb.bounded
  obtain ⟨C, hC0, hC⟩ := exists_bound_periodic_grad hψ hψp
  set t₀ : ℝ := (σ - a) / 2 with ht₀
  set T : ℝ := τ - a + 1 with hT
  have h0 : 0 < t₀ := by rw [ht₀]; linarith
  have h1 : t₀ < T := by rw [ht₀, hT]; linarith
  have hwin : ∀ t ∈ Ioc σ τ, t ∈ Icc (a + t₀) (a + T) := fun t ht => by
    constructor <;> [skip; skip] <;> simp only [ht₀, hT] <;> linarith [ht.1, ht.2]
  have hK : 0 ≤ Kc t₀ T := csNormLe_K_nonneg (h.cs 0 t₀ T h0 h1 (a + t₀) ⟨le_rfl, by linarith⟩)
  have hlim1 : Tendsto (fun i => pairing (g i) ψ τ - pairing (g i) ψ σ) atTop
      (𝓝 (pairing θs ψ τ - pairing θs ψ σ)) :=
    (h.tendsto_pairing hψ.continuous hψp hτa).sub (h.tendsto_pairing hψ.continuous hψp hσa)
  have hlim2 : Tendsto (fun i => ∫ t in σ..τ, incK b (κ i) ψ (g i) t) atTop
      (𝓝 (∫ t in σ..τ, incK b 0 ψ θs t)) := by
    simp only [intervalIntegral.integral_of_le hστ]
    refine tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc σ τ))
      (fun _ => Kc t₀ T * (2 * B * C + κbar * C)) (fun i => ?_) (integrable_const _)
      (fun i => ?_) ?_
    · have := (hint i ψ hψ hψp σ τ hσa hστ)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hστ] at this
      exact this.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have htw := hwin t ht
      have hta : a < t := by linarith [ht.1]
      rw [Real.norm_eq_abs]
      refine (abs_integral_cube_le (M := Kc t₀ T * (2 * B * C + κbar * C)) (fun x => ?_))
      rw [abs_mul]
      have hbd := drift_bound hB (κ i) hC t x
      have hk : |κ i| * C ≤ κbar * C := mul_le_mul_of_nonneg_right (hκb i) hC0
      exact mul_le_mul (h.bound h0 h1 i htw x) (hbd.trans (by linarith)) (abs_nonneg _) hK
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact h.tendsto_incK hb hκb hψ hψp (by linarith [ht.1])
  have heq : ∀ i, pairing (g i) ψ τ - pairing (g i) ψ σ = ∫ t in σ..τ, incK b (κ i) ψ (g i) t :=
    fun i => hinc i ψ hψ hψp σ hσ τ hτ hστ
  have hlim2' : Tendsto (fun i => pairing (g i) ψ τ - pairing (g i) ψ σ) atTop
      (𝓝 (∫ t in σ..τ, incK b 0 ψ θs t)) := by
    simp_rw [heq]; exact hlim2
  exact tendsto_nhds_unique hlim1 hlim2'

end LimData
end

/-! # The weak initial trace of the limit

`(u_i(a + t) - f_i, ψ)` is `O(t)` uniformly in `i` for smooth periodic `ψ`; this passes to the
limit and, by density and the `L²` bound, gives `u(a + t) ⇀ f_*` as `t ↓ 0`.
-/

/-- **Weak trace bound for a weak solution.** -/
theorem weak_trace_bound {b : ℝ → Vec 2 → Vec 2} {κ a T : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b)
    (h : IsWeakSolutionOnWith b κ a (a + T) f θ Dθ) {F : ℝ}
    (hl2 : ∀ t ∈ Icc a (a + T), l2NormSq (θ t) ≤ F ^ 2) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : IsZ2Periodic ψ) {W : ℝ}
    (hW : ∀ t x, |vecDot (b t x) (spaceGrad ψ x) + κ * lapl ψ x| ≤ W) {τ : ℝ} (hτ : a ≤ τ)
    (hτ2 : τ < a + T) :
    |pairing θ ψ τ - ∫ x in unitCube, f x * ψ x| ≤ (τ - a) * (W * ((1 + F ^ 2) / 2)) := by
  have h1 := weak_pairing_eq hb h hψ hψp hτ hτ2
  have hslice := h.1
  have hbd : ∀ s ∈ Set.uIoc a τ, ‖incK b κ ψ θ s‖ ≤ W * ((1 + F ^ 2) / 2) := by
    intro s hs
    have hs' : s ∈ Icc a (a + T) := by
      rw [Set.uIoc_of_le hτ] at hs
      exact ⟨hs.1.le, by linarith [hs.2]⟩
    rw [Real.norm_eq_abs]
    exact abs_integral_mul_le_l2 (hslice s hs').2 (fun x => hW s x) (hl2 s hs')
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hτ)] at h2
  rw [h1]
  have : (∫ x in unitCube, f x * ψ x) + (∫ t in a..τ, incK b κ ψ θ t) -
      ∫ x in unitCube, f x * ψ x = ∫ t in a..τ, incK b κ ψ θ t := by ring
  rw [this]
  linarith

/-- **Weak initial trace of the limit.** -/
theorem weak_trace_limit {a s F : ℝ} {Kc : ℝ → ℝ → ℝ} {κ : ℕ → ℝ} {g : ℕ → ℝ → Vec 2 → ℝ}
    {θs : ℝ → Vec 2 → ℝ} (h : LimData a s Kc κ g θs) (hs : 0 < s) (hF : 0 ≤ F)
    {f' : ℕ → Vec 2 → ℝ} {fstar : Vec 2 → ℝ} (hfs : MemL2On unitCube fstar)
    (hfsF : Real.sqrt (l2NormSq fstar) ≤ F)
    (hweak : ∀ g : Vec 2 → ℝ, MemL2On unitCube g →
      Tendsto (fun i => ∫ x in unitCube, f' i x * g x) atTop
        (𝓝 (∫ x in unitCube, fstar x * g x)))
    (hθl2 : ∀ t, a < t → l2NormSq (θs t) ≤ F ^ 2)
    (htr : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ → ∃ M : ℝ, ∀ i, ∀ t, a < t →
      |pairing (g i) ψ t - ∫ x in unitCube, f' i x * ψ x| ≤ (t - a) * M)
    (g0 : Vec 2 → ℝ) (hg0 : MemL2On unitCube g0) :
    Tendsto (fun t => ∫ x in unitCube, θs t x * g0 x) (𝓝[>] a)
      (𝓝 (∫ x in unitCube, fstar x * g0 x)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set η : ℝ := ε / (8 * (F + 1)) with hη
  have hη0 : 0 < η := by rw [hη]; positivity
  obtain ⟨ψ, hψs, hψp, hψ⟩ := exists_smooth_L2_approx hg0 (ε := η ^ 2) (by positivity)
  obtain ⟨M, hM⟩ := htr ψ hψs hψp
  have hψL : MemL2On unitCube ψ := memL2_continuous hψs.continuous
  have hdL : MemL2On unitCube (fun x => g0 x - ψ x) := hg0.sub hψL
  have hsq : Real.sqrt (l2NormSq (fun x => g0 x - ψ x)) < η := by
    rw [Real.sqrt_lt' hη0]; exact hψ
  have hM0 : 0 ≤ |M| := abs_nonneg M
  set r : ℝ := ε / (2 * (|M| + 1)) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  refine ⟨r, hr0, fun t ht hdist => ?_⟩
  have hta : a < t := ht
  have htr' : t - a < r := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.2 hta)] at hdist; exact hdist
  -- the smooth part
  have hsmooth : |(∫ x in unitCube, θs t x * ψ x) - ∫ x in unitCube, fstar x * ψ x| ≤
      (t - a) * M := by
    have h1 : Tendsto (fun i => pairing (g i) ψ t - ∫ x in unitCube, f' i x * ψ x) atTop
        (𝓝 (pairing θs ψ t - ∫ x in unitCube, fstar x * ψ x)) :=
      (h.tendsto_pairing hψs.continuous hψp hta).sub (hweak ψ hψL)
    have h2 := le_of_tendsto' h1.abs (fun i => hM i t hta)
    simpa [pairing] using h2
  -- the rough part
  have hθt : MemL2On unitCube (θs t) := memL2_continuous (h.theta_cont hs hta)
  have hc1 : |∫ x in unitCube, θs t x * (g0 x - ψ x)| ≤ F * η := by
    refine (abs_integral_mul_le_norms hθt hdL).trans ?_
    have : Real.sqrt (l2NormSq (θs t)) ≤ F := by
      rw [← Real.sqrt_sq hF]; exact Real.sqrt_le_sqrt (hθl2 t hta)
    exact mul_le_mul this hsq.le (Real.sqrt_nonneg _) hF
  have hc2 : |∫ x in unitCube, fstar x * (g0 x - ψ x)| ≤ F * η := by
    refine (abs_integral_mul_le_norms hfs hdL).trans ?_
    exact mul_le_mul hfsF hsq.le (Real.sqrt_nonneg _) hF
  have hsplit : (∫ x in unitCube, θs t x * g0 x) - ∫ x in unitCube, fstar x * g0 x =
      ((∫ x in unitCube, θs t x * ψ x) - ∫ x in unitCube, fstar x * ψ x) +
        (∫ x in unitCube, θs t x * (g0 x - ψ x)) - ∫ x in unitCube, fstar x * (g0 x - ψ x) := by
    have i1 := integrable_mul_memL2 hθt hψL
    have i2 := integrable_mul_memL2 hfs hψL
    have i3 := integrable_mul_memL2 hθt hdL
    have i4 := integrable_mul_memL2 hfs hdL
    have e1 : ∀ x, θs t x * g0 x = θs t x * ψ x + θs t x * (g0 x - ψ x) := fun x => by ring
    have e2 : ∀ x, fstar x * g0 x = fstar x * ψ x + fstar x * (g0 x - ψ x) := fun x => by ring
    simp_rw [e1, e2]
    rw [integral_add (f := fun x => θs t x * ψ x) (g := fun x => θs t x * (g0 x - ψ x)) i1 i3,
      integral_add (f := fun x => fstar x * ψ x) (g := fun x => fstar x * (g0 x - ψ x)) i2 i4]
    ring
  rw [Real.dist_eq, hsplit]
  have hFη : F * η ≤ ε / 8 := by
    rw [hη]
    have : F * (ε / (8 * (F + 1))) = ε / 8 * (F / (F + 1)) := by field_simp
    rw [this]
    have : F / (F + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith [hε]
  have htM : (t - a) * M ≤ ε / 2 := by
    calc (t - a) * M ≤ (t - a) * |M| := mul_le_mul_of_nonneg_left (le_abs_self M)
          (sub_pos.2 hta).le
      _ ≤ r * |M| := mul_le_mul_of_nonneg_right htr'.le hM0
      _ ≤ ε / 2 := by
          rw [hr]
          have : ε / (2 * (|M| + 1)) * |M| = ε / 2 * (|M| / (|M| + 1)) := by field_simp
          rw [this]
          have : |M| / (|M| + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          nlinarith [hε]
  set A := (∫ x in unitCube, θs t x * ψ x) - ∫ x in unitCube, fstar x * ψ x with hA
  set B := ∫ x in unitCube, θs t x * (g0 x - ψ x) with hB
  set C := ∫ x in unitCube, fstar x * (g0 x - ψ x) with hC
  calc |A + B - C| ≤ |A + B| + |C| := abs_sub _ _
    _ ≤ |A| + |B| + |C| := by gcongr; exact abs_add_le _ _
    _ < ε := by linarith

/-! # The distributional equation of the limit

Passing to the limit in the iterated weak form `∫_a^{a+T} ⟨u_i(t), ∂ₜφ̃ + b·∇φ̃ + κ_iΔφ̃⟩ dt = 0`
(`window_weak_iterated`), then unfolding the periodization of the test. -/

theorem weakOp_tendsto {a s : ℝ} {Kc : ℝ → ℝ → ℝ} {κ : ℕ → ℝ} {g : ℕ → ℝ → Vec 2 → ℝ}
    {θs : ℝ → Vec 2 → ℝ} (h : LimData a s Kc κ g θs) (b : ℝ → Vec 2 → Vec 2)
    (φ : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    Tendsto (fun i => weakOp b (κ i) φ t x) atTop (𝓝 (weakOp b 0 φ t x)) := by
  have := (tendsto_const_nhds (x := deriv (fun s => φ s x) t + vecDot (b t x) (spaceGrad (φ t) x))).add
    (h.κlim.mul_const (lapl (φ t) x))
  simpa [weakOp] using this

theorem tendsto_weak_integral {a s : ℝ} {Kc : ℝ → ℝ → ℝ} {κ : ℕ → ℝ} {g : ℕ → ℝ → Vec 2 → ℝ}
    {θs : ℝ → Vec 2 → ℝ} (h : LimData a s Kc κ g θs) {b : ℝ → Vec 2 → Vec 2}
    (hb : IsContDrift b) {κbar : ℝ} (hκb : ∀ i, |κ i| ≤ κbar) {t₂ : ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsWindowTestFunction t₂ φ) {t₀ T₀ : ℝ} (h0 : 0 < t₀) (h1 : t₀ < T₀)
    (hT : a + T₀ ≤ t₂) :
    Tendsto (fun i => ∫ t in Icc (a + t₀) (a + T₀), ∫ x in unitCube,
        g i t x * weakOp b (κ i) φ t x) atTop
      (𝓝 (∫ t in Icc (a + t₀) (a + T₀), ∫ x in unitCube, θs t x * weakOp b 0 φ t x)) := by
  obtain ⟨hWc, C₀, C₁, hC₀, hC₁, hWb⟩ := weakOp_regular hb hφ (a + t₀)
  have hK : 0 ≤ Kc t₀ T₀ :=
    csNormLe_K_nonneg (h.cs 0 t₀ T₀ h0 h1 (a + t₀) ⟨le_rfl, by linarith⟩)
  have hκ0 : 0 ≤ κbar := (abs_nonneg _).trans (hκb 0)
  have hwin : ∀ t ∈ Icc (a + t₀) (a + T₀), a < t := fun t ht => by linarith [ht.1]
  have hWbd : ∀ i, ∀ t ∈ Icc (a + t₀) (a + T₀), ∀ x,
      |weakOp b (κ i) φ t x| ≤ C₀ + κbar * C₁ := fun i t ht x =>
    (hWb (κ i) t ⟨ht.1, ht.2.trans hT⟩ x).trans
      (by have := mul_le_mul_of_nonneg_right (hκb i) hC₁; linarith)
  set M : ℝ := Kc t₀ T₀ * (C₀ + κbar * C₁) with hM
  have hFbd : ∀ i, ∀ t ∈ Icc (a + t₀) (a + T₀), ∀ x,
      |g i t x * weakOp b (κ i) φ t x| ≤ M := fun i t ht x => by
    rw [abs_mul]
    exact mul_le_mul (h.bound h0 h1 i ht x) (hWbd i t ht x) (abs_nonneg _) hK
  have hWslice : ∀ κ' t, Continuous (fun x => weakOp b κ' φ t x) := fun κ' t =>
    (hWc κ').comp (continuous_const.prodMk continuous_id)
  have hWt : ∀ κ' x, Continuous (fun t => weakOp b κ' φ t x) := fun κ' x =>
    (hWc κ').comp (continuous_id.prodMk continuous_const)
  have hcont : ∀ i, ContinuousOn (fun t => ∫ x in unitCube, g i t x * weakOp b (κ i) φ t x)
      (Icc (a + t₀) (a + T₀)) := by
    intro i
    refine continuousOn_of_dominated (bound := fun _ => M)
      (fun t ht => ((h.cont i t (hwin t ht)).mul (hWslice _ t)).aestronglyMeasurable)
      (fun t ht => Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hFbd i t ht x)
      (integrable_const M) (Eventually.of_forall fun x => ?_)
    exact ((h.tcont i x).mono hwin).mul (hWt _ x).continuousOn
  refine tendsto_integral_of_dominated_convergence (μ := volume.restrict (Icc (a + t₀) (a + T₀)))
    (fun _ => M) (fun i => (hcont i).aestronglyMeasurable measurableSet_Icc)
    (integrable_const M) (fun i => ?_) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs]
    exact abs_integral_cube_le (hFbd i t ht)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    refine tendsto_cube_integral (M := M) (fun i => ?_) (fun i x => hFbd i t ht x)
      (fun x => (h.conv t (hwin t ht) x).mul (weakOp_tendsto h b φ t x))
    exact ((h.cont i t (hwin t ht)).mul (hWslice _ t)).aestronglyMeasurable

theorem isClosedEmbedding_slice (σ : ℝ) :
    Topology.IsClosedEmbedding (fun z : Vec 2 => (σ, z)) :=
  Function.LeftInverse.isClosedEmbedding (f := Prod.snd) (g := fun z : Vec 2 => (σ, z))
    (fun _ => rfl) continuous_snd (by fun_prop)

/-- Slices of derivatives of a compactly supported smooth test are smooth with compact support. -/
theorem slice_fderiv_test {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (v : ℝ × Vec 2) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => fderiv ℝ φ (t, x) v) ∧
      HasCompactSupport (fun x : Vec 2 => fderiv ℝ φ (t, x) v) := by
  refine ⟨(contDiff_fderiv_apply_of_smooth hφ v).comp (contDiff_const.prodMk contDiff_id), ?_⟩
  exact (hasCompactSupport_fderiv_apply hc v).comp_isClosedEmbedding (isClosedEmbedding_slice t)

theorem perX_fderiv_time {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (t : ℝ) (x : Vec 2) :
    deriv (fun s => perTest φ s x) t = perX (fun y => fderiv ℝ φ (t, y) (1, 0)) x := by
  obtain ⟨R, hR⟩ := exists_supBdd_of_hasCompactSupport hc
  have := perST_deriv_time (ρ := slc φ) hR hφ t x
  unfold perTest
  rw [this]
  have e : (fun s y => deriv (fun r => slc φ r y) s) = fun s y => fderiv ℝ φ (s, y) (1, 0) :=
    funext fun s => funext fun y => deriv_slc_eq hφ s y
  rw [e]
  rfl

theorem perX_fderiv_space {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (t : ℝ) (x : Vec 2) (j : Fin 2) :
    spaceGrad (perTest φ t) x j = perX (fun y => fderiv ℝ φ (t, y) (0, basisVec j)) x := by
  obtain ⟨R, hR⟩ := exists_supBdd_of_hasCompactSupport hc
  have := spaceGrad_perST (ρ := slc φ) hR hφ t x j
  unfold perTest
  rw [this]
  have e : (fun s y => spaceGrad (slc φ s) y j) = fun s y => fderiv ℝ φ (s, y) (0, basisVec j) :=
    funext fun s => funext fun y => spaceGrad_slc_eq hφ s y j
  rw [e]
  rfl

/-- Spatial unfolding of the transport pairing against a compactly supported test. -/
theorem slice_unfold {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    {b : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b) {U : Vec 2 → ℝ} (hUc : Continuous U)
    (hUp : IsZ2Periodic U) (t : ℝ) :
    ∫ x, U x * (fderiv ℝ φ (t, x) (1, 0) +
        ∑ j : Fin 2, b t x j * fderiv ℝ φ (t, x) (0, basisVec j)) =
      ∫ x in unitCube, U x * weakOp b 0 (perTest φ) t x := by
  have hbi : ∀ j : Fin 2, Continuous fun x => b t x j := fun j =>
    (continuous_apply j).comp (hb.slice_continuous t)
  obtain ⟨hs0, hc0⟩ := slice_fderiv_test hφ hc (1, 0) t
  have hsj : ∀ j : Fin 2, _ := fun j => slice_fderiv_test hφ hc (0, basisVec j) t
  -- unfolding of each term
  have u0 : ∫ x, U x * fderiv ℝ φ (t, x) (1, 0) =
      ∫ x in unitCube, U x * perX (fun y => fderiv ℝ φ (t, y) (1, 0)) x :=
    integral_unfold_space hs0 hc0 hUp (integrableOn_cube_of_continuous hUc)
  have uj : ∀ j : Fin 2, ∫ x, (U x * b t x j) * fderiv ℝ φ (t, x) (0, basisVec j) =
      ∫ x in unitCube, (U x * b t x j) *
        perX (fun y => fderiv ℝ φ (t, y) (0, basisVec j)) x := fun j =>
    integral_unfold_space (hsj j).1 (hsj j).2 (fun n x => by simp [hUp n x, hb.periodic t n x])
      (integrableOn_cube_of_continuous (hUc.mul (hbi j)))
  -- integrability on the plane
  have i0 : Integrable (fun x => U x * fderiv ℝ φ (t, x) (1, 0)) :=
    (hUc.mul hs0.continuous).integrable_of_hasCompactSupport hc0.mul_left
  have ij : ∀ j : Fin 2, Integrable (fun x => (U x * b t x j) * fderiv ℝ φ (t, x) (0, basisVec j)) :=
    fun j => ((hUc.mul (hbi j)).mul (hsj j).1.continuous).integrable_of_hasCompactSupport
      (hsj j).2.mul_left
  -- the left side
  have hL : ∫ x, U x * (fderiv ℝ φ (t, x) (1, 0) +
        ∑ j : Fin 2, b t x j * fderiv ℝ φ (t, x) (0, basisVec j)) =
      (∫ x, U x * fderiv ℝ φ (t, x) (1, 0)) +
        ∑ j : Fin 2, ∫ x, (U x * b t x j) * fderiv ℝ φ (t, x) (0, basisVec j) := by
    rw [← integral_finsetSum _ fun j _ => ij j,
      ← integral_add i0 (integrable_finsetSum _ fun j _ => ij j)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Fin.sum_univ_two]; ring
  -- the right side
  have hR : ∫ x in unitCube, U x * weakOp b 0 (perTest φ) t x =
      (∫ x in unitCube, U x * perX (fun y => fderiv ℝ φ (t, y) (1, 0)) x) +
        ∑ j : Fin 2, ∫ x in unitCube, (U x * b t x j) *
          perX (fun y => fderiv ℝ φ (t, y) (0, basisVec j)) x := by
    have pc0 : Continuous (perX (fun y => fderiv ℝ φ (t, y) (1, 0))) :=
      (perX_contDiff hs0 hc0).continuous
    have pcj : ∀ j : Fin 2, Continuous
        (perX (fun y => fderiv ℝ φ (t, y) (0, basisVec j))) := fun j =>
      (perX_contDiff (hsj j).1 (hsj j).2).continuous
    have j0 : Integrable (fun x => U x * perX (fun y => fderiv ℝ φ (t, y) (1, 0)) x)
        (volume.restrict unitCube) := integrableOn_cube_of_continuous (hUc.mul pc0)
    have jj : ∀ j : Fin 2, Integrable (fun x => (U x * b t x j) *
        perX (fun y => fderiv ℝ φ (t, y) (0, basisVec j)) x) (volume.restrict unitCube) :=
      fun j => integrableOn_cube_of_continuous ((hUc.mul (hbi j)).mul (pcj j))
    rw [← integral_finsetSum _ fun j _ => jj j,
      ← integral_add j0 (integrable_finsetSum _ fun j _ => jj j)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [weakOp, vecDot, Fin.sum_univ_two, zero_mul, add_zero,
      perX_fderiv_time hφ hc t x, perX_fderiv_space hφ hc t x]
    ring
  rw [hL, hR, u0]
  congr 1
  exact Finset.sum_congr rfl fun j _ => uj j

/-- **The distributional equation from the iterated identity.** -/
theorem dist_eq_of_iterated {a : ℝ} {u : ℝ → Vec 2 → ℝ} {b : ℝ → Vec 2 → Vec 2}
    (hb : IsContDrift b)
    (ucont : ContinuousOn (fun p : ℝ × Vec 2 => u p.1 p.2) (Set.Ioi a ×ˢ Set.univ))
    (uper : ∀ t, a < t → IsZ2Periodic (u t)) {φ : ℝ × Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hts : tsupport φ ⊆ Set.Ioi a ×ˢ Set.univ) {t₀ T₀ : ℝ}
    (hz : ∀ t x, (t < a + t₀ ∨ a + T₀ < t) → φ (t, x) = 0) (h0 : 0 < t₀)
    (hid : ∫ t in Icc (a + t₀) (a + T₀), ∫ x in unitCube,
      u t x * weakOp b 0 (perTest φ) t x = 0) :
    ∫ p : ℝ × Vec 2, u p.1 p.2 * (fderiv ℝ φ p (1, 0) +
      ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j)) = 0 := by
  set Φ : ℝ × Vec 2 → ℝ := fun p => u p.1 p.2 * (fderiv ℝ φ p (1, 0) +
      ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j)) with hΦ
  have hvan : ∀ p, p ∉ tsupport φ → Φ p = 0 := fun p hp => by
    simp [hΦ, fderiv_of_notMem_tsupport (𝕜 := ℝ) hp]
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hbi : ∀ j : Fin 2, Continuous fun p : ℝ × Vec 2 => b p.1 p.2 j := fun j =>
    (continuous_apply j).comp hb.continuous
  have hdf : ∀ v : ℝ × Vec 2, Continuous fun p => fderiv ℝ φ p v := fun v =>
    (hφ1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hΦc : ContinuousOn Φ (Set.Ioi a ×ˢ Set.univ) := by
    refine ucont.mul (Continuous.continuousOn ?_)
    exact (hdf (1, 0)).add (continuous_finsetSum _ fun j _ => (hbi j).mul (hdf _))
  have hΦint : Integrable Φ := by
    have hK : IntegrableOn Φ (tsupport φ) :=
      (hΦc.mono hts).integrableOn_compact hc.isCompact
    exact hK.integrable_of_forall_notMem_eq_zero hvan
  have hΦint' : Integrable Φ (volume.prod volume) := by
    rwa [← Measure.volume_eq_prod]
  have hit : ∫ p, Φ p = ∫ t, ∫ x, Φ (t, x) := by
    rw [Measure.volume_eq_prod, integral_prod _ hΦint']
  -- slicewise identification
  have hslice : ∀ t, ∫ x, Φ (t, x) =
      ∫ x in unitCube, u t x * weakOp b 0 (perTest φ) t x := by
    intro t
    by_cases hta : a < t
    · have hUc : Continuous (u t) := by
        have hem : Continuous fun x : Vec 2 => ((t, x) : ℝ × Vec 2) :=
          continuous_const.prodMk continuous_id
        have := ucont.comp (hem.continuousOn (s := (Set.univ : Set (Vec 2))))
          (fun x _ => ⟨hta, trivial⟩)
        rwa [← continuousOn_univ]
      exact slice_unfold hφ hc hb hUc (uper t hta) t
    · push Not at hta
      have h1 : ∀ x, Φ (t, x) = 0 := fun x => hvan _ (fun hx => by
        have := (hts hx).1
        simp only [Set.mem_Ioi] at this; linarith)
      have h2 : ∀ x, weakOp b 0 (perTest φ) t x = 0 := fun x =>
        weakOp_perTest_eq_zero hz b 0 (Or.inl (by linarith)) x
      simp [h1, h2]
  simp_rw [hslice] at hit
  rw [hit]
  have e := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (s := Icc (a + t₀) (a + T₀))
    (f := fun t => ∫ x in unitCube, u t x * weakOp b 0 (perTest φ) t x) (fun t ht => by
      have : t < a + t₀ ∨ a + T₀ < t := by
        by_contra hcon
        push Not at hcon
        exact ht ⟨hcon.1, hcon.2⟩
      simp [weakOp_perTest_eq_zero hz b 0 this])
  rw [← e]
  exact hid

/-! # Pairing identities for continuous representatives

If `Θ(t) = θ(t)` a.e. on the cube for `t > a`, the pairing identity of the weak solution `θ`
(`weak_pairing_increment`) holds for `Θ` on `(a, ∞)`. -/

theorem pairing_congr {U V : ℝ → Vec 2 → ℝ} {ψ : Vec 2 → ℝ} {t : ℝ}
    (h : U t =ᵐ[volume.restrict unitCube] V t) : pairing U ψ t = pairing V ψ t :=
  integral_congr_ae (h.mono fun x hx => by simp [hx])

theorem incK_congr {U V : ℝ → Vec 2 → ℝ} {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {ψ : Vec 2 → ℝ} {t : ℝ}
    (h : U t =ᵐ[volume.restrict unitCube] V t) : incK b κ ψ U t = incK b κ ψ V t :=
  integral_congr_ae (h.mono fun x hx => by simp [hx])

theorem incIdent_of_weak {b : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b) {κ a : ℝ} {f : Vec 2 → ℝ}
    {θ Θ : ℝ → Vec 2 → ℝ}
    (hT : ∀ T : ℝ, 0 < T → IsWeakSolutionOn b κ a (a + T) f θ)
    (hΘ : ∀ t, a < t → Θ t =ᵐ[volume.restrict unitCube] θ t) :
    IncIdent b κ Θ (Ioi a) ∧ ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      ∀ σ τ : ℝ, a < σ → σ ≤ τ → IntervalIntegrable (incK b κ ψ Θ) volume σ τ := by
  constructor
  · intro ψ hψ hψp σ hσ τ hτ hστ
    have hσa : a < σ := hσ
    have hτa : a < τ := hτ
    obtain ⟨Dθ, hD⟩ := hT (τ - a + 1) (by linarith)
    have h1 := weak_pairing_increment hb hD hψ hψp hσa.le hστ (by linarith)
    rw [pairing_congr (hΘ τ hτa), pairing_congr (hΘ σ hσa)]
    rw [h1]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : a < t := by
      rw [Set.uIcc_of_le hστ] at ht; linarith [ht.1]
    exact (incK_congr (hΘ t ht')).symm
  · intro ψ hψ hψp σ τ hσ hστ
    obtain ⟨Dθ, hD⟩ := hT (τ - a + 1) (by linarith)
    have h1 := intervalIntegrable_incK hb hD hψ hψp hσ.le hστ (by linarith)
    refine h1.congr fun t ht => ?_
    have ht' : a < t := by
      rw [Set.uIoc_of_le hστ] at ht; linarith [ht.1]
    exact (incK_congr (hΘ t ht')).symm

/-! # Pairing the difference of two solutions with a test function

If two weak solutions on `[a, a + T₀ + 1]` differ by at most `E` in `L²(𝕋²)` at every time, then
their difference tested against `φ ∈ C_c^∞((a,∞) × ℝ²)` is at most `E·C_φ` with `C_φ` depending
only on `φ`. -/

theorem exists_test_constant {a : ℝ} {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) {t₀ T₀ : ℝ}
    (hz : ∀ t x, (t < a + t₀ ∨ a + T₀ < t) → φ (t, x) = 0) (h0 : 0 < t₀) (h1 : t₀ < T₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u v : ℝ → Vec 2 → ℝ) (b₁ b₂ : ℝ → Vec 2 → Vec 2) (κ₁ κ₂ : ℝ)
      (f₁ f₂ : Vec 2 → ℝ) (E : ℝ), 0 ≤ E →
      IsWeakSolutionOn b₁ κ₁ a (a + (T₀ + 1)) f₁ u →
      IsWeakSolutionOn b₂ κ₂ a (a + (T₀ + 1)) f₂ v →
      (∀ t ∈ Icc a (a + (T₀ + 1)), l2NormSq (fun x => u t x - v t x) ≤ E ^ 2) →
      |∫ p : ℝ × Vec 2, (u p.1 p.2 - v p.1 p.2) * φ p| ≤ E * C := by
  have hT0 : 0 < T₀ := by linarith
  have hwin : IsWindowTestFunction (a + (T₀ + 1)) (perTest φ) := by
    have := perTest_window hφ hc hz
    rwa [← add_assoc]
  obtain ⟨-, -, -, C₀, hC₀⟩ := window_test_regular hwin a
  set C₁ : ℝ := max C₀ 0 with hC₁
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  refine ⟨C₁ * (T₀ + 1), by positivity, ?_⟩
  intro u v b₁ b₂ κ₁ κ₂ f₁ f₂ E hE hu hv hl2
  obtain ⟨Du, hu1⟩ := hu
  obtain ⟨Dv, hv1⟩ := hv
  set S : Set ℝ := Set.Ioo a (a + (T₀ + 1)) with hS
  have hSm : MeasurableSet S := measurableSet_Ioo
  have hslu := hu1.1
  have hslv := hv1.1
  have hint : Integrable (fun p : ℝ × Vec 2 => u p.1 p.2 - v p.1 p.2)
      (volume.restrict (S ×ˢ unitCube)) :=
    (memLp_two_integrable_window hu1.2.2.1).sub (memLp_two_integrable_window hv1.2.2.1)
  have hper : ∀ᵐ t ∂(volume.restrict S), IsZ2Periodic (fun x => u t x - v t x) := by
    filter_upwards [ae_restrict_mem hSm] with t ht n x
    have := (hslu t ⟨ht.1.le, ht.2.le⟩).1 n x
    have := (hslv t ⟨ht.1.le, ht.2.le⟩).1 n x
    simp only [*]
  obtain ⟨-, hint2, heq⟩ := integral_unfold_cs (S := S) (G := fun t x => u t x - v t x) hSm hφ hc
    hper hint
  -- the whole-space integral is the integral over `S × ℝ²`
  have hwhole : ∫ p : ℝ × Vec 2, (u p.1 p.2 - v p.1 p.2) * φ p =
      ∫ p in S ×ˢ (Set.univ : Set (Vec 2)), (u p.1 p.2 - v p.1 p.2) * φ p := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
    have : p.1 < a + t₀ ∨ a + T₀ < p.1 := by
      by_contra hcon
      push Not at hcon
      exact hp ⟨⟨by linarith [hcon.1], by linarith [hcon.2]⟩, trivial⟩
    have hp0 : φ p = 0 := by
      have := hz p.1 p.2 this
      simpa using this
    simp [hp0]
  rw [hwhole, heq]
  -- iterate
  have hint2' : Integrable (fun p : ℝ × Vec 2 => (u p.1 p.2 - v p.1 p.2) *
      perST (slc φ) p.1 p.2) ((volume.restrict S).prod (volume.restrict unitCube)) := by
    rwa [← volume_restrict_prod_eq]
  have hit : ∫ p in S ×ˢ unitCube, (u p.1 p.2 - v p.1 p.2) * perST (slc φ) p.1 p.2 =
      ∫ t in S, ∫ x in unitCube, (u t x - v t x) * perST (slc φ) t x := by
    rw [volume_restrict_prod_eq, integral_prod _ hint2']
  rw [hit]
  have hbd : ∀ t ∈ S, ‖∫ x in unitCube, (u t x - v t x) * perST (slc φ) t x‖ ≤ E * C₁ := by
    intro t ht
    have htI : t ∈ Icc a (a + (T₀ + 1)) := ⟨ht.1.le, ht.2.le⟩
    have hDL : MemL2On unitCube (fun x => u t x - v t x) := (hslu t htI).2.sub (hslv t htI).2
    have hφL : MemL2On unitCube (perTest φ t) := by
      refine memL2_continuous ?_
      exact (perST_slc_contDiff hφ hc).continuous.comp (continuous_const.prodMk continuous_id)
    have hφb : ∀ x, |perTest φ t x| ≤ C₁ := fun x => (hC₀ t htI x).1.trans (le_max_left _ _)
    have h1 := abs_integral_mul_le_norms hDL hφL
    have h2 : Real.sqrt (l2NormSq (fun x => u t x - v t x)) ≤ E := by
      rw [← Real.sqrt_sq hE]; exact Real.sqrt_le_sqrt (hl2 t htI)
    have h3 : Real.sqrt (l2NormSq (perTest φ t)) ≤ C₁ := by
      rw [← Real.sqrt_sq hC₁0]
      refine Real.sqrt_le_sqrt ?_
      have := abs_integral_cube_le (g := fun x => perTest φ t x ^ 2) (M := C₁ ^ 2) (fun x => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb x) 2)
      exact (le_abs_self _).trans this
    rw [Real.norm_eq_abs]
    exact h1.trans (mul_le_mul h2 h3 (Real.sqrt_nonneg _) hE)
  have hvol : volume S < ⊤ := by simp [hS, Real.volume_Ioo]
  have := norm_setIntegral_le_of_norm_le_const_ae' (μ := volume) hvol
    (f := fun t => ∫ x in unitCube, (u t x - v t x) * perST (slc φ) t x)
    (Eventually.of_forall hbd)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  have hr : (volume : Measure ℝ).real S = T₀ + 1 := by
    simp [hS, Measure.real, Real.volume_Ioo]
    linarith
  rw [hr]; ring

/-! # The compactness core of the vanishing-diffusivity limits

Given weak solutions `θ_i` with diffusivities `κ_i → 0`, `L²` data bounded by `F`, and the uniform
`C^s` bounds `K(t₀, T)` on windows, a subsequence converges locally uniformly on `(a, ∞) × ℝ²`
to a transport solution with the stated properties (Corollary D(a) of the paper). -/

theorem limits_core {α s : ℝ} (hα : 0 < α) (hs : 0 < s) {b : ℝ → Vec 2 → Vec 2}
    (hbH : IsHolderDivFreeVelocity α b) (a F : ℝ) (hF : 0 ≤ F) (Kc : ℝ → ℝ → ℝ)
    (κ : ℕ → ℝ) (hκpos : ∀ i, 0 < κ i) (hκ : Tendsto κ atTop (𝓝 0))
    (f : ℕ → Vec 2 → ℝ) (hf : ∀ i, MemL2On unitCube (f i) ∧ Real.sqrt (l2NormSq (f i)) ≤ F)
    (θ : ℕ → ℝ → Vec 2 → ℝ)
    (hθ : ∀ i, ∀ T : ℝ, 0 < T → IsWeakSolutionOn b (κ i) a (a + T) (f i) (θ i))
    (hrep : ∀ i, ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ Θ : ℝ → Vec 2 → ℝ,
      ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
      ∀ t ∈ Set.Icc (a + t₀) (a + T), IsZ2Periodic (Θ t) ∧
        Θ t =ᵐ[volume.restrict unitCube] θ i t ∧ CsNormLe s (Θ t) (Kc t₀ T)) :
    ∃ (σ : ℕ → ℕ) (fstar : Vec 2 → ℝ) (Θ : ℕ → ℝ → Vec 2 → ℝ) (θstar : ℝ → Vec 2 → ℝ),
      StrictMono σ ∧ MemL2On unitCube fstar ∧
      (∀ g : Vec 2 → ℝ, MemL2On unitCube g →
        Tendsto (fun i => ∫ x in unitCube, f (σ i) x * g x) atTop
          (𝓝 (∫ x in unitCube, fstar x * g x))) ∧
      (∀ i, ContinuousOn (fun p : ℝ × Vec 2 => Θ i p.1 p.2) (Set.Ioi a ×ˢ Set.univ) ∧
        ∀ t, a < t → IsZ2Periodic (Θ i t) ∧ Θ i t =ᵐ[volume.restrict unitCube] θ i t) ∧
      TendstoLocallyUniformlyOn (fun i (p : ℝ × Vec 2) => Θ (σ i) p.1 p.2)
        (fun p : ℝ × Vec 2 => θstar p.1 p.2) atTop (Set.Ioi a ×ˢ Set.univ) ∧
      (∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Set.Ioi a ×ˢ Set.univ →
        ∫ p, θstar p.1 p.2 * (fderiv ℝ φ p (1, 0) +
          ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j)) = 0) ∧
      (∀ g : Vec 2 → ℝ, MemL2On unitCube g →
        Tendsto (fun t => ∫ x in unitCube, θstar t x * g x) (𝓝[>] a)
          (𝓝 (∫ x in unitCube, fstar x * g x))) ∧
      (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∀ t ∈ Set.Icc (a + t₀) (a + T),
        IsZ2Periodic (θstar t) ∧ CsNormLe s (θstar t) (Kc t₀ T)) ∧
      (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C' : ℝ,
        ∀ t ∈ Set.Icc (a + t₀) (a + T), ∀ t' ∈ Set.Icc (a + t₀) (a + T), ∀ x : Vec 2,
          |θstar t x - θstar t' x| ≤ C' * |t - t'| ^ (s / (1 + s))) := by
  have hb := isContDrift_of_holder hα hbH
  obtain ⟨B, hB0, hB⟩ := hb.bounded
  have hBj : ∀ t y (j : Fin 2), |b t y j| ≤ B := fun t y j => by
    simpa using (norm_le_pi_norm (b t y) j).trans (hB t y)
  -- Step 1: glue the representatives
  have hrep' : ∀ i, ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ Θ : ℝ → Vec 2 → ℝ,
      ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
      ∀ t ∈ Set.Icc (a + t₀) (a + T), IsZ2Periodic (Θ t) ∧
        Θ t =ᵐ[volume.restrict unitCube] θ i t := by
    intro i t₀ T h0 h1
    obtain ⟨Θ, hc, h⟩ := hrep i t₀ T h0 h1
    exact ⟨Θ, hc, fun t ht => ⟨(h t ht).1, (h t ht).2.1⟩⟩
  choose Θ hΘc hΘ using fun i => glue_reps (hrep' i)
  -- Step 2: the `C^s` bounds for the glued representatives
  have hCs : ∀ i, ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∀ t ∈ Set.Icc (a + t₀) (a + T),
      CsNormLe s (Θ i t) (Kc t₀ T) := by
    intro i t₀ T h0 h1 t ht
    obtain ⟨Θ', -, h'⟩ := hrep i t₀ T h0 h1
    obtain ⟨hp', hae', hcs'⟩ := h' t ht
    have hta : a < t := by linarith [ht.1]
    obtain ⟨hp, hae, hcont⟩ := hΘ i t hta
    have hc'' : Continuous (Θ' t) := continuous_of_csNormLe hs hcs'
    have : Θ i t = Θ' t := eq_of_ae_eq_cube hcont hc'' hp hp' (hae.trans hae'.symm)
    rw [this]; exact hcs'
  -- Step 3: the `L²` bound
  have hl2f : ∀ i, l2NormSq (f i) ≤ F ^ 2 := fun i => by
    have h := (hf i).2
    rw [← Real.sqrt_sq hF] at h
    exact (Real.sqrt_le_sqrt_iff (sq_nonneg _)).1 h
  have hl2 : ∀ i t, a < t → l2NormSq (Θ i t) ≤ F ^ 2 := by
    intro i t hta
    obtain ⟨hlt, -⟩ := l2NormSq_le_of_isHolderDivFreeVelocity hα hbH (hκpos i)
      (show a < a + (t - a + 1) by linarith) (hf i).1 (hθ i (t - a + 1) (by linarith))
    have h1 := hlt t ⟨hta.le, by linarith⟩
    have h2 : l2NormSq (Θ i t) = l2NormSq (θ i t) :=
      integral_congr_ae ((hΘ i t hta).2.1.mono fun x hx => by simp [hx])
    linarith [hl2f i]
  -- Step 4: the pairing identities
  have hinc : ∀ i, IncIdent b (κ i) (Θ i) (Set.Ioi a) ∧ ∀ ψ : Vec 2 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ → ∀ σ τ : ℝ, a < σ → σ ≤ τ →
        IntervalIntegrable (incK b (κ i) ψ (Θ i)) volume σ τ := fun i =>
    incIdent_of_weak hb (hθ i) (fun t ht => (hΘ i t ht).2.1)
  -- Step 5: weak compactness
  obtain ⟨σ₁, hσ₁, fstar, hfs, hfsF, hweak₁⟩ := exists_weak_subseq f hf
  -- Step 6: Arzelà–Ascoli
  obtain ⟨κbar, hκbar⟩ : ∃ κbar : ℝ, ∀ i, κ i ≤ κbar := by
    obtain ⟨M, hM⟩ := hκ.bddAbove_range
    exact ⟨M, fun i => hM ⟨i, rfl⟩⟩
  have hκbar0 : 0 ≤ κbar := (hκpos 0).le.trans (hκbar 0)
  obtain ⟨hbd, hequi⟩ := equi_of_data (a := a) (s := s) (B := B) (κbar := κbar) hs
    (b := b) (fun t => hb.slice_continuous t) hb.periodic hBj (κ := fun i => κ (σ₁ i))
    (fun i => (hκpos _).le) (fun i => hκbar _) (g := fun i => Θ (σ₁ i))
    (fun i t ht => (hΘ _ t ht).2.2) (fun i t ht => (hΘ _ t ht).1) (Kc := Kc)
    (fun i => hCs (σ₁ i)) (fun i => (hinc (σ₁ i)).1)
  obtain ⟨σ₂, hσ₂, θstar, hθcont, hconv⟩ := exists_locally_uniform_subseq
    (g := fun i => Θ (σ₁ i)) (fun n => hΘc (σ₁ n)) hbd hequi
  set σ : ℕ → ℕ := fun i => σ₁ (σ₂ i) with hσdef
  have hσ : StrictMono σ := hσ₁.comp hσ₂
  -- Step 7: the limit data
  have hLim : LimData a s Kc (fun i => κ (σ i)) (fun i => Θ (σ i)) θstar :=
    { conv := fun t ht x => hconv.tendsto_at
        (show ((t, x) : ℝ × Vec 2) ∈ Set.Ioi a ×ˢ (Set.univ : Set (Vec 2)) from ⟨ht, trivial⟩)
      cs := fun i t₀ T h0 h1 t ht => hCs (σ i) t₀ T h0 h1 t ht
      per := fun i t ht => (hΘ (σ i) t ht).1
      cont := fun i t ht => (hΘ (σ i) t ht).2.2
      jcont := fun i => hΘc (σ i)
      κlim := hκ.comp hσ.tendsto_atTop }
  have hκb : ∀ i, |κ (σ i)| ≤ κbar := fun i => by
    rw [abs_of_pos (hκpos _)]; exact hκbar _
  have hIncσ : ∀ i, IncIdent b (κ (σ i)) (Θ (σ i)) (Set.Ioi a) := fun i => (hinc (σ i)).1
  have hIncLim : IncIdent b 0 θstar (Set.Ioi a) :=
    hLim.incIdent_limit hb hκb hIncσ (fun i => (hinc (σ i)).2)
  refine ⟨σ, fstar, Θ, θstar, hσ, hfs, fun g hg => (hweak₁ g hg).comp hσ₂.tendsto_atTop,
    fun i => ⟨hΘc i, fun t ht => ⟨(hΘ i t ht).1, (hΘ i t ht).2.1⟩⟩, hconv, ?_, ?_, ?_, ?_⟩
  · -- the distributional equation
    intro φ hφ hc hts
    obtain ⟨t₀, T₀, h0, h1, hz⟩ := exists_test_window hc hts
    have hwin : IsWindowTestFunction (a + (T₀ + 1)) (perTest φ) := by
      have := perTest_window hφ hc hz
      rwa [← add_assoc]
    have hid : ∀ i, ∫ t in Set.Icc (a + t₀) (a + T₀), ∫ x in unitCube,
        Θ i t x * weakOp b (κ i) (perTest φ) t x = 0 := by
      intro i
      obtain ⟨Dθ, hD⟩ := hθ i (T₀ + 1) (by linarith)
      have hw := window_weak_iterated hb hD hwin
      have hr : ∫ x in unitCube, f i x * perTest φ a x = 0 := by
        have : ∀ x, perTest φ a x = 0 := fun x => perTest_eq_zero hz (Or.inl (by linarith)) x
        simp [this]
      rw [hr, neg_zero] at hw
      have hΘw : ∀ t ∈ Set.Ioo a (a + (T₀ + 1)), ∫ x in unitCube,
          Θ i t x * weakOp b (κ i) (perTest φ) t x =
          ∫ x in unitCube, θ i t x * weakOp b (κ i) (perTest φ) t x := fun t ht =>
        integral_congr_ae (((hΘ i t ht.1).2.1).mono fun x hx => by simp [hx])
      have e1 := setIntegral_congr_fun (μ := volume) measurableSet_Ioo hΘw
      have hsupp : ∀ t, t ∉ Set.Icc (a + t₀) (a + T₀) → ∫ x in unitCube,
          Θ i t x * weakOp b (κ i) (perTest φ) t x = 0 := by
        intro t ht
        have : t < a + t₀ ∨ a + T₀ < t := by
          by_contra hcon; push Not at hcon; exact ht ⟨hcon.1, hcon.2⟩
        simp [weakOp_perTest_eq_zero hz b (κ i) this]
      have hsupp' : ∀ t, t ∉ Set.Ioo a (a + (T₀ + 1)) → ∫ x in unitCube,
          Θ i t x * weakOp b (κ i) (perTest φ) t x = 0 := by
        intro t ht; apply hsupp; intro hI; apply ht
        exact ⟨by linarith [hI.1], by linarith [hI.2]⟩
      calc ∫ t in Set.Icc (a + t₀) (a + T₀), ∫ x in unitCube,
            Θ i t x * weakOp b (κ i) (perTest φ) t x
          = ∫ t, ∫ x in unitCube, Θ i t x * weakOp b (κ i) (perTest φ) t x :=
            setIntegral_eq_integral_of_forall_compl_eq_zero hsupp
        _ = ∫ t in Set.Ioo a (a + (T₀ + 1)), ∫ x in unitCube,
            Θ i t x * weakOp b (κ i) (perTest φ) t x :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp').symm
        _ = ∫ t in Set.Ioo a (a + (T₀ + 1)), ∫ x in unitCube,
            θ i t x * weakOp b (κ i) (perTest φ) t x := e1
        _ = 0 := hw
    have hlim := tendsto_weak_integral hLim hb (κbar := κbar) hκb hwin h0 h1
      (by linarith : a + T₀ ≤ a + (T₀ + 1))
    have h0lim : ∫ t in Set.Icc (a + t₀) (a + T₀), ∫ x in unitCube,
        θstar t x * weakOp b 0 (perTest φ) t x = 0 :=
      tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun i => (hid (σ i)).symm)
    exact dist_eq_of_iterated hb hθcont (fun t ht => hLim.theta_per ht) hφ hc hts hz h0 h0lim
  · -- the weak initial trace
    intro g0 hg0
    refine weak_trace_limit hLim hs hF (f' := fun i => f (σ i)) hfs hfsF
      (fun g hg => (hweak₁ g hg).comp hσ₂.tendsto_atTop)
      (fun t ht => hLim.theta_l2 (fun i t ht => hl2 (σ i) t ht) ht) ?_ g0 hg0
    intro ψ hψ hψp
    obtain ⟨C, hC0, hC⟩ := exists_bound_periodic_grad hψ hψp
    refine ⟨(2 * B * C + κbar * C) * ((1 + F ^ 2) / 2), fun i t hta => ?_⟩
    obtain ⟨hlt, Dθ, hD, -⟩ := l2NormSq_le_of_isHolderDivFreeVelocity hα hbH (hκpos (σ i))
      (show a < a + (t - a + 1) by linarith) (hf (σ i)).1 (hθ (σ i) (t - a + 1) (by linarith))
    have hW : ∀ s' x, |vecDot (b s' x) (spaceGrad ψ x) + κ (σ i) * lapl ψ x| ≤
        2 * B * C + κbar * C := fun s' x => by
      have := drift_bound hB (κ (σ i)) hC s' x
      have hk : |κ (σ i)| * C ≤ κbar * C := mul_le_mul_of_nonneg_right (hκb i) hC0
      linarith
    have h := weak_trace_bound hb hD (F := F)
      (fun t' ht' => (hlt t' ht').trans (hl2f _)) hψ hψp hW (τ := t) hta.le (by linarith)
    rw [pairing_congr (hΘ (σ i) t hta).2.1]
    exact h
  · -- the Cs bound
    intro t₀ T h0 h1 t ht
    exact ⟨hLim.theta_per (by linarith [ht.1]), hLim.theta_cs h0 h1 ht⟩
  · -- the time modulus
    intro t₀ T h0 h1
    have hIo : Set.Icc (a + t₀) (a + T) ⊆ Set.Ioi a := fun u hu => by
      simp only [mem_Ioi]; linarith [hu.1]
    have hincI : IncIdent b 0 θstar (Set.Icc (a + t₀) (a + T)) :=
      fun ψ hψ hψp σ' hσ' τ hτ hστ => hIncLim ψ hψ hψp σ' (hIo hσ') τ (hIo hτ) hστ
    have hUI : ∀ u ∈ Set.Icc (a + t₀) (a + T), Continuous (θstar u) ∧ IsZ2Periodic (θstar u) ∧
        CsNormLe s (θstar u) (Kc t₀ T) := fun u hu =>
      ⟨hLim.theta_cont hs (hIo hu), hLim.theta_per (hIo hu), hLim.theta_cs h0 h1 hu⟩
    have hK : 0 ≤ Kc t₀ T := csNormLe_K_nonneg (hLim.cs 0 t₀ T h0 h1 (a + t₀) ⟨le_rfl, by linarith⟩)
    obtain ⟨hC1, -⟩ := c12_nonneg
    have h4 : 0 < (4 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
    have he : s / (s + ((1 : ℕ) : ℝ)) = s / (1 + s) := by rw [Nat.cast_one, add_comm]
    refine ⟨2 * Kc t₀ T * 4 ^ s + Kc t₀ T * (B * (c1 0 + c1 1)) + 2 * Kc t₀ T * 4 ^ s, ?_⟩
    have hC'0 : 0 ≤ 2 * Kc t₀ T * 4 ^ s + Kc t₀ T * (B * (c1 0 + c1 1)) + 2 * Kc t₀ T * 4 ^ s := by
      positivity
    have key : ∀ σ' ∈ Set.Icc (a + t₀) (a + T), ∀ τ ∈ Set.Icc (a + t₀) (a + T), σ' < τ →
        ∀ x, |θstar τ x - θstar σ' x| ≤ (2 * Kc t₀ T * 4 ^ s + Kc t₀ T * (B * (c1 0 + c1 1)) +
          2 * Kc t₀ T * 4 ^ s) * |τ - σ'| ^ (s / (1 + s)) := by
      intro σ' hσ' τ hτ hστ x
      have := time_modulus_transport hs (ordConnected_Icc) (fun u hu => hb.slice_continuous u)
        (fun u hu => hb.periodic u) (fun u hu => hBj u) hUI hincI hσ' hτ hστ x
      rw [he] at this
      rwa [abs_of_pos (sub_pos.2 hστ)]
    intro t ht t' ht' x
    rcases lt_trichotomy t t' with hlt | heq | hgt
    · rw [abs_sub_comm t t', abs_sub_comm (θstar t x)]
      exact key t ht t' ht' hlt x
    · subst heq; simp only [sub_self, abs_zero]
      have : (0 : ℝ) ≤ 0 ^ (s / (1 + s)) := Real.rpow_nonneg le_rfl _
      positivity
    · exact key t' ht' t ht hgt x

/-! # The matched finite-velocity comparison

For `κ_i ∈ 𝒦_{M_i}`, `κ_i → 0`, the solutions with velocity `b_{M_i}` differ from the limit-velocity
solutions by `ϑ_i F` in `C(L²)`, `ϑ_i → 0`; hence they have the same distributional cluster points. -/

theorem exponent_facts {α q : ℝ} (hα : 0 < α) (hq : 1 < q) :
    0 < (1 + α) - ocGamma α q ∧
      0 < q * (1 + α) - ((1 + α) - ocGamma α q) := by
  have hq1 : 0 < q + 1 := by linarith
  have hb : 0 < 1 + α := by linarith
  unfold ocGamma
  constructor
  · have : (1 + α) - (q - 1) * (1 + α) / (q + 1) = 2 * (1 + α) / (q + 1) := by
      field_simp; ring
    rw [this]; positivity
  · have : q * (1 + α) - ((1 + α) - (q - 1) * (1 + α) / (q + 1)) =
        (1 + α) * ((q - 1) * (q + 2)) / (q + 1) := by
      field_simp; ring
    rw [this]
    have : 0 < q - 1 := by linarith
    positivity

/-- **Matched comparison.** -/
theorem matched_comparison (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (b : ℝ → Vec 2 → Vec 2)
    (hbΦ : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x)))
    (hb : IsContDrift b) (a F : ℝ) (hF : 0 ≤ F) (κ : ℕ → ℝ) (f : ℕ → Vec 2 → ℝ)
    (θ : ℕ → ℝ → Vec 2 → ℝ) (hκ : Tendsto κ atTop (𝓝 0))
    (hf : ∀ i, MemL2On unitCube (f i) ∧ Real.sqrt (l2NormSq (f i)) ≤ F)
    (hθ : ∀ i, ∀ T : ℝ, 0 < T → IsWeakSolutionOn b (κ i) a (a + T) (f i) (θ i))
    (Mi : ℕ → ℕ) (θ' : ℕ → ℝ → Vec 2 → ℝ)
    (hMi : ∀ i, 1 ≤ Mi i ∧ κ i ∈ Set.Icc
      (ocEpsilon q Λ (Mi i) ^ ((1 + α) - ocGamma α q) / 2)
      (2 * ocEpsilon q Λ (Mi i) ^ ((1 + α) - ocGamma α q)))
    (hθ' : ∀ i, ∀ T : ℝ, 0 < T →
      IsWeakSolutionOn (streamVel (Φ (Mi i))) (κ i) a (a + T) (f i) (θ' i))
    (φ : ℝ × Vec 2 → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hts : tsupport φ ⊆ Set.Ioi a ×ˢ Set.univ) :
    Tendsto (fun i => ∫ p : ℝ × Vec 2, (θ i p.1 p.2 - θ' i p.1 p.2) * φ p) atTop (𝓝 0) := by
  obtain ⟨φs, Cst, hCst0, -, hΦb, -, hdiff, hvel, hφsc, hφsp, -, -, -⟩ :=
    stream_tail_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hbΦ
  have hq1 : 1 < q := hq.1
  obtain ⟨he, hp⟩ := exponent_facts hα₀ hq1
  obtain ⟨B, hB0, hB⟩ := hb.bounded
  -- the limit stream is a full stream
  have hbfun : (fun p : ℝ × Vec 2 => streamVel φs p.1 p.2) = fun p => b p.1 p.2 := by
    funext p; exact hvel p.1 p.2
  have hfull : IsFullStream φs := by
    refine isFullStream_of hdiff hφsc ?_ ⟨B, fun t x => ?_⟩ hφsp
    · rw [hbfun]; exact hb.continuous
    · rw [hvel]; exact hB t x
  have hbs : streamVel φs = b := funext fun t => funext fun x => hvel t x
  -- positivity of the scales
  have heps : ∀ m, 0 < ocEpsilon q Λ m := fun m =>
    (Scales.epsilon_basic (m := m) hq1 hΛ).1
  have hκpos : ∀ i, 0 < κ i := fun i =>
    lt_of_lt_of_le (by have := heps (Mi i); positivity) (hMi i).2.1
  -- the tail ratio
  set ϑ : ℕ → ℝ := fun i => Cst * ocEpsilon q Λ (Mi i + 1) ^ (1 + α) / κ i with hϑ
  have hϑ0 : ∀ i, 0 ≤ ϑ i := fun i => by
    have := heps (Mi i + 1); have := hκpos i; positivity
  have hϑlim : Tendsto ϑ atTop (𝓝 0) := by
    refine vartheta_tendsto (C := Cst) (β := 1 + α) (e := (1 + α) - ocGamma α q)
      (p := q * (1 + α) - ((1 + α) - ocGamma α q)) (q := q) (κ := κ)
      (E0 := fun i => ocEpsilon q Λ (Mi i)) (E1 := fun i => ocEpsilon q Λ (Mi i + 1))
      hCst0 he hp (by linarith) (fun i => heps _) (fun i => heps _) hκpos hκ
      (fun i => (hMi i).2.1) (fun i => ocEpsilon_succ_le hq1 hΛ (hMi i).1) (by ring)
  -- the test function window
  obtain ⟨t₀, T₀, h0, h1, hz⟩ := exists_test_window hφc hts
  obtain ⟨Cφ, hCφ0, hCφ⟩ := exists_test_constant hφ hφc hz h0 h1
  have hT : 0 < T₀ + 1 := by linarith
  have hbound : ∀ i, |∫ p : ℝ × Vec 2, (θ i p.1 p.2 - θ' i p.1 p.2) * φ p| ≤ (ϑ i * F) * Cφ := by
    intro i
    have hκi := hκpos i
    have hψ : ∀ t x, |φs t x - Φ (Mi i) t x| ≤ κ i * ϑ i := fun t x => by
      have := hΦb (Mi i) t x
      have e : κ i * ϑ i = Cst * ocEpsilon q Λ (Mi i + 1) ^ (1 + α) := by
        rw [hϑ]; field_simp
      rw [e]; exact this
    have hu : IsWeakSolutionOn (streamVel φs) (κ i) a (a + (T₀ + 1)) (f i) (θ i) := by
      rw [hbs]; exact hθ i _ hT
    have hcmp := stream_comparison hfull (isSmoothStream_of_seq hζ hΛ hΦ (Mi i)) hκi
      (by linarith : a < a + (T₀ + 1)) hψ (hf i).1 hu (hθ' i _ hT)
    have hl2f : l2NormSq (f i) ≤ F ^ 2 := by
      have h := (hf i).2
      rw [← Real.sqrt_sq hF] at h
      exact (Real.sqrt_le_sqrt_iff (sq_nonneg _)).1 h
    refine hCφ (θ i) (θ' i) b (streamVel (Φ (Mi i))) (κ i) (κ i) (f i) (f i) (ϑ i * F)
      (mul_nonneg (hϑ0 i) hF) (hθ i _ hT) (hθ' i _ hT) (fun t ht => ?_)
    refine (hcmp t ht).trans ?_
    calc ϑ i ^ 2 * l2NormSq (f i) ≤ ϑ i ^ 2 * F ^ 2 :=
          mul_le_mul_of_nonneg_left hl2f (sq_nonneg _)
      _ = (ϑ i * F) ^ 2 := by ring
  have hlim0 : Tendsto (fun i => (ϑ i * F) * Cφ) atTop (𝓝 0) := by
    simpa using (hϑlim.mul_const F).mul_const Cφ
  refine squeeze_zero_norm (fun i => ?_) hlim0
  rw [Real.norm_eq_abs]; exact hbound i

end AVRegularity.Applications
end
