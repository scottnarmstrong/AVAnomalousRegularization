-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Limits.WindowWeak
import AVRegularity.Applications.Torus.JointContinuityMain
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import AVRegularity.External.FourierCarrierParseval
public import AVRegularity.Statements.Definitions.CsNormLe
import AVRegularity.Applications.TorusEnergy.StreamFacts
import Homogenization.Ambient.BlockMatrix
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVenhance Filter Topology
namespace AVRegularity.Applications

/-! # The pairing identity for weak solutions

For a weak solution `θ` on `[t₁, t₂]` with datum `f`, a smooth periodic `ψ` and `t₁ ≤ τ < t₂`,
`⟨θ(τ), ψ⟩ = ⟨f, ψ⟩ + ∫_{t₁}^{τ} ⟨θ(t), b(t)·∇ψ + κΔψ⟩ dt`.
-/

/-- The pairing `⟨U(t), ψ⟩` over the unit cube. -/
def pairing (U : ℝ → Vec 2 → ℝ) (ψ : Vec 2 → ℝ) (t : ℝ) : ℝ := ∫ x in unitCube, U t x * ψ x

/-- The transport/diffusion pairing `⟨U(t), b(t)·∇ψ + κΔψ⟩`. -/
def incK (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (ψ : Vec 2 → ℝ) (U : ℝ → Vec 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in unitCube, U t x * (vecDot (b t x) (spaceGrad ψ x) + κ * lapl ψ x)

theorem spaceGrad_const_mul_fun {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (c : ℝ) :
    spaceGrad (fun y => c * ψ y) = fun x => c • spaceGrad ψ x :=
  funext fun x => spaceGrad_const_mul hψ c x

theorem lapl_const_mul {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (c : ℝ) (x : Vec 2) :
    lapl (fun y => c * ψ y) x = c * lapl ψ x := by
  unfold lapl
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (fun y => spaceGrad (fun y => c * ψ y) y j) = fun y => c * spaceGrad ψ y j := by
    funext y; rw [spaceGrad_const_mul_fun hψ]; simp
  rw [h1, spaceGrad_const_mul (contDiff_spaceGrad_apply hψ j) c x]
  simp

theorem exists_bound_periodic_grad {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : IsZ2Periodic ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (∀ j : Fin 2, |spaceGrad ψ x j| ≤ C) ∧ |lapl ψ x| ≤ C := by
  have hg : ∀ j : Fin 2, ∃ C : ℝ, ∀ x, |spaceGrad ψ x j| ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := bounded_periodic_window (F := fun p : ℝ × Vec 2 => spaceGrad ψ p.2 j)
      ((continuous_spaceGrad_apply (contDiff_one_of_top hψ) j).comp continuous_snd)
      (fun t n x => by simp only [spaceGrad_periodic hp n x]) 0 0
    exact ⟨C, fun x => hC 0 ⟨le_rfl, le_rfl⟩ x⟩
  obtain ⟨C0, h0⟩ := hg 0
  obtain ⟨C1, h1⟩ := hg 1
  obtain ⟨C2, h2⟩ := bounded_periodic_window (F := fun p : ℝ × Vec 2 => lapl ψ p.2)
    ((continuous_lapl hψ).comp continuous_snd)
    (fun t n x => by simp only [lapl_periodic hp n x]) 0 0
  refine ⟨max (max |C0| |C1|) |C2|, by positivity, fun x => ⟨fun j => ?_, ?_⟩⟩
  · fin_cases j
    · exact (h0 x).trans ((le_abs_self _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    · exact (h1 x).trans ((le_abs_self _).trans ((le_max_right _ _).trans (le_max_left _ _)))
  · exact (h2 0 ⟨le_rfl, le_rfl⟩ x).trans ((le_abs_self _).trans (le_max_right _ _))

theorem drift_continuous {b : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b) (κ : ℝ) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Continuous (fun p : ℝ × Vec 2 =>
      vecDot (b p.1 p.2) (spaceGrad ψ p.2) + κ * lapl ψ p.2) := by
  have hbi : ∀ j : Fin 2, Continuous fun p : ℝ × Vec 2 => b p.1 p.2 j := fun j =>
    (continuous_apply j).comp hb.continuous
  have hg : ∀ j : Fin 2, Continuous fun p : ℝ × Vec 2 => spaceGrad ψ p.2 j := fun j =>
    (continuous_spaceGrad_apply (contDiff_one_of_top hψ) j).comp continuous_snd
  have hl : Continuous fun p : ℝ × Vec 2 => lapl ψ p.2 := (continuous_lapl hψ).comp continuous_snd
  simp only [vecDot, Fin.sum_univ_two]
  exact (((hbi 0).mul (hg 0)).add ((hbi 1).mul (hg 1))).add (continuous_const.mul hl)

theorem drift_bound {b : ℝ → Vec 2 → Vec 2} {B : ℝ} (hB : ∀ t x, ‖b t x‖ ≤ B) (κ : ℝ)
    {ψ : Vec 2 → ℝ} {C : ℝ} (hC : ∀ x, (∀ j : Fin 2, |spaceGrad ψ x j| ≤ C) ∧ |lapl ψ x| ≤ C)
    (t : ℝ) (x : Vec 2) :
    |vecDot (b t x) (spaceGrad ψ x) + κ * lapl ψ x| ≤ 2 * B * C + |κ| * C := by
  have hbj : ∀ j : Fin 2, |b t x j| ≤ B := fun j => by
    simpa using (norm_le_pi_norm (b t x) j).trans (hB t x)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t x)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans ((hC x).2)
  have h1 : ∀ j : Fin 2, |b t x j * spaceGrad ψ x j| ≤ B * C := fun j => by
    rw [abs_mul]; exact mul_le_mul (hbj j) ((hC x).1 j) (abs_nonneg _) hB0
  calc |vecDot (b t x) (spaceGrad ψ x) + κ * lapl ψ x|
      ≤ |vecDot (b t x) (spaceGrad ψ x)| + |κ * lapl ψ x| := abs_add_le _ _
    _ ≤ (B * C + B * C) + |κ| * C := by
        gcongr
        · simp only [vecDot, Fin.sum_univ_two]
          exact (abs_add_le _ _).trans (add_le_add (h1 0) (h1 1))
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC x).2 (abs_nonneg _)
    _ = 2 * B * C + |κ| * C := by ring

theorem incK_integrable {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b)
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : IsZ2Periodic ψ) :
    IntegrableOn (incK b κ ψ θ) (Set.Ioo t₁ t₂) := by
  obtain ⟨-, -, hL2, -⟩ := h
  obtain ⟨B, hB0, hB⟩ := hb.bounded
  obtain ⟨C, hC0, hC⟩ := exists_bound_periodic_grad hψ hψp
  set S : Set (ℝ × Vec 2) := Set.Ioo t₁ t₂ ×ˢ unitCube with hS
  have hθint : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2) (volume.restrict S) :=
    memLp_two_integrable_window hL2
  have hG : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 *
      (vecDot (b p.1 p.2) (spaceGrad ψ p.2) + κ * lapl ψ p.2)) (volume.restrict S) :=
    hθint.mul_bdd (drift_continuous hb κ hψ).aestronglyMeasurable (c := 2 * B * C + |κ| * C)
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; exact drift_bound hB κ hC p.1 p.2)
  rw [hS, volume_restrict_prod_eq] at hG
  exact hG.integral_prod_left

/-- **Pairing identity** for a weak solution. -/
theorem weak_pairing_eq {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b)
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : IsZ2Periodic ψ) {τ : ℝ} (hτ1 : t₁ ≤ τ) (hτ2 : τ < t₂) :
    pairing θ ψ τ = (∫ x in unitCube, f x * ψ x) + ∫ t in t₁..τ, incK b κ ψ θ t := by
  have hK := incK_integrable hb h hψ hψp
  obtain ⟨hslice, -, -, -, -, -, hcont, -⟩ := id h
  have hψ1 : ContDiff ℝ 1 ψ := contDiff_one_of_top hψ
  refine primitive_of_weak (A := pairing θ ψ) (K := incK b κ ψ θ)
    (c := ∫ x in unitCube, f x * ψ x) hτ1 hτ2 (by unfold pairing; exact hcont ψ hψ hψp) hK ?_
  intro δ hδ hδτ
  have hφ : IsWindowTestFunction t₂ (fun t x => etaCut τ δ t * ψ x) := by
    refine ⟨?_, fun t k x => ?_, fun t ht x => ?_⟩
    · exact (etaCut_contDiff.comp contDiff_fst).mul (hψ.comp contDiff_snd)
    · simp [hψp k x]
    · simp [etaCut_of_ge (t₁ := τ) (δ := δ) (t := t) (by linarith) hδ]
  have hw := window_weak_iterated hb h hφ
  have hinner : ∀ t ∈ Set.Ioo t₁ t₂,
      (∫ x in unitCube, θ t x * weakOp b κ (fun t x => etaCut τ δ t * ψ x) t x) =
        pairing θ ψ t * (-(kerCut τ δ t)) + etaCut τ δ t * incK b κ ψ θ t := by
    intro t ht
    have hs := hslice t ⟨ht.1.le, ht.2.le⟩
    have hdc : Continuous fun x => vecDot (b t x) (spaceGrad ψ x) + κ * lapl ψ x :=
      (drift_continuous hb κ hψ).comp (continuous_const.prodMk continuous_id)
    have i1 : Integrable (fun x => θ t x * ψ x) (volume.restrict unitCube) :=
      integrable_mul_memL2 hs.2 (memL2_continuous hψ.continuous)
    have i2 : Integrable (fun x => θ t x * (vecDot (b t x) (spaceGrad ψ x) + κ * lapl ψ x))
        (volume.restrict unitCube) := integrable_mul_memL2 hs.2 (memL2_continuous hdc)
    have hpt : ∀ x, θ t x * weakOp b κ (fun t x => etaCut τ δ t * ψ x) t x =
        -(kerCut τ δ t) * (θ t x * ψ x) +
          etaCut τ δ t * (θ t x * (vecDot (b t x) (spaceGrad ψ x) + κ * lapl ψ x)) := by
      intro x
      have e1 : deriv (fun s => etaCut τ δ s * ψ x) t = -(kerCut τ δ t) * ψ x :=
        ((hasDerivAt_etaCut t).mul_const (ψ x)).deriv
      have e2 : spaceGrad (fun y => etaCut τ δ t * ψ y) x = etaCut τ δ t • spaceGrad ψ x :=
        spaceGrad_const_mul hψ _ x
      simp only [weakOp]
      rw [e1, e2, lapl_const_mul hψ, vecDot_smul_right]
      ring
    simp_rw [hpt]
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
    simp only [pairing, incK]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hinner] at hw
  have hf : ∫ x in unitCube, f x * ((fun t x => etaCut τ δ t * ψ x) t₁ x) =
      ∫ x in unitCube, f x * ψ x := by
    simp [etaCut_of_le hτ1 hδ]
  rw [hf] at hw
  exact hw

theorem intervalIntegrable_incK {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b)
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : IsZ2Periodic ψ) {σ τ : ℝ} (hσ : t₁ ≤ σ) (hστ : σ ≤ τ)
    (hτ : τ < t₂) : IntervalIntegrable (incK b κ ψ θ) volume σ τ := by
  have hK := incK_integrable hb h hψ hψp
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hστ]
  refine hK.mono_set fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **Pairing increments** of a weak solution. -/
theorem weak_pairing_increment {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b)
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : IsZ2Periodic ψ) {σ τ : ℝ} (hσ : t₁ ≤ σ) (hστ : σ ≤ τ)
    (hτ : τ < t₂) :
    pairing θ ψ τ - pairing θ ψ σ = ∫ t in σ..τ, incK b κ ψ θ t := by
  rw [weak_pairing_eq hb h hψ hψp hσ (by linarith), weak_pairing_eq hb h hψ hψp (by linarith) hτ,
    ← intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_incK hb h hψ hψp (le_refl t₁) (by linarith) hτ)
      (intervalIntegrable_incK hb h hψ hψp (le_refl t₁) hσ (by linarith))]
  ring

/-! # A scaled mollifier with explicit derivative bounds

`mollK r x y = r⁻² ω₀((x - y)/r)` for a fixed normalized bump `ω₀` supported in the unit sup-ball.
The `L¹` norm of the `k`-th derivative is `r^{-k}` times a constant, which gives the time modulus.
-/

/-- The fixed bump: radii `1/2 < 1`. -/
def ωb : ContDiffBump (0 : Vec 2) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The normalized bump, supported in the open unit sup-ball. -/
def ω0 : Vec 2 → ℝ := ωb.normed volume

theorem ω0_contDiff : ContDiff ℝ (⊤ : ℕ∞) ω0 := ContDiffBump.contDiff_normed _

theorem ω0_nonneg (y : Vec 2) : 0 ≤ ω0 y := ContDiffBump.nonneg_normed _ _

theorem ω0_compact : HasCompactSupport ω0 := ContDiffBump.hasCompactSupport_normed _

theorem ω0_integral : ∫ y, ω0 y = 1 := ContDiffBump.integral_normed _

theorem ω0_support {y : Vec 2} (hy : ω0 y ≠ 0) : ‖y‖ < 1 := by
  have h : y ∈ Function.support ω0 := hy
  have h2 : y ∈ Function.support (ωb.normed volume) := h
  rw [ContDiffBump.support_normed_eq] at h2
  have hr : ωb.rOut = 1 := rfl
  rw [hr] at h2
  simpa [Metric.mem_ball] using h2

/-- The rescaled reflected translate `y ↦ h((x - y)/r)`. -/
def scl (r : ℝ) (x : Vec 2) (h : Vec 2 → ℝ) : Vec 2 → ℝ := fun y => h (r⁻¹ • (x - y))

theorem contDiff_scl (r : ℝ) (x : Vec 2) {h : Vec 2 → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (scl r x h) :=
  hh.comp ((contDiff_const.sub contDiff_id).const_smul r⁻¹)

theorem hasCompactSupport_scl {r : ℝ} (hr : 0 < r) (x : Vec 2) {h : Vec 2 → ℝ}
    (hh : HasCompactSupport h) : HasCompactSupport (scl r x h) := by
  have he : Topology.IsClosedEmbedding (fun y : Vec 2 => r⁻¹ • (x - y)) :=
    (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')).isClosedEmbedding.comp
      (Homeomorph.subLeft x).isClosedEmbedding
  exact hh.comp_isClosedEmbedding he

theorem integral_abs_scl {r : ℝ} (hr : 0 < r) (x : Vec 2) (h : Vec 2 → ℝ) :
    ∫ y, |scl r x h y| = r ^ 2 * ∫ z, |h z| := by
  unfold scl
  have h1 := integral_sub_left_eq_self (fun z : Vec 2 => |h (r⁻¹ • z)|) volume x
  have h2 := Measure.integral_comp_inv_smul (volume : Measure (Vec 2)) (fun z => |h z|) r
  simp only [Module.finrank_fin_fun, smul_eq_mul] at h2
  rw [h1, h2, abs_of_pos (pow_pos hr 2)]

theorem integral_scl {r : ℝ} (hr : 0 < r) (x : Vec 2) (h : Vec 2 → ℝ) :
    ∫ y, scl r x h y = r ^ 2 * ∫ z, h z := by
  unfold scl
  have h1 := integral_sub_left_eq_self (fun z : Vec 2 => h (r⁻¹ • z)) volume x
  have h2 := Measure.integral_comp_inv_smul (volume : Measure (Vec 2)) (fun z => h z) r
  simp only [Module.finrank_fin_fun, smul_eq_mul] at h2
  rw [h1, h2, abs_of_pos (pow_pos hr 2)]

theorem spaceGrad_scl {r : ℝ} (x : Vec 2) {h : Vec 2 → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (y : Vec 2) (j : Fin 2) :
    spaceGrad (scl r x h) y j = -r⁻¹ * spaceGrad h (r⁻¹ • (x - y)) j := by
  have hin : HasFDerivAt (fun y : Vec 2 => r⁻¹ • (x - y))
      (r⁻¹ • ((0 : Vec 2 →L[ℝ] Vec 2) - ContinuousLinearMap.id ℝ (Vec 2))) y :=
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y)).const_smul r⁻¹
  have hd : DifferentiableAt ℝ h (r⁻¹ • (x - y)) := hh.differentiable (by simp) _
  have := hd.hasFDerivAt.comp y hin
  simp only [spaceGrad]
  change fderiv ℝ (h ∘ fun y => r⁻¹ • (x - y)) y (basisVec j) = _
  rw [this.fderiv]
  simp

/-- The mollifier `y ↦ r⁻² ω₀((x - y)/r)`. -/
def mollK (r : ℝ) (x : Vec 2) : Vec 2 → ℝ := fun y => r⁻¹ ^ 2 * scl r x ω0 y

theorem kern_contDiff (r : ℝ) (x : Vec 2) : ContDiff ℝ (⊤ : ℕ∞) (mollK r x) :=
  contDiff_const.mul (contDiff_scl r x ω0_contDiff)

theorem kern_nonneg' {r : ℝ} (x y : Vec 2) : 0 ≤ mollK r x y :=
  mul_nonneg (sq_nonneg _) (ω0_nonneg _)

theorem kern_compact {r : ℝ} (hr : 0 < r) (x : Vec 2) : HasCompactSupport (mollK r x) :=
  (hasCompactSupport_scl hr x ω0_compact).mul_left

theorem kern_integral {r : ℝ} (hr : 0 < r) (x : Vec 2) : ∫ y, mollK r x y = 1 := by
  unfold mollK
  rw [integral_const_mul, integral_scl hr x, ω0_integral]
  field_simp

theorem kern_support {r : ℝ} (hr : 0 < r) {x y : Vec 2} (hy : mollK r x y ≠ 0) :
    dist y x < r := by
  have h1 : ω0 (r⁻¹ • (x - y)) ≠ 0 := fun h => hy (by simp [mollK, scl, h])
  have h2 := ω0_support h1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)] at h2
  have h3 : ‖x - y‖ < r := by
    rw [inv_mul_lt_iff₀ hr] at h2; linarith
  rwa [dist_eq_norm, norm_sub_rev]

/-- `L¹` norm constants of the first and second derivatives of the bump. -/
def c1 (j : Fin 2) : ℝ := ∫ z, |spaceGrad ω0 z j|

def c2 (j : Fin 2) : ℝ := ∫ z, |spaceGrad (fun w => spaceGrad ω0 w j) z j|

theorem c1_nonneg (j : Fin 2) : 0 ≤ c1 j := integral_nonneg fun _ => abs_nonneg _

theorem c2_nonneg (j : Fin 2) : 0 ≤ c2 j := integral_nonneg fun _ => abs_nonneg _

theorem spaceGrad_kern {r : ℝ} (x : Vec 2) (j : Fin 2) :
    (fun y => spaceGrad (mollK r x) y j) =
      fun y => (-(r⁻¹ ^ 3)) * scl r x (fun z => spaceGrad ω0 z j) y := by
  funext y
  have h := spaceGrad_const_mul_fun (contDiff_scl r x ω0_contDiff) (r⁻¹ ^ 2)
  have : mollK r x = fun y => r⁻¹ ^ 2 * scl r x ω0 y := rfl
  rw [this, h]
  simp only [Pi.smul_apply, smul_eq_mul, spaceGrad_scl x ω0_contDiff y j, scl]
  ring

theorem spaceGrad_spaceGrad_kern {r : ℝ} (x : Vec 2) (j : Fin 2) :
    (fun y => spaceGrad (fun w => spaceGrad (mollK r x) w j) y j) =
      fun y => (r⁻¹ ^ 4) * scl r x (fun z => spaceGrad (fun w => spaceGrad ω0 w j) z j) y := by
  funext y
  rw [spaceGrad_kern x j]
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z => spaceGrad ω0 z j) := contDiff_spaceGrad_apply ω0_contDiff j
  have h := spaceGrad_const_mul_fun (contDiff_scl r x hg) (-(r⁻¹ ^ 3))
  rw [h]
  simp only [Pi.smul_apply, smul_eq_mul, spaceGrad_scl x hg y j, scl]
  ring

theorem integral_abs_spaceGrad_kern {r : ℝ} (hr : 0 < r) (x : Vec 2) (j : Fin 2) :
    ∫ y, |spaceGrad (mollK r x) y j| = r⁻¹ * c1 j := by
  have h := congrFun (spaceGrad_kern (r := r) x j)
  simp_rw [h, abs_mul, abs_neg]
  rw [integral_const_mul, integral_abs_scl hr x]
  unfold c1
  rw [abs_of_pos (pow_pos (inv_pos.2 hr) 3)]
  field_simp

theorem integral_abs_spaceGrad_spaceGrad_kern {r : ℝ} (hr : 0 < r) (x : Vec 2) (j : Fin 2) :
    ∫ y, |spaceGrad (fun w => spaceGrad (mollK r x) w j) y j| = r⁻¹ ^ 2 * c2 j := by
  have h := congrFun (spaceGrad_spaceGrad_kern (r := r) x j)
  simp_rw [h, abs_mul]
  rw [integral_const_mul, integral_abs_scl hr x]
  unfold c2
  rw [abs_of_pos (pow_pos (inv_pos.2 hr) 4)]
  field_simp

/-- The mollification of a `C^s(𝕋²)` function is `K (4r)^s`-close to it. -/
theorem abs_sub_kern_le {s K r : ℝ} (hs : 0 < s) (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    {g : Vec 2 → ℝ} (hg : CsNormLe s g K) (x : Vec 2) :
    |g x - ∫ y, g y * mollK r x y| ≤ K * (2 * (2 * r)) ^ s := by
  have hK := csNormLe_K_nonneg hg
  have hgc := continuous_of_csNormLe hs hg
  have hwc := (kern_contDiff r x).continuous
  have hint : Integrable (fun y => g y * mollK r x y) volume :=
    (hgc.mul hwc).integrable_of_hasCompactSupport ((kern_compact hr x).mul_left)
  have hint1 : Integrable (fun y => mollK r x y) volume :=
    hwc.integrable_of_hasCompactSupport (kern_compact hr x)
  have hrepr : g x - ∫ y, g y * mollK r x y = ∫ y, (g x - g y) * mollK r x y := by
    have e1 := integral_sub (μ := volume) (f := fun y => g x * mollK r x y)
      (g := fun y => g y * mollK r x y) (hint1.const_mul _) hint
    have e2 := integral_const_mul (μ := volume) (g x) (fun y => mollK r x y)
    have e3 : (fun y => (g x - g y) * mollK r x y) =
        fun y => g x * mollK r x y - g y * mollK r x y := by
      funext y; ring
    rw [e3, e1, e2, kern_integral hr, mul_one]
  rw [hrepr]
  calc |∫ y, (g x - g y) * mollK r x y|
      ≤ ∫ y, |(g x - g y) * mollK r x y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, K * (2 * (2 * r)) ^ s * mollK r x y := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hint1.const_mul _) (Eventually.of_forall fun y => ?_)
        simp only
        rw [abs_mul, abs_of_nonneg (kern_nonneg' x y)]
        by_cases hy : mollK r x y = 0
        · simp [hy]
        · refine mul_le_mul_of_nonneg_right ?_ (kern_nonneg' x y)
          have hd := kern_support hr hy
          have he := eNorm_le_of_dist hd
          have he2 : eNorm (x - y) ≤ 1 / 2 := by
            rw [show x - y = -(y - x) by abel, eNorm_neg]; linarith
          calc |g x - g y| ≤ K * eNorm (x - y) ^ s := csNormLe_increment_euclid hs hg he2
            _ ≤ K * (2 * (2 * r)) ^ s := by
                gcongr
                · exact eNorm_nonneg _
                · rw [show x - y = -(y - x) by abel, eNorm_neg]; linarith
    _ = K * (2 * (2 * r)) ^ s := by rw [integral_const_mul, kern_integral hr, mul_one]

theorem spaceGrad_perX {ρ : Vec 2 → ℝ} (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (y : Vec 2) (i : Fin 2) : spaceGrad (perX ρ) y i = perX (fun z => spaceGrad ρ z i) y := by
  obtain ⟨R, hR⟩ := exists_supBdd_x hρc
  have h := spaceGrad_perST (ρ := fun _ z => ρ z) hR (hρs.comp contDiff_snd) 0 y i
  exact h

theorem hasCompactSupport_spaceGrad_apply {ρ : Vec 2 → ℝ} (hρc : HasCompactSupport ρ) (i : Fin 2) :
    HasCompactSupport (fun z => spaceGrad ρ z i) :=
  hasCompactSupport_fderiv_apply hρc (basisVec i)

theorem abs_integral_mul_le_of_bound {G ρ : Vec 2 → ℝ} {M : ℝ}
    (hM : ∀ y, |G y| ≤ M) (hρ : Integrable ρ) :
    |∫ y, G y * ρ y| ≤ M * ∫ y, |ρ y| := by
  have hint : Integrable (fun y => |ρ y|) := hρ.abs
  calc |∫ y, G y * ρ y| ≤ ∫ y, |G y * ρ y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, M * |ρ y| := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hint.const_mul M) (Eventually.of_forall fun y => ?_)
        simp only
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hM y) (abs_nonneg _)
    _ = M * ∫ y, |ρ y| := integral_const_mul _ _

/-- The pairing against the periodized mollifier is the mollification. -/
theorem pairing_perX_kern {r : ℝ} (hr : 0 < r) (x : Vec 2) {G : Vec 2 → ℝ} (hG : Continuous G)
    (hGp : IsZ2Periodic G) :
    ∫ y in unitCube, G y * perX (mollK r x) y = ∫ y, G y * mollK r x y :=
  (integral_unfold_space (kern_contDiff r x) (kern_compact hr x) hGp
    (integrableOn_cube_of_continuous hG)).symm

/-- **Bound on the drift/diffusion pairing against the periodized mollifier.** -/
theorem incK_kern_bound {r K B κ : ℝ} (hr : 0 < r) (hκ : 0 ≤ κ) (x : Vec 2)
    {b : ℝ → Vec 2 → Vec 2} {U : ℝ → Vec 2 → ℝ} {t : ℝ}
    (hbc : Continuous (b t)) (hbp : IsZ2Periodic (b t)) (hB : ∀ y j, |b t y j| ≤ B)
    (hUc : Continuous (U t)) (hUp : IsZ2Periodic (U t)) (hK : ∀ y, |U t y| ≤ K) :
    |incK b κ (perX (mollK r x)) U t| ≤
      K * (B * (r⁻¹ * (c1 0 + c1 1)) + κ * (r⁻¹ ^ 2 * (c2 0 + c2 1))) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  set k := mollK r x with hk
  have hks : ContDiff ℝ (⊤ : ℕ∞) k := kern_contDiff r x
  have hkc : HasCompactSupport k := kern_compact hr x
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (perX k) := perX_contDiff hks hkc
  have hbi : ∀ j : Fin 2, Continuous fun y => b t y j := fun j => (continuous_apply j).comp hbc
  have hgs : ∀ j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun z => spaceGrad k z j) := fun j =>
    contDiff_spaceGrad_apply hks j
  have hgc : ∀ j : Fin 2, HasCompactSupport (fun z => spaceGrad k z j) := fun j =>
    hasCompactSupport_spaceGrad_apply hkc j
  have hggs : ∀ j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun z => spaceGrad (fun w => spaceGrad k w j) z j) :=
    fun j => contDiff_spaceGrad_apply (hgs j) j
  have hggc : ∀ j : Fin 2, HasCompactSupport (fun z => spaceGrad (fun w => spaceGrad k w j) z j) :=
    fun j => hasCompactSupport_spaceGrad_apply (hgc j) j
  -- the first-order terms
  have hA : ∀ j : Fin 2, |∫ y in unitCube, (U t y * b t y j) * spaceGrad (perX k) y j| ≤
      K * B * (r⁻¹ * c1 j) := by
    intro j
    have hGc : Continuous fun y => U t y * b t y j := hUc.mul (hbi j)
    have hGp : IsZ2Periodic fun y => U t y * b t y j := fun n y => by
      simp [hUp n y, hbp n y]
    have e : ∫ y in unitCube, (U t y * b t y j) * spaceGrad (perX k) y j =
        ∫ y, (U t y * b t y j) * spaceGrad k y j := by
      simp_rw [spaceGrad_perX hks hkc]
      exact (integral_unfold_space (hgs j) (hgc j) hGp (integrableOn_cube_of_continuous hGc)).symm
    rw [e]
    have hM : ∀ y, |U t y * b t y j| ≤ K * B := fun y => by
      rw [abs_mul]; exact mul_le_mul (hK y) (hB y j) (abs_nonneg _) hK0
    refine (abs_integral_mul_le_of_bound hM
      ((hgs j).continuous.integrable_of_hasCompactSupport (hgc j))).trans ?_
    rw [integral_abs_spaceGrad_kern hr x j]
  have hB' : ∀ j : Fin 2, |∫ y in unitCube, U t y * spaceGrad (fun w => spaceGrad (perX k) w j) y j| ≤
      K * (r⁻¹ ^ 2 * c2 j) := by
    intro j
    have e0 : (fun w => spaceGrad (perX k) w j) = perX (fun z => spaceGrad k z j) :=
      funext fun w => spaceGrad_perX hks hkc w j
    have e : ∫ y in unitCube, U t y * spaceGrad (fun w => spaceGrad (perX k) w j) y j =
        ∫ y, U t y * spaceGrad (fun w => spaceGrad k w j) y j := by
      rw [e0]
      simp_rw [spaceGrad_perX (hgs j) (hgc j)]
      exact (integral_unfold_space (hggs j) (hggc j) hUp (integrableOn_cube_of_continuous hUc)).symm
    rw [e]
    refine (abs_integral_mul_le_of_bound hK
      ((hggs j).continuous.integrable_of_hasCompactSupport (hggc j))).trans ?_
    have := integral_abs_spaceGrad_spaceGrad_kern hr x j
    rw [← hk] at this
    rw [this]
  -- assemble
  have hexp : incK b κ (perX k) U t =
      (∑ j : Fin 2, ∫ y in unitCube, (U t y * b t y j) * spaceGrad (perX k) y j) +
        κ * ∑ j : Fin 2, ∫ y in unitCube,
          U t y * spaceGrad (fun w => spaceGrad (perX k) w j) y j := by
    have hψ1 : ContDiff ℝ 1 (perX k) := contDiff_one_of_top hψ
    have hg1 : ∀ j : Fin 2, Continuous fun y => spaceGrad (perX k) y j := fun j =>
      continuous_spaceGrad_apply hψ1 j
    have hg2 : ∀ j : Fin 2, Continuous fun y =>
        spaceGrad (fun w => spaceGrad (perX k) w j) y j := fun j =>
      continuous_spaceGrad_apply (contDiff_one_of_top (contDiff_spaceGrad_apply hψ j)) j
    have i1 : ∀ j : Fin 2, Integrable (fun y => (U t y * b t y j) * spaceGrad (perX k) y j)
        (volume.restrict unitCube) := fun j =>
      integrableOn_cube_of_continuous ((hUc.mul (hbi j)).mul (hg1 j))
    have i2 : ∀ j : Fin 2, Integrable (fun y => U t y *
        spaceGrad (fun w => spaceGrad (perX k) w j) y j) (volume.restrict unitCube) := fun j =>
      integrableOn_cube_of_continuous (hUc.mul (hg2 j))
    rw [← integral_finsetSum _ fun j _ => i1 j, ← integral_finsetSum _ fun j _ => i2 j,
      ← integral_const_mul, ← integral_add (integrable_finsetSum _ fun j _ => i1 j)
        ((integrable_finsetSum _ fun j _ => i2 j).const_mul κ)]
    unfold incK
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [vecDot, lapl, Fin.sum_univ_two]
    ring
  rw [hexp]
  calc |(∑ j : Fin 2, ∫ y in unitCube, (U t y * b t y j) * spaceGrad (perX k) y j) +
        κ * ∑ j : Fin 2, ∫ y in unitCube,
          U t y * spaceGrad (fun w => spaceGrad (perX k) w j) y j|
      ≤ |∑ j : Fin 2, ∫ y in unitCube, (U t y * b t y j) * spaceGrad (perX k) y j| +
        |κ * ∑ j : Fin 2, ∫ y in unitCube,
          U t y * spaceGrad (fun w => spaceGrad (perX k) w j) y j| := abs_add_le _ _
    _ ≤ (∑ j : Fin 2, K * B * (r⁻¹ * c1 j)) + κ * ∑ j : Fin 2, K * (r⁻¹ ^ 2 * c2 j) := by
        gcongr with j _
        · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hA j)
        · rw [abs_mul, abs_of_nonneg hκ]
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hB' j)
    _ = K * (B * (r⁻¹ * (c1 0 + c1 1)) + κ * (r⁻¹ ^ 2 * (c2 0 + c2 1))) := by
        simp only [Fin.sum_univ_two]; ring

/-! # Uniform time modulus

A function `U` with uniform `C^s(𝕋²)` bounds on a time interval and the pairing identity
`⟨U(τ), ψ⟩ - ⟨U(σ), ψ⟩ = ∫_σ^τ ⟨U(t), b·∇ψ + κΔψ⟩ dt` is Hölder continuous in time, with exponent
`s/(s+2)`, and with exponent `s/(s+1)` when `κ = 0`. The constants do not depend on `κ ≤ κ̄`. -/

/-- The pairing identity for `U` on the time set `I`. -/
def IncIdent (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (U : ℝ → Vec 2 → ℝ) (I : Set ℝ) : Prop :=
  ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ → ∀ σ ∈ I, ∀ τ ∈ I, σ ≤ τ →
    pairing U ψ τ - pairing U ψ σ = ∫ t in σ..τ, incK b κ ψ U t

theorem csNormLe_abs_le_lim {s K : ℝ} {g : Vec 2 → ℝ} (hg : CsNormLe s g K) (x : Vec 2) :
    |g x| ≤ K := by
  have hne : torusDist (0 : Vec 2) (fun _ => 1 / 4) ≠ 0 := by
    have hsmall : eNorm ((0 : Vec 2) - fun _ => 1 / 4) ≤ 1 / 2 := by
      unfold eNorm
      rw [Real.sqrt_le_left (by norm_num)]
      simp [vecNormSq, vecDot]
      norm_num
    have hne0 : (0 : Vec 2) ≠ fun _ => 1 / 4 := by
      intro h; have := congrFun h 0; norm_num at this
    exact (torusDist_pos_of_small hne0 hsmall).ne'
  have h := hg x 0 (fun _ => 1 / 4) hne
  have h1 : 0 ≤ |g 0 - g fun _ => 1 / 4| / torusDist 0 (fun _ => 1 / 4) ^ s :=
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg (torusDist_nonneg _ _) _)
  linarith

theorem time_balance {b : ℝ → Vec 2 → Vec 2} {U : ℝ → Vec 2 → ℝ} {κ K B s : ℝ} {I : Set ℝ}
    (hs : 0 < s) (hκ : 0 ≤ κ) (hI : I.OrdConnected)
    (hbc : ∀ t ∈ I, Continuous (b t)) (hbp : ∀ t ∈ I, IsZ2Periodic (b t))
    (hB : ∀ t ∈ I, ∀ y j, |b t y j| ≤ B)
    (hU : ∀ t ∈ I, Continuous (U t) ∧ IsZ2Periodic (U t) ∧ CsNormLe s (U t) K)
    (hinc : IncIdent b κ U I) {σ τ : ℝ} (hσ : σ ∈ I) (hτ : τ ∈ I) (hστ : σ ≤ τ) {r : ℝ}
    (hr : 0 < r) (hr4 : r ≤ 1 / 4) (x : Vec 2) :
    |U τ x - U σ x| ≤ 2 * (K * (2 * (2 * r)) ^ s) +
      (τ - σ) * (K * (B * (r⁻¹ * (c1 0 + c1 1)) + κ * (r⁻¹ ^ 2 * (c2 0 + c2 1)))) := by
  set ψ := perX (mollK r x) with hψ
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ := perX_contDiff (kern_contDiff r x) (kern_compact hr x)
  have hψp : IsZ2Periodic ψ := perX_periodic _
  have h1 := hinc ψ hψs hψp σ hσ τ hτ hστ
  have hmol : ∀ t ∈ I, |U t x - pairing U ψ t| ≤ K * (2 * (2 * r)) ^ s := by
    intro t ht
    obtain ⟨hc, hp, hcs⟩ := hU t ht
    have : pairing U ψ t = ∫ y, U t y * mollK r x y := pairing_perX_kern hr x hc hp
    rw [this]
    exact abs_sub_kern_le hs hr hr4 hcs x
  have hinc_bd : ∀ t ∈ Set.uIoc σ τ, ‖incK b κ ψ U t‖ ≤
      K * (B * (r⁻¹ * (c1 0 + c1 1)) + κ * (r⁻¹ ^ 2 * (c2 0 + c2 1))) := by
    intro t ht
    have htI : t ∈ I := by
      have ht' := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le hστ] at ht'
      exact hI.out hσ hτ ht'
    obtain ⟨hc, hp, hcs⟩ := hU t htI
    rw [Real.norm_eq_abs]
    exact incK_kern_bound hr hκ x (hbc t htI) (hbp t htI) (hB t htI) hc hp
      (fun y => csNormLe_abs_le_lim hcs y)
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const hinc_bd
  rw [abs_of_nonneg (sub_nonneg.2 hστ), Real.norm_eq_abs, ← h1] at h2
  have h3 := hmol τ hτ
  have h4 := hmol σ hσ
  have h5 : |U τ x - U σ x| ≤ |U τ x - pairing U ψ τ| + |pairing U ψ τ - pairing U ψ σ| +
      |pairing U ψ σ - U σ x| := by
    have := abs_sub_le (U τ x) (pairing U ψ τ) (U σ x)
    have h6 := abs_sub_le (pairing U ψ τ) (pairing U ψ σ) (U σ x)
    linarith
  rw [abs_sub_comm (pairing U ψ σ) (U σ x)] at h5
  have h7 : (τ - σ) * (K * (B * (r⁻¹ * (c1 0 + c1 1)) + κ * (r⁻¹ ^ 2 * (c2 0 + c2 1)))) =
      (K * (B * (r⁻¹ * (c1 0 + c1 1)) + κ * (r⁻¹ ^ 2 * (c2 0 + c2 1)))) * (τ - σ) := by ring
  rw [h7]
  linarith

theorem c12_nonneg : 0 ≤ c1 0 + c1 1 ∧ 0 ≤ c2 0 + c2 1 :=
  ⟨add_nonneg (c1_nonneg 0) (c1_nonneg 1), add_nonneg (c2_nonneg 0) (c2_nonneg 1)⟩

theorem rpow_four_mul {s r : ℝ} (hr : 0 < r) : (2 * (2 * r)) ^ s = (4 : ℝ) ^ s * r ^ s := by
  rw [show 2 * (2 * r) = 4 * r by ring, Real.mul_rpow (by norm_num) hr.le]

/-- **Time modulus** with exponent `s/(s+2)`. -/
theorem time_modulus {b : ℝ → Vec 2 → Vec 2} {U : ℝ → Vec 2 → ℝ} {κ K B s : ℝ} {I : Set ℝ}
    (hs : 0 < s) (hκ : 0 ≤ κ) (hI : I.OrdConnected)
    (hbc : ∀ t ∈ I, Continuous (b t)) (hbp : ∀ t ∈ I, IsZ2Periodic (b t))
    (hB : ∀ t ∈ I, ∀ y j, |b t y j| ≤ B)
    (hU : ∀ t ∈ I, Continuous (U t) ∧ IsZ2Periodic (U t) ∧ CsNormLe s (U t) K)
    (hinc : IncIdent b κ U I) {σ τ : ℝ} (hσ : σ ∈ I) (hτ : τ ∈ I) (hστ : σ < τ) (x : Vec 2) :
    |U τ x - U σ x| ≤ (2 * K * 4 ^ s + K * (B * (c1 0 + c1 1) + κ * (c2 0 + c2 1)) +
      2 * K * 4 ^ s) * (τ - σ) ^ (s / (s + (2 : ℕ))) := by
  obtain ⟨hC1, hC2⟩ := c12_nonneg
  have hK : 0 ≤ K := csNormLe_K_nonneg (hU σ hσ).2.2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB σ hσ 0 0)
  have h4 : 0 < (4 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
  refine modulus_balance hs 2 (by norm_num) (A := 2 * K * 4 ^ s)
    (R := K * (B * (c1 0 + c1 1) + κ * (c2 0 + c2 1))) (E := 2 * K) (by positivity)
    (by positivity) (by positivity) (sub_pos.2 hστ) ?_ ?_
  · have h1 := csNormLe_abs_le_lim (hU τ hτ).2.2 x
    have h2 := csNormLe_abs_le_lim (hU σ hσ).2.2 x
    have := abs_sub (U τ x) (U σ x)
    linarith
  · intro r hr hr4
    have h := time_balance hs hκ hI hbc hbp hB hU hinc hσ hτ hστ.le hr hr4 x
    refine h.trans ?_
    rw [rpow_four_mul hr]
    have hri : r⁻¹ ≤ r⁻¹ ^ 2 := by
      have : 1 ≤ r⁻¹ := by
        rw [one_le_inv₀ hr]; linarith
      nlinarith
    have hp : 0 ≤ τ - σ := (sub_pos.2 hστ).le
    have e1 : 2 * (K * (4 ^ s * r ^ s)) = 2 * K * 4 ^ s * r ^ s := by ring
    rw [e1]
    have : (τ - σ) * (K * (B * (r⁻¹ * (c1 0 + c1 1)) + κ * (r⁻¹ ^ 2 * (c2 0 + c2 1)))) ≤
        (τ - σ) * (K * (B * (c1 0 + c1 1) + κ * (c2 0 + c2 1))) * r⁻¹ ^ 2 := by
      have hq : B * (r⁻¹ * (c1 0 + c1 1)) + κ * (r⁻¹ ^ 2 * (c2 0 + c2 1)) ≤
          (B * (c1 0 + c1 1) + κ * (c2 0 + c2 1)) * r⁻¹ ^ 2 := by
        have : B * (r⁻¹ * (c1 0 + c1 1)) ≤ B * (c1 0 + c1 1) * r⁻¹ ^ 2 := by
          calc B * (r⁻¹ * (c1 0 + c1 1)) = B * (c1 0 + c1 1) * r⁻¹ := by ring
            _ ≤ B * (c1 0 + c1 1) * r⁻¹ ^ 2 :=
                mul_le_mul_of_nonneg_left hri (mul_nonneg hB0 hC1)
        nlinarith
      calc (τ - σ) * (K * (B * (r⁻¹ * (c1 0 + c1 1)) + κ * (r⁻¹ ^ 2 * (c2 0 + c2 1))))
          ≤ (τ - σ) * (K * ((B * (c1 0 + c1 1) + κ * (c2 0 + c2 1)) * r⁻¹ ^ 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hK) hp
        _ = (τ - σ) * (K * (B * (c1 0 + c1 1) + κ * (c2 0 + c2 1))) * r⁻¹ ^ 2 := by ring
    linarith

/-- **Transport time modulus** with exponent `s/(s+1)` (`κ = 0`). -/
theorem time_modulus_transport {b : ℝ → Vec 2 → Vec 2} {U : ℝ → Vec 2 → ℝ} {K B s : ℝ}
    {I : Set ℝ} (hs : 0 < s) (hI : I.OrdConnected)
    (hbc : ∀ t ∈ I, Continuous (b t)) (hbp : ∀ t ∈ I, IsZ2Periodic (b t))
    (hB : ∀ t ∈ I, ∀ y j, |b t y j| ≤ B)
    (hU : ∀ t ∈ I, Continuous (U t) ∧ IsZ2Periodic (U t) ∧ CsNormLe s (U t) K)
    (hinc : IncIdent b 0 U I) {σ τ : ℝ} (hσ : σ ∈ I) (hτ : τ ∈ I) (hστ : σ < τ) (x : Vec 2) :
    |U τ x - U σ x| ≤ (2 * K * 4 ^ s + K * (B * (c1 0 + c1 1)) + 2 * K * 4 ^ s) *
      (τ - σ) ^ (s / (s + (1 : ℕ))) := by
  obtain ⟨hC1, hC2⟩ := c12_nonneg
  have hK : 0 ≤ K := csNormLe_K_nonneg (hU σ hσ).2.2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB σ hσ 0 0)
  have h4 : 0 < (4 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
  refine modulus_balance hs 1 (by norm_num) (A := 2 * K * 4 ^ s)
    (R := K * (B * (c1 0 + c1 1))) (E := 2 * K) (by positivity)
    (by positivity) (by positivity) (sub_pos.2 hστ) ?_ ?_
  · have h1 := csNormLe_abs_le_lim (hU τ hτ).2.2 x
    have h2 := csNormLe_abs_le_lim (hU σ hσ).2.2 x
    have := abs_sub (U τ x) (U σ x)
    linarith
  · intro r hr hr4
    have h := time_balance hs le_rfl hI hbc hbp hB hU hinc hσ hτ hστ.le hr hr4 x
    refine h.trans ?_
    rw [rpow_four_mul hr]
    have e1 : 2 * (K * (4 ^ s * r ^ s)) = 2 * K * 4 ^ s * r ^ s := by ring
    rw [e1]
    have : (τ - σ) * (K * (B * (r⁻¹ * (c1 0 + c1 1)) + 0 * (r⁻¹ ^ 2 * (c2 0 + c2 1)))) =
        (τ - σ) * (K * (B * (c1 0 + c1 1))) * r⁻¹ ^ 1 := by ring
    rw [this]

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization AVenhance Set
namespace AVRegularity.Applications

/-! # Uniqueness and gluing of continuous periodic representatives

Two continuous `ℤ²`-periodic functions that agree a.e. on the unit cube agree everywhere.
Hence per-window jointly continuous representatives of the slices of a function glue to one
representative on `(a, ∞) × ℝ²`. -/

theorem isOpen_unitCube : IsOpen (unitCube : Set (Vec 2)) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

/-- Continuous periodic functions equal a.e. on the cube are equal. -/
theorem eq_of_ae_eq_cube {g h : Vec 2 → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hgp : IsZ2Periodic g) (hhp : IsZ2Periodic h) (hae : g =ᵐ[volume.restrict unitCube] h) :
    g = h := by
  have hon : EqOn g h unitCube :=
    Measure.eqOn_open_of_ae_eq hae isOpen_unitCube hg.continuousOn hh.continuousOn
  have hcl : EqOn g h (closure unitCube) := hon.closure hg hh
  have hclosure : closure (unitCube : Set (Vec 2)) = Set.pi Set.univ fun _ => Set.Icc 0 1 := by
    simp only [unitCube]
    rw [closure_pi_set]
    simp [closure_Ioo (zero_ne_one' ℝ)]
  funext x
  set n : Fin 2 → ℤ := fun i => ⌊x i⌋
  have hx : x - latticeShift n ∈ closure unitCube := by
    rw [hclosure]
    intro i _
    simp only [Pi.sub_apply, latticeShift, n]
    exact ⟨sub_nonneg.2 (Int.floor_le _), by linarith [Int.lt_floor_add_one (x i)]⟩
  have e1 : g x = g (x - latticeShift n) := by
    have := hgp n (x - latticeShift n); simp only [sub_add_cancel] at this; exact this
  have e2 : h x = h (x - latticeShift n) := by
    have := hhp n (x - latticeShift n); simp only [sub_add_cancel] at this; exact this
  rw [e1, e2, hcl hx]

/-- Per-window representatives glue to a representative on `(a, ∞) × ℝ²`. -/
theorem glue_reps {θ : ℝ → Vec 2 → ℝ} {a : ℝ}
    (hrep : ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ Θ : ℝ → Vec 2 → ℝ,
      ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
      ∀ t ∈ Set.Icc (a + t₀) (a + T), IsZ2Periodic (Θ t) ∧
        Θ t =ᵐ[volume.restrict unitCube] θ t) :
    ∃ Θ : ℝ → Vec 2 → ℝ,
      ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (Set.Ioi a ×ˢ Set.univ) ∧
      (∀ t, a < t → IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
        Continuous (Θ t)) := by
  classical
  -- the window attached to `t > a`
  have hw : ∀ t, a < t → 0 < (t - a) / 2 ∧ (t - a) / 2 < t - a + 1 := fun t ht =>
    ⟨by linarith, by linarith⟩
  set R : ℝ → ℝ → Vec 2 → ℝ := fun t =>
    if ht : a < t then Classical.choose (hrep _ _ (hw t ht).1 (hw t ht).2) else fun _ _ => 0
  set Θ : ℝ → Vec 2 → ℝ := fun t => R t t
  -- slice continuity of a window representative
  have hslice : ∀ {t₀ T : ℝ} {Ψ : ℝ → Vec 2 → ℝ},
      ContinuousOn (fun p : ℝ × Vec 2 => Ψ p.1 p.2) (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) →
      ∀ t ∈ Set.Icc (a + t₀) (a + T), Continuous (Ψ t) := by
    intro t₀ T Ψ hc t ht
    rw [continuous_iff_continuousAt]
    intro x
    have h1 : ContinuousWithinAt (fun p : ℝ × Vec 2 => Ψ p.1 p.2)
        (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) (t, x) := hc (t, x) ⟨ht, trivial⟩
    have h2 : ContinuousAt (fun y : Vec 2 => ((t, y) : ℝ × Vec 2)) x :=
      (continuous_const.prodMk continuous_id).continuousAt
    exact (ContinuousWithinAt.comp h1 h2.continuousWithinAt (fun y _ => ⟨ht, trivial⟩)).continuousAt
      Filter.univ_mem
  have hR : ∀ t, a < t → ∀ τ ∈ Set.Icc (a + (t - a) / 2) (a + (t - a + 1)),
      IsZ2Periodic (R t τ) ∧ R t τ =ᵐ[volume.restrict unitCube] θ τ ∧ Continuous (R t τ) := by
    intro t ht τ hτ
    have hs := Classical.choose_spec (hrep _ _ (hw t ht).1 (hw t ht).2)
    simp only [R, ht, ↓reduceDIte]
    exact ⟨(hs.2 τ hτ).1, (hs.2 τ hτ).2, hslice hs.1 τ hτ⟩
  have hRc : ∀ t, a < t → ContinuousOn (fun p : ℝ × Vec 2 => R t p.1 p.2)
      (Set.Icc (a + (t - a) / 2) (a + (t - a + 1)) ×ˢ Set.univ) := by
    intro t ht
    have hs := Classical.choose_spec (hrep _ _ (hw t ht).1 (hw t ht).2)
    simp only [R, ht, ↓reduceDIte]
    exact hs.1
  have hmem : ∀ t, a < t → t ∈ Set.Icc (a + (t - a) / 2) (a + (t - a + 1)) := fun t ht =>
    ⟨by linarith, by linarith⟩
  have hΘ : ∀ t, a < t → IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
      Continuous (Θ t) := fun t ht => hR t ht t (hmem t ht)
  refine ⟨Θ, ?_, hΘ⟩
  -- near `t`, `Θ` coincides with the representative of the window attached to `t`
  intro p hp
  obtain ⟨t, x⟩ := p
  have ht : a < t := hp.1
  have hnear : ∀ τ ∈ Set.Ioo (a + (t - a) * (2 / 3)) (t + 1 / 2),
      Θ τ = R t τ := by
    intro τ hτ
    have hτa : a < τ := by have := hτ.1; nlinarith
    have hτw : τ ∈ Set.Icc (a + (t - a) / 2) (a + (t - a + 1)) :=
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    obtain ⟨h1, h2, h3⟩ := hΘ τ hτa
    obtain ⟨g1, g2, g3⟩ := hR t ht τ hτw
    exact eq_of_ae_eq_cube h3 g3 h1 g1 (h2.trans g2.symm)
  have hopen : Set.Ioo (a + (t - a) * (2 / 3)) (t + 1 / 2) ×ˢ (Set.univ : Set (Vec 2)) ∈
      𝓝 (t, x) := by
    refine (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨by nlinarith, by linarith⟩, trivial⟩
  have hsub : Set.Ioo (a + (t - a) * (2 / 3)) (t + 1 / 2) ×ˢ (Set.univ : Set (Vec 2)) ⊆
      Set.Icc (a + (t - a) / 2) (a + (t - a + 1)) ×ˢ Set.univ := by
    rintro ⟨τ, y⟩ ⟨hτ, -⟩
    exact ⟨⟨by nlinarith [hτ.1], by linarith [hτ.2]⟩, trivial⟩
  have hca : ContinuousAt (fun p : ℝ × Vec 2 => R t p.1 p.2) (t, x) :=
    ((hRc t ht).mono hsub).continuousAt hopen
  refine (hca.congr ?_).continuousWithinAt
  filter_upwards [hopen] with q hq
  simp only [hnear q.1 hq.1]

/-! # Arzelà–Ascoli on the half-space `(a, ∞) × ℝ²`

A sequence of functions continuous on `(a, ∞) × ℝ²`, uniformly bounded and uniformly equicontinuous
on every window `[a + t₀, a + T] × ℝ²`, has a subsequence converging locally uniformly on
`(a, ∞) × ℝ²` to a continuous function. -/

theorem exists_window_of_compact {a : ℝ} {K : Set (ℝ × Vec 2)} (hK : IsCompact K)
    (hKS : K ⊆ Set.Ioi a ×ˢ Set.univ) :
    ∃ t₀ T : ℝ, 0 < t₀ ∧ t₀ < T ∧ ∀ p ∈ K, p.1 ∈ Set.Icc (a + t₀) (a + T) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 2, one_pos, one_lt_two, fun p hp => absurd hp (Set.notMem_empty p)⟩
  · obtain ⟨p₁, hp₁, hmin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
    obtain ⟨p₂, hp₂, hmax⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
    have h1 : a < p₁.1 := (hKS hp₁).1
    refine ⟨p₁.1 - a, max (p₂.1 - a) (p₁.1 - a + 1), by linarith, ?_, fun p hp => ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · refine ⟨?_, ?_⟩
      · have := hmin hp; simp only [mem_ofPred_eq] at this; linarith
      · have := hmax hp; simp only [mem_ofPred_eq] at this
        have := le_max_left (p₂.1 - a) (p₁.1 - a + 1)
        linarith

theorem exists_locally_uniform_subseq {a : ℝ} {g : ℕ → ℝ → Vec 2 → ℝ}
    (hcont : ∀ n, ContinuousOn (fun p : ℝ × Vec 2 => g n p.1 p.2) (Set.Ioi a ×ˢ Set.univ))
    (hbd : ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ M : ℝ, ∀ n, ∀ t ∈ Set.Icc (a + t₀) (a + T), ∀ x,
      |g n t x| ≤ M)
    (hequi : ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n,
      ∀ t ∈ Set.Icc (a + t₀) (a + T), ∀ t' ∈ Set.Icc (a + t₀) (a + T), ∀ x x' : Vec 2,
        |t - t'| < δ → dist x x' < δ → |g n t x - g n t' x'| < ε) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ θstar : ℝ → Vec 2 → ℝ,
      ContinuousOn (fun p : ℝ × Vec 2 => θstar p.1 p.2) (Set.Ioi a ×ˢ Set.univ) ∧
      TendstoLocallyUniformlyOn (fun i (p : ℝ × Vec 2) => g (σ i) p.1 p.2)
        (fun p : ℝ × Vec 2 => θstar p.1 p.2) atTop (Set.Ioi a ×ˢ Set.univ) := by
  classical
  set S : Set (ℝ × Vec 2) := Set.Ioi a ×ˢ Set.univ with hS
  have hSo : IsOpen S := isOpen_Ioi.prod isOpen_univ
  have : LocallyCompactSpace S := hSo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have : SigmaCompactSpace S := inferInstance
  have : WeaklyLocallyCompactSpace S := inferInstance
  let F : ℕ → C(S, ℝ) := fun n => ⟨fun p => g n p.1.1 p.1.2, (hcont n).domRestrict⟩
  have hFapp : ∀ n (p : S), F n p = g n p.1.1 p.1.2 := fun n p => rfl
  -- windows of compact sets
  have hwin : ∀ K : Set S, IsCompact K → ∃ t₀ T : ℝ, 0 < t₀ ∧ t₀ < T ∧
      ∀ p ∈ K, p.1.1 ∈ Set.Icc (a + t₀) (a + T) := by
    intro K hK
    have hK' : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
    obtain ⟨t₀, T, h0, h1, hw⟩ := exists_window_of_compact hK' (by
      rintro _ ⟨p, -, rfl⟩; exact p.2)
    exact ⟨t₀, T, h0, h1, fun p hp => hw p.1 ⟨p, hp, rfl⟩⟩
  have hbounded : ∀ K : Set S, IsCompact K → ∃ M : ℝ, ∀ n : ℕ, ∀ x, x ∈ K → ‖F n x‖ ≤ M := by
    intro K hK
    obtain ⟨t₀, T, h0, h1, hw⟩ := hwin K hK
    obtain ⟨M, hM⟩ := hbd t₀ T h0 h1
    exact ⟨M, fun n x hx => by
      rw [Real.norm_eq_abs, hFapp]; exact hM n _ (hw x hx) _⟩
  have hequicont : ∀ K : Set S, IsCompact K → EquicontinuousOn (fun n x => F n x) K := by
    intro K hK
    obtain ⟨t₀, T, h0, h1, hw⟩ := hwin K hK
    refine (equicontinuous_restrict_iff _).1 (fun x₀ => ?_)
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hequi t₀ T h0 h1 ε hε
    refine ⟨δ, hδ, fun x hx n => ?_⟩
    have hdist : dist x.1.1 x₀.1.1 < δ := by simpa [Subtype.dist_eq] using hx
    rw [Prod.dist_eq, max_lt_iff] at hdist
    obtain ⟨hdt, hdx⟩ := hdist
    have := hδ' n x₀.1.1.1 (hw x₀.1 x₀.2) x.1.1.1 (hw x.1 x.2) x₀.1.1.2 x.1.1.2
      (by rw [← Real.dist_eq, dist_comm]; exact hdt) (by rw [dist_comm]; exact hdx)
    simpa [hFapp, Real.dist_eq] using this
  obtain ⟨φ, L, hφ, hlim⟩ := External.arzelaAscoliDiagonal F hbounded hequicont
  refine ⟨φ, hφ, fun t x => if h : a < t then L ⟨(t, x), ⟨h, trivial⟩⟩ else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (S.domRestrict fun p : ℝ × Vec 2 =>
        (fun t x => if h : a < t then L ⟨(t, x), ⟨h, trivial⟩⟩ else 0) p.1 p.2) = fun p => L p := by
      funext p
      have hp : a < p.1.1 := p.2.1
      simp only [Set.domRestrict_apply, hp, ↓reduceDIte]
    rw [this]
    exact L.continuous
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hSo]
    intro K hKS hK
    rw [Metric.tendstoUniformlyOn_iff]
    have hKX : IsCompact ((Subtype.val : S → ℝ × Vec 2) ⁻¹' K) := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      rwa [Set.image_preimage_eq_of_subset (by simpa using hKS)]
    have hu := (tendstoLocallyUniformly_iff_forall_isCompact.1 hlim) _ hKX
    rw [Metric.tendstoUniformlyOn_iff] at hu
    intro ε hε
    filter_upwards [hu ε hε] with n hn p hp
    have hpS : p ∈ S := hKS hp
    have := hn ⟨p, hpS⟩ hp
    have hp1 : a < p.1 := hpS.1
    simpa [hp1, hFapp] using this

/-! # Periodization of space-time tests

For `φ ∈ C_c^∞(ℝ × ℝ²)` supported in `(a,∞) × ℝ²`, the spatial periodization
`φ̃ = perST (slc φ)` is a window test function, vanishing identically (with its derivatives) for
times outside a compact subinterval of `(a, ∞)`. -/

/-- The spatial periodization of a space-time test function. -/
def perTest (φ : ℝ × Vec 2 → ℝ) : ℝ → Vec 2 → ℝ := perST (slc φ)

theorem exists_test_window {a : ℝ} {φ : ℝ × Vec 2 → ℝ} (hc : HasCompactSupport φ)
    (hts : tsupport φ ⊆ Set.Ioi a ×ˢ Set.univ) :
    ∃ t₀ T₀ : ℝ, 0 < t₀ ∧ t₀ < T₀ ∧ ∀ t x, (t < a + t₀ ∨ a + T₀ < t) → φ (t, x) = 0 := by
  obtain ⟨t₀, T₀, h0, h1, hw⟩ := exists_window_of_compact hc.isCompact hts
  refine ⟨t₀, T₀, h0, h1, fun t x ht => ?_⟩
  by_contra hne
  have := hw (t, x) (subset_tsupport _ hne)
  simp only at this
  rcases ht with h | h <;> linarith [this.1, this.2]

theorem perTest_eq_zero {φ : ℝ × Vec 2 → ℝ} {a t₀ T₀ : ℝ}
    (hz : ∀ t x, (t < a + t₀ ∨ a + T₀ < t) → φ (t, x) = 0) {t : ℝ}
    (ht : t < a + t₀ ∨ a + T₀ < t) (x : Vec 2) : perTest φ t x = 0 := by
  unfold perTest perST
  exact finsum_eq_zero_of_forall_eq_zero fun n => hz t _ ht

theorem perTest_window {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) {a t₀ T₀ : ℝ}
    (hz : ∀ t x, (t < a + t₀ ∨ a + T₀ < t) → φ (t, x) = 0) :
    IsWindowTestFunction (a + T₀ + 1) (perTest φ) := by
  refine ⟨perST_slc_contDiff hφ hc, fun t => perST_periodic _ t, fun t ht x => ?_⟩
  exact perTest_eq_zero hz (Or.inr (by linarith)) x

theorem weakOp_perTest_eq_zero {φ : ℝ × Vec 2 → ℝ} {a t₀ T₀ : ℝ}
    (hz : ∀ t x, (t < a + t₀ ∨ a + T₀ < t) → φ (t, x) = 0) (b : ℝ → Vec 2 → Vec 2) (κ : ℝ)
    {t : ℝ} (ht : t < a + t₀ ∨ a + T₀ < t) (x : Vec 2) :
    weakOp b κ (perTest φ) t x = 0 := by
  have hev : ∀ᶠ s in 𝓝 t, ∀ y, perTest φ s y = 0 := by
    rcases ht with h | h
    · filter_upwards [Iio_mem_nhds h] with s hs y using
        perTest_eq_zero hz (Or.inl hs) y
    · filter_upwards [Ioi_mem_nhds h] with s hs y using
        perTest_eq_zero hz (Or.inr hs) y
  have hfun : perTest φ t = fun _ => 0 := funext fun y => perTest_eq_zero hz ht y
  have hd : deriv (fun s => perTest φ s x) t = 0 := by
    have : (fun s => perTest φ s x) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with s hs using hs x
    rw [this.deriv_eq]; simp
  have hg : ∀ y j, spaceGrad (perTest φ t) y j = 0 := fun y j => by
    rw [hfun]; simp [spaceGrad]
  have hl : lapl (perTest φ t) x = 0 := by
    unfold lapl
    refine Finset.sum_eq_zero fun j _ => ?_
    have : (fun y => spaceGrad (perTest φ t) y j) = fun _ => 0 := funext fun y => hg y j
    rw [this]; simp [spaceGrad]
  simp [weakOp, hd, hl, vecDot, hg]

/-! # Uniform boundedness and equicontinuity of the viscous solutions

Spatial `C^s` bounds and the time modulus (`time_modulus`) give uniform boundedness and uniform
equicontinuity of a sequence `g n` with `IncIdent` on every window `[a + t₀, a + T]`. -/

theorem exists_small_rpow_aux {c e ε : ℝ} (he : 0 < e) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ c * δ ^ e < ε := by
  have hcont : Continuous fun δ : ℝ => c * |δ| ^ e :=
    continuous_const.mul (continuous_abs.rpow_const fun _ => Or.inr he.le)
  have h0 := hcont.tendsto 0
  simp only [abs_zero, Real.zero_rpow he.ne', mul_zero] at h0
  have hev := (h0.eventually (gt_mem_nhds hε)).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  obtain ⟨δ, hδ1, hδ2⟩ := (hev.and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))).exists
  refine ⟨δ, hδ2.1, hδ2.2.le, ?_⟩
  rwa [abs_of_pos hδ2.1] at hδ1

/-- Boundedness and equicontinuity on windows. -/
theorem equi_of_data {a s B κbar : ℝ} (hs : 0 < s) {b : ℝ → Vec 2 → Vec 2}
    (hbc : ∀ t, Continuous (b t)) (hbp : ∀ t, IsZ2Periodic (b t)) (hB : ∀ t y j, |b t y j| ≤ B)
    {κ : ℕ → ℝ} (hκ0 : ∀ i, 0 ≤ κ i) (hκ : ∀ i, κ i ≤ κbar)
    {g : ℕ → ℝ → Vec 2 → ℝ} (hgc : ∀ i t, a < t → Continuous (g i t))
    (hgp : ∀ i t, a < t → IsZ2Periodic (g i t)) {Kc : ℝ → ℝ → ℝ}
    (hCs : ∀ i t₀ T, 0 < t₀ → t₀ < T → ∀ t ∈ Icc (a + t₀) (a + T), CsNormLe s (g i t) (Kc t₀ T))
    (hinc : ∀ i, IncIdent b (κ i) (g i) (Ioi a)) :
    (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ M : ℝ, ∀ n, ∀ t ∈ Icc (a + t₀) (a + T), ∀ x,
      |g n t x| ≤ M) ∧
    (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n,
      ∀ t ∈ Icc (a + t₀) (a + T), ∀ t' ∈ Icc (a + t₀) (a + T), ∀ x x' : Vec 2,
        |t - t'| < δ → dist x x' < δ → |g n t x - g n t' x'| < ε) := by
  refine ⟨fun t₀ T h0 h1 => ⟨Kc t₀ T, fun n t ht x => csNormLe_abs_le_lim (hCs n t₀ T h0 h1 t ht) x⟩,
    fun t₀ T h0 h1 ε hε => ?_⟩
  obtain ⟨hC1, hC2⟩ := c12_nonneg
  have hK : 0 ≤ Kc t₀ T := csNormLe_K_nonneg (hCs 0 t₀ T h0 h1 (a + t₀) ⟨le_rfl, by linarith⟩)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0 0)
  have h4 : 0 < (4 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
  set e : ℝ := s / (s + ((2 : ℕ) : ℝ)) with he
  have he0 : 0 < e := by rw [he]; positivity
  set Cbar : ℝ := 2 * Kc t₀ T * 4 ^ s + Kc t₀ T * (B * (c1 0 + c1 1) + κbar * (c2 0 + c2 1)) +
    2 * Kc t₀ T * 4 ^ s with hCbar
  have hCbar0 : 0 ≤ Cbar := by
    have : 0 ≤ κbar := (hκ0 0).trans (hκ 0)
    positivity
  obtain ⟨δ₁, hδ₁, hδ₁4, hδ₁ε⟩ := exists_small_rpow_aux (c := Kc t₀ T * 2 ^ s) (e := s) (ε := ε / 2)
    hs (half_pos hε)
  obtain ⟨δ₂, hδ₂, -, hδ₂ε⟩ := exists_small_rpow_aux (c := Cbar) (e := e) (ε := ε / 2) he0
    (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun n t ht t' ht' x x' htt hxx => ?_⟩
  have hδ : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
  have hδ' : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
  -- spatial increment
  have hsp : |g n t x - g n t x'| ≤ Kc t₀ T * 2 ^ s * δ₁ ^ s := by
    have hd : dist x x' < δ₁ := lt_of_lt_of_le hxx hδ
    have he1 := eNorm_le_of_dist (y := x) (x := x') (r := δ₁) hd
    have he2 : eNorm (x - x') ≤ 1 / 2 := by linarith
    calc |g n t x - g n t x'| ≤ Kc t₀ T * eNorm (x - x') ^ s :=
          csNormLe_increment_euclid hs (hCs n t₀ T h0 h1 t ht) he2
      _ ≤ Kc t₀ T * (2 * δ₁) ^ s := by gcongr; exact eNorm_nonneg _
      _ = Kc t₀ T * 2 ^ s * δ₁ ^ s := by
          rw [Real.mul_rpow (by norm_num) hδ₁.le]; ring
  -- time increment
  have htime : |g n t x' - g n t' x'| ≤ Cbar * δ₂ ^ e := by
    have hIo : Set.Icc (a + t₀) (a + T) ⊆ Set.Ioi a := fun u hu => by
      simp only [mem_Ioi]; linarith [hu.1]
    have hincI : IncIdent b (κ n) (g n) (Set.Icc (a + t₀) (a + T)) := fun ψ hψ hψp σ hσ τ hτ hστ =>
      hinc n ψ hψ hψp σ (hIo hσ) τ (hIo hτ) hστ
    have hUI : ∀ u ∈ Set.Icc (a + t₀) (a + T), Continuous (g n u) ∧ IsZ2Periodic (g n u) ∧
        CsNormLe s (g n u) (Kc t₀ T) := fun u hu =>
      ⟨hgc n u (hIo hu), hgp n u (hIo hu), hCs n t₀ T h0 h1 u hu⟩
    have key : ∀ σ ∈ Set.Icc (a + t₀) (a + T), ∀ τ ∈ Set.Icc (a + t₀) (a + T), σ < τ →
        τ - σ < δ₂ → |g n τ x' - g n σ x'| ≤ Cbar * δ₂ ^ e := by
      intro σ hσ τ hτ hστ hlt
      have hm := time_modulus hs (hκ0 n) (ordConnected_Icc) (fun u hu => hbc u) (fun u hu => hbp u)
        (fun u hu => hB u) hUI hincI hσ hτ hστ x'
      refine hm.trans ?_
      have hκn : κ n * (c2 0 + c2 1) ≤ κbar * (c2 0 + c2 1) :=
        mul_le_mul_of_nonneg_right (hκ n) hC2
      have hco : 2 * Kc t₀ T * 4 ^ s + Kc t₀ T * (B * (c1 0 + c1 1) + κ n * (c2 0 + c2 1)) +
          2 * Kc t₀ T * 4 ^ s ≤ Cbar := by
        rw [hCbar]; gcongr
      have hpw : (τ - σ) ^ e ≤ δ₂ ^ e :=
        Real.rpow_le_rpow (sub_nonneg.2 hστ.le) hlt.le he0.le
      calc _ ≤ Cbar * (τ - σ) ^ e := by
            have : 0 ≤ (τ - σ) ^ e := Real.rpow_nonneg (sub_nonneg.2 hστ.le) _
            simp only [he] at hpw this ⊢
            exact mul_le_mul_of_nonneg_right hco this
        _ ≤ Cbar * δ₂ ^ e := mul_le_mul_of_nonneg_left hpw hCbar0
    have hdt : |t - t'| < δ₂ := lt_of_lt_of_le htt hδ'
    rcases lt_trichotomy t t' with hlt | heq | hgt
    · rw [abs_sub_comm]
      rw [abs_of_neg (sub_neg.2 hlt)] at hdt
      exact key t ht t' ht' hlt (by linarith)
    · subst heq; simp only [sub_self, abs_zero]; positivity
    · rw [abs_of_pos (sub_pos.2 hgt)] at hdt
      exact key t' ht' t ht hgt hdt
  calc |g n t x - g n t' x'| ≤ |g n t x - g n t x'| + |g n t x' - g n t' x'| := abs_sub_le _ _ _
    _ < ε := by linarith

end AVRegularity.Applications
end
