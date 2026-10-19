-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.RetainedCompact
public import AVRegularity.CycleWords.MixedWords.CompactDiscardOfParts
public import AVRegularity.CycleWords.Assembly.MixedWordsB1Transfer
import Mathlib.Analysis.PSeries

@[expose] public section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # `L²` limits of amplitudes

An `L²`-Cauchy sequence has an `L²` limit (`exists_eLpNorm_limit`, completeness of `Lp`), unique up
to null sets (`ae_eq_of_tendsto_eLpNorm`). Band-limited functions depend on their amplitudes only
up to null sets (`ampFun_congr_ae`), linearly (`ampFun_add_smul`) and continuously from `L²` of the
ball to pointwise values (`tendsto_ampFun`). The moment norm is absolutely homogeneous
(`momentNorm_smul_le`). -/

section
section L2

variable {E : Type*} [NormedAddCommGroup E]

/-- **An `L²`-Cauchy sequence has an `L²` limit.** -/
theorem exists_eLpNorm_limit [CompleteSpace E] {a : ℕ → Vec 2 → E}
    (ha : ∀ k, MemLp (a k) 2 volume)
    (hc : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ k ≥ N, ∀ l ≥ N, eLpNorm (a k - a l) 2 volume < ε) :
    ∃ A : Vec 2 → E, MemLp A 2 volume ∧
      Tendsto (fun k => eLpNorm (a k - A) 2 volume) atTop (𝓝 0) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set L : ℕ → Lp E 2 volume := fun k => (ha k).toLp (a k) with hLdef
  have hL : ∀ k, (L k : Vec 2 → E) =ᵐ[volume] a k := fun k => MemLp.coeFn_toLp (ha k)
  have hcs : CauchySeq L := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
    refine ⟨N, fun n hn => ?_⟩
    rw [Lp.dist_def, eLpNorm_congr_ae ((hL n).sub (hL N))]
    exact ENNReal.toReal_lt_of_lt_ofReal (hN n hn N le_rfl)
  obtain ⟨Linf, hLinf⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨Linf, Lp.memLp Linf, ?_⟩
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hLinf
  refine hLinf.congr fun k => ?_
  exact eLpNorm_congr_ae ((hL k).sub (EventuallyEq.refl _ _))

/-- `L²` limits are unique up to null sets. -/
theorem ae_eq_of_tendsto_eLpNorm {a : ℕ → Vec 2 → E} {A A' : Vec 2 → E}
    (h1 : Tendsto (fun k => eLpNorm (a k - A) 2 volume) atTop (𝓝 0))
    (h2 : Tendsto (fun k => eLpNorm (a k - A') 2 volume) atTop (𝓝 0)) : A =ᵐ[volume] A' := by
  have hle : ∀ k, eLpNorm (A - A') 2 volume ≤
      eLpNorm (a k - A) 2 volume + eLpNorm (a k - A') 2 volume := fun k => by
    have hs : A - A' = (A - a k) + (a k - A') := by abel
    calc eLpNorm (A - A') 2 volume = eLpNorm ((A - a k) + (a k - A')) 2 volume := by rw [← hs]
      _ ≤ eLpNorm (A - a k) 2 volume + eLpNorm (a k - A') 2 volume :=
          eLpNorm_add_le (by norm_num)
      _ = _ := by rw [eLpNorm_sub_comm A (a k)]
  have h0 : eLpNorm (A - A') 2 volume ≤ 0 := by
    have ht := h1.add h2
    rw [add_zero] at ht
    exact ge_of_tendsto' ht hle
  have hz : eLpNorm (A - A') 2 volume = 0 := le_antisymm h0 zero_le
  rw [eLpNorm_eq_zero_iff two_ne_zero] at hz
  filter_upwards [hz] with θ hθ
  exact sub_eq_zero.1 hθ

end L2

section Amp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ampFun_congr_ae {r : ℝ} {A A' B B' : Vec 2 → E} (hA : A =ᵐ[volume] A')
    (hB : B =ᵐ[volume] B') : ampFun r A B = ampFun r A' B' := by
  funext z
  unfold ampFun
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hA, hB] with θ h1 h2
  rw [h1, h2]

theorem ampFun_add_smul {r : ℝ} {A₁ B₁ A₂ B₂ : Vec 2 → E}
    (hA₁ : IntegrableOn A₁ {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hB₁ : IntegrableOn B₁ {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hA₂ : IntegrableOn A₂ {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hB₂ : IntegrableOn B₂ {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (a b : ℝ) :
    ampFun r (fun θ => a • A₁ θ + b • A₂ θ) (fun θ => a • B₁ θ + b • B₂ θ) =
      fun z => a • ampFun r A₁ B₁ z + b • ampFun r A₂ B₂ z := by
  funext z
  unfold ampFun
  have hs : ∀ θ, Real.cos (vecDot θ z) • (a • A₁ θ + b • A₂ θ) +
      Real.sin (vecDot θ z) • (a • B₁ θ + b • B₂ θ) =
      a • (Real.cos (vecDot θ z) • A₁ θ + Real.sin (vecDot θ z) • B₁ θ) +
        b • (Real.cos (vecDot θ z) • A₂ θ + Real.sin (vecDot θ z) • B₂ θ) := fun θ => by
    simp only [smul_add, smul_comm _ a, smul_comm _ b]
    abel
  simp_rw [hs]
  rw [integral_add (f := fun θ => a • (Real.cos (vecDot θ z) • A₁ θ + Real.sin (vecDot θ z) • B₁ θ))
    (g := fun θ => b • (Real.cos (vecDot θ z) • A₂ θ + Real.sin (vecDot θ z) • B₂ θ))
    ((integrableOn_ampIntegrand hA₁ hB₁ z).smul a)
    ((integrableOn_ampIntegrand hA₂ hB₂ z).smul b), integral_smul, integral_smul]

omit [NormedSpace ℝ E] in
/-- On the ball, `L²` amplitudes are integrable. -/
theorem integrableOn_ampBall_of_memLp {X : Vec 2 → E} (hX : MemLp X 2 volume) (r : ℝ) :
    IntegrableOn X {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} := by
  have : IsFiniteMeasure (volume.restrict {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact amplitudeBall_volume_lt_top r⟩
  exact memLp_one_iff_integrable.1 ((hX.restrict _).mono_exponent (by norm_num))

omit [NormedSpace ℝ E] in
/-- The `L¹` norm on the ball by the `L²` norm. -/
theorem eLpNorm_one_ampBall_le {X : Vec 2 → E} (hX : AEStronglyMeasurable X volume) (r : ℝ) :
    eLpNorm X 1 (volume.restrict {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) ≤
      eLpNorm X 2 volume * volume {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} ^ (1 / 2 : ℝ) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict
    {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (p := 1) (q := 2) (by norm_num) hX.restrict
  rw [Measure.restrict_apply_univ] at h
  refine h.trans (mul_le_mul' (eLpNorm_restrict_le _ _ _ _) (le_of_eq ?_))
  norm_num

/-- **Band-limited functions converge pointwise** when their amplitudes converge in `L²`. -/
theorem tendsto_ampFun {r : ℝ} {A B : ℕ → Vec 2 → E} {A₀ B₀ : Vec 2 → E}
    (hA : ∀ k, MemLp (A k) 2 volume) (hB : ∀ k, MemLp (B k) 2 volume)
    (hA₀ : MemLp A₀ 2 volume) (hB₀ : MemLp B₀ 2 volume)
    (hlimA : Tendsto (fun k => eLpNorm (A k - A₀) 2 volume) atTop (𝓝 0))
    (hlimB : Tendsto (fun k => eLpNorm (B k - B₀) 2 volume) atTop (𝓝 0)) (z : Vec 2) :
    Tendsto (fun k => ampFun r (A k) (B k) z) atTop (𝓝 (ampFun r A₀ B₀ z)) := by
  set V := volume {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} ^ (1 / 2 : ℝ) with hV
  have hVt : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (amplitudeBall_volume_lt_top r).ne
  set b : ℕ → ℝ≥0∞ := fun k => (eLpNorm (A k - A₀) 2 volume + eLpNorm (B k - B₀) 2 volume) * V
    with hb
  have hbt : Tendsto b atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const (hlimA.add hlimB) (Or.inr hVt)
    simpa [hb] using this
  have hbfin : ∀ k, b k ≠ ⊤ := fun k => ENNReal.mul_ne_top
    (ENNReal.add_ne_top.2 ⟨MemLp.eLpNorm_ne_top ((hA k).sub hA₀),
      MemLp.eLpNorm_ne_top ((hB k).sub hB₀)⟩) hVt
  have hbound : ∀ k, ‖ampFun r (A k) (B k) z - ampFun r A₀ B₀ z‖ ≤ (b k).toReal := by
    intro k
    have hiA := integrableOn_ampBall_of_memLp ((hA k).sub hA₀) r
    have hiB := integrableOn_ampBall_of_memLp ((hB k).sub hB₀) r
    have hdiff : ampFun r (A k) (B k) z - ampFun r A₀ B₀ z =
        ampFun r (A k - A₀) (B k - B₀) z := by
      have h := congrFun (ampFun_add_smul (integrableOn_ampBall_of_memLp (hA k) r)
        (integrableOn_ampBall_of_memLp (hB k) r) (integrableOn_ampBall_of_memLp hA₀ r)
        (integrableOn_ampBall_of_memLp hB₀ r) 1 (-1)) z
      simp only [one_smul, neg_one_smul, ← sub_eq_add_neg] at h
      rw [← h]
      rfl
    rw [hdiff]
    refine (norm_ampFun_le hiA hiB z).trans ?_
    rw [integral_add hiA.norm hiB.norm]
    have e1 := eLpNorm_one_ampBall_le (MemLp.aestronglyMeasurable ((hA k).sub hA₀)) r
    have e2 := eLpNorm_one_ampBall_le (MemLp.aestronglyMeasurable ((hB k).sub hB₀)) r
    have i1 : ∫ θ in {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}, ‖(A k - A₀) θ‖ =
        (eLpNorm (A k - A₀) 1 (volume.restrict {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm]
      all_goals exact hiA.1
    have i2 : ∫ θ in {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}, ‖(B k - B₀) θ‖ =
        (eLpNorm (B k - B₀) 1 (volume.restrict {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm]
      all_goals exact hiB.1
    rw [i1, i2, ← ENNReal.toReal_add (ne_of_lt (memLp_one_iff_integrable.2 hiA))
      (ne_of_lt (memLp_one_iff_integrable.2 hiB))]
    refine ENNReal.toReal_mono (hbfin k) ?_
    simp only [hb, add_mul]
    exact add_le_add e1 e2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hbt
  rw [ENNReal.toReal_zero] at this
  exact this

end Amp

section Moment

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- **The moment norm is absolutely homogeneous** (one direction). -/
theorem momentNorm_smul_le (π : ι → ℝ) (n : ℕ) (s c : ℝ) (F : ∀ v, Vec 2 → h v) :
    momentNorm π n s (fun v z => c • F v z) ≤ ‖c‖ₑ * momentNorm π n s F := by
  unfold momentNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun β _ => ?_
  rw [mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  have he : ∀ v, eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • c • F v z) 2 volume =
      ‖c‖ₑ * eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • F v z) 2 volume := fun v => by
    rw [← eLpNorm_const_smul]
    congr 1
    funext z
    simp only [Pi.smul_apply]
    rw [smul_comm]
  simp_rw [he, mul_pow, ← mul_assoc, mul_comm _ (‖c‖ₑ ^ 2), mul_assoc, ← Finset.mul_sum]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

end Moment
end

/-! # Extending an amplitude assignment from compact data by `L²` limits

An amplitude assignment on smooth compactly supported families that is linear and bounded in `L²`
by a moment norm (`IsAmpAssignment`) has, at every measurable field of finite moment norm, an `L²`
limit along approximating sequences of compact data (`ampLim`); the amplitudes along *every* such
sequence converge to it (`tendsto_ampLim`). -/

section
section Extension

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- Smooth compactly supported families. -/
def IsCompactFamily (φ : ∀ x, Vec 2 → h x) : Prop :=
  ∀ x, ContDiff ℝ (⊤ : ℕ∞) (φ x) ∧ HasCompactSupport (φ x)

omit [Fintype ι] in
theorem IsCompactFamily.add_smul {φ ψ : ∀ x, Vec 2 → h x} (hφ : IsCompactFamily φ)
    (hψ : IsCompactFamily ψ) (a b : ℝ) : IsCompactFamily fun x z => a • φ x z + b • ψ x z :=
  fun x => ⟨((hφ x).1.const_smul a).add ((hψ x).1.const_smul b),
    ((hφ x).2.smul_left (f := fun _ => a)).add ((hψ x).2.smul_left (f := fun _ => b))⟩

/-- A linear assignment of amplitudes to compact data, bounded in `L²` by the moment norm. -/
structure IsAmpAssignment (π : ι → ℝ) (n : ℕ) (s : ℝ) (Cx : ι → ℝ)
    (amp : (∀ x, Vec 2 → h x) → ∀ x, Vec 2 → h x) : Prop where
  lin : ∀ φ ψ, IsCompactFamily φ → IsCompactFamily ψ → ∀ a b : ℝ,
    amp (fun x z => a • φ x z + b • ψ x z) = fun x θ => a • amp φ x θ + b • amp ψ x θ
  mem : ∀ φ, IsCompactFamily φ → ∀ x, MemLp (amp φ x) 2 volume
  bd : ∀ φ, IsCompactFamily φ → ∀ x,
    eLpNorm (amp φ x) 2 volume ≤ ENNReal.ofReal (Cx x) * momentNorm π n s φ

open Classical in
/-- The `L²` limit of the amplitudes along compact data approximating `F`, `0` if there is none. -/
noncomputable def ampLim (π : ι → ℝ) (n : ℕ) (s : ℝ) (amp : (∀ x, Vec 2 → h x) → ∀ x, Vec 2 → h x)
    (F : ∀ x, Vec 2 → h x) (x : ι) : Vec 2 → h x :=
  if hA : ∃ A : Vec 2 → h x, MemLp A 2 volume ∧ ∃ φs : ℕ → ∀ y, Vec 2 → h y,
      (∀ k, IsCompactFamily (φs k)) ∧
      Tendsto (fun k => momentNorm π n s (fun y z => F y z - φs k y z)) atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (amp (φs k) x - A) 2 volume) atTop (𝓝 0)
  then hA.choose else 0

/-- The difference of two compact data in the amplitudes. -/
theorem IsAmpAssignment.sub {π : ι → ℝ} {n : ℕ} {s : ℝ} {Cx : ι → ℝ}
    {amp : (∀ x, Vec 2 → h x) → ∀ x, Vec 2 → h x} (hamp : IsAmpAssignment π n s Cx amp)
    {φ ψ : ∀ x, Vec 2 → h x} (hφ : IsCompactFamily φ) (hψ : IsCompactFamily ψ) (x : ι) :
    eLpNorm (amp φ x - amp ψ x) 2 volume ≤
      ENNReal.ofReal (Cx x) * momentNorm π n s (fun y z => φ y z - ψ y z) := by
  have hl := hamp.lin φ ψ hφ hψ 1 (-1)
  have he : amp φ x - amp ψ x = amp (fun y z => (1 : ℝ) • φ y z + (-1 : ℝ) • ψ y z) x := by
    rw [hl]
    funext θ
    simp [sub_eq_add_neg]
  have hm : (fun y z => φ y z - ψ y z) = fun y z => (1 : ℝ) • φ y z + (-1 : ℝ) • ψ y z := by
    funext y z
    simp [sub_eq_add_neg]
  rw [he, hm]
  exact hamp.bd _ (hφ.add_smul hψ 1 (-1)) x

/-- The moment distance of two approximants. -/
theorem momentNorm_sub_le_approx (π : ι → ℝ) (n : ℕ) (s : ℝ) (F φ ψ : ∀ x, Vec 2 → h x) :
    momentNorm π n s (fun y z => φ y z - ψ y z) ≤
      momentNorm π n s (fun y z => F y z - φ y z) +
        momentNorm π n s (fun y z => F y z - ψ y z) := by
  have hs : (fun y z => φ y z - ψ y z) =
      fun y z => (fun y z => φ y z - F y z) y z + (fun y z => F y z - ψ y z) y z := by
    funext y z
    simp
  rw [hs]
  refine (momentNorm_add_le π n s _ _).trans (le_of_eq ?_)
  rw [momentNorm_sub_comm]

/-- The amplitudes of two approximating sequences come together. -/
theorem tendsto_amp_pair {π : ι → ℝ} {n : ℕ} {s : ℝ} {Cx : ι → ℝ}
    {amp : (∀ x, Vec 2 → h x) → ∀ x, Vec 2 → h x} (hamp : IsAmpAssignment π n s Cx amp)
    {F : ∀ x, Vec 2 → h x} {as bs : ℕ → ∀ y, Vec 2 → h y} (has : ∀ k, IsCompactFamily (as k))
    (hbs : ∀ k, IsCompactFamily (bs k))
    (hac : Tendsto (fun k => momentNorm π n s (fun y z => F y z - as k y z)) atTop (𝓝 0))
    (hbc : Tendsto (fun k => momentNorm π n s (fun y z => F y z - bs k y z)) atTop (𝓝 0))
    (x : ι) :
    Tendsto (fun p : ℕ × ℕ => eLpNorm (amp (as p.1) x - amp (bs p.2) x) 2 volume) atTop (𝓝 0) := by
  have h1 : Tendsto (fun p : ℕ × ℕ => momentNorm π n s (fun y z => F y z - as p.1 y z))
      atTop (𝓝 0) := by
    rw [← prod_atTop_atTop_eq]
    exact hac.comp tendsto_fst
  have h2 : Tendsto (fun p : ℕ × ℕ => momentNorm π n s (fun y z => F y z - bs p.2 y z))
      atTop (𝓝 0) := by
    rw [← prod_atTop_atTop_eq]
    exact hbc.comp tendsto_snd
  have hu := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Cx x)) (h1.add h2)
    (Or.inr ENNReal.ofReal_ne_top)
  rw [add_zero, mul_zero] at hu
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun _ => zero_le)
    fun p => ?_
  exact (hamp.sub (has p.1) (hbs p.2) x).trans
    (mul_le_mul' le_rfl (momentNorm_sub_le_approx π n s F _ _))

/-- The limit exists along an approximating sequence. -/
theorem exists_ampLim_witness [∀ i, CompleteSpace (h i)] {π : ι → ℝ} {n : ℕ} {s : ℝ}
    {Cx : ι → ℝ} {amp : (∀ x, Vec 2 → h x) → ∀ x, Vec 2 → h x}
    (hamp : IsAmpAssignment π n s Cx amp) {F : ∀ x, Vec 2 → h x}
    {φs : ℕ → ∀ y, Vec 2 → h y} (hφs : ∀ k, IsCompactFamily (φs k))
    (hφconv : Tendsto (fun k => momentNorm π n s (fun y z => F y z - φs k y z)) atTop (𝓝 0))
    (x : ι) :
    ∃ A : Vec 2 → h x, MemLp A 2 volume ∧ ∃ φs : ℕ → ∀ y, Vec 2 → h y,
      (∀ k, IsCompactFamily (φs k)) ∧
      Tendsto (fun k => momentNorm π n s (fun y z => F y z - φs k y z)) atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (amp (φs k) x - A) 2 volume) atTop (𝓝 0) := by
  have hc := tendsto_amp_pair hamp hφs hφs hφconv hφconv x
  obtain ⟨A, hA, hlim⟩ := exists_eLpNorm_limit (fun k => hamp.mem (φs k) (hφs k) x)
    fun ε hε => by
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hc.eventually (gt_mem_nhds hε))
      refine ⟨max N.1 N.2, fun k hk l hl => hN (k, l) ?_⟩
      exact Prod.mk_le_mk.2 ⟨(le_max_left _ _).trans hk, (le_max_right _ _).trans hl⟩
  exact ⟨A, hA, φs, hφs, hφconv, hlim⟩

/-- **Convergence of the amplitudes** along every approximating sequence of compact data. -/
theorem tendsto_ampLim [∀ i, CompleteSpace (h i)] {π : ι → ℝ} {n : ℕ} {s : ℝ} {Cx : ι → ℝ}
    {amp : (∀ x, Vec 2 → h x) → ∀ x, Vec 2 → h x} (hamp : IsAmpAssignment π n s Cx amp)
    {F : ∀ x, Vec 2 → h x} {φs : ℕ → ∀ y, Vec 2 → h y} (hφs : ∀ k, IsCompactFamily (φs k))
    (hφconv : Tendsto (fun k => momentNorm π n s (fun y z => F y z - φs k y z)) atTop (𝓝 0))
    {ψs : ℕ → ∀ y, Vec 2 → h y} (hψs : ∀ k, IsCompactFamily (ψs k))
    (hψconv : Tendsto (fun k => momentNorm π n s (fun y z => F y z - ψs k y z)) atTop (𝓝 0))
    (x : ι) :
    MemLp (ampLim π n s amp F x) 2 volume ∧
      Tendsto (fun k => eLpNorm (amp (ψs k) x - ampLim π n s amp F x) 2 volume) atTop (𝓝 0) := by
  have hex := exists_ampLim_witness hamp hφs hφconv x
  have hdef : ampLim π n s amp F x = hex.choose := by
    simp only [ampLim, hex, ↓reduceDIte]
  obtain ⟨hAmem, φs', hφs', hφ'conv, hφ'lim⟩ := hex.choose_spec
  rw [hdef]
  refine ⟨hAmem, ?_⟩
  have hd := tendsto_amp_pair hamp hψs hφs' hψconv hφ'conv x
  have hkk : Tendsto (fun k : ℕ => (k, k)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  have hsum := (hd.comp hkk).add hφ'lim
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun k => ?_
  have hs : amp (ψs k) x - hex.choose = (amp (ψs k) x - amp (φs' k) x) +
      (amp (φs' k) x - hex.choose) := by abel
  rw [hs]
  exact eLpNorm_add_le (by norm_num)

end Extension
end

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # Weighted lattice sums over the unit cell

`∑_k ⟨z+k⟩^{-4} ≤ latticeConst` for `z` in the unit cell (`⟨y⟩^4 ≥ (1+y₀²)(1+y₁²)`), hence by
Cauchy–Schwarz over the lattice and the tiling of the plane by translated cells,
`∫_cell (∑_k ⟨z+k⟩^n ‖g(z+k)‖)² ≤ latticeConst ∫ ⟨y⟩^{2n+4} ‖g(y)‖²`
(`lintegral_cell_latticeSum_sq_le`). -/

theorem rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Cauchy–Schwarz for finite sums in `[0, ∞]`. -/
theorem ennreal_sum_mul_sq_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 := by
  have h := ENNReal.inner_le_Lp_mul_Lq s f g Real.HolderConjugate.two_two
  simp only [ENNReal.rpow_two] at h
  calc (∑ i ∈ s, f i * g i) ^ 2
      ≤ ((∑ i ∈ s, f i ^ 2) ^ (1 / 2 : ℝ) * (∑ i ∈ s, g i ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
    _ = (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 := by rw [mul_pow, rpow_half_sq, rpow_half_sq]

/-- Cauchy–Schwarz for series in `[0, ∞]`. -/
theorem ennreal_tsum_mul_sq_le {ι : Type*} (f g : ι → ℝ≥0∞) :
    (∑' i, f i * g i) ^ 2 ≤ (∑' i, f i ^ 2) * ∑' i, g i ^ 2 := by
  have hfin : ∀ s : Finset ι, (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑' i, f i ^ 2) * ∑' i, g i ^ 2 :=
    fun s => (ennreal_sum_mul_sq_le s f g).trans
      (mul_le_mul' (ENNReal.sum_le_tsum s) (ENNReal.sum_le_tsum s))
  exact le_of_tendsto' (((ENNReal.continuous_pow 2).tendsto _).comp
    ENNReal.summable.hasSum) hfin

theorem one_add_sq_mul_le_jbracket_pow (y : Vec 2) :
    (1 + y 0 ^ 2) * (1 + y 1 ^ 2) ≤ jbracket y ^ 4 := by
  have h : jbracket y ^ 2 = 1 + (y 0 ^ 2 + y 1 ^ 2) := Real.sq_sqrt (by positivity)
  have h4 : jbracket y ^ 4 = (1 + (y 0 ^ 2 + y 1 ^ 2)) ^ 2 := by rw [← h]; ring
  rw [h4]
  nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), mul_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1))]

theorem one_add_sq_le_three_mul {t : ℝ} (ht : |t| ≤ 1) (m : ℝ) :
    1 + m ^ 2 ≤ 3 * (1 + (t + m) ^ 2) := by
  have ht2 : t ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg t]
  nlinarith [sq_nonneg (2 * t + m)]

theorem summable_inv_one_add_sq : Summable fun m : ℤ => (1 + (m : ℝ) ^ 2)⁻¹ := by
  have h := (Real.summable_one_div_int_add_rpow (1 / 2) 2).2 (by norm_num)
  refine (h.mul_left 2).of_nonneg_of_le (fun _ => by positivity) fun m => ?_
  have hne : (m : ℝ) + 1 / 2 ≠ 0 := by
    intro h0
    have : (2 * m + 1 : ℤ) = 0 := by exact_mod_cast (by linarith : 2 * (m : ℝ) + 1 = 0)
    omega
  have hpos : 0 < ((m : ℝ) + 1 / 2) ^ 2 := by positivity
  rw [Real.rpow_two, sq_abs, inv_eq_one_div, ← mul_div_assoc, mul_one,
    div_le_div_iff₀ (by positivity) hpos]
  nlinarith [sq_nonneg ((m : ℝ) - 1 / 2)]

/-- The constant of the lattice sum `∑_k ⟨z+k⟩^{-4}` over the unit cell. -/
noncomputable def latticeConst : ℝ≥0∞ :=
  9 * (∑' m : ℤ, ENNReal.ofReal ((1 + (m : ℝ) ^ 2)⁻¹)) ^ 2

theorem latticeConst_ne_top : latticeConst ≠ ⊤ := by
  unfold latticeConst
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) summable_inv_one_add_sq]
  exact ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem tsum_inv_jbracket_pow_le {z : Vec 2} (hz : ∀ i, |z i| ≤ 1) :
    ∑' k : Fin 2 → ℤ, ENNReal.ofReal ((jbracket (z + fun i => (k i : ℝ)) ^ 4)⁻¹) ≤
      latticeConst := by
  set a : ℤ → ℝ≥0∞ := fun m => ENNReal.ofReal ((1 + (m : ℝ) ^ 2)⁻¹) with ha
  have hterm : ∀ k : Fin 2 → ℤ, ENNReal.ofReal ((jbracket (z + fun i => (k i : ℝ)) ^ 4)⁻¹) ≤
      (3 * a (k 0)) * (3 * a (k 1)) := by
    intro k
    have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by norm_num
    rw [ha, h3, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := one_add_sq_mul_le_jbracket_pow (z + fun i => (k i : ℝ))
    have h0 := one_add_sq_le_three_mul (hz 0) (k 0 : ℝ)
    have h1' := one_add_sq_le_three_mul (hz 1) (k 1 : ℝ)
    simp only [Pi.add_apply] at h1
    calc (jbracket (z + fun i => (k i : ℝ)) ^ 4)⁻¹
        ≤ ((1 + (z 0 + k 0) ^ 2) * (1 + (z 1 + k 1) ^ 2))⁻¹ := inv_anti₀ (by positivity) h1
      _ ≤ ((1 + (k 0 : ℝ) ^ 2) / 3 * ((1 + (k 1 : ℝ) ^ 2) / 3))⁻¹ :=
          inv_anti₀ (by positivity) (mul_le_mul (by linarith) (by linarith) (by positivity)
            (by positivity))
      _ = 3 * (1 + (k 0 : ℝ) ^ 2)⁻¹ * (3 * (1 + (k 1 : ℝ) ^ 2)⁻¹) := by
          field_simp
  calc ∑' k : Fin 2 → ℤ, ENNReal.ofReal ((jbracket (z + fun i => (k i : ℝ)) ^ 4)⁻¹)
      ≤ ∑' k : Fin 2 → ℤ, (3 * a (k 0)) * (3 * a (k 1)) := ENNReal.tsum_le_tsum hterm
    _ = ∑' p : ℤ × ℤ, (3 * a p.1) * (3 * a p.2) :=
        (finTwoArrowEquiv ℤ).tsum_eq (fun p => (3 * a p.1) * (3 * a p.2))
    _ = latticeConst := by
        rw [ENNReal.tsum_prod']
        simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
        rw [ENNReal.tsum_mul_left, latticeConst, ← ha]
        ring

theorem abs_le_one_of_mem_cellI {z : Vec 2} (hz : z ∈ Applications.cellI) (i : Fin 2) :
    |z i| ≤ 1 := by
  have h := hz i (Set.mem_univ i)
  rw [abs_le]
  exact ⟨by linarith [h.1], h.2.le⟩

/-- **Cell integral of a squared weighted lattice sum.** -/
theorem lintegral_cell_latticeSum_sq_le {E : Type*} [NormedAddCommGroup E] {g : Vec 2 → E}
    (hg : Measurable fun y => ‖g y‖) (n : ℕ) :
    ∫⁻ z in Applications.cellI, (∑' k : Fin 2 → ℤ, ENNReal.ofReal
        (jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g (z + fun i => (k i : ℝ))‖)) ^ 2 ≤
      latticeConst * ∫⁻ y, ENNReal.ofReal (jbracket y ^ (2 * n + 4) * ‖g y‖ ^ 2) := by
  have hjc : Continuous jbracket := jbracket_contDiff.continuous
  have hmeas : Measurable fun y => ENNReal.ofReal (jbracket y ^ (2 * n + 4) * ‖g y‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hjc.measurable.pow_const _).mul (hg.pow_const 2))
  have hmk : ∀ k : Fin 2 → ℤ, Measurable fun z : Vec 2 => ENNReal.ofReal
      (jbracket (z + fun i => (k i : ℝ)) ^ (2 * n + 4) *
        ‖g (z + fun i => (k i : ℝ))‖ ^ 2) := fun k => hmeas.comp (measurable_add_const _)
  have hpt : ∀ z ∈ Applications.cellI, (∑' k : Fin 2 → ℤ, ENNReal.ofReal
      (jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g (z + fun i => (k i : ℝ))‖)) ^ 2 ≤
      latticeConst * ∑' k : Fin 2 → ℤ, ENNReal.ofReal
        (jbracket (z + fun i => (k i : ℝ)) ^ (2 * n + 4) * ‖g (z + fun i => (k i : ℝ))‖ ^ 2) := by
    intro z hz
    have hfac : ∀ k : Fin 2 → ℤ, ENNReal.ofReal
        (jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g (z + fun i => (k i : ℝ))‖) =
        ENNReal.ofReal ((jbracket (z + fun i => (k i : ℝ)) ^ 2)⁻¹) *
          ENNReal.ofReal (jbracket (z + fun i => (k i : ℝ)) ^ (n + 2) *
            ‖g (z + fun i => (k i : ℝ))‖) := by
      intro k
      have hj := jbracket_pos (z + fun i => (k i : ℝ))
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring
    rw [tsum_congr hfac]
    refine (ennreal_tsum_mul_sq_le _ _).trans (mul_le_mul' ?_ (le_of_eq ?_))
    · refine le_trans (le_of_eq (tsum_congr fun k => ?_)) (tsum_inv_jbracket_pow_le
        (abs_le_one_of_mem_cellI hz))
      rw [← ENNReal.ofReal_pow (inv_nonneg.2 (pow_nonneg (jbracket_pos _).le 2))]
      congr 1
      ring
    · refine tsum_congr fun k => ?_
      rw [← ENNReal.ofReal_pow (mul_nonneg (pow_nonneg (jbracket_pos _).le _) (norm_nonneg _))]
      congr 1
      ring
  calc ∫⁻ z in Applications.cellI, (∑' k : Fin 2 → ℤ, ENNReal.ofReal
        (jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g (z + fun i => (k i : ℝ))‖)) ^ 2
      ≤ ∫⁻ z in Applications.cellI, latticeConst * ∑' k : Fin 2 → ℤ, ENNReal.ofReal
        (jbracket (z + fun i => (k i : ℝ)) ^ (2 * n + 4) *
          ‖g (z + fun i => (k i : ℝ))‖ ^ 2) :=
        setLIntegral_mono (measurable_const.mul (Measurable.tsum hmk)) hpt
    _ = latticeConst * ∑' k : Fin 2 → ℤ, ∫⁻ z in Applications.cellI, ENNReal.ofReal
        (jbracket (z + fun i => (k i : ℝ)) ^ (2 * n + 4) *
          ‖g (z + fun i => (k i : ℝ))‖ ^ 2) := by
        rw [lintegral_const_mul _ (Measurable.tsum hmk),
          lintegral_tsum fun k => (hmk k).aemeasurable]
    _ = latticeConst * ∫⁻ y, ENNReal.ofReal (jbracket y ^ (2 * n + 4) * ‖g y‖ ^ 2) := by
        rw [CycleJointProofs.lintegral_tiling_translate _ hmeas]
        rfl

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The band and the finite-moment subspaces

Measurable fields of finite moment norm form a submodule (`finiteMomentSubmodule`), and so do the
fields whose components are smooth of every order with Fourier support in a ball
(`bandSubmodule`; amplitude pairs add, `IsRetainedAmplitude.add_smul`). A band-limited function
with amplitudes integrable on the ball has the amplitudes cut off to the ball
(`isRetainedAmplitude_ampFun`). Smooth compactly supported families have finite moment norm
(`momentNorm_lt_top_of_compact`). -/

section
universe v

section Amplitude

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsRetainedAmplitude.add_smul {g g' A A' B B' : Vec 2 → E} {r : ℝ}
    (hg : IsRetainedAmplitude g r A B) (hg' : IsRetainedAmplitude g' r A' B') (a b : ℝ) :
    IsRetainedAmplitude (fun z => a • g z + b • g' z) r (fun θ => a • A θ + b • A' θ)
      (fun θ => a • B θ + b • B' θ) := by
  obtain ⟨hv, hA, hB, hrep⟩ := hg
  obtain ⟨hv', hA', hB', hrep'⟩ := hg'
  refine ⟨fun θ hθ => ?_, (hA.smul a).add (hA'.smul b), (hB.smul a).add (hB'.smul b), fun z => ?_⟩
  · simp [(hv θ hθ).1, (hv θ hθ).2, (hv' θ hθ).1, (hv' θ hθ).2]
  · show a • g z + b • g' z = _
    rw [hrep z, hrep' z]
    exact (congrFun (ampFun_add_smul hA hB hA' hB' a b) z).symm

theorem measurableSet_ampBall (r : ℝ) : MeasurableSet {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} :=
  measurableSet_le (by unfold vecDot; fun_prop) measurable_const

/-- A band-limited function has its amplitudes cut off to the ball. -/
theorem isRetainedAmplitude_ampFun {r : ℝ} {A B : Vec 2 → E}
    (hA : IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hB : IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) :
    IsRetainedAmplitude (ampFun r A B) r ({θ : Vec 2 | vecDot θ θ ≤ r ^ 2}.indicator A)
      ({θ : Vec 2 | vecDot θ θ ≤ r ^ 2}.indicator B) := by
  have hm := measurableSet_ampBall r
  refine ⟨fun θ hθ => ?_, ?_, ?_, fun z => ?_⟩
  · have hn : θ ∉ {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} := fun h' => absurd h' (not_le.2 hθ)
    exact ⟨Set.indicator_of_notMem hn A, Set.indicator_of_notMem hn B⟩
  · exact hA.congr_fun (fun θ hθ => (Set.indicator_of_mem hθ A).symm) hm
  · exact hB.congr_fun (fun θ hθ => (Set.indicator_of_mem hθ B).symm) hm
  · unfold ampFun
    refine setIntegral_congr_fun hm fun θ hθ => ?_
    simp only [Set.indicator_of_mem hθ]

end Amplitude

section Submodules

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem momentNorm_zero_family (π : ι → ℝ) (n : ℕ) (s : ℝ) :
    momentNorm π n s (0 : ∀ x, Vec 2 → h x) = 0 := by
  unfold momentNorm
  refine Finset.sum_eq_zero fun β _ => ?_
  simp [ENNReal.zero_rpow_of_pos]

/-- Measurable fields of finite moment norm. -/
def finiteMomentSubmodule (π : ι → ℝ) (n : ℕ) (s : ℝ) : Submodule ℝ (∀ x, Vec 2 → h x) where
  carrier := {F | (∀ x, AEStronglyMeasurable (F x) volume) ∧ momentNorm π n s F < ⊤}
  zero_mem' := ⟨fun _ => aestronglyMeasurable_const, by
    rw [momentNorm_zero_family]
    exact ENNReal.zero_lt_top⟩
  add_mem' := fun {F G} hF hG => ⟨fun x => (hF.1 x).add (hG.1 x),
    (momentNorm_add_le π n s F G).trans_lt (ENNReal.add_lt_top.2 ⟨hF.2, hG.2⟩)⟩
  smul_mem' := fun c F hF => ⟨fun x => (hF.1 x).const_smul c,
    (momentNorm_smul_le π n s c F).trans_lt (ENNReal.mul_lt_top enorm_lt_top hF.2)⟩

/-- Fields smooth of every order with Fourier support in the ball of radius `r`. -/
def bandSubmodule (r : ℝ) : Submodule ℝ (∀ x, Vec 2 → h x) where
  carrier := {G | ∀ x, (∀ M : ℕ, ContDiff ℝ M (G x)) ∧ HasFourierSupportIn (G x) r}
  zero_mem' := fun _ => ⟨fun _ => contDiff_const, ⟨_, _, isRetainedAmplitude_zero r⟩⟩
  add_mem' := fun {F G} hF hG x => ⟨fun M => ((hF x).1 M).add ((hG x).1 M), by
    obtain ⟨A, B, hAB⟩ := (hF x).2
    obtain ⟨A', B', hAB'⟩ := (hG x).2
    have := IsRetainedAmplitude.add_smul hAB hAB' 1 1
    simp only [one_smul] at this
    exact ⟨_, _, this⟩⟩
  smul_mem' := fun c F hF x => ⟨fun M => ((hF x).1 M).const_smul c, by
    obtain ⟨A, B, hAB⟩ := (hF x).2
    have := IsRetainedAmplitude.add_smul hAB hAB c 0
    simp only [zero_smul, add_zero] at this
    exact ⟨_, _, this⟩⟩

omit [Fintype ι] in
theorem IsCompactFamily.aestronglyMeasurable {φ : ∀ x, Vec 2 → h x} (hφ : IsCompactFamily φ)
    (x : ι) : AEStronglyMeasurable (φ x) volume :=
  (hφ x).1.continuous.aestronglyMeasurable

/-- Smooth compactly supported families have finite moment norm. -/
theorem momentNorm_lt_top_of_compact (π : ι → ℝ) (n : ℕ) (s : ℝ) {φ : ∀ x, Vec 2 → h x}
    (hφ : IsCompactFamily φ) : momentNorm π n s φ < ⊤ := by
  unfold momentNorm
  refine ENNReal.sum_lt_top.2 fun β _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.sum_lt_top.2 fun x _ =>
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_).ne
  have hc : Continuous fun z : Vec 2 => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • φ x z :=
    (by fun_prop : Continuous fun z : Vec 2 => (s * z 0) ^ β.1 * (s * z 1) ^ β.2).smul
      (hφ x).1.continuous
  have hs : HasCompactSupport fun z : Vec 2 => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • φ x z :=
    (hφ x).2.smul_left
  exact ENNReal.pow_lt_top (hc.memLp_of_hasCompactSupport hs)

end Submodules
end

/-! # The limit amplitudes are linear

On the measurable fields of finite moment norm, the limit amplitudes `ampLim` of an amplitude
assignment agree with the assignment on compact data (`ampLim_compact_ae`), vanish on null fields
(`ampLim_null_ae`) and are linear (`ampLim_add_smul_ae`), all up to null sets. -/

section
section Limits

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The density of compact data in the finite moment norms (A4, second conjunct). -/
def IsCompactDense (F : ∀ x, Vec 2 → h x) : Prop :=
  ∃ φs : ℕ → ∀ x, Vec 2 → h x, (∀ k, IsCompactFamily (φs k)) ∧
    ∀ (π : ι → ℝ) (n : ℕ) (s : ℝ), momentNorm π n s F < ⊤ →
      Tendsto (fun k => momentNorm π n s (fun x z => F x z - φs k x z)) atTop (𝓝 0)

theorem momentNorm_eq_zero_of_ae (π : ι → ℝ) (n : ℕ) (s : ℝ) {F : ∀ x, Vec 2 → h x}
    (hF : ∀ x, F x =ᵐ[volume] 0) : momentNorm π n s F = 0 := by
  unfold momentNorm
  refine Finset.sum_eq_zero fun β _ => ?_
  have h0 : ∀ x, eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • F x z) 2 volume = 0 :=
    fun x => by
      rw [eLpNorm_eq_zero_iff two_ne_zero]
      filter_upwards [hF x] with z hz
      simp [hz]
  simp [h0, ENNReal.zero_rpow_of_pos]

omit [Fintype ι] in
theorem isCompactFamily_zero : IsCompactFamily (0 : ∀ x, Vec 2 → h x) :=
  fun _ => ⟨contDiff_const, HasCompactSupport.zero⟩

variable {π : ι → ℝ} {n : ℕ} {s : ℝ} {Cx : ι → ℝ} {amp : (∀ x, Vec 2 → h x) → ∀ x, Vec 2 → h x}

theorem IsAmpAssignment.amp_zero (hamp : IsAmpAssignment π n s Cx amp) : amp 0 = 0 := by
  have hl := hamp.lin 0 0 isCompactFamily_zero isCompactFamily_zero 0 0
  have h0 : (fun x z => (0 : ℝ) • (0 : ∀ x, Vec 2 → h x) x z +
      (0 : ℝ) • (0 : ∀ x, Vec 2 → h x) x z) = (0 : ∀ x, Vec 2 → h x) := by
    funext x z
    simp
  rw [h0] at hl
  rw [hl]
  funext x θ
  simp

variable [∀ i, CompleteSpace (h i)]

omit [∀ i, CompleteSpace (h i)] in
/-- The approximating sequence of a field in the finite-moment subspace. -/
theorem exists_compact_approx {F : ∀ x, Vec 2 → h x} (hd : IsCompactDense F)
    (hF : F ∈ finiteMomentSubmodule π n s) : ∃ φs : ℕ → ∀ x, Vec 2 → h x,
      (∀ k, IsCompactFamily (φs k)) ∧
      Tendsto (fun k => momentNorm π n s (fun x z => F x z - φs k x z)) atTop (𝓝 0) := by
  obtain ⟨φs, hφs, hconv⟩ := hd
  exact ⟨φs, hφs, hconv π n s hF.2⟩

theorem ampLim_memLp (hamp : IsAmpAssignment π n s Cx amp) {F : ∀ x, Vec 2 → h x}
    (hd : IsCompactDense F) (hF : F ∈ finiteMomentSubmodule π n s) (x : ι) :
    MemLp (ampLim π n s amp F x) 2 volume := by
  obtain ⟨φs, hφs, hconv⟩ := exists_compact_approx hd hF
  exact (tendsto_ampLim hamp hφs hconv hφs hconv x).1

/-- Along any compact approximation, the amplitudes converge to the limit amplitude. -/
theorem tendsto_ampLim_of_approx (hamp : IsAmpAssignment π n s Cx amp) {F : ∀ x, Vec 2 → h x}
    (hd : IsCompactDense F) (hF : F ∈ finiteMomentSubmodule π n s)
    {ψs : ℕ → ∀ y, Vec 2 → h y} (hψs : ∀ k, IsCompactFamily (ψs k))
    (hψconv : Tendsto (fun k => momentNorm π n s (fun y z => F y z - ψs k y z)) atTop (𝓝 0))
    (x : ι) :
    Tendsto (fun k => eLpNorm (amp (ψs k) x - ampLim π n s amp F x) 2 volume) atTop (𝓝 0) := by
  obtain ⟨φs, hφs, hconv⟩ := exists_compact_approx hd hF
  exact (tendsto_ampLim hamp hφs hconv hψs hψconv x).2

theorem eLpNorm_eq_zero_of_tendsto_const {E : Type*} [NormedAddCommGroup E] {X : Vec 2 → E}
    (h0 : Tendsto (fun _ : ℕ => eLpNorm X 2 volume) atTop (𝓝 0)) : X =ᵐ[volume] 0 := by
  have hz : eLpNorm X 2 volume = 0 := tendsto_nhds_unique tendsto_const_nhds h0
  exact (eLpNorm_eq_zero_iff two_ne_zero).1 hz

/-- **On compact data**, the limit amplitude is the amplitude. -/
theorem ampLim_compact_ae (hamp : IsAmpAssignment π n s Cx amp) {φ : ∀ x, Vec 2 → h x}
    (hφ : IsCompactFamily φ) (hd : IsCompactDense φ) (x : ι) :
    ampLim π n s amp φ x =ᵐ[volume] amp φ x := by
  have hW : φ ∈ finiteMomentSubmodule π n s :=
    ⟨hφ.aestronglyMeasurable, momentNorm_lt_top_of_compact π n s hφ⟩
  have hc : Tendsto (fun _ : ℕ => momentNorm π n s (fun y z => φ y z - φ y z)) atTop (𝓝 0) := by
    have : momentNorm π n s (fun y z => φ y z - φ y z) = 0 :=
      momentNorm_eq_zero_of_ae π n s fun y => Eventually.of_forall fun z => by simp
    rw [this]
    exact tendsto_const_nhds
  have ht := tendsto_ampLim_of_approx hamp hd hW (fun _ => hφ) hc x
  filter_upwards [eLpNorm_eq_zero_of_tendsto_const ht] with θ hθ
  exact (sub_eq_zero.1 hθ).symm

/-- **On null fields**, the limit amplitude vanishes. -/
theorem ampLim_null_ae (hamp : IsAmpAssignment π n s Cx amp) {N : ∀ x, Vec 2 → h x}
    (hN : ∀ x, N x =ᵐ[volume] 0) (hd : IsCompactDense N) (x : ι) :
    ampLim π n s amp N x =ᵐ[volume] 0 := by
  have hm : momentNorm π n s N = 0 := momentNorm_eq_zero_of_ae π n s hN
  have hW : N ∈ finiteMomentSubmodule π n s :=
    ⟨fun y => aestronglyMeasurable_zero.congr (hN y).symm, by rw [hm]; exact ENNReal.zero_lt_top⟩
  have hc : Tendsto (fun _ : ℕ => momentNorm π n s
      (fun y z => N y z - (0 : ∀ x, Vec 2 → h x) y z)) atTop (𝓝 0) := by
    have : momentNorm π n s (fun y z => N y z - (0 : ∀ x, Vec 2 → h x) y z) = 0 :=
      momentNorm_eq_zero_of_ae π n s fun y => (hN y).mono fun z hz => by simp [hz]
    rw [this]
    exact tendsto_const_nhds
  have ht := tendsto_ampLim_of_approx hamp hd hW (fun _ => isCompactFamily_zero) hc x
  rw [hamp.amp_zero] at ht
  filter_upwards [eLpNorm_eq_zero_of_tendsto_const ht] with θ hθ
  simpa using hθ

/-- **Linearity** of the limit amplitudes. -/
theorem ampLim_add_smul_ae (hamp : IsAmpAssignment π n s Cx amp) {F G : ∀ x, Vec 2 → h x}
    (hdF : IsCompactDense F) (hdG : IsCompactDense G) (hF : F ∈ finiteMomentSubmodule π n s)
    (hG : G ∈ finiteMomentSubmodule π n s) (a b : ℝ)
    (hdFG : IsCompactDense fun y z => a • F y z + b • G y z) (x : ι) :
    ampLim π n s amp (fun y z => a • F y z + b • G y z) x =ᵐ[volume]
      fun θ => a • ampLim π n s amp F x θ + b • ampLim π n s amp G x θ := by
  obtain ⟨φF, hφF, hcF⟩ := exists_compact_approx hdF hF
  obtain ⟨φG, hφG, hcG⟩ := exists_compact_approx hdG hG
  set ψs : ℕ → ∀ y, Vec 2 → h y := fun k y z => a • φF k y z + b • φG k y z with hψs
  have hψ : ∀ k, IsCompactFamily (ψs k) := fun k => (hφF k).add_smul (hφG k) a b
  have hFG : (fun y z => a • F y z + b • G y z) ∈ finiteMomentSubmodule π n s :=
    (finiteMomentSubmodule π n s).add_mem ((finiteMomentSubmodule π n s).smul_mem a hF)
      ((finiteMomentSubmodule π n s).smul_mem b hG)
  have hbd : ∀ k, momentNorm π n s (fun y z => (a • F y z + b • G y z) - ψs k y z) ≤
      ‖a‖ₑ * momentNorm π n s (fun y z => F y z - φF k y z) +
        ‖b‖ₑ * momentNorm π n s (fun y z => G y z - φG k y z) := by
    intro k
    have he : (fun y z => (a • F y z + b • G y z) - ψs k y z) =
        fun y z => (fun y z => a • (F y z - φF k y z)) y z +
          (fun y z => b • (G y z - φG k y z)) y z := by
      funext y z
      simp only [hψs, smul_sub]
      abel
    rw [he]
    exact (momentNorm_add_le π n s _ _).trans (add_le_add
      (momentNorm_smul_le π n s a fun y z => F y z - φF k y z)
      (momentNorm_smul_le π n s b fun y z => G y z - φG k y z))
  have hlimbd := (ENNReal.Tendsto.const_mul (a := ‖a‖ₑ) hcF (Or.inr enorm_ne_top)).add
    (ENNReal.Tendsto.const_mul (a := ‖b‖ₑ) hcG (Or.inr enorm_ne_top))
  rw [mul_zero, mul_zero, add_zero] at hlimbd
  have hψconv : Tendsto (fun k => momentNorm π n s
      (fun y z => (a • F y z + b • G y z) - ψs k y z)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimbd (fun _ => zero_le) hbd
  have ht1 := tendsto_ampLim_of_approx hamp hdFG hFG hψ hψconv x
  have htF := tendsto_ampLim_of_approx hamp hdF hF hφF hcF x
  have htG := tendsto_ampLim_of_approx hamp hdG hG hφG hcG x
  have ht2 : Tendsto (fun k => eLpNorm (amp (ψs k) x -
      fun θ => a • ampLim π n s amp F x θ + b • ampLim π n s amp G x θ) 2 volume) atTop (𝓝 0) := by
    have hlim2 := (ENNReal.Tendsto.const_mul (a := ‖a‖ₑ) htF (Or.inr enorm_ne_top)).add
      (ENNReal.Tendsto.const_mul (a := ‖b‖ₑ) htG (Or.inr enorm_ne_top))
    rw [mul_zero, mul_zero, add_zero] at hlim2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim2 (fun _ => zero_le)
      fun k => ?_
    have hl := congrFun (hamp.lin (φF k) (φG k) (hφF k) (hφG k) a b) x
    have he : amp (ψs k) x - (fun θ => a • ampLim π n s amp F x θ + b • ampLim π n s amp G x θ) =
        a • (amp (φF k) x - ampLim π n s amp F x) + b • (amp (φG k) x - ampLim π n s amp G x) := by
      rw [show amp (ψs k) x = _ from hl]
      funext θ
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_sub]
      abel
    rw [he]
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ ?_)
    · rw [eLpNorm_const_smul]
    · rw [eLpNorm_const_smul]
  exact ae_eq_of_tendsto_eLpNorm ht1 ht2

end Limits

section Fatou

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The moment norm of order `0` as an unweighted jet norm with zero padding. -/
theorem weightedJetNorm_pad (π : ι → ℝ) (s r : ℝ) {G : ∀ x, Vec 2 → h x}
    (hG : ∀ x, AEStronglyMeasurable (G x) volume) :
    weightedJetNorm π 0 0 s r (fun x a _ z => if a = 0 then G x z else 0) =
      momentNorm π 0 1 G := by
  have hidx : momentIndices 0 = {(0, 0)} := by decide
  simp only [weightedJetNorm, momentNorm, hidx, Finset.sum_singleton, zero_add,
    Finset.range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one,
    ENNReal.ofReal_one, one_mul, inv_one, one_smul, ↓reduceIte, zero_div, Real.rpow_zero,
    Fintype.sum_unique, Real.sqrt_sq_eq_abs, abs_norm]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by rw [eLpNorm_norm (G x) (hG x)]

/-- **Fatou for the moment norm of order `0`.** -/
theorem momentNorm_zero_le_liminf (π : ι → ℝ) {G : ℕ → ∀ x, Vec 2 → h x}
    {G₀ : ∀ x, Vec 2 → h x} (hG : ∀ k x, AEStronglyMeasurable (G k x) volume)
    (hG₀ : ∀ x, AEStronglyMeasurable (G₀ x) volume)
    (hlim : ∀ x z, Tendsto (fun k => G k x z) atTop (𝓝 (G₀ x z))) :
    momentNorm π 0 1 G₀ ≤ liminf (fun k => momentNorm π 0 1 (G k)) atTop := by
  rw [← weightedJetNorm_pad π 1 1 hG₀]
  simp_rw [← weightedJetNorm_pad π 1 1 (hG _)]
  refine weightedJetNorm_le_liminf π 0 0 1 1 _ _ (fun k x a w => ?_) (fun x a w => ?_)
    (fun x a w z => ?_)
  · by_cases ha : a = 0
    · simp only [ha, ↓reduceIte]
      exact hG k x
    · simp only [ha, ↓reduceIte]
      exact aestronglyMeasurable_const
  · by_cases ha : a = 0
    · simp only [ha, ↓reduceIte]
      exact hG₀ x
    · simp only [ha, ↓reduceIte]
      exact aestronglyMeasurable_const
  · by_cases ha : a = 0
    · simp only [ha, ↓reduceIte]
      exact hlim x z
    · simp only [ha, ↓reduceIte]
      exact tendsto_const_nhds

end Fatou
end

end AVRegularity.CycleWords.Assembly
end
