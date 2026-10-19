-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Wellposed.Existence
public import AVRegularity.Applications.Tubes.Periodic
import AVRegularity.Applications.Microscopic.Main
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVenhance.Infra.Parabolic.FourierGalerkin.WeakGradientPeriodization
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Applications

/-! # Restriction and continuation of weak solutions on windows

A weak solution on `[t₁, t₂]` restricts to a weak solution on `[t₁, t₃]` for `t₁ < t₃ ≤ t₂`;
with uniqueness, the
solution on a longer window agrees with the given one on the shorter window. -/

theorem isWeakSolutionOn_restrict {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ t₃ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} (h32 : t₃ ≤ t₂) (h : IsWeakSolutionOn b κ t₁ t₂ f θ) :
    IsWeakSolutionOn b κ t₁ t₃ f θ := by
  obtain ⟨Dθ, hslice, ⟨C, hC⟩, hL2, hDL2, hH1, hint, hcont, hweak⟩ := h
  have hIcc : Set.Icc t₁ t₃ ⊆ Set.Icc t₁ t₂ := Set.Icc_subset_Icc le_rfl h32
  have hIoo : Set.Ioo t₁ t₃ ×ˢ unitCube ⊆ Set.Ioo t₁ t₂ ×ˢ unitCube :=
    Set.prod_mono (Set.Ioo_subset_Ioo le_rfl h32) le_rfl
  have hmono : volume.restrict (Set.Ioo t₁ t₃ ×ˢ unitCube) ≤
      volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube) := Measure.restrict_mono hIoo le_rfl
  refine ⟨Dθ, fun t ht => hslice t (hIcc ht), ⟨C, fun t ht => hC t (hIcc ht)⟩,
    hL2.mono_measure hmono, fun i => (hDL2 i).mono_measure hmono, ?_, hint.mono_measure hmono,
    fun ψ hψ hψp => (hcont ψ hψ hψp).mono hIcc, ?_⟩
  · exact ae_restrict_of_ae_restrict_of_subset (Set.Ioo_subset_Ioo le_rfl h32) hH1
  · intro φ hφ
    obtain ⟨hsm, hper, hvan⟩ := hφ
    have hφ2 : IsWindowTestFunction t₂ φ := ⟨hsm, hper, fun t ht x => hvan t (h32.trans ht) x⟩
    have hw := hweak φ hφ2
    have hzero : ∀ p ∈ Set.Ioo t₁ t₂ ×ˢ unitCube \ Set.Ioo t₁ t₃ ×ˢ unitCube,
        (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
          + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
          + κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2)) = 0 := by
      rintro ⟨t, x⟩ ⟨⟨⟨ht1, ht2⟩, hx⟩, hnot⟩
      have ht3 : t₃ ≤ t := by
        by_contra hlt
        push Not at hlt
        exact hnot ⟨⟨ht1, hlt⟩, hx⟩
      -- `φ` vanishes on the closed half-space `t ≥ t₃`, hence near any `t > t₃`, and its
      -- slice is identically zero there; at `t = t₃` the time derivative is one-sided zero.
      have hφt : φ t = fun _ => 0 := funext fun y => hvan t ht3 y
      have hgrad : spaceGrad (φ t) x = 0 := by
        rw [hφt]
        funext i
        simp [spaceGrad]
      have hderiv : deriv (fun s => φ s x) t = 0 := by
        have hd : HasDerivAt (fun s => φ s x) (deriv (fun s => φ s x) t) t := by
          have hdiff : Differentiable ℝ (fun s => φ s x) :=
            (hsm.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
          exact (hdiff t).hasDerivAt
        have hright : HasDerivWithinAt (fun s => φ s x) 0 (Set.Ici t) t := by
          apply (hasDerivWithinAt_const t (Set.Ici t) (0 : ℝ)).congr
          · intro s hs; exact hvan s (ht3.trans hs) x
          · exact hvan t ht3 x
        exact (uniqueDiffWithinAt_Ici t).eq_deriv _ hd.hasDerivWithinAt hright
      simp [hgrad, hderiv, hvan t ht3 x, vecDot]
    have hmeas : MeasurableSet (Set.Ioo t₁ t₂ ×ˢ unitCube) :=
      measurableSet_Ioo.prod (by
        unfold unitCube; exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hIoo hzero] at hw
    exact hw

/-- A solution on a longer window agrees with the given solution on the shorter one. -/
theorem isWeakSolutionOn_extend_eq {α : ℝ} (hα : 0 < α) {b : ℝ → Vec 2 → Vec 2}
    (hb : IsHolderDivFreeVelocity α b) {κ : ℝ} (hκ : 0 < κ) {t₁ t₂ t₃ : ℝ} (h12 : t₁ < t₂)
    (h23 : t₂ ≤ t₃) {f : Vec 2 → ℝ} (hf : MemL2On unitCube f) {θ θ' : ℝ → Vec 2 → ℝ}
    (hθ : IsWeakSolutionOn b κ t₁ t₂ f θ) (hθ' : IsWeakSolutionOn b κ t₁ t₃ f θ') :
    ∀ t ∈ Set.Icc t₁ t₂, θ' t =ᵐ[volume.restrict unitCube] θ t := by
  obtain ⟨θ₀, -, huniq⟩ :=
    Wellposed.exists_unique_isWeakSolutionOn_of_isHolderDivFreeVelocity α hα b hb κ hκ t₁ t₂
      h12 f hf
  intro t ht
  have h1 := huniq θ hθ t ht
  have h2 := huniq θ' (isWeakSolutionOn_restrict h23 hθ') t ht
  exact h2.trans h1.symm

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization Set
namespace AVRegularity.Applications

/-! # Periodic functions are locally integrable

The covering argument of `ball_mass_le`: a disc of radius `≤ 1/2` is a.e. covered by four unit squares. -/

/-- A disc of radius `≤ 1/2` is a.e. covered by four unit squares. -/
theorem ball_ae_subset_cubes {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (y : Vec 2) :
    euclidBall y ρ ≤ᵐ[volume]
      ⋃ e ∈ (Finset.univ : Finset (Fin 2 → Fin 2)),
        cubeShift (fun i => ⌊y i - ρ⌋ + ((e i : ℕ) : ℤ)) := by
  set k : Fin 2 → ℤ := fun i => ⌊y i - ρ⌋ with hk
  set mv : (Fin 2 → Fin 2) → (Fin 2 → ℤ) := fun e i => k i + ((e i : ℕ) : ℤ) with hmv
  set S : Set (Vec 2) := ⋃ e ∈ (Finset.univ : Finset (Fin 2 → Fin 2)), cubeShift (mv e) with hS
  -- the disc is a.e. contained in `S`
  set N : Set (Vec 2) := ⋃ (i : Fin 2) (m : ℤ), {x : Vec 2 | x i = (m : ℝ)} with hN
  have hNnull : volume N = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun m => ?_
    have := Measure.pi_hyperplane (fun _ : Fin 2 => (volume : Measure ℝ)) i (m : ℝ)
    rw [← volume_pi] at this
    exact this
  have hcov : euclidBall y ρ ≤ᵐ[volume] S := by
    have hae : ∀ᵐ x ∂(volume : Measure (Vec 2)), x ∉ N := by
      rw [ae_iff]; simpa using hNnull
    filter_upwards [hae] with x hxN hxb
    simp only [hN, mem_iUnion, mem_ofPred_eq, not_exists] at hxN
    have hcoord : ∀ i, |x i - y i| < ρ := by
      intro i
      have h1 := sq_apply_le_vecNormSq (x - y) i
      have h2 : vecNormSq (x - y) < ρ ^ 2 := hxb
      simp only [Pi.sub_apply] at h1
      exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt h1 h2) hρ.le
    simp only [hS, mem_iUnion, Finset.mem_univ, exists_true_left]
    refine ⟨fun i => if x i < (k i : ℝ) + 1 then 0 else 1, ?_⟩
    rw [mem_cubeShift]
    intro i
    have hi := abs_lt.1 (hcoord i)
    have hk1 : (k i : ℝ) ≤ y i - ρ := Int.floor_le _
    have hk2 : y i - ρ < (k i : ℝ) + 1 := Int.lt_floor_add_one _
    have hne := hxN i (k i + 1)
    push_cast at hne
    by_cases hlt : x i < (k i : ℝ) + 1
    · simp only [hmv, hlt, ↓reduceIte]
      push_cast
      constructor <;> simp <;> linarith [hi.1]
    · have hgt : (k i : ℝ) + 1 < x i := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne)
      simp only [hmv, hlt, ↓reduceIte]
      push_cast
      constructor <;> simp <;> linarith [hi.2]
  exact hcov

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization AVenhance Set
namespace AVRegularity.Applications

/-! # Identification of local traces with the canonical weak trace

If a continuous `W` is the `L²` limit from below (along a.e. times) of the slices of a weak
solution on discs `B_ρ(x)` for every `x`, then `W = θ(t)` a.e.: the weak continuity of `θ` in time identifies the weak limit. -/

theorem nhdsLT_inf_ae_neBot (t : ℝ) : (𝓝[<] t ⊓ ae (volume : Measure ℝ)).NeBot := by
  rw [inf_neBot_iff]
  intro s hs s' hs'
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hs
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hnull : volume s'ᶜ = 0 := hs'
  have hsub' : Ioo l t ⊆ s'ᶜ := fun y hy hy' => (Set.eq_empty_iff_forall_notMem.1 hne) y
    ⟨hsub hy, hy'⟩
  have := measure_mono_null hsub' hnull
  rw [Real.volume_Ioo] at this
  have hlt : 0 < t - l := by linarith [show l < t from hl]
  simp [ENNReal.ofReal_eq_zero.not.2 (not_le.2 hlt)] at this

theorem memLp_cubeShift {f : Vec 2 → ℝ} (n : Fin 2 → ℤ)
    (hper : ∀ x, f (x + AVenhance.latticeShift n) = f x)
    (hf : MemLp f 2 (volume.restrict unitCube)) : MemLp f 2 (volume.restrict (cubeShift n)) := by
  set e := MeasurableEquiv.addRight (AVenhance.latticeShift n)
  have hmp : MeasurePreserving e volume volume :=
    measurePreserving_add_right volume (AVenhance.latticeShift n)
  have hpre : e ⁻¹' cubeShift n = unitCube := by
    ext x; simp [e, cubeShift]
  have hmap : Measure.map e (volume.restrict unitCube) = volume.restrict (cubeShift n) := by
    rw [← hpre, ← e.measurableEmbedding.restrict_map, hmp.map_eq]
  rw [← hmap, e.measurableEmbedding.memLp_map_measure_iff]
  refine hf.congr_norm ?_ ?_
  · exact (hf.aestronglyMeasurable).congr (Eventually.of_forall fun x => by simp [e, hper x])
  · exact Eventually.of_forall fun x => by simp [e, hper x]

/-- A periodic `L²(cube)` function is `L²` on every small disc. -/
theorem memLp_ball_of_periodic {f : Vec 2 → ℝ}
    (hper : ∀ (n : Fin 2 → ℤ) x, f (x + AVenhance.latticeShift n) = f x)
    (hf : MemLp f 2 (volume.restrict unitCube)) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    (y : Vec 2) : MemLp f 2 (volume.restrict (euclidBall y ρ)) := by
  set mv : (Fin 2 → Fin 2) → (Fin 2 → ℤ) := fun e i => ⌊y i - ρ⌋ + ((e i : ℕ) : ℤ)
  have hcov := ball_ae_subset_cubes hρ hρ2 y
  have hU : (⋃ e ∈ (Finset.univ : Finset (Fin 2 → Fin 2)), cubeShift (mv e)) =
      ⋃ e : Fin 2 → Fin 2, cubeShift (mv e) := by
    ext x; simp
  have hm : AEStronglyMeasurable f
      (volume.restrict (⋃ e : Fin 2 → Fin 2, cubeShift (mv e))) :=
    aestronglyMeasurable_iUnion_iff.2 fun e =>
      (memLp_cubeShift (mv e) (hper _) hf).aestronglyMeasurable
  have hi : IntegrableOn (fun x => f x ^ 2) (⋃ e : Fin 2 → Fin 2, cubeShift (mv e)) := by
    rw [← hU]
    exact (integrableOn_finset_iUnion).2 fun e _ =>
      (memLp_cubeShift (mv e) (hper _) hf).integrable_sq
  have hmem : MemLp f 2 (volume.restrict (⋃ e : Fin 2 → Fin 2, cubeShift (mv e))) :=
    (memLp_two_iff_integrable_sq hm).2 hi
  rw [hU] at hcov
  exact hmem.mono_measure (Measure.restrict_mono_ae hcov)

open AVenhance.Infra.Parabolic.FourierGalerkin in
/-- Pairing a periodic `L²(cube)` function with a test supported in a disc. -/
theorem integral_ball_eq_cube {g ψ : Vec 2 → ℝ} (hg : MemLp g 2 (volume.restrict unitCube))
    (hgp : IsZ2Periodic g) {x : Vec 2} {ρ : ℝ} (hψ : IsSpTest (euclidBall x ρ) ψ) :
    ∫ y in euclidBall x ρ, g y * ψ y = ∫ y in unitCube, g y * compactTestPeriodization ψ y := by
  have h1 := (WeakGradientPeriodization.integral_periodic_mul_compact_eq_cell_periodization hg hgp
    hψ.1.continuous hψ.2.1).2
  rw [setIntegral_congr_set WeakGradientPeriodization.periodCell_ae_unitCube] at h1
  rw [← h1]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  have : y ∉ tsupport ψ := fun h => hy (hψ.2.2 h)
  simp [image_eq_zero_of_notMem_tsupport this]

open AVenhance.Infra.Parabolic.FourierGalerkin in
/-- **Trace identification.** -/
theorem ae_eq_of_trace_from_below {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} (hθ : IsWeakSolutionOn b κ t₁ t₂ f θ) {t : ℝ} (ht₁ : t₁ < t)
    (ht₂ : t ≤ t₂) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) {W : Vec 2 → ℝ} (hWc : Continuous W)
    (hW : ∀ x, Tendsto (fun σ => ∫ y in euclidBall x ρ, (θ σ y - W y) ^ 2)
      (𝓝[<] t ⊓ ae volume) (𝓝 0)) :
    W =ᵐ[volume.restrict unitCube] θ t := by
  obtain ⟨Dθ, hslice, -, -, -, -, -, hcont, -⟩ := hθ
  have hper : ∀ σ ∈ Set.Icc t₁ t₂, ∀ (n : Fin 2 → ℤ) y,
      θ σ (y + AVenhance.latticeShift n) = θ σ y := fun σ hσ n y => (hslice σ hσ).1 n y
  have := nhdsLT_inf_ae_neBot t
  set F := 𝓝[<] t ⊓ ae (volume : Measure ℝ)
  have hev : ∀ᶠ σ in F, σ ∈ Set.Icc t₁ t₂ := by
    have : Set.Ioo t₁ t ∈ 𝓝[<] t := Ioo_mem_nhdsLT ht₁
    filter_upwards [mem_inf_of_left this] with σ hσ using ⟨hσ.1.le, hσ.2.le.trans ht₂⟩
  have htmem : t ∈ Set.Icc t₁ t₂ := ⟨ht₁.le, ht₂⟩
  -- on each disc, `W = θ t` a.e.
  have hball : ∀ x : Vec 2, ∀ᵐ y ∂(volume : Measure (Vec 2)),
      y ∈ euclidBall x ρ → W y - θ t y = 0 := by
    intro x
    set B := euclidBall x ρ
    have hBo : IsOpen B := isOpen_euclidBall x ρ
    have hBfin : volume B ≠ ⊤ := euclidBall_volume_ne_top x ρ
    have hfinB0 : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
    have hθtB : MemLp (θ t) 2 (volume.restrict B) :=
      memLp_ball_of_periodic (hper t htmem) (hslice t htmem).2 hρ hρ2 x
    have hWB : MemLp W 2 (volume.restrict B) := by
      have hfin : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
      obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ closure B, ‖W y‖ ≤ M := by
        have hcpt : IsCompact (closure B) := by
          refine (Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_)
          refine (Metric.isBounded_closedBall (x := x) (r := |ρ| + 1)).subset ?_
          refine closure_minimal ?_ Metric.isClosed_closedBall
          intro y hy
          rw [Metric.mem_closedBall, dist_pi_le_iff (by positivity)]
          intro i
          have h1 := sq_apply_le_vecNormSq (y - x) i
          have h2 : vecNormSq (y - x) < ρ ^ 2 := hy
          rw [Real.dist_eq]
          simp only [Pi.sub_apply] at h1
          have : |y i - x i| < |ρ| := by
            refine abs_lt_of_sq_lt_sq ?_ (abs_nonneg ρ)
            rw [sq_abs]; linarith
          linarith
        obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn hWc.continuousOn
        exact ⟨M, hM⟩
      refine memLp_of_bounded (μ := volume.restrict B) (a := -M) (b := M) ?_
        hWc.aestronglyMeasurable 2
      refine (ae_restrict_iff' (External.Campanato.euclidBall_measurable x ρ)).2
        (Eventually.of_forall fun y hy => ?_)
      have := hM y (subset_closure hy)
      rw [Real.norm_eq_abs, abs_le] at this
      exact this
    refine hBo.ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
    · have hint : IntegrableOn (fun y => W y - θ t y) B := (hWB.sub hθtB).integrable one_le_two
      exact hint.locallyIntegrableOn
    · intro ψ hψs hψc hψt
      have hψ : IsSpTest B ψ := ⟨hψs, hψc, hψt⟩
      -- the pairing converges along `F` to both values
      have hlimW : Tendsto (fun σ => ∫ y in B, θ σ y * ψ y) F (𝓝 (∫ y in B, W y * ψ y)) := by
        obtain ⟨Cψ, hCψ⟩ := hψs.continuous.bounded_above_of_compact_support hψc
        have hVB : 0 ≤ (volume B).toReal := ENNReal.toReal_nonneg
        have hbound : ∀ᶠ σ in F, |(∫ y in B, θ σ y * ψ y) - ∫ y in B, W y * ψ y| ≤
            Cψ * Real.sqrt ((volume B).toReal * ∫ y in B, (θ σ y - W y) ^ 2) := by
          filter_upwards [hev] with σ hσ
          have hθσ : MemLp (θ σ) 2 (volume.restrict B) :=
            memLp_ball_of_periodic (hper σ hσ) (hslice σ hσ).2 hρ hρ2 x
          have hfinB : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
          have hd : MemLp (fun y => θ σ y - W y) 2 (volume.restrict B) := hθσ.sub hWB
          have i1 : Integrable (fun y => θ σ y * ψ y) (volume.restrict B) :=
            (hθσ.integrable one_le_two).mul_bdd hψs.continuous.aestronglyMeasurable
              (Eventually.of_forall hCψ)
          have i2 : Integrable (fun y => W y * ψ y) (volume.restrict B) :=
            (hWB.integrable one_le_two).mul_bdd hψs.continuous.aestronglyMeasurable
              (Eventually.of_forall hCψ)
          rw [← integral_sub i1 i2]
          have hCψ0 : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ x)
          calc |∫ y in B, (θ σ y * ψ y - W y * ψ y)|
              ≤ ∫ y in B, |θ σ y - W y| * Cψ := by
                refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
                  (Eventually.of_forall fun _ => abs_nonneg _)
                  ((hd.integrable one_le_two).abs.mul_const _) (Eventually.of_forall fun y => ?_))
                simp only
                rw [← sub_mul, abs_mul]
                exact mul_le_mul_of_nonneg_left (by simpa using hCψ y) (abs_nonneg _)
            _ = Cψ * ∫ y in B, |θ σ y - W y| := by rw [integral_mul_const]; ring
            _ ≤ Cψ * Real.sqrt ((volume B).toReal * ∫ y in B, (θ σ y - W y) ^ 2) := by
                refine mul_le_mul_of_nonneg_left ?_ hCψ0
                have hone : MemLp (fun _ : Vec 2 => (1 : ℝ)) (ENNReal.ofReal 2)
                    (volume.restrict B) := by
                  simpa using memLp_const (μ := volume.restrict B) (p := ENNReal.ofReal 2) (1 : ℝ)
                have habs : MemLp (fun y => |θ σ y - W y|) (ENNReal.ofReal 2)
                    (volume.restrict B) := by
                  simpa [Real.norm_eq_abs] using hd.norm
                have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict B)
                  (p := 2) (q := 2) Real.HolderConjugate.two_two (f := fun _ => (1 : ℝ))
                  (g := fun y => |θ σ y - W y|) (Eventually.of_forall fun _ => zero_le_one)
                  (Eventually.of_forall fun _ => abs_nonneg _) hone habs
                simp only [one_mul, Real.one_rpow, integral_const, smul_eq_mul, mul_one] at hcs
                have hsq : (fun y => |θ σ y - W y| ^ (2 : ℝ)) = fun y => (θ σ y - W y) ^ 2 := by
                  funext y; rw [Real.rpow_two, sq_abs]
                rw [hsq] at hcs
                have hmeas : (volume.restrict B).real Set.univ = (volume B).toReal := by
                  simp [measureReal_def]
                rw [hmeas] at hcs
                refine hcs.trans (le_of_eq ?_)
                rw [Real.sqrt_eq_rpow, Real.mul_rpow hVB (setIntegral_nonneg_of_ae_restrict
                  (Eventually.of_forall fun _ => sq_nonneg _))]
        have hlim0 : Tendsto (fun σ => Cψ * Real.sqrt ((volume B).toReal *
            ∫ y in B, (θ σ y - W y) ^ 2)) F (𝓝 0) := by
          have := ((hW x).const_mul (volume B).toReal).sqrt.const_mul Cψ
          simpa using this
        refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall
          fun _ => norm_nonneg _) ?_ hlim0)
        filter_upwards [hbound] with σ hσ
        rwa [Real.norm_eq_abs]
      have hlimP : Tendsto (fun σ => ∫ y in B, θ σ y * ψ y) F (𝓝 (∫ y in B, θ t y * ψ y)) := by
        set ψp := compactTestPeriodization ψ
        have hψp : ContDiff ℝ (⊤ : ℕ∞) ψp := compactTestPeriodization_contDiff hψc hψs
        have hcontP := hcont ψp hψp compactTestPeriodization_periodic
        have hP : Tendsto (fun σ => ∫ y in unitCube, θ σ y * ψp y) F
            (𝓝 (∫ y in unitCube, θ t y * ψp y)) := by
          have h1 := (hcontP t htmem).tendsto
          have h2 : F ≤ 𝓝[Set.Icc t₁ t₂] t := by
            refine (inf_le_left.trans ?_)
            rw [← nhdsWithin_Ioo_eq_nhdsLT ht₁]
            exact nhdsWithin_mono t (Set.Ioo_subset_Icc_self.trans
              (Set.Icc_subset_Icc le_rfl ht₂))
          exact h1.mono_left h2
        rw [integral_ball_eq_cube (hslice t htmem).2 (hslice t htmem).1 hψ]
        refine hP.congr' ?_
        filter_upwards [hev] with σ hσ
        exact (integral_ball_eq_cube (hslice σ hσ).2 (hslice σ hσ).1 hψ).symm
      have heq := tendsto_nhds_unique hlimW hlimP
      have i1 : Integrable (fun y => ψ y * W y) (volume.restrict B) := by
        obtain ⟨Cψ, hCψ⟩ := hψs.continuous.bounded_above_of_compact_support hψc
        simpa [mul_comm] using (hWB.integrable one_le_two).mul_bdd
          hψs.continuous.aestronglyMeasurable (Eventually.of_forall hCψ)
      have i2 : Integrable (fun y => ψ y * θ t y) (volume.restrict B) := by
        obtain ⟨Cψ, hCψ⟩ := hψs.continuous.bounded_above_of_compact_support hψc
        simpa [mul_comm] using (hθtB.integrable one_le_two).mul_bdd
          hψs.continuous.aestronglyMeasurable (Eventually.of_forall hCψ)
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) fun y hy => by
        have : y ∉ tsupport ψ := fun h => hy (hψt h)
        simp [image_eq_zero_of_notMem_tsupport this]]
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub i1 i2]
      have e1 : ∫ y in B, ψ y * W y = ∫ y in B, W y * ψ y := by congr 1; funext y; ring
      have e2 : ∫ y in B, ψ y * θ t y = ∫ y in B, θ t y * ψ y := by congr 1; funext y; ring
      rw [e1, e2, heq, sub_self]
  -- cover the cube by countably many discs
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Vec 2)
  have hall : ∀ᵐ y ∂(volume : Measure (Vec 2)), W y = θ t y := by
    have hD : ∀ᵐ y ∂(volume : Measure (Vec 2)), ∀ x ∈ D, y ∈ euclidBall x ρ → W y - θ t y = 0 :=
      (ae_ball_iff hDc).2 fun x _ => hball x
    filter_upwards [hD] with y hy
    obtain ⟨x, hxD, hxy⟩ := hDd.exists_mem_open (Metric.isOpen_ball (x := y) (ε := ρ / 2))
      ⟨y, Metric.mem_ball_self (by positivity)⟩
    have hmem : y ∈ euclidBall x ρ := by
      simp only [euclidBall, Set.mem_ofPred_eq]
      rw [Metric.mem_ball, dist_comm, dist_pi_lt_iff (by positivity)] at hxy
      have h0 := hxy 0
      have h1 := hxy 1
      rw [Real.dist_eq] at h0 h1
      simp only [vecNormSq, Homogenization.vecDot, Fin.sum_univ_two, Pi.sub_apply]
      nlinarith [abs_lt.1 h0, abs_lt.1 h1]
    exact sub_eq_zero.1 (hy x hxD hmem)
  exact ae_restrict_of_ae hall

end AVRegularity.Applications
end
