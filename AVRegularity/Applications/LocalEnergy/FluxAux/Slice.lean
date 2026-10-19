-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Applications.LocalEnergy.DivFreeMollify.Limit
import AVRegularity.Applications.LocalEnergy.MolEnergy
public import AVRegularity.Applications.Parabolic.SliceGrad
import Mathlib.MeasureTheory.Function.L2Space

public section
noncomputable section

section
open MeasureTheory Homogenization
namespace AVRegularity.Applications.LocalEnergy.Flux

/-! # Integrability of the terms of the flux identity on the unit cylinder -/

theorem isFiniteMeasure_openCyl : IsFiniteMeasure ((volume : Measure (ℝ × Vec 2)).restrict
    (openCyl 0 1)) := by
  rw [Moll.restrict_openCyl]
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioo (-1 : ℝ) 0)) :=
    ⟨by simp⟩
  have : IsFiniteMeasure ((volume : Measure (Vec 2)).restrict (euclidBall (0 : Vec 2) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 Moll.volume_unitBall_ne_top⟩
  infer_instance

/-- A continuous compactly supported function is bounded. -/
theorem exists_bound_of_cpt {α : Type*} [TopologicalSpace α] {f : α → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) : ∃ C, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  exact ⟨C, fun x => by simpa using hC x⟩


section Terms

variable {K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {d : ℝ × Vec 2 → Vec 2}
  {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2} {kK kd : ℝ}

theorem integrable_w2 {μ : Measure (ℝ × Vec 2)} {w1 w2 a : ℝ × Vec 2 → ℝ} {C1 C2 : ℝ}
    (ha : Integrable a μ) (h1 : AEStronglyMeasurable w1 μ) (h2 : AEStronglyMeasurable w2 μ)
    (hC1 : 0 ≤ C1) (b1 : ∀ᵐ p ∂μ, |w1 p| ≤ C1) (b2 : ∀ᵐ p ∂μ, |w2 p| ≤ C2) :
    Integrable (fun p => w1 p * w2 p * a p) μ := by
  refine ha.bdd_mul (c := C1 * C2) (h1.mul h2) ?_
  filter_upwards [b1, b2] with p hp1 hp2
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hp1 hp2 (abs_nonneg _) hC1

theorem abs_matrix_entry_le {A : Matrix (Fin 2) (Fin 2) ℝ} {k : ℝ}
    (h : ∀ e : Vec 2, vecNormSq (A.mulVec e) ≤ k ^ 2 * vecNormSq e) (i j : Fin 2) :
    |A i j| ≤ |k| := by
  have h1 := h (basisVec j)
  rw [vecNormSq_basisVec, mul_one] at h1
  have h2 : A.mulVec (basisVec j) = fun i => A i j := by
    ext i
    fin_cases j <;> simp [Matrix.mulVec, dotProduct, basisVec, Pi.single_apply]
  rw [h2] at h1
  exact Moll.abs_coord_le (x := fun i => A i j) h1 i


/-- Integrability of the four terms of the flux identity on `Q₁`. -/
theorem flux_terms_integrable
    (hKm : ∀ i j : Fin 2, AEStronglyMeasurable (fun p => K p i j) (volume.restrict (openCyl 0 1)))
    (hdm : ∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1)))
    (hbound : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)),
      (∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ kK ^ 2 * vecNormSq e) ∧ vecNormSq (d p) ≤ kd ^ 2)
    (hU : MemLp U 2 (volume.restrict (openCyl 0 1)))
    (hDU : ∀ i : Fin 2, MemLp (fun p => DU p i) 2 (volume.restrict (openCyl 0 1)))
    (c : ℝ) {φ : ℝ × Vec 2 → ℝ} (hφ : IsSTTest (openCyl 0 1) φ) :
    Integrable (fun p => -(U p * stTimeDeriv φ p)) (volume.restrict (openCyl 0 1)) ∧
    Integrable (fun p => vecDot ((1 + K p).mulVec (DU p)) (stSpaceGrad φ p))
      (volume.restrict (openCyl 0 1)) ∧
    Integrable (fun p => vecDot (d p) (DU p) * φ p) (volume.restrict (openCyl 0 1)) ∧
    Integrable (fun p => (U p - c) * vecDot (d p) (stSpaceGrad φ p))
      (volume.restrict (openCyl 0 1)) := by
  have hfin := isFiniteMeasure_openCyl
  set μ : Measure (ℝ × Vec 2) := volume.restrict (openCyl 0 1) with hμ
  have hUi : Integrable U μ := hU.integrable (by norm_num)
  have hDUi : ∀ i, Integrable (fun p => DU p i) μ := fun i => (hDU i).integrable (by norm_num)
  have hUc : Integrable (fun p => U p - c) μ := hUi.sub (integrable_const c)
  -- bounds on `φ` and its derivatives
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := hφ.1
  have hφcont : Continuous φ := hφs.continuous
  have hfd : Continuous (fderiv ℝ φ) := hφs.continuous_fderiv (by simp)
  have hcl : ∀ v : ℝ × Vec 2, Continuous (fun p => fderiv ℝ φ p v) := fun v =>
    hfd.clm_apply continuous_const
  have hcs : ∀ v : ℝ × Vec 2, HasCompactSupport (fun p => fderiv ℝ φ p v) := fun v =>
    (hφ.2.1.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℝ × Vec 2 →L[ℝ] ℝ => L v) (by simp)
  obtain ⟨Cφ, hCφ⟩ := exists_bound_of_cpt hφcont hφ.2.1
  obtain ⟨Ct, hCt⟩ := exists_bound_of_cpt (hcl (1, 0)) (hcs (1, 0))
  obtain ⟨Cg, hCg⟩ := (fun i : Fin 2 => exists_bound_of_cpt (hcl (0, basisVec i)) (hcs _)) |> fun h =>
    (⟨max |(h 0).choose| |(h 1).choose|, fun i p => by
      fin_cases i
      · exact ((h 0).choose_spec p).trans ((le_abs_self _).trans (le_max_left _ _))
      · exact ((h 1).choose_spec p).trans ((le_abs_self _).trans (le_max_right _ _))⟩ :
      ∃ C, ∀ (i : Fin 2) p, |fderiv ℝ φ p (0, basisVec i)| ≤ C)
  have hCg0 : 0 ≤ Cg := (abs_nonneg _).trans (hCg 0 0)
  have hCφ0 : 0 ≤ Cφ := (abs_nonneg _).trans (hCφ 0)
  have hdb : ∀ᵐ p ∂μ, ∀ i, |d p i| ≤ |kd| := by
    filter_upwards [hbound] with p hp i using Moll.abs_coord_le hp.2 i
  have hKb : ∀ᵐ p ∂μ, ∀ i j, |(1 + K p) i j| ≤ 1 + |kK| := by
    filter_upwards [hbound] with p hp i j
    have h1 := abs_matrix_entry_le hp.1 i j
    calc |(1 + K p) i j| = |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j + K p i j| := by simp
      _ ≤ |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| + |K p i j| := abs_add_le _ _
      _ ≤ 1 + |kK| := by
        refine add_le_add ?_ h1
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hgm : ∀ i : Fin 2, AEStronglyMeasurable (fun p => stSpaceGrad φ p i) μ := fun i =>
    (hcl (0, basisVec i)).aestronglyMeasurable
  have hgb : ∀ i : Fin 2, ∀ᵐ p ∂μ, |stSpaceGrad φ p i| ≤ Cg := fun i =>
    Filter.Eventually.of_forall fun p => hCg i p
  have hKm' : ∀ i j : Fin 2, AEStronglyMeasurable (fun p => (1 + K p) i j) μ := fun i j => by
    have : (fun p => (1 + K p) i j) =
        fun p => (1 : Matrix (Fin 2) (Fin 2) ℝ) i j + K p i j := by ext p; simp
    rw [this]
    exact aestronglyMeasurable_const.add (hKm i j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : Integrable (fun p => U p * stTimeDeriv φ p) μ :=
      hUi.mul_bdd (c := Ct) (hcl (1, 0)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => by simpa [stTimeDeriv] using hCt p)
    exact this.neg
  · have e : (fun p => vecDot ((1 + K p).mulVec (DU p)) (stSpaceGrad φ p)) =
        fun p => ((1 + K p) 0 0 * stSpaceGrad φ p 0 * DU p 0 +
          (1 + K p) 0 1 * stSpaceGrad φ p 0 * DU p 1) +
          ((1 + K p) 1 0 * stSpaceGrad φ p 1 * DU p 0 +
          (1 + K p) 1 1 * stSpaceGrad φ p 1 * DU p 1) := by
      ext p
      simp only [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [e]
    have t : ∀ i j, Integrable (fun p => (1 + K p) i j * stSpaceGrad φ p i * DU p j) μ :=
      fun i j => integrable_w2 (hDUi j) (hKm' i j) (hgm i) (by positivity)
        (hKb.mono fun p hp => hp i j) (hgb i)
    exact ((t 0 0).add (t 0 1)).add ((t 1 0).add (t 1 1))
  · have e : (fun p => vecDot (d p) (DU p) * φ p) =
        fun p => d p 0 * φ p * DU p 0 + d p 1 * φ p * DU p 1 := by
      ext p
      simp only [vecDot, Fin.sum_univ_two]
      ring
    rw [e]
    have t : ∀ i, Integrable (fun p => d p i * φ p * DU p i) μ := fun i =>
      integrable_w2 (hDUi i) (hdm i) hφcont.aestronglyMeasurable (abs_nonneg _)
        (hdb.mono fun p hp => hp i) (Filter.Eventually.of_forall hCφ)
    exact (t 0).add (t 1)
  · have e : (fun p => (U p - c) * vecDot (d p) (stSpaceGrad φ p)) =
        fun p => d p 0 * stSpaceGrad φ p 0 * (U p - c) +
          d p 1 * stSpaceGrad φ p 1 * (U p - c) := by
      ext p
      simp only [vecDot, Fin.sum_univ_two]
      ring
    rw [e]
    have t : ∀ i, Integrable (fun p => d p i * stSpaceGrad φ p i * (U p - c)) μ := fun i =>
      integrable_w2 hUc (hdm i) (hgm i) (abs_nonneg _) (hdb.mono fun p hp => hp i) (hgb i)
    exact (t 0).add (t 1)

end Terms

end AVRegularity.Applications.LocalEnergy.Flux
end

section
open MeasureTheory Homogenization Filter Topology
open AVRegularity.Applications.LocalEnergy.Moll
namespace AVRegularity.Applications.LocalEnergy.Flux

/-! # The slice identity behind the flux form

For a.e. time `τ`, `(U(τ,·) - c) φ(τ,·)` is an `H¹` function compactly supported in the unit disc
with gradient `φ DU + (U - c) ∇φ`, so the divergence-free drift annihilates its gradient. -/

theorem memLp_mul_cpt {B : Set (Vec 2)} {g f : Vec 2 → ℝ} (hg : MemLp g 2 (volume.restrict B))
    (hf : Continuous f) (hc : HasCompactSupport f) :
    MemLp (fun y => f y * g y) 2 (volume.restrict B) := by
  have h1 : MemLp f ⊤ (volume.restrict B) := hf.memLp_of_hasCompactSupport (p := ⊤) hc
  exact h1.mul hg

theorem ae_slice_memLp {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 (volume.restrict (openCyl 0 1))) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo (-1 : ℝ) 0)),
      MemLp (fun y => f (τ, y)) 2 (volume.restrict (euclidBall (0 : Vec 2) 1)) := by
  have hint : Integrable (fun p => f p ^ 2) (volume.restrict (openCyl 0 1)) := hf.integrable_sq
  rw [restrict_openCyl] at hint
  have h1 := hint.prod_right_ae
  have h2 := ae_slice_aestronglyMeasurable hf.aestronglyMeasurable
  filter_upwards [h1, h2] with τ i1 m1
  exact (memLp_two_iff_integrable_sq m1).2 i1

theorem spGrad_slice {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (τ : ℝ) (y : Vec 2)
    (i : Fin 2) : spGrad (fun z => φ (τ, z)) y i = stSpaceGrad φ (τ, y) i := by
  have h1 : HasFDerivAt φ (fderiv ℝ φ (τ, y)) (τ, y) :=
    ((hφ.differentiable (by simp)) (τ, y)).hasFDerivAt
  have h2 := h1.comp y (hasFDerivAt_prodMk_right τ y)
  simp only [spGrad, stSpaceGrad]
  have := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) h2.fderiv
  exact this

/-- Compact slice support set. -/
def sliceSupport (φ : ℝ × Vec 2 → ℝ) : Set (Vec 2) := Prod.snd '' tsupport φ

theorem sliceSupport_compact {φ : ℝ × Vec 2 → ℝ} (hc : HasCompactSupport φ) :
    IsCompact (sliceSupport φ) := hc.isCompact.image continuous_snd

theorem sliceSupport_subset {φ : ℝ × Vec 2 → ℝ} (hφ : tsupport φ ⊆ openCyl 0 1) :
    sliceSupport φ ⊆ euclidBall (0 : Vec 2) 1 := by
  rintro _ ⟨p, hp, rfl⟩
  have := hφ hp
  rw [openCyl_zero_one] at this
  exact this.2

theorem slice_zero_off {φ : ℝ × Vec 2 → ℝ} (τ : ℝ) (y : Vec 2) (hy : y ∉ sliceSupport φ) :
    φ (τ, y) = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hy ⟨(τ, y), h, rfl⟩)

theorem slice_isSpTest {φ : ℝ × Vec 2 → ℝ} (hφ : IsSTTest (openCyl 0 1) φ) (τ : ℝ) :
    IsSpTest (euclidBall (0 : Vec 2) 1) (fun y => φ (τ, y)) := by
  have hKc := sliceSupport_compact hφ.2.1
  refine ⟨hφ.1.comp (contDiff_const.prodMk contDiff_id),
    HasCompactSupport.intro hKc (fun y hy => slice_zero_off τ y hy), ?_⟩
  refine (closure_minimal (fun y hy => ?_) hKc.isClosed).trans (sliceSupport_subset hφ.2.2)
  by_contra h
  exact hy (slice_zero_off τ y h)


theorem spGrad_cont_cpt {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (i : Fin 2) :
    Continuous (fun y => spGrad f y i) ∧ HasCompactSupport (fun y => spGrad f y i) :=
  ⟨(hf.continuous_fderiv (by simp)).clm_apply continuous_const,
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) (by simp)⟩

/-- The slice identity: `∫ (d·DU) φ + (U - c) d·∇φ = 0` on a good time slice. -/
theorem flux_slice_identity {d : ℝ × Vec 2 → Vec 2} {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2}
    (c : ℝ) {φ : ℝ × Vec 2 → ℝ} (hφ : IsSTTest (openCyl 0 1) φ) {τ : ℝ}
    (hUτ : MemLp (fun y => U (τ, y)) 2 (volume.restrict (euclidBall (0 : Vec 2) 1)))
    (hDUτ : ∀ i : Fin 2, MemLp (fun y => DU (τ, y) i) 2
      (volume.restrict (euclidBall (0 : Vec 2) 1)))
    (hwτ : HasWeakGradientOn (euclidBall (0 : Vec 2) 1) (fun y => U (τ, y))
      (fun y => DU (τ, y)))
    (hdτ : ∀ (ψ : Vec 2 → ℝ) (Dψ : Vec 2 → Vec 2),
        MemLp ψ 2 (volume.restrict (euclidBall 0 1)) →
        (∀ i : Fin 2, MemLp (fun y => Dψ y i) 2 (volume.restrict (euclidBall 0 1))) →
        HasWeakGradientOn (euclidBall 0 1) ψ Dψ →
        (∃ Kc : Set (Vec 2), IsCompact Kc ∧ Kc ⊆ euclidBall 0 1 ∧ ∀ y, y ∉ Kc → ψ y = 0) →
        ∫ y in euclidBall 0 1, vecDot (d (τ, y)) (Dψ y) = 0) :
    ∫ y in euclidBall (0 : Vec 2) 1, (vecDot (d (τ, y)) (DU (τ, y)) * φ (τ, y) +
      (U (τ, y) - c) * vecDot (d (τ, y)) (stSpaceGrad φ (τ, y))) = 0 := by
  have hB := isOpen_unitBall
  have hfin : IsFiniteMeasure (volume.restrict (euclidBall (0 : Vec 2) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 volume_unitBall_ne_top⟩
  have hχ := slice_isSpTest hφ τ
  have hu' : MemLp (fun y => U (τ, y) - c) 2 (volume.restrict (euclidBall (0 : Vec 2) 1)) :=
    hUτ.sub (memLp_const c)
  have hwc := hasWeakGradientOn_sub_const hB hwτ c
  have hprod := hasWeakGradientOn_smul_smooth hB hwc hu' hDUτ hχ
  have hψ : MemLp (fun y => φ (τ, y) * (U (τ, y) - c)) 2
      (volume.restrict (euclidBall (0 : Vec 2) 1)) :=
    memLp_mul_cpt hu' hχ.1.continuous hχ.2.1
  have hDψ : ∀ i : Fin 2, MemLp (fun y => (φ (τ, y) • DU (τ, y) +
      (U (τ, y) - c) • spGrad (fun z => φ (τ, z)) y) i) 2
      (volume.restrict (euclidBall (0 : Vec 2) 1)) := by
    intro i
    have h1 := memLp_mul_cpt (hDUτ i) hχ.1.continuous hχ.2.1
    have h2 := memLp_mul_cpt hu' (spGrad_cont_cpt hχ.1 hχ.2.1 i).1 (spGrad_cont_cpt hχ.1 hχ.2.1 i).2
    refine (memLp_congr_ae (Filter.Eventually.of_forall fun y => ?_)).1 (h1.add h2)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h := hdτ _ _ hψ hDψ hprod ⟨sliceSupport φ, sliceSupport_compact hφ.2.1,
    sliceSupport_subset hφ.2.2, fun y hy => by rw [slice_zero_off τ y hy, zero_mul]⟩
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hg : spGrad (fun z => φ (τ, z)) y = stSpaceGrad φ (τ, y) := by
    ext i; exact spGrad_slice hφ.1 τ y i
  simp only [vecDot, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hg]
  ring

end AVRegularity.Applications.LocalEnergy.Flux
end
