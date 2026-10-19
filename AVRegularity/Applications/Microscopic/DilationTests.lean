-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Parabolic.SliceGrad
import Mathlib.MeasureTheory.Function.L2Space
public import AVRegularity.External.Campanato.Holder

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # Parabolic dilations

`parDil z r (τ, y) = (z.1 + r² τ, z.2 + r y)` maps `Q₁` onto `Q_r(z)` and scales Lebesgue
measure on `ℝ × ℝ²` by `r⁴`. -/

/-- The parabolic dilation `(τ, y) ↦ (z.1 + r² τ, z.2 + r y)`. -/
def parDil (z : ℝ × Vec 2) (r : ℝ) (p : ℝ × Vec 2) : ℝ × Vec 2 :=
  (z.1 + r ^ 2 * p.1, z.2 + r • p.2)

/-- The inverse dilation. -/
def parDilInv (z : ℝ × Vec 2) (r : ℝ) (p : ℝ × Vec 2) : ℝ × Vec 2 :=
  ((p.1 - z.1) / r ^ 2, r⁻¹ • (p.2 - z.2))

theorem measurable_parDil (z : ℝ × Vec 2) (r : ℝ) : Measurable (parDil z r) := by
  unfold parDil
  fun_prop

theorem measurable_parDilInv (z : ℝ × Vec 2) (r : ℝ) : Measurable (parDilInv z r) := by
  unfold parDilInv
  fun_prop

theorem parDilInv_parDil (z : ℝ × Vec 2) {r : ℝ} (hr : r ≠ 0) (p : ℝ × Vec 2) :
    parDilInv z r (parDil z r p) = p := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  rcases p with ⟨τ, y⟩
  simp only [parDilInv, parDil, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul,
    Prod.mk.injEq, and_true]
  field_simp

theorem parDil_parDilInv (z : ℝ × Vec 2) {r : ℝ} (hr : r ≠ 0) (p : ℝ × Vec 2) :
    parDil z r (parDilInv z r p) = p := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  rcases p with ⟨t, x⟩
  simp only [parDil, parDilInv, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel,
    Prod.mk.injEq, and_true]
  field_simp
  ring

/-- `parDil` as a measurable equivalence. -/
def parDilEquiv (z : ℝ × Vec 2) {r : ℝ} (hr : r ≠ 0) : (ℝ × Vec 2) ≃ᵐ (ℝ × Vec 2) where
  toFun := parDil z r
  invFun := parDilInv z r
  left_inv := parDilInv_parDil z hr
  right_inv := parDil_parDilInv z hr
  measurable_toFun := measurable_parDil z r
  measurable_invFun := measurable_parDilInv z r

theorem map_time_affine_volume (a c : ℝ) (hc : c ≠ 0) :
    Measure.map (fun x : ℝ => a + c * x) volume = ENNReal.ofReal |c⁻¹| • volume := by
  have hfun : (fun x : ℝ => a + c * x) = (fun x => x + a) ∘ (fun x => c * x) := by
    funext x
    simp [add_comm]
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Real.map_volume_mul_left hc]
  rw [Measure.map_smul _ (by fun_prop), map_add_right_eq_self]

theorem map_space_affine_volume (c : Vec 2) {r : ℝ} (hr : r ≠ 0) :
    Measure.map (fun y : Vec 2 => c + r • y) volume = ENNReal.ofReal (|r ^ 2|⁻¹) • volume := by
  have hfun : (fun y : Vec 2 => c + r • y) = (fun y => y + c) ∘ (fun y => r • y) := by
    funext y
    simp [add_comm]
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Measure.map_addHaar_smul volume hr, Module.finrank_fin_fun]
  rw [Measure.map_smul _ (by fun_prop), map_add_right_eq_self, abs_inv]

/-- Lebesgue measure on `ℝ × ℝ²` scales by `r⁴` under `parDil z r`. -/
theorem map_parDil_volume (z : ℝ × Vec 2) {r : ℝ} (hr : r ≠ 0) :
    Measure.map (parDil z r) (volume : Measure (ℝ × Vec 2)) =
      ENNReal.ofReal (r ^ 4)⁻¹ • volume := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  rw [Measure.volume_eq_prod ℝ (Vec 2)]
  change Measure.map (Prod.map (fun τ : ℝ => z.1 + r ^ 2 * τ) (fun y : Vec 2 => z.2 + r • y))
    (volume.prod volume) = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) (by fun_prop)]
  rw [map_time_affine_volume z.1 (r ^ 2) hr2, map_space_affine_volume z.2 hr,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ← ENNReal.ofReal_mul]
  · congr 2
    rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r)), abs_of_nonneg (sq_nonneg r)]
    rw [← mul_inv, ← pow_add]
  · exact abs_nonneg _

/-- Integrals over a dilated set: `∫_S f ∘ T = r⁻⁴ ∫_{T(S)} f`. -/
theorem integral_parDil (z : ℝ × Vec 2) {r : ℝ} (hr : r ≠ 0) (f : ℝ × Vec 2 → ℝ)
    (S : Set (ℝ × Vec 2)) :
    ∫ p in S, f (parDil z r p) = (r ^ 4)⁻¹ * ∫ p in parDil z r '' S, f p := by
  have hemb : MeasurableEmbedding (parDil z r) := (parDilEquiv z hr).measurableEmbedding
  have hmeas : Measure.map (parDil z r) (volume.restrict S) =
      (ENNReal.ofReal (r ^ 4)⁻¹ • volume).restrict (parDil z r '' S) := by
    rw [← map_parDil_volume z hr, hemb.restrict_map,
      Set.preimage_image_eq _ hemb.injective]
  have h1 : ∫ p in S, f (parDil z r p) =
      ∫ p, f p ∂(Measure.map (parDil z r) (volume.restrict S)) :=
    (integral_map_equiv (parDilEquiv z hr) f).symm
  rw [h1, hmeas, Measure.restrict_smul, integral_smul_measure]
  have hpos : 0 ≤ (r ^ 4)⁻¹ := inv_nonneg.mpr (by positivity)
  rw [ENNReal.toReal_ofReal hpos, smul_eq_mul]

end AVRegularity.Applications
end
end
end

section
@[expose] public section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # Statements of the Caccioppoli step (Step 1 of the proof of Lemma 3.3 of the paper)

These are the statements of the flux form and of the Caccioppoli inequality for the small
skew/drift problem. The Campanato assembly is written against
them and they are discharged by `AVRegularity.Applications.Construction`. -/

/-- Hypotheses on the coefficients: measurability and the bounds `|K e| ≤ kK |e|`, `|d| ≤ kd`. -/
def IsSkewDriftCoeff (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
    (kK kd : ℝ) : Prop :=
  (∀ i j : Fin 2, AEStronglyMeasurable (fun p => K p i j) (volume.restrict (openCyl 0 1))) ∧
  (∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1))) ∧
  ∀ᵐ p ∂(volume.restrict (openCyl 0 1)),
    (∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ kK ^ 2 * vecNormSq e) ∧ vecNormSq (d p) ≤ kd ^ 2

/-- Step 1: the weak form with the flux `P_c = (I+K)∇U - (U-c)d`. -/
def SkewDriftFluxStmt : Prop :=
  ∀ (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
    (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) (kK kd : ℝ),
    IsSkewDriftCoeff K d kK kd → IsDivFreeQ1 d → IsEnergyClassQ1 U DU →
    IsSkewDriftWeak K d U DU → ∀ (c : ℝ) (φ : ℝ × Vec 2 → ℝ), IsSTTest (openCyl 0 1) φ →
      ∫ p in openCyl 0 1, (-(U p * stTimeDeriv φ p)
        + vecDot ((1 + K p).mulVec (DU p) - (U p - c) • d p) (stSpaceGrad φ p)) = 0

/-- Step 2: `∫_{Q_{3/4}} |∇U|² ≤ C₀ ∫_{Q₁} |U - c|²` when `kK + kd ≤ 1`. -/
def SkewDriftCaccioppoliStmt : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
    (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) (kK kd : ℝ),
    0 ≤ kK → 0 ≤ kd → kK + kd ≤ 1 → IsSkewDriftCoeff K d kK kd →
    (∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (K p).transpose = -K p) →
    IsDivFreeQ1 d → IsEnergyClassQ1 U DU → IsSkewDriftWeak K d U DU → ∀ c : ℝ,
      ∫ p in openCyl 0 (3 / 4), vecNormSq (DU p) ≤ C₀ * ∫ p in openCyl 0 1, (U p - c) ^ 2

end AVRegularity.Applications
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVRegularity.External.Campanato
namespace AVRegularity.Applications

/-! # Auxiliary facts for the excess decay

open and closed-top cylinders agree a.e.; the excess is the least mean-square deviation from a
constant; Cauchy–Schwarz on a set; weak gradients are linear. -/

theorem openCyl_ae_eq_cylinder (z : ℝ × Vec 2) (r : ℝ) :
    openCyl z r =ᵐ[volume] AVRegularity.External.Campanato.cylinder z r := by
  rw [Measure.volume_eq_prod]
  exact Measure.set_prod_ae_eq Ioo_ae_eq_Ioc (Filter.EventuallyEq.refl _ _)

theorem restrict_openCyl_eq (z : ℝ × Vec 2) (r : ℝ) :
    volume.restrict (openCyl z r) = volume.restrict (AVRegularity.External.Campanato.cylinder z r) :=
  Measure.restrict_congr_set (openCyl_ae_eq_cylinder z r)

theorem openCyl_subset_cylinder (z : ℝ × Vec 2) (r : ℝ) : openCyl z r ⊆ AVRegularity.External.Campanato.cylinder z r :=
  Set.prod_mono Set.Ioo_subset_Ioc_self le_rfl

theorem cylinder_volume_pos (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (AVRegularity.External.Campanato.cylinder z r) := by
  have hl := cylinder_volume_lower z hr
  have hu := cylinder_volume_upper z hr
  have hne : volume (AVRegularity.External.Campanato.cylinder z r) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  rw [measureReal_def]
  refine ENNReal.toReal_pos ?_ hne
  exact ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hl)

theorem cylinder_volumeReal_le (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    volume.real (AVRegularity.External.Campanato.cylinder z r) ≤ 4 * r ^ 4 := by
  have hu := cylinder_volume_upper z hr
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hu

theorem cylinder_volumeReal_ge (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    r ^ 4 ≤ volume.real (AVRegularity.External.Campanato.cylinder z r) := by
  have hl := cylinder_volume_lower z hr
  have hu := cylinder_volume_upper z hr
  have hne : volume (AVRegularity.External.Campanato.cylinder z r) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  rw [measureReal_def]
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hl

theorem cylinder_volume_ne_top (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    volume (AVRegularity.External.Campanato.cylinder z r) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (cylinder_volume_upper z hr)

/-- The excess is at most the mean-square deviation from any constant. -/
theorem cylinderExcess_le (f : ℝ × Vec 2 → ℝ) (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r)
    (hf : MemLp f 2 (volume.restrict (AVRegularity.External.Campanato.cylinder z r))) (m : ℝ) :
    cylinderExcess f z r ≤ ⨍ p in AVRegularity.External.Campanato.cylinder z r, (f p - m) ^ 2 := by
  set μ := volume.restrict (AVRegularity.External.Campanato.cylinder z r)
  set c := cylinderMean f z r
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (cylinder_volume_ne_top z hr)
  have hfi : Integrable f μ := hf.integrable one_le_two
  have hf2 : Integrable (fun p => f p ^ 2) μ := hf.integrable_sq
  have hV : 0 < volume.real (AVRegularity.External.Campanato.cylinder z r) := cylinder_volume_pos z hr
  have hmean : ∫ p in AVRegularity.External.Campanato.cylinder z r, f p = volume.real (AVRegularity.External.Campanato.cylinder z r) * c := by
    simp only [c, cylinderMean, setAverage_eq, smul_eq_mul]
    field_simp
  have hexp : ∀ a : ℝ, ∫ p in AVRegularity.External.Campanato.cylinder z r, (f p - a) ^ 2 =
      (∫ p in AVRegularity.External.Campanato.cylinder z r, f p ^ 2) - 2 * a * (volume.real (AVRegularity.External.Campanato.cylinder z r) * c) +
        volume.real (AVRegularity.External.Campanato.cylinder z r) * a ^ 2 := by
    intro a
    have h1 : (fun p => (f p - a) ^ 2) = fun p => f p ^ 2 - 2 * a * f p + a ^ 2 := by
      funext p; ring
    rw [h1]
    change ∫ p, (f p ^ 2 - 2 * a * f p + a ^ 2) ∂μ = _
    rw [integral_add (f := fun p => f p ^ 2 - 2 * a * f p) (g := fun _ => a ^ 2)
        (hf2.sub (hfi.const_mul _)) (integrable_const _),
      integral_sub (f := fun p => f p ^ 2) (g := fun p => 2 * a * f p) hf2 (hfi.const_mul _),
      integral_const_mul]
    change (∫ p in AVRegularity.External.Campanato.cylinder z r, f p ^ 2) - 2 * a * (∫ p in AVRegularity.External.Campanato.cylinder z r, f p) +
      ∫ p in AVRegularity.External.Campanato.cylinder z r, a ^ 2 = _
    rw [hmean, setIntegral_const, smul_eq_mul]
  unfold cylinderExcess
  rw [setAverage_eq, setAverage_eq, hexp, hexp]
  simp only [smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hV.le)
  have hkey : -2 * c * (volume.real (AVRegularity.External.Campanato.cylinder z r) * c) + volume.real (AVRegularity.External.Campanato.cylinder z r) * c ^ 2 ≤
      -2 * m * (volume.real (AVRegularity.External.Campanato.cylinder z r) * c) + volume.real (AVRegularity.External.Campanato.cylinder z r) * m ^ 2 := by
    nlinarith [mul_nonneg hV.le (sq_nonneg (m - c))]
  linarith

/-- Cauchy–Schwarz on a set of finite measure: `(∫_S |h|)² ≤ |S| ∫_S h²`. -/
theorem sq_setIntegral_abs_le {S : Set (ℝ × Vec 2)} (hS : volume S ≠ ⊤) {h : ℝ × Vec 2 → ℝ}
    (hh : MemLp h 2 (volume.restrict S)) :
    (∫ p in S, |h p|) ^ 2 ≤ volume.real S * ∫ p in S, h p ^ 2 := by
  have hfin : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS
  have habs : MemLp (fun p => |h p|) (ENNReal.ofReal 2) (volume.restrict S) := by
    simpa [Real.norm_eq_abs] using hh.norm
  have hone : MemLp (fun _ : ℝ × Vec 2 => (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict S) := by
    simpa using memLp_const (μ := volume.restrict S) (p := ENNReal.ofReal 2) (1 : ℝ)
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict S)
    (p := 2) (q := 2) Real.HolderConjugate.two_two (f := fun _ => (1 : ℝ)) (g := fun p => |h p|)
    (Filter.Eventually.of_forall fun _ => zero_le_one)
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) hone habs
  simp only [one_mul, Real.one_rpow, integral_const, smul_eq_mul, mul_one] at hcs
  have hsq : (fun p => |h p| ^ (2 : ℝ)) = fun p => h p ^ 2 := by
    funext p
    rw [Real.rpow_two, sq_abs]
  rw [hsq] at hcs
  have hI : 0 ≤ ∫ p in S, h p ^ 2 := setIntegral_nonneg_of_ae_restrict
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have hA : 0 ≤ ∫ p in S, |h p| := setIntegral_nonneg_of_ae_restrict
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  have hmeas : (volume.restrict S).real Set.univ = volume.real S := by
    simp [measureReal_def]
  rw [hmeas] at hcs
  calc (∫ p in S, |h p|) ^ 2
      ≤ (volume.real S ^ (1 / (2 : ℝ)) * (∫ p in S, h p ^ 2) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ hA hcs 2
    _ = volume.real S * ∫ p in S, h p ^ 2 := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (x := (∫ p in S, h p ^ 2) ^ _),
          ← Real.rpow_mul measureReal_nonneg, ← Real.rpow_mul hI]
        norm_num

theorem HasWeakGradientOn.sub' {B : Set (Vec 2)} {u v : Vec 2 → ℝ} {Du Dv : Vec 2 → Vec 2}
    (hu : HasWeakGradientOn B u Du) (hv : HasWeakGradientOn B v Dv)
    (hui : ∀ φ : Vec 2 → ℝ, IsSpTest B φ → ∀ i : Fin 2,
      IntegrableOn (fun x => u x * fderiv ℝ φ x (basisVec i)) B ∧
      IntegrableOn (fun x => Du x i * φ x) B)
    (hvi : ∀ φ : Vec 2 → ℝ, IsSpTest B φ → ∀ i : Fin 2,
      IntegrableOn (fun x => v x * fderiv ℝ φ x (basisVec i)) B ∧
      IntegrableOn (fun x => Dv x i * φ x) B) :
    HasWeakGradientOn B (fun x => u x - v x) (fun x => Du x - Dv x) := by
  intro i φ hφ hcs hts
  have h1 := hu i φ hφ hcs hts
  have h2 := hv i φ hφ hcs hts
  obtain ⟨hu1, hu2⟩ := hui φ ⟨hφ, hcs, hts⟩ i
  obtain ⟨hv1, hv2⟩ := hvi φ ⟨hφ, hcs, hts⟩ i
  simp only [Pi.sub_apply, sub_mul]
  rw [integral_sub hu1 hv1, integral_sub hu2 hv2, h1, h2]
  ring

/-! # Cylinders, averages and a.e. statements under parabolic dilation -/

theorem vecNormSq_smul (r : ℝ) (y : Vec 2) : vecNormSq (r • y) = r ^ 2 * vecNormSq y := by
  simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem mem_euclidBall_dil {c y : Vec 2} {r ρ : ℝ} (hr : 0 < r) :
    c + r • y ∈ euclidBall c (r * ρ) ↔ y ∈ euclidBall 0 ρ := by
  simp only [euclidBall, Set.mem_ofPred_eq, add_sub_cancel_left, sub_zero, vecNormSq_smul]
  constructor
  · intro h
    have hr2 : 0 < r ^ 2 := by positivity
    have : r ^ 2 * vecNormSq y < r ^ 2 * ρ ^ 2 := by nlinarith
    exact lt_of_mul_lt_mul_left this hr2.le
  · intro h
    have hr2 : 0 < r ^ 2 := by positivity
    nlinarith

theorem parDil_mem_openCyl {z p : ℝ × Vec 2} {r ρ : ℝ} (hr : 0 < r) :
    parDil z r p ∈ openCyl z (r * ρ) ↔ p ∈ openCyl 0 ρ := by
  rcases p with ⟨τ, y⟩
  simp only [parDil, openCyl, Set.mem_prod, Set.mem_Ioo, mem_euclidBall_dil hr]
  have hr2 : 0 < r ^ 2 := by positivity
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, h3⟩
    · have : r ^ 2 * (-ρ ^ 2) < r ^ 2 * τ := by nlinarith
      simpa using (lt_of_mul_lt_mul_left this hr2.le)
    · have : r ^ 2 * τ < r ^ 2 * 0 := by nlinarith
      simpa using (lt_of_mul_lt_mul_left this hr2.le)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, h3⟩
    · simp only [Prod.fst_zero] at h1; nlinarith
    · simp only [Prod.fst_zero] at h2; nlinarith

theorem parDil_mem_cylinder {z p : ℝ × Vec 2} {r ρ : ℝ} (hr : 0 < r) :
    parDil z r p ∈ AVRegularity.External.Campanato.cylinder z (r * ρ) ↔ p ∈ AVRegularity.External.Campanato.cylinder 0 ρ := by
  rcases p with ⟨τ, y⟩
  simp only [parDil, AVRegularity.External.Campanato.cylinder, Set.mem_prod, Set.mem_Ioc, mem_euclidBall_dil hr]
  have hr2 : 0 < r ^ 2 := by positivity
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, h3⟩
    · have : r ^ 2 * (-ρ ^ 2) < r ^ 2 * τ := by nlinarith
      simpa using (lt_of_mul_lt_mul_left this hr2.le)
    · have : r ^ 2 * τ ≤ r ^ 2 * 0 := by nlinarith
      simpa using (le_of_mul_le_mul_left this hr2)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, h3⟩
    · simp only [Prod.fst_zero] at h1; nlinarith
    · simp only [Prod.fst_zero] at h2; nlinarith

theorem image_parDil_eq {z : ℝ × Vec 2} {r : ℝ} (hr : r ≠ 0) {S S' : Set (ℝ × Vec 2)}
    (h : ∀ p, parDil z r p ∈ S' ↔ p ∈ S) : parDil z r '' S = S' := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (h p).2 hp
  · intro hq
    refine ⟨parDilInv z r q, (h _).1 ?_, parDil_parDilInv z hr q⟩
    rwa [parDil_parDilInv z hr q]

theorem image_parDil_openCyl (z : ℝ × Vec 2) {r ρ : ℝ} (hr : 0 < r) :
    parDil z r '' openCyl 0 ρ = openCyl z (r * ρ) :=
  image_parDil_eq hr.ne' fun _ => parDil_mem_openCyl hr

theorem image_parDil_cylinder (z : ℝ × Vec 2) {r ρ : ℝ} (hr : 0 < r) :
    parDil z r '' AVRegularity.External.Campanato.cylinder 0 ρ = AVRegularity.External.Campanato.cylinder z (r * ρ) :=
  image_parDil_eq hr.ne' fun _ => parDil_mem_cylinder hr

/-- The restricted measure pushed forward by a dilation. -/
theorem map_parDil_restrict (z : ℝ × Vec 2) {r : ℝ} (hr : r ≠ 0) (S : Set (ℝ × Vec 2)) :
    Measure.map (parDil z r) (volume.restrict S) =
      ENNReal.ofReal (r ^ 4)⁻¹ • volume.restrict (parDil z r '' S) := by
  have hemb : MeasurableEmbedding (parDil z r) := (parDilEquiv z hr).measurableEmbedding
  rw [← Measure.restrict_smul, ← map_parDil_volume z hr, hemb.restrict_map,
    Set.preimage_image_eq _ hemb.injective]

/-- a.e. statements transfer along a dilation. -/
theorem ae_restrict_parDil {z : ℝ × Vec 2} {r : ℝ} (hr : r ≠ 0) {S : Set (ℝ × Vec 2)}
    {P : ℝ × Vec 2 → Prop} (h : ∀ᵐ q ∂(volume.restrict (parDil z r '' S)), P q) :
    ∀ᵐ p ∂(volume.restrict S), P (parDil z r p) := by
  have hemb : MeasurableEmbedding (parDil z r) := (parDilEquiv z hr).measurableEmbedding
  rw [← hemb.ae_map_iff, map_parDil_restrict z hr S]
  exact Measure.ae_smul_measure h _

theorem volume_image_parDil (z : ℝ × Vec 2) {r : ℝ} (hr : r ≠ 0) (S : Set (ℝ × Vec 2)) :
    volume (parDil z r '' S) = ENNReal.ofReal (r ^ 4) * volume S := by
  have hemb : MeasurableEmbedding (parDil z r) := (parDilEquiv z hr).measurableEmbedding
  have h := congrArg (fun μ : Measure (ℝ × Vec 2) => μ (parDil z r '' S)) (map_parDil_volume z hr)
  simp only [Measure.smul_apply, smul_eq_mul] at h
  rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective] at h
  have hpos : 0 < r ^ 4 := by positivity
  rw [h, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one,
    one_mul]

theorem volumeReal_image_parDil (z : ℝ × Vec 2) {r : ℝ} (hr : r ≠ 0) (S : Set (ℝ × Vec 2)) :
    volume.real (parDil z r '' S) = r ^ 4 * volume.real S := by
  have hpos : 0 < r ^ 4 := by positivity
  simp only [measureReal_def, volume_image_parDil z hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hpos.le]

/-- Averages are invariant under dilation. -/
theorem setAverage_parDil (z : ℝ × Vec 2) {r : ℝ} (hr : r ≠ 0) (f : ℝ × Vec 2 → ℝ)
    (S : Set (ℝ × Vec 2)) :
    ⨍ p in S, f (parDil z r p) = ⨍ p in parDil z r '' S, f p := by
  rw [setAverage_eq, setAverage_eq, integral_parDil z hr, volumeReal_image_parDil z hr]
  have hpos : 0 < r ^ 4 := by positivity
  simp only [smul_eq_mul, mul_inv]
  field_simp

theorem cylinderMean_parDil (z : ℝ × Vec 2) {r ρ : ℝ} (hr : 0 < r)
    (f : ℝ × Vec 2 → ℝ) :
    cylinderMean (fun p => f (parDil z r p)) 0 ρ = cylinderMean f z (r * ρ) := by
  unfold cylinderMean
  rw [setAverage_parDil z hr.ne', image_parDil_cylinder z hr]

theorem cylinderExcess_parDil (z : ℝ × Vec 2) {r ρ : ℝ} (hr : 0 < r)
    (f : ℝ × Vec 2 → ℝ) :
    cylinderExcess (fun p => f (parDil z r p)) 0 ρ = cylinderExcess f z (r * ρ) := by
  unfold cylinderExcess
  rw [cylinderMean_parDil z hr]
  rw [setAverage_parDil z hr.ne' (fun p => (f p - cylinderMean f z (r * ρ)) ^ 2),
    image_parDil_cylinder z hr]

end AVRegularity.Applications
end
end
end

section
@[expose] public section
open MeasureTheory Filter Topology Homogenization AVRegularity.External.Campanato
namespace AVRegularity.Applications

/-! # Statement of the microscopic oscillation lemma (first part)

`OcMicroscopicStatement` is, verbatim, the statement of the main result
`Providers.oc_microscopic`, quantified over `0 < a' < 1`. Theorems that depend on it
take it as an explicit hypothesis. -/

/-- The microscopic oscillation lemma, as in `Providers.oc_microscopic`; Lemma 3.3 of the paper
follows from it. -/
def OcMicroscopicStatement : Prop :=
  ∀ a' : ℝ, 0 < a' → a' < 1 →
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧
      ∀ (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
        (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2),
        (∀ i j : Fin 2, AEStronglyMeasurable (fun p => K p i j) (volume.restrict (openCyl 0 1))) →
        (∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1))) →
        (∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (K p).transpose = -K p) →
        (∃ kK kd : ℝ, 0 ≤ kK ∧ 0 ≤ kd ∧ kK + kd ≤ η ∧
          ∀ᵐ p ∂(volume.restrict (openCyl 0 1)),
            (∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ kK ^ 2 * vecNormSq e) ∧
            vecNormSq (d p) ≤ kd ^ 2) →
        IsDivFreeQ1 d → IsEnergyClassQ1 U DU → IsSkewDriftWeak K d U DU →
        ∃ Ut : ℝ × Vec 2 → ℝ,
          ContinuousOn Ut (cylinder 0 (1 / 2)) ∧
          Ut =ᵐ[volume.restrict (cylinder 0 (1 / 2))] U ∧
          Tendsto (fun τ => ∫ y in euclidBall 0 (1 / 2), (U (τ, y) - Ut (0, y)) ^ 2)
            (𝓝[<] 0 ⊓ ae volume) (𝓝 0) ∧
          ∀ c : ℝ, ∀ x ∈ cylinder 0 (1 / 2), ∀ z ∈ cylinder 0 (1 / 2),
            ∀ w ∈ cylinder 0 (1 / 2), z ≠ w →
              |Ut z - Ut w| / parabolicHolderDistance z w ^ a' + |Ut x - cylinderMean U 0 1|
                ≤ C * Real.sqrt (⨍ p in openCyl 0 1, (U p - c) ^ 2)

end AVRegularity.Applications
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # Spatial dilations and weak gradients

`spDil c r y = c + r y` on `ℝ²`; weak gradients transform by
`∇(u ∘ spDil c r) = r (∇u) ∘ spDil c r`. -/

/-- The spatial dilation `y ↦ c + r y`. -/
def spDil (c : Vec 2) (r : ℝ) (y : Vec 2) : Vec 2 := c + r • y

/-- Its inverse `x ↦ r⁻¹ (x - c)`. -/
def spDilInv (c : Vec 2) (r : ℝ) (x : Vec 2) : Vec 2 := r⁻¹ • (x - c)

theorem spDilInv_spDil (c : Vec 2) {r : ℝ} (hr : r ≠ 0) (y : Vec 2) :
    spDilInv c r (spDil c r y) = y := by
  simp [spDil, spDilInv, smul_smul, inv_mul_cancel₀ hr]

theorem spDil_spDilInv (c : Vec 2) {r : ℝ} (hr : r ≠ 0) (x : Vec 2) :
    spDil c r (spDilInv c r x) = x := by
  simp [spDil, spDilInv, smul_smul, mul_inv_cancel₀ hr]

theorem measurable_spDil (c : Vec 2) (r : ℝ) : Measurable (spDil c r) := by
  unfold spDil; fun_prop

theorem measurable_spDilInv (c : Vec 2) (r : ℝ) : Measurable (spDilInv c r) := by
  unfold spDilInv; fun_prop

/-- `spDil` as a measurable equivalence. -/
def spDilEquiv (c : Vec 2) {r : ℝ} (hr : r ≠ 0) : Vec 2 ≃ᵐ Vec 2 where
  toFun := spDil c r
  invFun := spDilInv c r
  left_inv := spDilInv_spDil c hr
  right_inv := spDil_spDilInv c hr
  measurable_toFun := measurable_spDil c r
  measurable_invFun := measurable_spDilInv c r

theorem map_spDil_restrict (c : Vec 2) {r : ℝ} (hr : r ≠ 0) (S : Set (Vec 2)) :
    Measure.map (spDil c r) (volume.restrict S) =
      ENNReal.ofReal (r ^ 2)⁻¹ • volume.restrict (spDil c r '' S) := by
  have hemb : MeasurableEmbedding (spDil c r) := (spDilEquiv c hr).measurableEmbedding
  have hmap : Measure.map (spDil c r) volume = ENNReal.ofReal (r ^ 2)⁻¹ • volume := by
    have := map_space_affine_volume c hr
    rw [abs_of_nonneg (sq_nonneg r)] at this
    exact this
  rw [← Measure.restrict_smul, ← hmap, hemb.restrict_map,
    Set.preimage_image_eq _ hemb.injective]

theorem integral_spDil (c : Vec 2) {r : ℝ} (hr : r ≠ 0) (f : Vec 2 → ℝ) (S : Set (Vec 2)) :
    ∫ y in S, f (spDil c r y) = (r ^ 2)⁻¹ * ∫ x in spDil c r '' S, f x := by
  have h1 : ∫ y in S, f (spDil c r y) =
      ∫ x, f x ∂(Measure.map (spDil c r) (volume.restrict S)) :=
    (integral_map_equiv (spDilEquiv c hr) f).symm
  rw [h1, map_spDil_restrict c hr, integral_smul_measure]
  have hpos : 0 ≤ (r ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg r)
  rw [ENNReal.toReal_ofReal hpos, smul_eq_mul]

theorem image_spDil_euclidBall (c : Vec 2) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    spDil c r '' euclidBall 0 ρ = euclidBall c (r * ρ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_euclidBall_dil hr).2 hy
  · intro hx
    refine ⟨spDilInv c r x, (mem_euclidBall_dil (c := c) hr).1 ?_, spDil_spDilInv c hr.ne' x⟩
    change spDil c r (spDilInv c r x) ∈ _
    rwa [spDil_spDilInv c hr.ne' x]

theorem ae_restrict_spDil {c : Vec 2} {r : ℝ} (hr : r ≠ 0) {S : Set (Vec 2)}
    {P : Vec 2 → Prop} (h : ∀ᵐ x ∂(volume.restrict (spDil c r '' S)), P x) :
    ∀ᵐ y ∂(volume.restrict S), P (spDil c r y) := by
  have hemb : MeasurableEmbedding (spDil c r) := (spDilEquiv c hr).measurableEmbedding
  rw [← hemb.ae_map_iff, map_spDil_restrict c hr S]
  exact Measure.ae_smul_measure h _

/-- The spatially pushed test function `ψ ∘ spDilInv c r`. -/
def pushSp (c : Vec 2) (r : ℝ) (ψ : Vec 2 → ℝ) : Vec 2 → ℝ := fun x => ψ (spDilInv c r x)

theorem hasFDerivAt_spDilInv (c : Vec 2) (r : ℝ) (x : Vec 2) :
    HasFDerivAt (spDilInv c r) (r⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)) x := by
  have h : spDilInv c r = fun x => (r⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)) x - r⁻¹ • c := by
    funext x
    simp [spDilInv, smul_sub]
  rw [h]
  exact (r⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)).hasFDerivAt.sub_const _

theorem contDiff_spDilInv (c : Vec 2) (r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (spDilInv c r) := by
  unfold spDilInv
  fun_prop

theorem fderiv_pushSp (c : Vec 2) (r : ℝ) {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (x v : Vec 2) :
    fderiv ℝ (pushSp c r ψ) x v = r⁻¹ * fderiv ℝ ψ (spDilInv c r x) v := by
  have hd : DifferentiableAt ℝ ψ (spDilInv c r x) :=
    (hψ.differentiable (by simp)).differentiableAt
  have hcomp := hd.hasFDerivAt.comp x (hasFDerivAt_spDilInv c r x)
  change fderiv ℝ (ψ ∘ spDilInv c r) x v = _
  rw [hcomp.fderiv]
  simp

theorem spGrad_pushSp (c : Vec 2) {r : ℝ} (hr : r ≠ 0) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : Vec 2) :
    spGrad (pushSp c r ψ) (spDil c r y) = r⁻¹ • spGrad ψ y := by
  funext i
  simp [spGrad, fderiv_pushSp c r hψ, spDilInv_spDil c hr]

theorem continuous_spDil (c : Vec 2) (r : ℝ) : Continuous (spDil c r) := by
  unfold spDil; fun_prop

/-- `spDil` as a homeomorphism. -/
def spDilHomeo (c : Vec 2) {r : ℝ} (hr : r ≠ 0) : Vec 2 ≃ₜ Vec 2 where
  toFun := spDil c r
  invFun := spDilInv c r
  left_inv := spDilInv_spDil c hr
  right_inv := spDil_spDilInv c hr
  continuous_toFun := continuous_spDil c r
  continuous_invFun := (contDiff_spDilInv c r).continuous

theorem tsupport_pushSp (c : Vec 2) {r : ℝ} (hr : r ≠ 0) (ψ : Vec 2 → ℝ) :
    tsupport (pushSp c r ψ) = spDil c r '' tsupport ψ := by
  have hsupp : Function.support (pushSp c r ψ) = spDilInv c r ⁻¹' Function.support ψ := rfl
  have himg : ∀ A : Set (Vec 2), spDilInv c r ⁻¹' A = spDil c r '' A := by
    intro A
    ext x
    constructor
    · intro hx
      exact ⟨spDilInv c r x, hx, spDil_spDilInv c hr x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [Set.mem_preimage, spDilInv_spDil c hr] using hy
  unfold tsupport
  rw [hsupp, himg]
  exact ((spDilHomeo c hr).image_closure (Function.support ψ)).symm

theorem isSpTest_pushSp (c : Vec 2) {r : ℝ} (hr : 0 < r) {ψ : Vec 2 → ℝ} {ρ : ℝ}
    (hψ : IsSpTest (euclidBall 0 ρ) ψ) : IsSpTest (euclidBall c (r * ρ)) (pushSp c r ψ) := by
  obtain ⟨hsm, hcs, hts⟩ := hψ
  refine ⟨hsm.comp (contDiff_spDilInv c r), ?_, ?_⟩
  · exact hcs.comp_homeomorph (spDilHomeo c hr.ne').symm
  · rw [tsupport_pushSp c hr.ne', ← image_spDil_euclidBall c hr]
    exact Set.image_mono hts

/-- Monotonicity of weak gradients in the domain. -/
theorem HasWeakGradientOn.mono_set {U V : Set (Vec 2)} (hVU : V ⊆ U)
    (hUm : MeasurableSet U) {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : HasWeakGradientOn U u Du) : HasWeakGradientOn V u Du := by
  intro i φ hφ hcs hts
  have hφU := h i φ hφ hcs (hts.trans hVU)
  have hzero1 : ∀ x ∈ U \ V, u x * (fderiv ℝ φ x) (basisVec i) = 0 := by
    intro x hx
    have hx' : x ∉ tsupport φ := fun hx' => hx.2 (hts hx')
    simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx']
  have hzero2 : ∀ x ∈ U \ V, Du x i * φ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport φ := fun hx' => hx.2 (hts hx')
    simp [image_eq_zero_of_notMem_tsupport hx']
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUm hVU hzero1,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUm hVU hzero2] at hφU
  exact hφU

/-- Weak gradients under spatial dilation: if `∇u = Du` weakly on `B_{rρ}(c)`, then
`∇(u ∘ spDil c r) = r (Du ∘ spDil c r)` weakly on `B_ρ(0)`. -/
theorem HasWeakGradientOn.comp_spDil {c : Vec 2} {r ρ : ℝ} (hr : 0 < r) {u : Vec 2 → ℝ}
    {Du : Vec 2 → Vec 2} (h : HasWeakGradientOn (euclidBall c (r * ρ)) u Du) :
    HasWeakGradientOn (euclidBall 0 ρ) (fun y => u (spDil c r y))
      (fun y => r • Du (spDil c r y)) := by
  intro i ψ hψ hcs hts
  have htest : IsSpTest (euclidBall c (r * ρ)) (pushSp c r ψ) :=
    isSpTest_pushSp c hr ⟨hψ, hcs, hts⟩
  have hw := h i (pushSp c r ψ) htest.1 htest.2.1 htest.2.2
  have hr0 : r ≠ 0 := hr.ne'
  -- rewrite both integrals over `B_ρ(0)` by the change of variables
  have hL : ∫ y in euclidBall 0 ρ, u (spDil c r y) * (fderiv ℝ ψ y) (basisVec i) =
      r * ((r ^ 2)⁻¹ * ∫ x in euclidBall c (r * ρ), u x *
        (fderiv ℝ (pushSp c r ψ) x) (basisVec i)) := by
    rw [← image_spDil_euclidBall c hr, ← integral_spDil c hr0, ← integral_const_mul]
    refine setIntegral_congr_fun (External.Campanato.euclidBall_measurable 0 ρ) fun y _ => ?_
    simp only [fderiv_pushSp c r hψ, spDilInv_spDil c hr0]
    field_simp
  have hR : ∫ y in euclidBall 0 ρ, (r • Du (spDil c r y)) i * ψ y =
      r * ((r ^ 2)⁻¹ * ∫ x in euclidBall c (r * ρ), Du x i * pushSp c r ψ x) := by
    rw [← image_spDil_euclidBall c hr, ← integral_spDil c hr0, ← integral_const_mul]
    refine setIntegral_congr_fun (External.Campanato.euclidBall_measurable 0 ρ) fun y _ => ?_
    simp only [pushSp, spDilInv_spDil c hr0, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hL, hR, hw]
  ring

/-! # Test functions under parabolic dilation

For `φ̃ ∈ C^∞_c(Q₁)` the function `φ = φ̃ ∘ parDilInv z r` lies in `C^∞_c(Q_r(z))`, with
`∂ₜφ ∘ T = r⁻² ∂τφ̃` and `∇ₓφ ∘ T = r⁻¹ ∇_yφ̃`. -/

/-- The linear part of `parDilInv z r`. -/
def parDilInvLin (r : ℝ) : (ℝ × Vec 2) →L[ℝ] (ℝ × Vec 2) :=
  ContinuousLinearMap.prodMap ((r ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    (r⁻¹ • ContinuousLinearMap.id ℝ (Vec 2))

@[simp] theorem parDilInvLin_apply (r : ℝ) (v : ℝ × Vec 2) :
    parDilInvLin r v = ((r ^ 2)⁻¹ * v.1, r⁻¹ • v.2) := rfl

theorem parDilInv_eq_lin (z : ℝ × Vec 2) (r : ℝ) (p : ℝ × Vec 2) :
    parDilInv z r p = parDilInvLin r p + parDilInv z r 0 := by
  rcases p with ⟨t, x⟩
  simp only [parDilInv, parDilInvLin_apply, Prod.fst_zero, Prod.snd_zero, Prod.mk_add_mk,
    zero_sub]
  refine Prod.ext ?_ ?_
  · simp only
    ring
  · simp only [smul_sub, smul_neg]
    abel

theorem hasFDerivAt_parDilInv (z : ℝ × Vec 2) (r : ℝ) (q : ℝ × Vec 2) :
    HasFDerivAt (parDilInv z r) (parDilInvLin r) q := by
  have h : parDilInv z r = fun p => parDilInvLin r p + parDilInv z r 0 :=
    funext (parDilInv_eq_lin z r)
  rw [h]
  exact (parDilInvLin r).hasFDerivAt.add_const _

theorem contDiff_parDilInv (z : ℝ × Vec 2) (r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (parDilInv z r) := by
  have h : parDilInv z r = fun p => parDilInvLin r p + parDilInv z r 0 :=
    funext (parDilInv_eq_lin z r)
  rw [h]
  exact (parDilInvLin r).contDiff.add contDiff_const

theorem continuous_parDil (z : ℝ × Vec 2) (r : ℝ) : Continuous (parDil z r) := by
  unfold parDil
  fun_prop

/-- `parDil` as a homeomorphism. -/
def parDilHomeo (z : ℝ × Vec 2) {r : ℝ} (hr : r ≠ 0) : (ℝ × Vec 2) ≃ₜ (ℝ × Vec 2) where
  toFun := parDil z r
  invFun := parDilInv z r
  left_inv := parDilInv_parDil z hr
  right_inv := parDil_parDilInv z hr
  continuous_toFun := continuous_parDil z r
  continuous_invFun := (contDiff_parDilInv z r).continuous

/-- The pushed test function `φ̃ ∘ parDilInv z r`. -/
def pushTest (z : ℝ × Vec 2) (r : ℝ) (φ : ℝ × Vec 2 → ℝ) : ℝ × Vec 2 → ℝ :=
  fun q => φ (parDilInv z r q)

theorem fderiv_pushTest (z : ℝ × Vec 2) (r : ℝ) {φ : ℝ × Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (q v : ℝ × Vec 2) :
    fderiv ℝ (pushTest z r φ) q v = fderiv ℝ φ (parDilInv z r q) (parDilInvLin r v) := by
  have hd : DifferentiableAt ℝ φ (parDilInv z r q) :=
    (hφ.differentiable (by simp)).differentiableAt
  have hcomp := hd.hasFDerivAt.comp q (hasFDerivAt_parDilInv z r q)
  change fderiv ℝ (φ ∘ parDilInv z r) q v = _
  rw [hcomp.fderiv]
  rfl

theorem stTimeDeriv_pushTest (z : ℝ × Vec 2) {r : ℝ} {φ : ℝ × Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (p : ℝ × Vec 2) (hr : r ≠ 0) :
    stTimeDeriv (pushTest z r φ) (parDil z r p) = (r ^ 2)⁻¹ * stTimeDeriv φ p := by
  unfold stTimeDeriv
  rw [fderiv_pushTest z r hφ, parDilInv_parDil z hr]
  have : parDilInvLin r (1, 0) = (r ^ 2)⁻¹ • ((1 : ℝ), (0 : Vec 2)) := by
    simp
  rw [this, map_smul, smul_eq_mul]

theorem stSpaceGrad_pushTest (z : ℝ × Vec 2) {r : ℝ} {φ : ℝ × Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (p : ℝ × Vec 2) (hr : r ≠ 0) :
    stSpaceGrad (pushTest z r φ) (parDil z r p) = r⁻¹ • stSpaceGrad φ p := by
  funext i
  unfold stSpaceGrad
  rw [fderiv_pushTest z r hφ, parDilInv_parDil z hr]
  have : parDilInvLin r (0, basisVec i) = r⁻¹ • ((0 : ℝ), basisVec i) := by
    simp
  rw [this, map_smul]
  simp

theorem contDiff_pushTest (z : ℝ × Vec 2) (r : ℝ) {φ : ℝ × Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : ContDiff ℝ (⊤ : ℕ∞) (pushTest z r φ) :=
  hφ.comp (contDiff_parDilInv z r)

theorem tsupport_pushTest (z : ℝ × Vec 2) {r : ℝ} (hr : r ≠ 0) (φ : ℝ × Vec 2 → ℝ) :
    tsupport (pushTest z r φ) = parDil z r '' tsupport φ := by
  have hsupp : Function.support (pushTest z r φ) = parDilInv z r ⁻¹' Function.support φ := rfl
  unfold tsupport
  rw [hsupp]
  have himg : ∀ A : Set (ℝ × Vec 2), parDilInv z r ⁻¹' A = parDil z r '' A := by
    intro A
    ext q
    constructor
    · intro hq
      exact ⟨parDilInv z r q, hq, parDil_parDilInv z hr q⟩
    · rintro ⟨p, hp, rfl⟩
      simpa [Set.mem_preimage, parDilInv_parDil z hr] using hp
  rw [himg]
  exact ((parDilHomeo z hr).image_closure (Function.support φ)).symm

theorem isSTTest_pushTest (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) {φ : ℝ × Vec 2 → ℝ}
    {ρ : ℝ} (hφ : IsSTTest (openCyl 0 ρ) φ) :
    IsSTTest (openCyl z (r * ρ)) (pushTest z r φ) := by
  obtain ⟨hsm, hcs, hts⟩ := hφ
  refine ⟨contDiff_pushTest z r hsm, ?_, ?_⟩
  · have := hcs.comp_homeomorph (parDilHomeo z hr.ne').symm
    exact this
  · rw [tsupport_pushTest z hr.ne', ← image_parDil_openCyl z hr]
    exact Set.image_mono hts

end AVRegularity.Applications
end
end
end
