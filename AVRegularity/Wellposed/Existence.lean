-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVenhance.Statements.Roots.IsWeakSolution
public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
import AVenhance.Statements.Roots.WeakWellposed
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Wellposed

/-- The forward space-time affine map from the unit time interval to a window. -/
def windowForward (t₁ T : ℝ) (p : ℝ × Vec 2) : ℝ × Vec 2 :=
  (t₁ + T * p.1, p.2)

/-- The inverse space-time affine map. -/
def windowBackward (t₁ T : ℝ) (p : ℝ × Vec 2) : ℝ × Vec 2 :=
  ((p.1 - t₁) / T, p.2)

def timeForward (t₁ T s : ℝ) : ℝ := t₁ + T * s

def timeBackward (t₁ T t : ℝ) : ℝ := (t - t₁) / T

theorem measurable_windowForward (t₁ T : ℝ) : Measurable (windowForward t₁ T) := by
  fun_prop [windowForward]

theorem measurable_windowBackward (t₁ T : ℝ) : Measurable (windowBackward t₁ T) := by
  fun_prop [windowBackward]

theorem measurable_timeForward (t₁ T : ℝ) : Measurable (timeForward t₁ T) := by
  fun_prop [timeForward]

theorem measurable_timeBackward (t₁ T : ℝ) : Measurable (timeBackward t₁ T) := by
  fun_prop [timeBackward]

def windowEquiv (t₁ T : ℝ) (hT : T ≠ 0) : (ℝ × Vec 2) ≃ᵐ (ℝ × Vec 2) where
  toFun := windowForward t₁ T
  invFun := windowBackward t₁ T
  left_inv p := by
    rcases p with ⟨t, x⟩
    apply Prod.ext
    · change ((t₁ + T * t - t₁) / T) = t
      field_simp [hT]
      ring
    · rfl
  right_inv p := by
    rcases p with ⟨s, x⟩
    apply Prod.ext
    · change t₁ + T * ((s - t₁) / T) = s
      field_simp [hT]
      ring
    · rfl
  measurable_toFun := measurable_windowForward t₁ T
  measurable_invFun := measurable_windowBackward t₁ T

theorem map_affine_volume (a c : ℝ) (hc : c ≠ 0) :
    Measure.map (fun x : ℝ => a + c * x) volume = ENNReal.ofReal |c⁻¹| • volume := by
  let scale : ℝ → ℝ := fun x => c * x
  let shift : ℝ → ℝ := fun x => x + a
  have hfun : (fun x : ℝ => a + c * x) = shift ∘ scale := by
    funext x
    simp [shift, scale, add_comm]
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Real.map_volume_mul_left hc]
  rw [Measure.map_smul _ (by fun_prop), map_add_right_eq_self]

theorem map_windowForward_volume (t₁ T : ℝ) (hT : T ≠ 0) :
    Measure.map (windowForward t₁ T) (volume : Measure (ℝ × Vec 2)) =
      ENNReal.ofReal |T⁻¹| • volume := by
  rw [Measure.volume_eq_prod ℝ (Vec 2)]
  change Measure.map (Prod.map (fun s : ℝ => t₁ + T * s) id) (volume.prod volume) = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) (by fun_prop)]
  rw [map_affine_volume t₁ T hT, Measure.map_id, Measure.prod_smul_left]

theorem map_windowBackward_volume (t₁ T : ℝ) (hT : T ≠ 0) :
    Measure.map (windowBackward t₁ T) (volume : Measure (ℝ × Vec 2)) =
      ENNReal.ofReal |T| • volume := by
  have hTi : T⁻¹ ≠ 0 := inv_ne_zero hT
  have hmap := map_windowForward_volume ((-t₁) / T) T⁻¹ hTi
  have hfun : windowBackward t₁ T = windowForward ((-t₁) / T) T⁻¹ := by
    funext p
    rcases p with ⟨t, x⟩
    simp [windowBackward, windowForward]
    ring
  have habs : |(T⁻¹)⁻¹| = |T| := by simp
  calc
    Measure.map (windowBackward t₁ T) volume =
        Measure.map (windowForward ((-t₁) / T) T⁻¹) volume := by rw [hfun]
    _ = ENNReal.ofReal |T| • volume := by simpa [habs] using hmap

theorem map_restrict_windowForward {t₁ T : ℝ} (hT : 0 < T)
    {U V : Set ℝ} {S : Set (Vec 2)}
    (hpre : windowForward t₁ T ⁻¹' (V ×ˢ S) = U ×ˢ S)
    (hV : MeasurableSet (V ×ˢ S)) :
    Measure.map (windowForward t₁ T) (volume.restrict (U ×ˢ S)) =
      ENNReal.ofReal T⁻¹ • volume.restrict (V ×ˢ S) := by
  have hTne : T ≠ 0 := ne_of_gt hT
  calc
    Measure.map (windowForward t₁ T) (volume.restrict (U ×ˢ S)) =
        Measure.map (windowForward t₁ T)
          (volume.restrict (windowForward t₁ T ⁻¹' (V ×ˢ S))) := by rw [hpre]
    _ = (Measure.map (windowForward t₁ T) volume).restrict (V ×ˢ S) :=
      (Measure.restrict_map (measurable_windowForward t₁ T) hV).symm
    _ = ENNReal.ofReal T⁻¹ • volume.restrict (V ×ˢ S) := by
      rw [map_windowForward_volume t₁ T hTne]
      have hinv : 0 ≤ T⁻¹ := le_of_lt (inv_pos.mpr hT)
      rw [abs_of_nonneg hinv, Measure.restrict_smul]

theorem map_restrict_windowBackward {t₁ T : ℝ} (hT : 0 < T)
    {U V : Set ℝ} {S : Set (Vec 2)}
    (hpre : windowBackward t₁ T ⁻¹' (U ×ˢ S) = V ×ˢ S)
    (hU : MeasurableSet (U ×ˢ S)) :
    Measure.map (windowBackward t₁ T) (volume.restrict (V ×ˢ S)) =
      ENNReal.ofReal T • volume.restrict (U ×ˢ S) := by
  have hTne : T ≠ 0 := ne_of_gt hT
  calc
    Measure.map (windowBackward t₁ T) (volume.restrict (V ×ˢ S)) =
        Measure.map (windowBackward t₁ T)
          (volume.restrict (windowBackward t₁ T ⁻¹' (U ×ˢ S))) := by rw [hpre]
    _ = (Measure.map (windowBackward t₁ T) volume).restrict (U ×ˢ S) :=
      (Measure.restrict_map (measurable_windowBackward t₁ T) hU).symm
    _ = ENNReal.ofReal T • volume.restrict (U ×ˢ S) := by
      rw [map_windowBackward_volume t₁ T hTne, abs_of_pos hT, Measure.restrict_smul]

theorem map_timeForward_volume (t₁ T : ℝ) (hT : T ≠ 0) :
    Measure.map (timeForward t₁ T) (volume : Measure ℝ) = ENNReal.ofReal |T⁻¹| • volume := by
  change Measure.map (fun x : ℝ => t₁ + T * x) volume = _
  exact map_affine_volume t₁ T hT

theorem map_timeBackward_volume (t₁ T : ℝ) (hT : T ≠ 0) :
    Measure.map (timeBackward t₁ T) (volume : Measure ℝ) = ENNReal.ofReal |T| • volume := by
  have hTi : T⁻¹ ≠ 0 := inv_ne_zero hT
  have hmap := map_affine_volume ((-t₁) / T) T⁻¹ hTi
  have hfun : timeBackward t₁ T = fun t => ((-t₁) / T) + T⁻¹ * t := by
    funext t
    simp [timeBackward]
    field_simp [hT]
    ring
  have habs : |(T⁻¹)⁻¹| = |T| := by simp
  calc
    Measure.map (timeBackward t₁ T) volume =
        Measure.map (fun t => ((-t₁) / T) + T⁻¹ * t) volume := by rw [hfun]
    _ = ENNReal.ofReal |T| • volume := by simpa [habs] using hmap

theorem map_restrict_timeForward {t₁ T : ℝ} (hT : 0 < T)
    {U V : Set ℝ} (hpre : timeForward t₁ T ⁻¹' V = U)
    (hV : MeasurableSet V) :
    Measure.map (timeForward t₁ T) (volume.restrict U) =
      ENNReal.ofReal T⁻¹ • volume.restrict V := by
  have hTne : T ≠ 0 := ne_of_gt hT
  calc
    Measure.map (timeForward t₁ T) (volume.restrict U) =
        Measure.map (timeForward t₁ T) (volume.restrict (timeForward t₁ T ⁻¹' V)) := by rw [hpre]
    _ = (Measure.map (timeForward t₁ T) volume).restrict V :=
      (Measure.restrict_map (measurable_timeForward t₁ T) hV).symm
    _ = ENNReal.ofReal T⁻¹ • volume.restrict V := by
      rw [map_timeForward_volume t₁ T hTne]
      rw [abs_of_nonneg (le_of_lt (inv_pos.mpr hT)), Measure.restrict_smul]

theorem map_restrict_timeBackward {t₁ T : ℝ} (hT : 0 < T)
    {U V : Set ℝ} (hpre : timeBackward t₁ T ⁻¹' U = V)
    (hU : MeasurableSet U) :
    Measure.map (timeBackward t₁ T) (volume.restrict V) =
      ENNReal.ofReal T • volume.restrict U := by
  have hTne : T ≠ 0 := ne_of_gt hT
  calc
    Measure.map (timeBackward t₁ T) (volume.restrict V) =
        Measure.map (timeBackward t₁ T) (volume.restrict (timeBackward t₁ T ⁻¹' U)) := by rw [hpre]
    _ = (Measure.map (timeBackward t₁ T) volume).restrict U :=
      (Measure.restrict_map (measurable_timeBackward t₁ T) hU).symm
    _ = ENNReal.ofReal T • volume.restrict U := by
      rw [map_timeBackward_volume t₁ T hTne, abs_of_pos hT, Measure.restrict_smul]

theorem windowForward_maps_interval {t₁ T : ℝ} (hT : 0 < T) :
    windowForward t₁ T ⁻¹' (Set.Icc t₁ (t₁ + T) ×ˢ Set.univ) =
      Set.Icc (0 : ℝ) 1 ×ˢ Set.univ := by
  apply Set.ext
  intro p
  rcases p with ⟨s, x⟩
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc, Set.mem_univ, windowForward]
  simp only [and_true]
  change (t₁ ≤ t₁ + T * s ∧ t₁ + T * s ≤ t₁ + T) ↔ (0 ≤ s ∧ s ≤ 1)
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · have : 0 ≤ T * s := by linarith
      exact (mul_nonneg_iff_of_pos_left hT).mp this
    · have : T * s ≤ T := by linarith
      have hmul : T * s ≤ T * 1 := by simpa using this
      exact (mul_le_mul_iff_of_pos_left hT).mp hmul
  · rintro ⟨hlo, hhi⟩
    constructor
    · have : 0 ≤ T * s := (mul_nonneg_iff_of_pos_left hT).2 hlo
      linarith
    · have : T * s ≤ T * 1 := (mul_le_mul_iff_of_pos_left hT).2 hhi
      linarith

theorem timeForward_maps_interval {t₁ T : ℝ} (hT : 0 < T) :
    timeForward t₁ T ⁻¹' Set.Icc t₁ (t₁ + T) = Set.Icc (0 : ℝ) 1 := by
  ext s
  simp only [Set.mem_preimage, Set.mem_Icc, timeForward]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · exact (mul_nonneg_iff_of_pos_left hT).mp (by linarith)
    · have h' : T * s ≤ T := by linarith
      apply (mul_le_mul_iff_of_pos_left hT).mp
      simpa using h'
  · rintro ⟨hlo, hhi⟩
    constructor
    · linarith [mul_nonneg (le_of_lt hT) hlo]
    · have hm : T * s ≤ T * 1 := (mul_le_mul_iff_of_pos_left hT).2 hhi
      linarith

theorem timeBackward_maps_interval {t₁ T : ℝ} (hT : 0 < T) :
    timeBackward t₁ T ⁻¹' Set.Icc (0 : ℝ) 1 = Set.Icc t₁ (t₁ + T) := by
  ext t
  simp only [Set.mem_preimage, Set.mem_Icc, timeBackward]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · have hm : 0 ≤ ((t - t₁) / T) * T := mul_nonneg hlo hT.le
      have heq : ((t - t₁) / T) * T = t - t₁ := by field_simp [ne_of_gt hT]
      rw [heq] at hm
      linarith
    · rw [div_le_iff₀ hT] at hhi
      linarith
  · rintro ⟨hlo, hhi⟩
    constructor
    · exact div_nonneg (by linarith) hT.le
    · apply (div_le_one hT).2
      linarith

theorem timeForward_maps_Ioo {t₁ T : ℝ} (hT : 0 < T) :
    timeForward t₁ T ⁻¹' Set.Ioo t₁ (t₁ + T) = Set.Ioo (0 : ℝ) 1 := by
  ext s
  simp only [Set.mem_preimage, Set.mem_Ioo, timeForward]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · exact (mul_lt_mul_iff_of_pos_left hT).mp (by linarith)
    · have hm : T * s < T := by linarith
      exact (mul_lt_mul_iff_of_pos_left hT).mp (by simpa using hm)
  · rintro ⟨hlo, hhi⟩
    constructor
    · have hm : 0 < T * s := mul_pos hT hlo
      linarith
    · have hm : T * s < T * 1 := (mul_lt_mul_iff_of_pos_left hT).2 hhi
      linarith

theorem timeBackward_maps_Ioo {t₁ T : ℝ} (hT : 0 < T) :
    timeBackward t₁ T ⁻¹' Set.Ioo (0 : ℝ) 1 = Set.Ioo t₁ (t₁ + T) := by
  ext t
  simp only [Set.mem_preimage, Set.mem_Ioo, timeBackward]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · have hm : 0 < ((t - t₁) / T) * T := mul_pos hlo hT
      have heq : ((t - t₁) / T) * T = t - t₁ := by field_simp [ne_of_gt hT]
      rw [heq] at hm
      linarith
    · rw [div_lt_iff₀ hT] at hhi
      linarith
  · rintro ⟨hlo, hhi⟩
    constructor
    · exact div_pos (by linarith) hT
    · exact (div_lt_one hT).2 (by linarith)

theorem windowForward_maps_Ioo_product {t₁ T : ℝ} (hT : 0 < T)
    (S : Set (Vec 2)) :
    windowForward t₁ T ⁻¹' (Set.Ioo t₁ (t₁ + T) ×ˢ S) =
      Set.Ioo (0 : ℝ) 1 ×ˢ S := by
  ext p
  rcases p with ⟨s, x⟩
  have hs := congrArg (fun A : Set ℝ => s ∈ A)
    (timeForward_maps_Ioo (t₁ := t₁) (T := T) hT)
  have htime : timeForward t₁ T s ∈ Set.Ioo t₁ (t₁ + T) ↔ s ∈ Set.Ioo 0 1 := by
    simpa [Set.mem_preimage] using hs
  change (timeForward t₁ T s ∈ Set.Ioo t₁ (t₁ + T) ∧ x ∈ S) ↔
    (s ∈ Set.Ioo 0 1 ∧ x ∈ S)
  exact and_congr htime Iff.rfl

theorem windowBackward_maps_Ioo_product {t₁ T : ℝ} (hT : 0 < T)
    (S : Set (Vec 2)) :
    windowBackward t₁ T ⁻¹' (Set.Ioo (0 : ℝ) 1 ×ˢ S) =
      Set.Ioo t₁ (t₁ + T) ×ˢ S := by
  ext p
  rcases p with ⟨t, x⟩
  have ht := congrArg (fun A : Set ℝ => t ∈ A)
    (timeBackward_maps_Ioo (t₁ := t₁) (T := T) hT)
  have htime : timeBackward t₁ T t ∈ Set.Ioo 0 1 ↔ t ∈ Set.Ioo t₁ (t₁ + T) := by
    simpa [Set.mem_preimage] using ht
  change (timeBackward t₁ T t ∈ Set.Ioo 0 1 ∧ x ∈ S) ↔
    (t ∈ Set.Ioo t₁ (t₁ + T) ∧ x ∈ S)
  exact and_congr htime Iff.rfl

theorem unitCube_measurable : MeasurableSet unitCube :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem windowForwardMeasurePreserving {t₁ T : ℝ} (hT : 0 < T) :
    MeasurePreserving (windowForward t₁ T)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
      (ENNReal.ofReal T⁻¹ • volume.restrict (Set.Icc t₁ (t₁ + T) ×ˢ Set.univ)) := by
  refine ⟨measurable_windowForward t₁ T, ?_⟩
  exact map_restrict_windowForward hT (windowForward_maps_interval hT)
    (measurableSet_Icc.prod MeasurableSet.univ)

theorem windowForwardOpenCubeMeasurePreserving {t₁ T : ℝ} (hT : 0 < T) :
    MeasurePreserving (windowForward t₁ T)
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube))
      (ENNReal.ofReal T⁻¹ • volume.restrict (Set.Ioo t₁ (t₁ + T) ×ˢ unitCube)) := by
  refine ⟨measurable_windowForward t₁ T, ?_⟩
  exact map_restrict_windowForward hT (windowForward_maps_Ioo_product hT unitCube)
    (measurableSet_Ioo.prod unitCube_measurable)

theorem windowBackwardOpenCubeMeasurePreserving {t₁ T : ℝ} (hT : 0 < T) :
    MeasurePreserving (windowBackward t₁ T)
      (volume.restrict (Set.Ioo t₁ (t₁ + T) ×ˢ unitCube))
      (ENNReal.ofReal T • volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube)) := by
  refine ⟨measurable_windowBackward t₁ T, ?_⟩
  exact map_restrict_windowBackward hT (windowBackward_maps_Ioo_product hT unitCube)
    (measurableSet_Ioo.prod unitCube_measurable)

theorem timeForwardOpenMeasurePreserving {t₁ T : ℝ} (hT : 0 < T) :
    MeasurePreserving (timeForward t₁ T)
      (volume.restrict (Set.Ioo (0 : ℝ) 1))
      (ENNReal.ofReal T⁻¹ • volume.restrict (Set.Ioo t₁ (t₁ + T))) := by
  refine ⟨measurable_timeForward t₁ T, ?_⟩
  exact map_restrict_timeForward hT (timeForward_maps_Ioo hT) measurableSet_Ioo

theorem timeBackwardOpenMeasurePreserving {t₁ T : ℝ} (hT : 0 < T) :
    MeasurePreserving (timeBackward t₁ T)
      (volume.restrict (Set.Ioo t₁ (t₁ + T)))
      (ENNReal.ofReal T • volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  refine ⟨measurable_timeBackward t₁ T, ?_⟩
  exact map_restrict_timeBackward hT (timeBackward_maps_Ioo hT) measurableSet_Ioo

theorem integral_windowForward_scale {t₁ T : ℝ} (hT : 0 < T)
    (g : ℝ × Vec 2 → ℝ) :
    ∫ p, g (windowForward t₁ T p) ∂(volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube)) =
      T⁻¹ * ∫ p, g p ∂(volume.restrict (Set.Ioo t₁ (t₁ + T) ×ˢ unitCube)) := by
  let hmp := windowForwardOpenCubeMeasurePreserving (t₁ := t₁) (T := T) hT
  have hcalc := hmp.integral_comp (windowEquiv t₁ T (ne_of_gt hT)).measurableEmbedding g
  have hc : (ENNReal.ofReal T⁻¹).toReal = T⁻¹ :=
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hT))
  calc
    ∫ p, g (windowForward t₁ T p) ∂(volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube)) =
        ∫ p, g p ∂(ENNReal.ofReal T⁻¹ •
          volume.restrict (Set.Ioo t₁ (t₁ + T) ×ˢ unitCube)) := by
            simpa [hmp] using hcalc
    _ = T⁻¹ * ∫ p, g p ∂(volume.restrict (Set.Ioo t₁ (t₁ + T) ×ˢ unitCube)) := by
      rw [integral_smul_measure, hc]
      simp only [smul_eq_mul]

/-- Pull a window test function back to the unit interval. -/
def testToUnit (t₁ T : ℝ) (φ : ℝ → Vec 2 → ℝ) : ℝ → Vec 2 → ℝ :=
  fun s x => φ (AVRegularity.Wellposed.timeForward t₁ T s) x

/-- Push a unit-interval test function forward to a physical window. -/
def testToWindow (t₁ T : ℝ) (ψ : ℝ → Vec 2 → ℝ) : ℝ → Vec 2 → ℝ :=
  fun t x => ψ (AVRegularity.Wellposed.timeBackward t₁ T t) x

theorem testToUnit_isTestFunction {t₁ T : ℝ} (hT : 0 < T) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsWindowTestFunction (t₁ + T) φ) : IsTestFunction (testToUnit t₁ T φ) := by
  refine ⟨?_, ?_, ?_⟩
  · change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ (timeForward t₁ T p.1) p.2)
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (windowForward t₁ T) := by fun_prop [windowForward]
    exact hφ.1.comp hmap
  · intro s
    exact hφ.2.1 (timeForward t₁ T s)
  · intro s hs x
    apply hφ.2.2 (timeForward t₁ T s)
    have hm : T ≤ T * s := by
      simpa only [mul_one] using (mul_le_mul_iff_of_pos_left hT).2 hs
    have hend : t₁ + T ≤ t₁ + T * s := by simpa [add_comm] using add_le_add_left hm t₁
    simpa [timeForward] using hend

theorem testToWindow_isWindowTestFunction {t₁ T : ℝ} (hT : 0 < T) {ψ : ℝ → Vec 2 → ℝ}
    (hψ : IsTestFunction ψ) : IsWindowTestFunction (t₁ + T) (testToWindow t₁ T ψ) := by
  refine ⟨?_, ?_, ?_⟩
  · change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ (timeBackward t₁ T p.1) p.2)
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (windowBackward t₁ T) := by fun_prop [windowBackward]
    exact hψ.1.comp hmap
  · intro t
    exact hψ.2.1 (timeBackward t₁ T t)
  · intro t ht x
    apply hψ.2.2 (timeBackward t₁ T t)
    have hs : 1 ≤ timeBackward t₁ T t := by
      apply (le_div_iff₀ hT).2
      linarith
    exact hs

theorem deriv_testToUnit {t₁ T s : ℝ} (φ : ℝ → Vec 2 → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2)) (x : Vec 2) :
    deriv (fun u => testToUnit t₁ T φ u x) s =
      T * deriv (fun u => φ u x) (timeForward t₁ T s) := by
  let g : ℝ → ℝ := fun u => φ u x
  have hgc : ContDiff ℝ (⊤ : ℕ∞) g := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => φ u x)
    have hcomp := hφ.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (u, x)))
    change ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => φ u x) at hcomp
    exact hcomp
  have hg : DifferentiableAt ℝ g (timeForward t₁ T s) :=
    hgc.differentiable (by simp) (timeForward t₁ T s)
  have hinner : HasDerivAt (timeForward t₁ T) T s := by
    change HasDerivAt (fun u : ℝ => t₁ + T * u) T s
    exact (hasDerivAt_const_mul T).const_add t₁
  have hcomp := HasDerivAt.comp (hh₂ := hg.hasDerivAt) (hh := hinner)
  have hderiv := hcomp.deriv
  simpa [testToUnit, g, Function.comp_def, mul_comm] using hderiv

theorem deriv_testToWindow {t₁ T t : ℝ} (ψ : ℝ → Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2)) (x : Vec 2) :
    deriv (fun u => testToWindow t₁ T ψ u x) t =
      T⁻¹ * deriv (fun u => ψ u x) (timeBackward t₁ T t) := by
  let g : ℝ → ℝ := fun u => ψ u x
  have hgc : ContDiff ℝ (⊤ : ℕ∞) g := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => ψ u x)
    have hcomp := hψ.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (u, x)))
    change ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => ψ u x) at hcomp
    exact hcomp
  have hg : DifferentiableAt ℝ g (timeBackward t₁ T t) :=
    hgc.differentiable (by simp) (timeBackward t₁ T t)
  have hinner : HasDerivAt (timeBackward t₁ T) T⁻¹ t := by
    change HasDerivAt (fun u : ℝ => (u - t₁) / T) T⁻¹ t
    convert ((hasDerivAt_id t).sub_const t₁).div_const T using 1 <;> simp [one_div]
  have hcomp := HasDerivAt.comp (hh₂ := hg.hasDerivAt) (hh := hinner)
  have hderiv := hcomp.deriv
  calc
    deriv (fun u => testToWindow t₁ T ψ u x) t =
        deriv (fun u => ψ u x) (timeBackward t₁ T t) * T⁻¹ := by
          simpa [testToWindow, g, Function.comp_def] using hderiv
    _ = T⁻¹ * deriv (fun u => ψ u x) (timeBackward t₁ T t) := by ring

end AVRegularity.Wellposed
end

section
open MeasureTheory Filter Topology Homogenization AVenhance
namespace AVRegularity.Wellposed

def rescaledDrift (b : ℝ → Vec 2 → Vec 2) (t₁ T : ℝ) : ℝ → Vec 2 → Vec 2 :=
  fun s x => T • b (timeForward t₁ T s) x

def stateToUnit (t₁ T : ℝ) (θ : ℝ → Vec 2 → ℝ) : ℝ → Vec 2 → ℝ :=
  fun s x => θ (timeForward t₁ T s) x

def gradientToUnit (t₁ T : ℝ) (Dθ : ℝ → Vec 2 → Vec 2) : ℝ → Vec 2 → Vec 2 :=
  fun s x => Dθ (timeForward t₁ T s) x

def stateToWindow (t₁ T : ℝ) (η : ℝ → Vec 2 → ℝ) : ℝ → Vec 2 → ℝ :=
  fun t x => η (timeBackward t₁ T t) x

def gradientToWindow (t₁ T : ℝ) (Dη : ℝ → Vec 2 → Vec 2) : ℝ → Vec 2 → Vec 2 :=
  fun t x => Dη (timeBackward t₁ T t) x

private theorem vecDot_smul_left (c : ℝ) (v w : Vec 2) :
    vecDot (c • v) w = c * vecDot v w := by
  change (∑ i : Fin 2, (c * v i) * w i) = c * ∑ i : Fin 2, v i * w i
  calc
    (∑ i : Fin 2, (c * v i) * w i) = ∑ i : Fin 2, c * (v i * w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = c * ∑ i : Fin 2, v i * w i := (Finset.mul_sum Finset.univ _ c).symm

private theorem timeBackward_timeForward {t₁ T s : ℝ} (hT : 0 < T) :
    timeBackward t₁ T (timeForward t₁ T s) = s := by
  dsimp [timeBackward, timeForward]
  field_simp [ne_of_gt hT]
  ring

private theorem timeForward_timeBackward {t₁ T t : ℝ} (hT : 0 < T) :
    timeForward t₁ T (timeBackward t₁ T t) = t := by
  dsimp [timeBackward, timeForward]
  field_simp [ne_of_gt hT]
  ring

theorem timeForward_mem_Icc {t₁ T s : ℝ} (hT : 0 < T)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : timeForward t₁ T s ∈ Set.Icc t₁ (t₁ + T) := by
  have hs' : s ∈ timeForward t₁ T ⁻¹' Set.Icc t₁ (t₁ + T) := by
    rw [timeForward_maps_interval hT]
    exact hs
  simpa [Set.mem_preimage] using hs'

theorem timeBackward_mem_Icc {t₁ T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Set.Icc t₁ (t₁ + T)) : timeBackward t₁ T t ∈ Set.Icc (0 : ℝ) 1 := by
  have ht' : t ∈ timeBackward t₁ T ⁻¹' Set.Icc (0 : ℝ) 1 := by
    rw [timeBackward_maps_interval hT]
    exact ht
  simpa [Set.mem_preimage] using ht'

private theorem unitWindow_memLp_from_window {t₁ T : ℝ} (hT : 0 < T)
    {g : ℝ × Vec 2 → ℝ} (hg : MemLp g 2
      (volume.restrict (Set.Ioo t₁ (t₁ + T) ×ˢ unitCube))) :
    MemLp (g ∘ windowForward t₁ T) 2
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube)) := by
  have hc : ENNReal.ofReal T⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  exact (hg.smul_measure hc).comp_measurePreserving (windowForwardOpenCubeMeasurePreserving hT)

private theorem window_memLp_from_unit {t₁ T : ℝ} (hT : 0 < T)
    {g : ℝ × Vec 2 → ℝ} (hg : MemLp g 2
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube))) :
    MemLp (g ∘ windowBackward t₁ T) 2
      (volume.restrict (Set.Ioo t₁ (t₁ + T) ×ˢ unitCube)) := by
  have hc : ENNReal.ofReal T ≠ ⊤ := ENNReal.ofReal_ne_top
  exact (hg.smul_measure hc).comp_measurePreserving (windowBackwardOpenCubeMeasurePreserving hT)

theorem isWeakSolutionOn_to_isWeakSolution {b : ℝ → Vec 2 → Vec 2}
    {κ t₁ T : ℝ} (hT : 0 < T) {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hθ : IsWeakSolutionOn b κ t₁ (t₁ + T) f θ) :
    IsWeakSolution (rescaledDrift b t₁ T) (T * κ) f (stateToUnit t₁ T θ) := by
  rcases hθ with ⟨Dθ, hslice, hbound, hstateLP, hgradLP, hH1, hdrift, hcont, hweak⟩
  refine ⟨gradientToUnit t₁ T Dθ, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact hslice _ (timeForward_mem_Icc (t₁ := t₁) (T := T) (s := s) hT hs)
  · obtain ⟨C, hC⟩ := hbound
    exact ⟨C, fun s hs => hC _
      (timeForward_mem_Icc (t₁ := t₁) (T := T) (s := s) hT hs)⟩
  · change MemLp (fun p : ℝ × Vec 2 => θ (timeForward t₁ T p.1) p.2) 2
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube))
    exact unitWindow_memLp_from_window hT hstateLP
  · intro i
    change MemLp (fun p : ℝ × Vec 2 => Dθ (timeForward t₁ T p.1) p.2 i) 2
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube))
    exact unitWindow_memLp_from_window hT (hgradLP i)
  · have hscaled : ∀ᵐ t ∂(ENNReal.ofReal T⁻¹ •
        volume.restrict (Set.Ioo t₁ (t₁ + T))),
        IsPeriodicH1With (θ t) (Dθ t) := Measure.ae_smul_measure hH1 (ENNReal.ofReal T⁻¹)
    have hAE := (timeForwardOpenMeasurePreserving (t₁ := t₁) (T := T) hT).quasiMeasurePreserving.ae hscaled
    filter_upwards [hAE] with s hs
    exact hs
  · have hc : ENNReal.ofReal T⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
    have hscaled := hdrift.smul_measure hc
    have hcomp : Integrable
        ((fun p : ℝ × Vec 2 => vecDot (b p.1 p.2) (Dθ p.1 p.2)) ∘ windowForward t₁ T)
        (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube)) := by
      exact ((windowForwardOpenCubeMeasurePreserving (t₁ := t₁) (T := T) hT).integrable_comp
        hscaled.aestronglyMeasurable).mpr hscaled
    have hmul := hcomp.const_mul T
    have hfun :
        (fun p : ℝ × Vec 2 =>
          vecDot (rescaledDrift b t₁ T p.1 p.2) (gradientToUnit t₁ T Dθ p.1 p.2)) =
        (fun p => T * (fun q : ℝ × Vec 2 => vecDot (b q.1 q.2) (Dθ q.1 q.2))
          (windowForward t₁ T p)) := by
      funext p
      rcases p with ⟨s, x⟩
      change vecDot (T • b (timeForward t₁ T s) x) (Dθ (timeForward t₁ T s) x) =
        T * vecDot (b (timeForward t₁ T s) x) (Dθ (timeForward t₁ T s) x)
      exact vecDot_smul_left T _ _
    rw [hfun]
    exact hmul
  · intro ψ hψ hper
    have hcont' := hcont ψ hψ hper
    have hAcont : ContinuousOn (timeForward t₁ T) (Set.Icc (0 : ℝ) 1) := by
      change ContinuousOn (fun s => t₁ + T * s) (Set.Icc (0 : ℝ) 1)
      exact (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
    have hmaps : Set.MapsTo (timeForward t₁ T) (Set.Icc (0 : ℝ) 1)
        (Set.Icc t₁ (t₁ + T)) := fun s hs =>
          timeForward_mem_Icc (t₁ := t₁) (T := T) (s := s) hT hs
    change ContinuousOn
      ((fun t => ∫ x in unitCube, θ t x * ψ x) ∘ timeForward t₁ T)
      (Set.Icc (0 : ℝ) 1)
    simpa only [Function.comp_apply] using hcont'.comp hAcont hmaps
  · intro ψ hψ
    have htest : IsWindowTestFunction (t₁ + T) (testToWindow t₁ T ψ) :=
      testToWindow_isWindowTestFunction hT hψ
    have hwindow := hweak (testToWindow t₁ T ψ) htest
    let g : ℝ × Vec 2 → ℝ := fun p =>
      (-(θ p.1 p.2) * deriv (fun u => testToWindow t₁ T ψ u p.2) p.1
        + vecDot (b p.1 p.2) (Dθ p.1 p.2) * testToWindow t₁ T ψ p.1 p.2
        + κ * vecDot (Dθ p.1 p.2)
            (spaceGrad (testToWindow t₁ T ψ p.1) p.2))
    have hpoint : ∀ p : ℝ × Vec 2,
        (-(stateToUnit t₁ T θ p.1 p.2) * deriv (fun u => ψ u p.2) p.1
          + vecDot (rescaledDrift b t₁ T p.1 p.2)
              (gradientToUnit t₁ T Dθ p.1 p.2) * ψ p.1 p.2
          + (T * κ) * vecDot (gradientToUnit t₁ T Dθ p.1 p.2)
              (spaceGrad (ψ p.1) p.2)) = T * g (windowForward t₁ T p) := by
      intro p
      rcases p with ⟨s, x⟩
      have htime := timeBackward_timeForward hT (t₁ := t₁) (T := T) (s := s)
      have hderiv := deriv_testToWindow (t₁ := t₁) (T := T) (t := timeForward t₁ T s)
        ψ hψ.1 x
      rw [htime] at hderiv
      have hsection : testToWindow t₁ T ψ (timeForward t₁ T s) = ψ s := by
        funext y
        simp [testToWindow, htime]
      have hsection' : testToWindow t₁ T ψ (t₁ + T * s) = ψ s := by
        simpa [timeForward] using hsection
      have hderiv' : deriv (fun u => testToWindow t₁ T ψ u x) (t₁ + T * s) =
          T⁻¹ * deriv (fun u => ψ u x) s := by
        simpa [timeForward] using hderiv
      simp only [stateToUnit, gradientToUnit, rescaledDrift, windowForward, timeForward]
      simp only [g]
      rw [hsection']
      rw [hderiv']
      simp_rw [vecDot_smul_left]
      field_simp [ne_of_gt hT]
    calc
      ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ unitCube,
          (-(stateToUnit t₁ T θ p.1 p.2) * deriv (fun u => ψ u p.2) p.1
            + vecDot (rescaledDrift b t₁ T p.1 p.2)
                (gradientToUnit t₁ T Dθ p.1 p.2) * ψ p.1 p.2
            + (T * κ) * vecDot (gradientToUnit t₁ T Dθ p.1 p.2)
                (spaceGrad (ψ p.1) p.2)) =
          T * ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ unitCube, g (windowForward t₁ T p) := by
            simp_rw [hpoint]
            rw [integral_const_mul]
      _ = T * (T⁻¹ * ∫ p in Set.Ioo t₁ (t₁ + T) ×ˢ unitCube, g p) := by
            rw [integral_windowForward_scale hT g]
      _ = ∫ p in Set.Ioo t₁ (t₁ + T) ×ˢ unitCube, g p := by
            field_simp [ne_of_gt hT]
      _ = ∫ p in Set.Ioo t₁ (t₁ + T) ×ˢ unitCube,
          (-(θ p.1 p.2) * deriv (fun u => testToWindow t₁ T ψ u p.2) p.1
            + vecDot (b p.1 p.2) (Dθ p.1 p.2) * testToWindow t₁ T ψ p.1 p.2
            + κ * vecDot (Dθ p.1 p.2)
                (spaceGrad (testToWindow t₁ T ψ p.1) p.2)) := by rfl
      _ = ∫ x in unitCube, f x * testToWindow t₁ T ψ t₁ x := hwindow
      _ = ∫ x in unitCube, f x * ψ 0 x := by
            congr 1
            funext x
            simp [testToWindow, timeBackward]

theorem isWeakSolution_to_isWeakSolutionOn {b : ℝ → Vec 2 → Vec 2}
    {κ t₁ T : ℝ} (hT : 0 < T) {f : Vec 2 → ℝ} {η : ℝ → Vec 2 → ℝ}
    (hη : IsWeakSolution (rescaledDrift b t₁ T) (T * κ) f η) :
    IsWeakSolutionOn b κ t₁ (t₁ + T) f (stateToWindow t₁ T η) := by
  rcases hη with ⟨Dη, hslice, hbound, hstateLP, hgradLP, hH1, hdrift, hcont, hweak⟩
  refine ⟨gradientToWindow t₁ T Dη, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hs := timeBackward_mem_Icc (t₁ := t₁) (T := T) (t := t) hT ht
    exact hslice _ hs
  · obtain ⟨C, hC⟩ := hbound
    exact ⟨C, fun t ht => hC _
      (timeBackward_mem_Icc (t₁ := t₁) (T := T) (t := t) hT ht)⟩
  · change MemLp (fun p : ℝ × Vec 2 => η (timeBackward t₁ T p.1) p.2) 2
      (volume.restrict (Set.Ioo t₁ (t₁ + T) ×ˢ unitCube))
    exact window_memLp_from_unit hT hstateLP
  · intro i
    change MemLp (fun p : ℝ × Vec 2 => Dη (timeBackward t₁ T p.1) p.2 i) 2
      (volume.restrict (Set.Ioo t₁ (t₁ + T) ×ˢ unitCube))
    exact window_memLp_from_unit hT (hgradLP i)
  · have hscaled : ∀ᵐ s ∂(ENNReal.ofReal T • volume.restrict (Set.Ioo (0 : ℝ) 1)),
        IsPeriodicH1With (η s) (Dη s) := Measure.ae_smul_measure hH1 (ENNReal.ofReal T)
    have hmp := timeBackwardOpenMeasurePreserving (t₁ := t₁) (T := T) hT
    exact hmp.quasiMeasurePreserving.ae hscaled
  · have hc : ENNReal.ofReal T ≠ ⊤ := ENNReal.ofReal_ne_top
    have hscaled := hdrift.smul_measure hc
    have hcomp : Integrable
        ((fun p : ℝ × Vec 2 =>
          vecDot (rescaledDrift b t₁ T p.1 p.2) (Dη p.1 p.2)) ∘ windowBackward t₁ T)
        (volume.restrict (Set.Ioo t₁ (t₁ + T) ×ˢ unitCube)) := by
      exact ((windowBackwardOpenCubeMeasurePreserving (t₁ := t₁) (T := T) hT).integrable_comp
        hscaled.aestronglyMeasurable).mpr hscaled
    have hmul := hcomp.const_mul T⁻¹
    have hfun :
        (fun p : ℝ × Vec 2 => vecDot (b p.1 p.2)
          (gradientToWindow t₁ T Dη p.1 p.2)) =
        (fun p => T⁻¹ * (fun q : ℝ × Vec 2 =>
          vecDot (rescaledDrift b t₁ T q.1 q.2) (Dη q.1 q.2))
          (windowBackward t₁ T p)) := by
      funext p
      rcases p with ⟨t, x⟩
      have htime := timeForward_timeBackward (t₁ := t₁) (T := T) (t := t) hT
      change vecDot (b t x) (Dη (timeBackward t₁ T t) x) =
        T⁻¹ * vecDot (T • b (timeForward t₁ T (timeBackward t₁ T t)) x)
          (Dη (timeBackward t₁ T t) x)
      rw [htime, vecDot_smul_left]
      field_simp [ne_of_gt hT]
    rw [hfun]
    exact hmul
  · intro ψ hψ hper
    have hcont' := hcont ψ hψ hper
    have hGcont : ContinuousOn (timeBackward t₁ T) (Set.Icc t₁ (t₁ + T)) := by
      change ContinuousOn (fun t => (t - t₁) / T) (Set.Icc t₁ (t₁ + T))
      fun_prop
    have hmaps : Set.MapsTo (timeBackward t₁ T) (Set.Icc t₁ (t₁ + T))
        (Set.Icc (0 : ℝ) 1) := fun t ht =>
          timeBackward_mem_Icc (t₁ := t₁) (T := T) (t := t) hT ht
    change ContinuousOn
      ((fun s => ∫ x in unitCube, η s x * ψ x) ∘ timeBackward t₁ T)
      (Set.Icc t₁ (t₁ + T))
    simpa only [Function.comp_apply] using hcont'.comp hGcont hmaps
  · intro φ hφ
    have htest : IsTestFunction (testToUnit t₁ T φ) := testToUnit_isTestFunction hT hφ
    have hunit := hweak (testToUnit t₁ T φ) htest
    let g : ℝ × Vec 2 → ℝ := fun p =>
      (-(stateToWindow t₁ T η p.1 p.2) * deriv (fun u => φ u p.2) p.1
        + vecDot (b p.1 p.2) (gradientToWindow t₁ T Dη p.1 p.2) * φ p.1 p.2
        + κ * vecDot (gradientToWindow t₁ T Dη p.1 p.2)
            (spaceGrad (φ p.1) p.2))
    have hpoint : ∀ p : ℝ × Vec 2,
        (-(η p.1 p.2) * deriv (fun u => testToUnit t₁ T φ u p.2) p.1
          + vecDot (rescaledDrift b t₁ T p.1 p.2)
              (Dη p.1 p.2) * testToUnit t₁ T φ p.1 p.2
          + (T * κ) * vecDot (Dη p.1 p.2)
              (spaceGrad (testToUnit t₁ T φ p.1) p.2)) = T * g (windowForward t₁ T p) := by
      intro p
      rcases p with ⟨s, x⟩
      have htime := timeBackward_timeForward (t₁ := t₁) (T := T) (s := s) hT
      have htime' : timeBackward t₁ T (t₁ + T * s) = s := by
        simpa [timeForward] using htime
      have hsection : testToUnit t₁ T φ s = φ (timeForward t₁ T s) := rfl
      have hderiv := deriv_testToUnit (t₁ := t₁) (T := T) (s := s) φ hφ.1 x
      simp only [windowForward]
      simp only [g]
      simp [rescaledDrift, stateToWindow, gradientToWindow, htime']
      rw [hsection]
      rw [hderiv]
      rw [vecDot_smul_left]
      simp only [timeForward]
      ring_nf
    have hunit_int :
        ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ unitCube,
          (-(η p.1 p.2) * deriv (fun u => testToUnit t₁ T φ u p.2) p.1
            + vecDot (rescaledDrift b t₁ T p.1 p.2) (Dη p.1 p.2) *
                testToUnit t₁ T φ p.1 p.2
            + (T * κ) * vecDot (Dη p.1 p.2)
                (spaceGrad (testToUnit t₁ T φ p.1) p.2)) =
          T * ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ unitCube, g (windowForward t₁ T p) := by
      simp_rw [hpoint]
      rw [integral_const_mul]
    calc
      ∫ p in Set.Ioo t₁ (t₁ + T) ×ˢ unitCube,
          (-(stateToWindow t₁ T η p.1 p.2) * deriv (fun u => φ u p.2) p.1
            + vecDot (b p.1 p.2) (gradientToWindow t₁ T Dη p.1 p.2) * φ p.1 p.2
            + κ * vecDot (gradientToWindow t₁ T Dη p.1 p.2)
                (spaceGrad (φ p.1) p.2)) =
          T * ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ unitCube, g (windowForward t₁ T p) := by
            rw [integral_windowForward_scale hT g]
            field_simp [ne_of_gt hT]
            simp [g]
      _ = ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ unitCube,
          (-(η p.1 p.2) * deriv (fun u => testToUnit t₁ T φ u p.2) p.1
            + vecDot (rescaledDrift b t₁ T p.1 p.2) (Dη p.1 p.2) *
                testToUnit t₁ T φ p.1 p.2
            + (T * κ) * vecDot (Dη p.1 p.2)
                (spaceGrad (testToUnit t₁ T φ p.1) p.2)) := hunit_int.symm
      _ = ∫ x in unitCube, f x * testToUnit t₁ T φ 0 x := by
            simpa [AVenhance.timeCube] using hunit
      _ = ∫ x in unitCube, f x * φ t₁ x := by
            congr 1
            funext x
            simp [testToUnit, timeForward]

end AVRegularity.Wellposed
end

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Wellposed

theorem exists_unique_isWeakSolutionOn
    (t₁ t₂ : ℝ) (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc t₁ t₂ ×ˢ Set.univ)))
    (hb_bdd : ∃ C, ∀ t ∈ Set.Icc t₁ t₂, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc t₁ t₂, IsZ2Periodic (b t))
    (κ : ℝ) (hκ : 0 < κ) (h12 : t₁ < t₂)
    (f : Vec 2 → ℝ) (hf : MemL2On unitCube f) :
    ∃ θ, IsWeakSolutionOn b κ t₁ t₂ f θ ∧
      ∀ θ', IsWeakSolutionOn b κ t₁ t₂ f θ' →
        ∀ t ∈ Set.Icc t₁ t₂, θ' t =ᵐ[volume.restrict unitCube] θ t := by
  let T : ℝ := t₂ - t₁
  have hT : 0 < T := sub_pos.mpr h12
  have hEnd : t₁ + T = t₂ := by dsimp [T]; ring
  let B := rescaledDrift b t₁ T
  have hb_meas' : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc t₁ (t₁ + T) ×ˢ Set.univ)) := by
    simpa [hEnd] using hb_meas
  have hB_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => B p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) := by
    have hscaled := hb_meas'.smul_measure (ENNReal.ofReal T⁻¹)
    have hcomp := hscaled.comp_measurePreserving
      (windowForwardMeasurePreserving (t₁ := t₁) (T := T) hT)
    change AEStronglyMeasurable
      (fun p : ℝ × Vec 2 =>
        T • b (windowForward t₁ T p).1 (windowForward t₁ T p).2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
    exact hcomp.const_smul T
  obtain ⟨C, hC⟩ := hb_bdd
  have hC_nonneg : 0 ≤ C := by
    have ht : t₁ ∈ Set.Icc t₁ t₂ := ⟨le_rfl, le_of_lt h12⟩
    have h := hC t₁ ht (0 : Vec 2)
    exact le_trans (norm_nonneg _) h
  have hB_bdd : ∃ C', ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖B s x‖ ≤ C' := by
    refine ⟨T * C, ?_⟩
    intro s hs x
    have htime := timeForward_mem_Icc (t₁ := t₁) (T := T) (s := s) hT hs
    have htime' : timeForward t₁ T s ∈ Set.Icc t₁ t₂ := by simpa [hEnd] using htime
    calc
      ‖B s x‖ = T * ‖b (timeForward t₁ T s) x‖ := by
        simp [B, rescaledDrift, norm_smul, Real.norm_eq_abs, abs_of_pos hT]
      _ ≤ T * C := mul_le_mul_of_nonneg_left (hC _ htime' x) hT.le
  have hB_per : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (B s) := by
    intro s hs
    have htime := timeForward_mem_Icc (t₁ := t₁) (T := T) (s := s) hT hs
    have htime' : timeForward t₁ T s ∈ Set.Icc t₁ t₂ := by simpa [hEnd] using htime
    intro n x
    change T • b (timeForward t₁ T s) (x + latticeShift n) =
      T • b (timeForward t₁ T s) x
    exact congrArg (fun v : Vec 2 => T • v) (hb_per _ htime' n x)
  obtain ⟨η, hη, hη_unique⟩ := AVenhance.weak_wellposed B hB_meas hB_bdd hB_per
    (T * κ) (mul_pos hT hκ) f hf
  let θ := stateToWindow t₁ T η
  have hθ : IsWeakSolutionOn b κ t₁ (t₁ + T) f θ := by
    simpa [θ] using isWeakSolution_to_isWeakSolutionOn (b := b) hT hη
  refine ⟨θ, ?_, ?_⟩
  · simpa [hEnd] using hθ
  · intro θ' hθ' t ht
    have hθ'window : IsWeakSolutionOn b κ t₁ (t₁ + T) f θ' := by
      simpa [hEnd] using hθ'
    have hη' : IsWeakSolution B (T * κ) f (stateToUnit t₁ T θ') :=
      isWeakSolutionOn_to_isWeakSolution (b := b) hT hθ'window
    have hs : timeBackward t₁ T t ∈ Set.Icc (0 : ℝ) 1 :=
      timeBackward_mem_Icc (t₁ := t₁) (T := T) (t := t) hT (by simpa [hEnd] using ht)
    have heq := hη_unique (stateToUnit t₁ T θ') hη' (timeBackward t₁ T t) hs
    have hcomp : timeForward t₁ T (timeBackward t₁ T t) = t := by
      dsimp [timeForward, timeBackward]
      field_simp [ne_of_gt hT]
      ring
    filter_upwards [heq] with x hx
    have hx' : θ' (timeForward t₁ T (timeBackward t₁ T t)) x =
        η (timeBackward t₁ T t) x := by simpa [stateToUnit] using hx
    simpa [θ, stateToWindow, hcomp] using hx'

private theorem continuous_joint_of_holder {α : ℝ} (hα : 0 < α)
    {b : ℝ → Vec 2 → Vec 2}
    (hholder : ∃ C, ∀ t u : ℝ, ∀ x y : Vec 2,
      ‖b t x - b u y‖ ≤ C * (|t - u| + Real.sqrt (vecNormSq (x - y))) ^ α) :
    Continuous (fun p : ℝ × Vec 2 => b p.1 p.2) := by
  obtain ⟨C, hC⟩ := hholder
  have hC_nonneg : 0 ≤ C := by
    have h := hC 0 1 (0 : Vec 2) 0
    have hsqrt : Real.sqrt (vecNormSq (0 : Vec 2)) = 0 := by
      simp [Homogenization.vecNormSq, Homogenization.vecDot]
    have hbound : ‖b 0 0 - b 1 0‖ ≤ C := by
      simpa [hsqrt] using h
    exact le_trans (norm_nonneg _) hbound
  apply continuous_iff_continuousAt.mpr
  intro p
  have hd : ContinuousAt
      (fun q : ℝ × Vec 2 => |q.1 - p.1| + Real.sqrt (vecNormSq (q.2 - p.2))) p := by
    fun_prop [Homogenization.vecNormSq, Homogenization.vecDot]
  have hdp : |p.1 - p.1| + Real.sqrt (vecNormSq (p.2 - p.2)) = 0 := by
    simp [Homogenization.vecNormSq, Homogenization.vecDot]
  have hpow : ContinuousAt
      (fun q : ℝ × Vec 2 =>
        C * (|q.1 - p.1| + Real.sqrt (vecNormSq (q.2 - p.2))) ^ α) p := by
    have hpow' := hd.rpow_const (Or.inr hα.le)
    exact continuousAt_const.mul hpow'
  have hpow_zero :
      C * (|p.1 - p.1| + Real.sqrt (vecNormSq (p.2 - p.2))) ^ α = 0 := by
    have hdist0 : |p.1 - p.1| + Real.sqrt (vecNormSq (p.2 - p.2)) = 0 := by
      simp [Homogenization.vecNormSq, Homogenization.vecDot]
    rw [hdist0]
    simp [hα.ne']
  refine Metric.continuousAt_iff.mpr ?_
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := Metric.continuousAt_iff.mp hpow ε hε
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  have hHolder := hC q.1 p.1 q.2 p.2
  have hle : dist (b q.1 q.2) (b p.1 p.2) ≤
      C * (|q.1 - p.1| + Real.sqrt (vecNormSq (q.2 - p.2))) ^ α := by
    simpa [dist_eq_norm] using hHolder
  have hpow_bound :
      C * (|q.1 - p.1| + Real.sqrt (vecNormSq (q.2 - p.2))) ^ α < ε := by
    have hd' := hδbound hq
    have hnonneg : 0 ≤ C * (|q.1 - p.1| + Real.sqrt (vecNormSq (q.2 - p.2))) ^ α := by
      exact mul_nonneg hC_nonneg
        (Real.rpow_nonneg (add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) α)
    rw [hpow_zero] at hd'
    have hd0 : |C * (|q.1 - p.1| + Real.sqrt (vecNormSq (q.2 - p.2))) ^ α| < ε := by
      simpa [Real.dist_eq] using hd'
    rw [abs_of_nonneg hnonneg] at hd0
    exact hd0
  exact lt_of_le_of_lt hle hpow_bound

theorem exists_unique_isWeakSolutionOn_of_isHolderDivFreeVelocity
    (α : ℝ) (hα : 0 < α) (b : ℝ → Vec 2 → Vec 2)
    (hvel : IsHolderDivFreeVelocity α b)
    (κ : ℝ) (hκ : 0 < κ) (t₁ t₂ : ℝ) (h12 : t₁ < t₂)
    (f : Vec 2 → ℝ) (hf : MemL2On unitCube f) :
    ∃ θ, IsWeakSolutionOn b κ t₁ t₂ f θ ∧
      ∀ θ', IsWeakSolutionOn b κ t₁ t₂ f θ' →
        ∀ t ∈ Set.Icc t₁ t₂, θ' t =ᵐ[volume.restrict unitCube] θ t := by
  rcases hvel with ⟨hper, htimeper, hbdd, hholder, hdiv⟩
  have hcont := continuous_joint_of_holder hα hholder
  have hmeas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc t₁ t₂ ×ˢ Set.univ)) := hcont.aestronglyMeasurable
  exact exists_unique_isWeakSolutionOn t₁ t₂ b hmeas
    ⟨hbdd.choose, fun t ht x => hbdd.choose_spec t x⟩
    (fun t ht => hper t) κ hκ h12 f hf

end AVRegularity.Wellposed
end
