-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.EuclidBall
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section
noncomputable section

section
open Filter Homogenization MeasureTheory Set
open scoped Topology
namespace AVRegularity.External.Campanato

/-- The backward parabolic cylinder with spatial Euclidean radius `r`. -/
def cylinder (z : ℝ × Vec 2) (r : ℝ) : Set (ℝ × Vec 2) :=
  Set.Ioc (z.1 - r ^ 2) z.1 ×ˢ euclidBall z.2 r

/-- The unit backward cylinder based at `(t₀,x₀)`. -/
def window (z : ℝ × Vec 2) : Set (ℝ × Vec 2) := cylinder z 1

/-- The interior cylinder used in the Campanato conclusion. -/
def halfWindow (z : ℝ × Vec 2) : Set (ℝ × Vec 2) := cylinder z (1 / 2 : ℝ)

private def innerBox (c : Vec 2) (r : ℝ) : Set (Vec 2) :=
  Set.pi Set.univ (fun i => Set.Ioo (c i - r / 2) (c i + r / 2))

private def outerBox (c : Vec 2) (r : ℝ) : Set (Vec 2) :=
  Set.pi Set.univ (fun i => Set.Ioo (c i - r) (c i + r))

private theorem innerBox_subset_euclidBall (c : Vec 2) {r : ℝ} (hr : 0 < r) :
    innerBox c r ⊆ euclidBall c r := by
  intro y hy
  change vecNormSq (y - c) < r ^ 2
  have hi : ∀ i : Fin 2, |y i - c i| < r / 2 := by
    intro i
    have h := hy i (Set.mem_univ i)
    rw [Set.mem_Ioo] at h
    rw [abs_lt]
    constructor <;> linarith
  have hsq : ∀ i : Fin 2, (y i - c i) ^ 2 < (r / 2) ^ 2 := by
    intro i
    have hi' := hi i
    have hprod : 0 < (r / 2 - |y i - c i|) * (r / 2 + |y i - c i|) := by
      apply mul_pos
      · linarith
      · positivity
    nlinarith [sq_abs (y i - c i), hprod]
  have hsum : ∑ i : Fin 2, (y i - c i) ^ 2 < ∑ i : Fin 2, (r / 2) ^ 2 :=
    Finset.sum_lt_sum (fun i hi' => (hsq i).le) ⟨0, Finset.mem_univ 0, hsq 0⟩
  have hnorm : vecNormSq (y - c) = ∑ i : Fin 2, (y i - c i) ^ 2 := by
    simp [vecNormSq, vecDot, pow_two]
  rw [hnorm]
  have hcard : (∑ i : Fin 2, (r / 2) ^ 2) = 2 * (r / 2) ^ 2 := by simp
  rw [hcard] at hsum
  nlinarith

private theorem euclidBall_subset_outerBox (c : Vec 2) {r : ℝ} (hr : 0 < r) :
    euclidBall c r ⊆ outerBox c r := by
  intro y hy i hi
  have hnorm : vecNormSq (y - c) < r ^ 2 := hy
  have hcoord := sq_apply_le_vecNormSq (y - c) i
  have habs : |y i - c i| < r :=
    abs_lt_of_sq_lt_sq (lt_of_le_of_lt hcoord hnorm) hr.le
  rcases abs_lt.mp habs with ⟨hlo, hhi⟩
  rw [Set.mem_Ioo]
  constructor <;> linarith

private theorem volume_innerBox (c : Vec 2) {r : ℝ} (hr : 0 < r) :
    volume (innerBox c r) = ENNReal.ofReal (r ^ 2) := by
  rw [innerBox, Real.volume_pi_Ioo]
  simp_rw [show ∀ i : Fin 2, c i + r / 2 - (c i - r / 2) = r by intro i; ring]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hr.le 2]

private theorem volume_outerBox (c : Vec 2) {r : ℝ} (hr : 0 < r) :
    volume (outerBox c r) = ENNReal.ofReal ((2 * r) ^ 2) := by
  rw [outerBox, Real.volume_pi_Ioo]
  simp_rw [show ∀ i : Fin 2, c i + r - (c i - r) = 2 * r by intro i; ring]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (mul_nonneg zero_le_two hr.le) 2]

private theorem volume_timeWindow {t : ℝ} {r : ℝ} (_hr : 0 < r) :
    volume (Set.Ioc (t - r ^ 2) t) = ENNReal.ofReal (r ^ 2) := by
  rw [Real.volume_Ioc]
  congr 1
  ring

private theorem volume_product_set (s : Set ℝ) (u : Set (Vec 2)) :
    volume (s ×ˢ u : Set (ℝ × Vec 2)) = volume s * volume u := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod_prod s u

private theorem volume_innerCylinder (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    volume (Set.Ioc (z.1 - r ^ 2) z.1 ×ˢ innerBox z.2 r) = ENNReal.ofReal (r ^ 4) := by
  rw [volume_product_set, volume_timeWindow hr, volume_innerBox z.2 hr]
  rw [← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  ring

private theorem volume_outerCylinder (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    volume (Set.Ioc (z.1 - r ^ 2) z.1 ×ˢ outerBox z.2 r) = ENNReal.ofReal (4 * r ^ 4) := by
  rw [volume_product_set, volume_timeWindow hr, volume_outerBox z.2 hr]
  rw [← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  ring

/-- A metric adapted to parabolic scaling, using the spatial sup norm. -/
def parabolicDist (z w : ℝ × Vec 2) : ℝ :=
  max (Real.sqrt |z.1 - w.1|) (dist z.2 w.2)

def parabolicBall (z : ℝ × Vec 2) (r : ℝ) : Set (ℝ × Vec 2) :=
  {w | parabolicDist z w < r}

/-- Closed balls for the parabolic distance, with no global metric instance required. -/
def parabolicClosedBall (z : ℝ × Vec 2) (r : ℝ) : Set (ℝ × Vec 2) :=
  {w | parabolicDist z w ≤ r}

private theorem sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hleft := Real.sq_sqrt (add_nonneg ha hb)
  have h₁ := Real.sq_sqrt ha
  have h₂ := Real.sq_sqrt hb
  have hcross : 0 ≤ Real.sqrt a * Real.sqrt b := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  nlinarith [hleft, h₁, h₂, hcross]

theorem parabolicDist_self (z : ℝ × Vec 2) : parabolicDist z z = 0 := by
  simp [parabolicDist]

theorem parabolicDist_comm (z w : ℝ × Vec 2) : parabolicDist z w = parabolicDist w z := by
  simp [parabolicDist, abs_sub_comm, dist_comm]

theorem parabolicDist_triangle (z w v : ℝ × Vec 2) :
    parabolicDist z v ≤ parabolicDist z w + parabolicDist w v := by
  have habs : |z.1 - v.1| ≤ |z.1 - w.1| + |w.1 - v.1| := by
    calc
      |z.1 - v.1| = |(z.1 - w.1) + (w.1 - v.1)| := by congr 1; ring
      _ ≤ |z.1 - w.1| + |w.1 - v.1| := abs_add_le _ _
  have htime : Real.sqrt |z.1 - v.1| ≤
      Real.sqrt |z.1 - w.1| + Real.sqrt |w.1 - v.1| := by
    calc
      Real.sqrt |z.1 - v.1| ≤ Real.sqrt (|z.1 - w.1| + |w.1 - v.1|) :=
        Real.sqrt_le_sqrt habs
      _ ≤ _ := sqrt_add_le _ _ (abs_nonneg _) (abs_nonneg _)
  unfold parabolicDist
  apply max_le
  · calc
      Real.sqrt |z.1 - v.1| ≤ Real.sqrt |z.1 - w.1| + Real.sqrt |w.1 - v.1| := htime
      _ ≤ max (Real.sqrt |z.1 - w.1|) (dist z.2 w.2) +
          max (Real.sqrt |w.1 - v.1|) (dist w.2 v.2) := by gcongr <;> apply le_max_left
  · calc
      dist z.2 v.2 ≤ dist z.2 w.2 + dist w.2 v.2 := dist_triangle _ _ _
      _ ≤ max (Real.sqrt |z.1 - w.1|) (dist z.2 w.2) +
          max (Real.sqrt |w.1 - v.1|) (dist w.2 v.2) := by gcongr <;> apply le_max_right

theorem parabolicDist_isOpen_iff (s : Set (ℝ × Vec 2)) :
    IsOpen s ↔ ∀ z ∈ s, ∃ r > 0, ∀ w, parabolicDist z w < r → w ∈ s := by
  rw [Metric.isOpen_iff]
  constructor
  · intro hs z hz
    obtain ⟨δ, hδ, hball⟩ := hs z hz
    refine ⟨min δ (Real.sqrt δ), lt_min hδ (Real.sqrt_pos.2 hδ), ?_⟩
    intro w hw
    have hparts := (max_lt_iff.mp hw)
    have htime : |z.1 - w.1| < (min δ (Real.sqrt δ)) ^ 2 :=
      (Real.sqrt_lt' (lt_min hδ (Real.sqrt_pos.2 hδ))).1 hparts.1
    have hspace : dist z.2 w.2 < min δ (Real.sqrt δ) := hparts.2
    have hminSq : (min δ (Real.sqrt δ)) ^ 2 ≤ δ := by
      calc
        (min δ (Real.sqrt δ)) ^ 2 ≤ (Real.sqrt δ) ^ 2 := by
          gcongr
          exact min_le_right _ _
        _ = δ := Real.sq_sqrt hδ.le
    have hstd : dist z w < δ := by
      rw [Prod.dist_eq, Real.dist_eq, max_lt_iff]
      exact ⟨lt_of_lt_of_le htime hminSq, lt_of_lt_of_le hspace (min_le_left _ _)⟩
    exact hball (Metric.mem_ball.mpr (by simpa [dist_comm] using hstd))
  · intro hs z hz
    obtain ⟨r, hr, hball⟩ := hs z hz
    let δ := min (r ^ 2) r
    have hδ : 0 < δ := lt_min (sq_pos_of_pos hr) hr
    refine ⟨δ, hδ, ?_⟩
    intro w hw
    have hparts : |w.1 - z.1| < δ ∧ dist w.2 z.2 < δ := by
      simpa [Prod.dist_eq, Real.dist_eq, max_lt_iff] using hw
    have htimeAbs : |z.1 - w.1| < r ^ 2 := by
      calc
        |z.1 - w.1| = |w.1 - z.1| := by rw [abs_sub_comm]
        _ < δ := hparts.1
        _ ≤ r ^ 2 := min_le_left _ _
    have htime : Real.sqrt |z.1 - w.1| < r := by
      exact (Real.sqrt_lt' hr).2 htimeAbs
    have hspace : dist z.2 w.2 < r := by
      simpa [dist_comm] using lt_of_lt_of_le hparts.2 (min_le_right _ _)
    exact hball w (by simpa [parabolicDist] using max_lt_iff.mpr ⟨htime, hspace⟩)

local instance instParabolicPseudoMetricSpace : PseudoMetricSpace (ℝ × Vec 2) :=
  PseudoMetricSpace.ofDistTopology parabolicDist parabolicDist_self parabolicDist_comm
    parabolicDist_triangle parabolicDist_isOpen_iff

@[simp]
theorem metric_ball_eq_parabolicBall (z : ℝ × Vec 2) (r : ℝ) :
    Metric.ball z r = parabolicBall z r := by
  ext w
  change parabolicDist w z < r ↔ parabolicDist z w < r
  rw [parabolicDist_comm]

theorem parabolic_closedBall_eq_rect (z : ℝ × Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    parabolicClosedBall z r =
      Set.Icc (z.1 - r ^ 2) (z.1 + r ^ 2) ×ˢ Metric.closedBall z.2 r := by
  ext w
  change parabolicDist z w ≤ r ↔
    (w.1 ∈ Set.Icc (z.1 - r ^ 2) (z.1 + r ^ 2) ∧ dist w.2 z.2 ≤ r)
  constructor
  · intro hw
    unfold parabolicDist at hw
    rcases max_le_iff.mp hw with ⟨ht, hx⟩
    rcases Real.sqrt_le_iff.mp ht with ⟨_, habs⟩
    have htime : w.1 ∈ Set.Icc (z.1 - r ^ 2) (z.1 + r ^ 2) := by
      rw [Set.mem_Icc, abs_le] at *
      constructor <;> linarith
    exact ⟨htime, by simpa [dist_comm] using hx⟩
  · rintro ⟨ht, hx⟩
    have habs : |z.1 - w.1| ≤ r ^ 2 := by
      rw [Set.mem_Icc] at ht
      rw [abs_le]
      constructor <;> linarith
    have htime : Real.sqrt |z.1 - w.1| ≤ r :=
      Real.sqrt_le_iff.mpr ⟨hr, habs⟩
    have hdist : dist z.2 w.2 ≤ r := by simpa [dist_comm] using hx
    have hpara : parabolicDist z w ≤ r := max_le htime hdist
    exact hpara

@[simp]
theorem metric_closedBall_eq_parabolicClosedBall (z : ℝ × Vec 2) (r : ℝ) :
    Metric.closedBall z r = parabolicClosedBall z r := by
  ext w
  change parabolicDist w z ≤ r ↔ parabolicDist z w ≤ r
  rw [parabolicDist_comm]

theorem parabolic_closedBall_volume (z : ℝ × Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    volume (parabolicClosedBall z r) = ENNReal.ofReal (8 * r ^ 4) := by
  rw [parabolic_closedBall_eq_rect z hr, volume_product_set, Real.volume_Icc,
    Real.volume_pi_closedBall z.2 hr]
  rw [← ENNReal.ofReal_mul (by nlinarith [sq_nonneg r])]
  simp only [Fintype.card_fin]
  congr 1
  ring

private theorem innerCylinder_subset_cylinder (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    Set.Ioc (z.1 - r ^ 2) z.1 ×ˢ innerBox z.2 r ⊆ cylinder z r := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  exact ⟨ht, innerBox_subset_euclidBall z.2 hr hx⟩

private theorem cylinder_subset_outerCylinder (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    cylinder z r ⊆ Set.Ioc (z.1 - r ^ 2) z.1 ×ˢ outerBox z.2 r := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  exact ⟨ht, euclidBall_subset_outerBox z.2 hr hx⟩

theorem cylinder_volume_lower (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (r ^ 4) ≤ volume (cylinder z r) := by
  calc
    ENNReal.ofReal (r ^ 4) = volume (Set.Ioc (z.1 - r ^ 2) z.1 ×ˢ innerBox z.2 r) :=
      (volume_innerCylinder z hr).symm
    _ ≤ volume (cylinder z r) := measure_mono (innerCylinder_subset_cylinder z hr)

theorem cylinder_volume_upper (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    volume (cylinder z r) ≤ ENNReal.ofReal (4 * r ^ 4) := by
  calc
    volume (cylinder z r) ≤
        volume (Set.Ioc (z.1 - r ^ 2) z.1 ×ˢ outerBox z.2 r) :=
      measure_mono (cylinder_subset_outerCylinder z hr)
    _ = ENNReal.ofReal (4 * r ^ 4) := volume_outerCylinder z hr

local instance instParabolicDoubling :
    IsUnifLocDoublingMeasure (volume : Measure (ℝ × Vec 2)) where
  exists_measure_closedBall_le_mul'' := by
    refine ⟨16, ?_⟩
    filter_upwards [eventually_mem_nhdsWithin] with r hr z
    have hrpos : 0 < r := hr
    rw [metric_closedBall_eq_parabolicClosedBall, parabolic_closedBall_volume z (by positivity : 0 ≤ 2 * r),
      metric_closedBall_eq_parabolicClosedBall,
      parabolic_closedBall_volume z (le_of_lt hr)]
    have hscale : 8 * (2 * r) ^ 4 = 16 * (8 * r ^ 4) := by ring
    rw [hscale]
    rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (16 : ℝ))]
    norm_num

theorem cylinder_subset_window (z₀ z : ℝ × Vec 2) {r : ℝ}
    (hz : z ∈ halfWindow z₀) (hr₀ : 0 < r) (hr₁ : r < 1 / 4) :
    cylinder z r ⊆ window z₀ := by
  intro y hy
  rcases hy with ⟨hyt, hyx⟩
  rcases hz with ⟨hzt, hzx⟩
  change y.1 ∈ Set.Ioc (z₀.1 - 1 ^ 2) z₀.1 ∧
    vecNormSq (y.2 - z₀.2) < 1 ^ 2
  refine ⟨?_, ?_⟩
  · change z₀.1 - 1 ^ 2 < y.1 ∧ y.1 ≤ z₀.1
    have hrSq : r ^ 2 < (1 / 4 : ℝ) ^ 2 := by nlinarith
    exact ⟨by nlinarith [hyt.1, hzt.1], hyt.2.trans hzt.2⟩
  · change vecNormSq (z.2 - z₀.2) < (1 / 2 : ℝ) ^ 2 at hzx
    have hdecomp : y.2 - z₀.2 = (y.2 - z.2) + (z.2 - z₀.2) := by
      ext i
      simp
    rw [hdecomp]
    have hsum := vecNormSq_add_le (y.2 - z.2) (z.2 - z₀.2)
    have hsum' : vecNormSq (y.2 - z₀.2) ≤
        2 * (vecNormSq (y.2 - z.2) + vecNormSq (z.2 - z₀.2)) := by
      rw [hdecomp]
      exact hsum
    have hyx' : vecNormSq (y.2 - z.2) < r ^ 2 := by simpa [euclidBall] using hyx
    have hzx' : vecNormSq (z.2 - z₀.2) < (1 / 2 : ℝ) ^ 2 := by
      simpa [euclidBall] using hzx
    have hrSq : r ^ 2 < (1 / 4 : ℝ) ^ 2 := by nlinarith
    have hnorm : vecNormSq (y.2 - z₀.2) < 1 := by
      nlinarith [hsum', hyx', hzx', hrSq]
    rw [hdecomp] at hnorm
    simpa using hnorm

theorem halfWindow_subset_window (z : ℝ × Vec 2) : halfWindow z ⊆ window z := by
  intro y hy
  rcases hy with ⟨hyt, hyx⟩
  change y.1 ∈ Set.Ioc (z.1 - 1 ^ 2) z.1 ∧ vecNormSq (y.2 - z.2) < 1 ^ 2
  refine ⟨?_, ?_⟩
  · change z.1 - 1 ^ 2 < y.1 ∧ y.1 ≤ z.1
    change z.1 - (1 / 2 : ℝ) ^ 2 < y.1 ∧ y.1 ≤ z.1 at hyt
    exact ⟨by nlinarith [hyt.1], hyt.2⟩
  · change vecNormSq (y.2 - z.2) < (1 / 2 : ℝ) ^ 2 at hyx
    nlinarith

/-- Lebesgue differentiation in the parabolic metric, for mean absolute error. -/
theorem ae_tendsto_parabolic_ball_average_norm_sub {f : ℝ × Vec 2 → ℝ}
    (hf : LocallyIntegrable f (volume : Measure (ℝ × Vec 2))) :
    ∀ᵐ z ∂(volume : Measure (ℝ × Vec 2)),
      ∀ {ι : Type*} {l : Filter ι} (w : ι → ℝ × Vec 2) (δ : ι → ℝ)
        (_ : Tendsto δ l (𝓝[>] (0 : ℝ)))
        (_ : ∀ᶠ j in l, z ∈ parabolicClosedBall (w j) (2 * δ j)),
        Tendsto (fun j => ⨍ y in parabolicClosedBall (w j) (δ j), |f y - f z| ∂volume)
          l (𝓝 0) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
      (μ := (volume : Measure (ℝ × Vec 2))) hf 2] with z hz
  intro ι l w δ hδ hmem
  have hδ' : Tendsto δ l (𝓝[>] (0 : ℝ)) := hδ
  have hmem' : ∀ᶠ j in l, z ∈ Metric.closedBall (w j) (2 * δ j) := by
    filter_upwards [hmem] with j hj
    simpa only [metric_closedBall_eq_parabolicClosedBall] using hj
  have hlim := hz w δ hδ' hmem'
  simpa only [metric_closedBall_eq_parabolicClosedBall, Real.norm_eq_abs] using hlim

/-- Every backward cylinder lies in the parabolic closed ball with the same endpoint and radius. -/
theorem cylinder_subset_parabolic_closedBall (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    cylinder z r ⊆ parabolicClosedBall z r := by
  intro w hw
  rw [parabolic_closedBall_eq_rect z hr.le]
  refine ⟨?_, ?_⟩
  · rw [Set.mem_Icc]
    exact ⟨by linarith [hw.1.1], by nlinarith [hw.1.2]⟩
  · change dist w.2 z.2 ≤ r
    have hbox : w.2 ∈ outerBox z.2 r := euclidBall_subset_outerBox z.2 hr hw.2
    rw [dist_pi_le_iff hr.le]
    intro i
    have hi := hbox i (Set.mem_univ i)
    rw [Set.mem_Ioo] at hi
    rw [Real.dist_eq, abs_le]
    exact ⟨by linarith, by linarith⟩

/-- Closed balls for the parabolic metric are compact. -/
theorem parabolic_closedBall_isCompact (z : ℝ × Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    IsCompact (parabolicClosedBall z r) := by
  rw [parabolic_closedBall_eq_rect z hr]
  exact isCompact_Icc.prod (isCompact_closedBall z.2 r)

end AVRegularity.External.Campanato
end

section
open Filter Homogenization MeasureTheory Set
open scoped ENNReal Topology
namespace AVRegularity.External.Campanato

theorem euclidBall_measurable (c : Vec 2) (r : ℝ) : MeasurableSet (euclidBall c r) := by
  have hcont : Continuous (fun x : Vec 2 => vecNormSq (x - c)) := by
    unfold vecNormSq vecDot
    fun_prop
  change MeasurableSet {x | vecNormSq (x - c) < r ^ 2}
  exact isOpen_Iio.preimage hcont |>.measurableSet

theorem cylinder_measurable (z : ℝ × Vec 2) (r : ℝ) : MeasurableSet (cylinder z r) := by
  exact measurableSet_Ioc.prod (euclidBall_measurable z.2 r)

theorem window_measurable (z : ℝ × Vec 2) : MeasurableSet (window z) := by
  simpa [window] using cylinder_measurable z 1

theorem halfWindow_measurable (z : ℝ × Vec 2) : MeasurableSet (halfWindow z) := by
  simpa [halfWindow] using cylinder_measurable z (1 / 2)

/-- The normalized mean on a backward parabolic cylinder. -/
def cylinderMean (f : ℝ × Vec 2 → ℝ) (z : ℝ × Vec 2) (r : ℝ) : ℝ :=
  ⨍ y in cylinder z r, f y ∂volume

/-- The normalized mean-square oscillation about the cylinder mean. -/
def cylinderExcess (f : ℝ × Vec 2 → ℝ) (z : ℝ × Vec 2) (r : ℝ) : ℝ :=
  ⨍ y in cylinder z r, (f y - cylinderMean f z r) ^ 2 ∂volume

theorem cylinderMean_indicator_eq (z₀ z : ℝ × Vec 2) (u : ℝ × Vec 2 → ℝ) {r : ℝ}
    (hsub : cylinder z r ⊆ window z₀) :
    cylinderMean ((window z₀).indicator u) z r = cylinderMean u z r := by
  rw [cylinderMean, cylinderMean]
  apply MeasureTheory.setAverage_congr_fun (cylinder_measurable z r)
  filter_upwards [] with y hy
  simp [Set.indicator_of_mem (hsub hy)]

theorem cylinderExcess_indicator_eq (z₀ z : ℝ × Vec 2) (u : ℝ × Vec 2 → ℝ) {r : ℝ}
    (hsub : cylinder z r ⊆ window z₀) :
    cylinderExcess ((window z₀).indicator u) z r = cylinderExcess u z r := by
  unfold cylinderExcess
  rw [cylinderMean_indicator_eq z₀ z u hsub]
  apply MeasureTheory.setAverage_congr_fun (cylinder_measurable z r)
  filter_upwards [] with y hy
  simp [Set.indicator_of_mem (hsub hy)]

end AVRegularity.External.Campanato
end

section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.External.Campanato

/-- On a probability space, the absolute mean is bounded by the root mean square. -/
theorem average_abs_le_sqrt_average_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] (f : α → ℝ) (hf : MemLp f 2 μ) :
    |⨍ x, f x ∂μ| ≤ Real.sqrt (⨍ x, f x ^ 2 ∂μ) := by
  have hfabs : MemLp (fun x => |f x|) (ENNReal.ofReal 2) μ := by
    simpa [Real.norm_eq_abs] using hf.norm
  have hconst : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    simpa using (memLp_const (μ := μ) (p := ENNReal.ofReal 2) (1 : ℝ))
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hnonnegf : 0 ≤ᵐ[μ] fun x => |f x| := by
    filter_upwards [] with x
    exact abs_nonneg _
  have hnonneg1 : 0 ≤ᵐ[μ] fun _ : α => (1 : ℝ) := by
    filter_upwards [] with x
    norm_num
  have hcauchy := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hnonnegf hnonneg1 hfabs hconst
  have hmean : |⨍ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := by
    rw [average_eq_integral]
    simpa [Real.norm_eq_abs] using (norm_integral_le_integral_norm (f := f) (μ := μ))
  have hrewrite : (∫ x, |f x| * (1 : ℝ) ∂μ) = ∫ x, |f x| ∂μ := by simp
  have hsqR : ∫ x, |f x| ^ (2 : ℝ) ∂μ = ∫ x, f x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [sq_abs]
  have hone : ∫ x, (1 : ℝ) ^ 2 ∂μ = 1 := by simp
  have hbound : ∫ x, |f x| ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
    calc
      ∫ x, |f x| ∂μ = ∫ x, |f x| * (1 : ℝ) ∂μ := hrewrite.symm
      _ ≤ (∫ x, |f x| ^ 2 ∂μ) ^ (1 / 2) *
          (∫ x, (1 : ℝ) ^ 2 ∂μ) ^ (1 / 2) := hcauchy
      _ = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
        have hpow : (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) =
            (∫ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := congrArg (fun v : ℝ => v ^ (1 / 2 : ℝ)) hsqR
        have honeReal : ∫ x, (1 : ℝ) ^ (2 : ℝ) ∂μ = 1 := by
          simp
        have honepow : (∫ x, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) = 1 := by
          rw [honeReal]
          simp
        calc
          (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
              (∫ x, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
              = (∫ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * 1 := by
                exact congrArg₂ (· * ·) hpow honepow
          _ = (∫ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by ring
          _ = Real.sqrt (∫ x, f x ^ 2 ∂μ) := (Real.sqrt_eq_rpow _).symm
  calc
    |⨍ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := hmean
    _ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) := hbound
    _ = Real.sqrt (⨍ x, f x ^ 2 ∂μ) := by rw [average_eq_integral]

/-- The same Cauchy--Schwarz estimate for a normalized average over a set. -/
theorem setAverage_abs_le_sqrt_setAverage_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hμ0 : μ s ≠ 0) (hμtop : μ s ≠ ∞)
    (f : α → ℝ) (hf : MemLp f 2 (μ.restrict s)) :
    |⨍ x in s, f x ∂μ| ≤ Real.sqrt (⨍ x in s, f x ^ 2 ∂μ) := by
  let ν : Measure α := (μ s)⁻¹ • μ.restrict s
  have hν : ν Set.univ = 1 := by
    simp only [ν, Measure.smul_apply, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hμ0 hμtop
  have hνinst : IsProbabilityMeasure ν := ⟨hν⟩
  have hfν : MemLp f 2 ν := hf.smul_measure (by simp [hμ0])
  have hmean : ⨍ x, f x ∂ν = ⨍ x in s, f x ∂μ := by
    rw [@average_eq_integral α ℝ _ _ _ ν f hνinst, setAverage_eq']
  have hsecond : ⨍ x, f x ^ 2 ∂ν = ⨍ x in s, f x ^ 2 ∂μ := by
    rw [@average_eq_integral α ℝ _ _ _ ν (fun x => f x ^ 2) hνinst, setAverage_eq']
  have h := @average_abs_le_sqrt_average_sq α _ ν hνinst f hfν
  rw [hmean, hsecond] at h
  exact h


/-- Translation commutes with a normalized average on a positive finite-measure set. -/
theorem setAverage_sub_const_of_memLp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hμ0 : μ s ≠ 0) (hμtop : μ s ≠ ∞)
    (f : α → ℝ) (hf : MemLp f 2 μ) (c : ℝ) :
    ⨍ x in s, (f x - c) ∂μ = (⨍ x in s, f x ∂μ) - c := by
  let ν : Measure α := (μ s)⁻¹ • μ.restrict s
  have hν : ν Set.univ = 1 := by
    simp only [ν, Measure.smul_apply, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hμ0 hμtop
  have hνinst : IsProbabilityMeasure ν := ⟨hν⟩
  have hνfin : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.one_lt_top⟩
  have hfν : MemLp f 2 ν := by
    have hfr : MemLp f 2 (μ.restrict s) :=
      MemLp.mono_measure Measure.restrict_le_self hf
    exact hfr.smul_measure (by simp [hμ0])
  have hfi : Integrable f ν :=
    @MemLp.integrable α ℝ _ ν _ _ 2 (by norm_num) f hνfin hfν
  have hci : Integrable (fun _ : α => c) ν := integrable_const _
  rw [setAverage_eq', setAverage_eq']
  change (∫ x, f x - c ∂ν) = (∫ x, f x ∂ν) - c
  rw [integral_sub hfi hci, integral_const]
  simp

/-- The absolute value of an average is at most the average absolute value. -/
theorem setAverage_abs_le_setAverage_abs {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hμ0 : μ s ≠ 0) (hμtop : μ s ≠ ∞)
    (f : α → ℝ) (hf : MemLp f 2 (μ.restrict s)) :
    |⨍ x in s, f x ∂μ| ≤ ⨍ x in s, |f x| ∂μ := by
  let ν : Measure α := (μ s)⁻¹ • μ.restrict s
  have hν : ν Set.univ = 1 := by
    simp only [ν, Measure.smul_apply, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hμ0 hμtop
  have hνinst : IsProbabilityMeasure ν := ⟨hν⟩
  have hνfin : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.one_lt_top⟩
  have hfν : MemLp f 2 ν := hf.smul_measure (by simp [hμ0])
  have hfi : Integrable f ν :=
    @MemLp.integrable α ℝ _ ν _ _ 2 (by norm_num) f hνfin hfν
  have hleft : (⨍ x in s, f x ∂μ) = ∫ x, f x ∂ν := by
    rw [setAverage_eq']
  have hright : (⨍ x in s, |f x| ∂μ) = ∫ x, |f x| ∂ν := by
    rw [setAverage_eq']
  rw [hleft, hright, ← Real.norm_eq_abs]
  exact norm_integral_le_integral_norm (f := f) (μ := ν)

/-- A nonnegative average over a subset is bounded by the measure ratio times the larger-set
average. -/
theorem setAverage_le_measure_ratio {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s t : Set α} {f : α → ℝ}
    (hst : s ⊆ t) (hspos : 0 < (μ s).toReal) (htpos : 0 < (μ t).toReal)
    (hfi : IntegrableOn f t μ) (hfn : ∀ x, 0 ≤ f x) :
    ⨍ x in s, f x ∂μ ≤ ((μ t).toReal / (μ s).toReal) * (⨍ x in t, f x ∂μ) := by
  let a : ℝ := (μ s).toReal
  let b : ℝ := (μ t).toReal
  have hmono : (∫ x in s, f x ∂μ) ≤ ∫ x in t, f x ∂μ := by
    apply setIntegral_mono_set hfi
    · exact Filter.Eventually.of_forall hfn
    · exact Filter.Eventually.of_forall fun x hx => hst hx
  have hfactor : b / a * b⁻¹ = a⁻¹ := by
    dsimp [a, b]
    field_simp
  rw [setAverage_eq, setAverage_eq]
  simp only [smul_eq_mul]
  change a⁻¹ * (∫ x in s, f x ∂μ) ≤
    (b / a) * (b⁻¹ * (∫ x in t, f x ∂μ))
  calc
    a⁻¹ * (∫ x in s, f x ∂μ) ≤ a⁻¹ * (∫ x in t, f x ∂μ) :=
      mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hspos.le)
    _ = (b / a) * (b⁻¹ * (∫ x in t, f x ∂μ)) := by
      rw [← mul_assoc, hfactor]


/-- A nonnegative function has nonnegative set average. -/
theorem setAverage_nonneg_of_nonneg {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f : α → ℝ}
    (hfn : ∀ x, 0 ≤ f x) : 0 ≤ ⨍ x in s, f x ∂μ := by
  rw [setAverage_eq]
  apply smul_nonneg
  · exact inv_nonneg.mpr ENNReal.toReal_nonneg
  · exact setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall hfn)

end AVRegularity.External.Campanato
end

section
open Filter Homogenization MeasureTheory Set
open scoped ENNReal Topology
namespace AVRegularity.External.Campanato

/-- The radii used in the dyadic Campanato construction. -/
def campanatoScale (n : ℕ) : ℝ := (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ n

theorem campanatoScale_pos (n : ℕ) : 0 < campanatoScale n := by
  unfold campanatoScale
  positivity

theorem campanatoScale_lt_quarter (n : ℕ) : campanatoScale n < 1 / 4 := by
  unfold campanatoScale
  have hp : (1 / 2 : ℝ) ^ n ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem campanatoScale_succ (n : ℕ) :
    campanatoScale (n + 1) = campanatoScale n / 2 := by
  unfold campanatoScale
  simp only [pow_succ]
  ring

theorem cylinder_measure_ne_zero (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    volume (cylinder z r) ≠ 0 := by
  apply ne_of_gt
  exact lt_of_lt_of_le
    (ENNReal.ofReal_pos.mpr (by positivity : 0 < r ^ 4)) (cylinder_volume_lower z hr)

theorem cylinder_measure_ne_top (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    volume (cylinder z r) ≠ ∞ := by
  apply ne_of_lt
  exact lt_of_le_of_lt (cylinder_volume_upper z hr) ENNReal.ofReal_lt_top

theorem cylinder_measureReal_pos (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    0 < (volume (cylinder z r)).toReal := by
  have hlo := cylinder_volume_lower z hr
  have hhi := cylinder_volume_upper z hr
  have htop : volume (cylinder z r) < ∞ :=
    lt_of_le_of_lt hhi (ENNReal.ofReal_lt_top)
  have hzero : volume (cylinder z r) ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hlo
  exact ENNReal.toReal_pos hzero (ne_of_lt htop)

theorem cylinder_volume_ratio_half (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    (volume (cylinder z r)).toReal /
      (volume (cylinder z (r / 2))).toReal ≤ 64 := by
  have hbig := cylinder_volume_upper z hr
  have hsmall := cylinder_volume_lower z (by positivity : 0 < r / 2)
  have hbigTop : volume (cylinder z r) < ∞ :=
    lt_of_le_of_lt hbig ENNReal.ofReal_lt_top
  have hsmallTop : volume (cylinder z (r / 2)) < ∞ :=
    lt_of_le_of_lt (cylinder_volume_upper z (by positivity : 0 < r / 2))
      ENNReal.ofReal_lt_top
  have hnum : (volume (cylinder z r)).toReal ≤ 4 * r ^ 4 := by
    have h := (ENNReal.toReal_le_toReal (ne_of_lt hbigTop)
      ENNReal.ofReal_ne_top).2 hbig
    have h' : (volume (cylinder z r)).toReal ≤ 4 * r ^ 4 := by
      calc
        (volume (cylinder z r)).toReal ≤ (ENNReal.ofReal (4 * r ^ 4)).toReal := h
        _ = 4 * r ^ 4 := by rw [ENNReal.toReal_ofReal (by positivity)]
    exact h'
  have hden : (r / 2) ^ 4 ≤ (volume (cylinder z (r / 2))).toReal := by
    have h := ENNReal.toReal_mono (ne_of_lt hsmallTop) hsmall
    have h' : (r / 2) ^ 4 ≤ (volume (cylinder z (r / 2))).toReal := by
      calc
        (r / 2) ^ 4 = (ENNReal.ofReal ((r / 2) ^ 4)).toReal :=
          (ENNReal.toReal_ofReal (by positivity)).symm
        _ ≤ (volume (cylinder z (r / 2))).toReal := h
    exact h'
  have hpos : 0 < (volume (cylinder z (r / 2))).toReal :=
    cylinder_measureReal_pos z (by positivity)
  apply (div_le_iff₀ hpos).2
  calc
    (volume (cylinder z r)).toReal ≤ 4 * r ^ 4 := hnum
    _ = 64 * (r / 2) ^ 4 := by ring
    _ ≤ 64 * (volume (cylinder z (r / 2))).toReal :=
      mul_le_mul_of_nonneg_left hden (by norm_num)

theorem cylinder_parabolicBall_volume_ratio (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) :
    (volume (parabolicClosedBall z r)).toReal /
      (volume (cylinder z r)).toReal ≤ 8 := by
  have hnum : (volume (parabolicClosedBall z r)).toReal = 8 * r ^ 4 := by
    rw [parabolic_closedBall_volume z hr.le, ENNReal.toReal_ofReal]
    positivity
  have htop : volume (cylinder z r) < ∞ :=
    lt_of_le_of_lt (cylinder_volume_upper z hr) ENNReal.ofReal_lt_top
  have hden : r ^ 4 ≤ (volume (cylinder z r)).toReal := by
    have h := ENNReal.toReal_mono (ne_of_lt htop) (cylinder_volume_lower z hr)
    calc
      r ^ 4 = (ENNReal.ofReal (r ^ 4)).toReal := by
        rw [ENNReal.toReal_ofReal (by positivity)]
      _ ≤ (volume (cylinder z r)).toReal := h
  have hpos := cylinder_measureReal_pos z hr
  apply (div_le_iff₀ hpos).2
  rw [hnum]
  calc
    8 * r ^ 4 ≤ 8 * (volume (cylinder z r)).toReal :=
      mul_le_mul_of_nonneg_left hden (by norm_num)
    _ = 8 * (volume (cylinder z r)).toReal := rfl

theorem cylinder_volume_ratio_of_le_six {z w : ℝ × Vec 2} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hRr : R ≤ 6 * r) :
    (volume (cylinder z R)).toReal / (volume (cylinder w r)).toReal ≤ 5184 := by
  have htopR : volume (cylinder z R) < ∞ :=
    lt_of_le_of_lt (cylinder_volume_upper z hR) ENNReal.ofReal_lt_top
  have htopr : volume (cylinder w r) < ∞ :=
    lt_of_le_of_lt (cylinder_volume_upper w hr) ENNReal.ofReal_lt_top
  have hnum : (volume (cylinder z R)).toReal ≤ 4 * R ^ 4 := by
    have h := (ENNReal.toReal_le_toReal (ne_of_lt htopR) ENNReal.ofReal_ne_top).2
      (cylinder_volume_upper z hR)
    calc
      (volume (cylinder z R)).toReal ≤ (ENNReal.ofReal (4 * R ^ 4)).toReal := h
      _ = 4 * R ^ 4 := by rw [ENNReal.toReal_ofReal (by positivity)]
  have hden : r ^ 4 ≤ (volume (cylinder w r)).toReal := by
    have h := ENNReal.toReal_mono (ne_of_lt htopr) (cylinder_volume_lower w hr)
    calc
      r ^ 4 = (ENNReal.ofReal (r ^ 4)).toReal := by
        rw [ENNReal.toReal_ofReal (by positivity)]
      _ ≤ (volume (cylinder w r)).toReal := h
  have hdenpos := cylinder_measureReal_pos w hr
  apply (div_le_iff₀ hdenpos).2
  calc
    (volume (cylinder z R)).toReal ≤ 4 * R ^ 4 := hnum
    _ ≤ 4 * (6 * r) ^ 4 := by gcongr
    _ = 5184 * r ^ 4 := by ring
    _ ≤ 5184 * (volume (cylinder w r)).toReal :=
      mul_le_mul_of_nonneg_left hden (by norm_num)

theorem cylinder_subset_same_center {z : ℝ × Vec 2} {r R : ℝ}
    (hr : 0 < r) (hrr : r ≤ R) : cylinder z r ⊆ cylinder z R := by
  intro w hw
  refine ⟨?_, ?_⟩
  · exact ⟨by nlinarith [hw.1.1], hw.1.2⟩
  · change vecNormSq (w.2 - z.2) < R ^ 2
    have hs : vecNormSq (w.2 - z.2) < r ^ 2 := by simpa [euclidBall] using hw.2
    nlinarith [sq_nonneg R, sq_nonneg r]

/-- One dyadic Campanato step, with the cylinder geometry constants made explicit. -/
theorem cylinderMean_dyadic_difference
    {z : ℝ × Vec 2} {f : ℝ × Vec 2 → ℝ} {a M : ℝ}
    (hf : MemLp f 2 volume) (hM : 0 ≤ M)
    (hcamp : ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess f z r ≤ M * r ^ (2 * a))
    {r : ℝ} (hr : 0 < r) (hrr : r < 1 / 4) :
    |cylinderMean f z (r / 2) - cylinderMean f z r| ≤
      8 * Real.sqrt M * r ^ a := by
  let c := cylinderMean f z r
  let g : ℝ × Vec 2 → ℝ := fun y => f y - c
  have hshift : cylinderMean f z (r / 2) - c =
      ⨍ y in cylinder z (r / 2), g y ∂volume := by
    unfold cylinderMean g
    exact (setAverage_sub_const_of_memLp
      (cylinder_measure_ne_zero z (by positivity))
      (cylinder_measure_ne_top z (by positivity)) f hf c).symm
  have hbigTop : volume (cylinder z r) < ∞ := by
    exact lt_of_le_of_lt (cylinder_volume_upper z hr) ENNReal.ofReal_lt_top
  let μbig : Measure (ℝ × Vec 2) := volume.restrict (cylinder z r)
  have hμbig : IsFiniteMeasure μbig := by
    refine ⟨?_⟩
    simpa [μbig] using hbigTop
  have hfBig : MemLp f 2 μbig := by
    simpa [μbig] using (MemLp.restrict (cylinder z r) hf)
  have hcBig : MemLp (fun _ : ℝ × Vec 2 => c) 2 μbig :=
    @memLp_const (ℝ × Vec 2) ℝ _ 2 μbig _ c hμbig
  have hgBig : MemLp g 2 μbig := by
    exact hfBig.sub hcBig
  have hfiBig : IntegrableOn (fun y => g y ^ 2) (cylinder z r) volume := by
    change Integrable (fun y => g y ^ 2) μbig
    exact hgBig.integrable_sq
  have hsub : cylinder z (r / 2) ⊆ cylinder z r :=
    cylinder_subset_same_center (by positivity) (by linarith)
  have hrestrict : volume.restrict (cylinder z (r / 2)) ≤ μbig := by
    simpa [μbig] using
      (Measure.restrict_mono_ae (μ := volume)
        (Filter.Eventually.of_forall fun y hy => hsub hy))
  have hgSmall : MemLp g 2 (volume.restrict (cylinder z (r / 2))) :=
    MemLp.mono_measure hrestrict hgBig
  have hratio := setAverage_le_measure_ratio
    (s := cylinder z (r / 2)) (t := cylinder z r) hsub
    (cylinder_measureReal_pos z (by positivity))
    (cylinder_measureReal_pos z hr) hfiBig (fun y => sq_nonneg (g y))
  have hratio' : (volume (cylinder z r)).toReal /
      (volume (cylinder z (r / 2))).toReal ≤ 64 := cylinder_volume_ratio_half z hr
  have hsmallSq : (⨍ y in cylinder z (r / 2), g y ^ 2 ∂volume) ≤
      64 * (⨍ y in cylinder z r, g y ^ 2 ∂volume) := by
    calc
      _ ≤ ((volume (cylinder z r)).toReal /
          (volume (cylinder z (r / 2))).toReal) *
            (⨍ y in cylinder z r, g y ^ 2 ∂volume) := hratio
      _ ≤ 64 * (⨍ y in cylinder z r, g y ^ 2 ∂volume) := by
        apply mul_le_mul_of_nonneg_right hratio'
        exact setAverage_nonneg_of_nonneg (fun y => sq_nonneg (g y))
  have hbig : (⨍ y in cylinder z r, g y ^ 2 ∂volume) = cylinderExcess f z r := by
    simp [g, c, cylinderExcess, cylinderMean]
  have hroot : Real.sqrt (⨍ y in cylinder z (r / 2), g y ^ 2 ∂volume) ≤
      8 * Real.sqrt M * r ^ a := by
    have hbound : (⨍ y in cylinder z (r / 2), g y ^ 2 ∂volume) ≤
        64 * (M * r ^ (2 * a)) := by
      calc
        _ ≤ 64 * (⨍ y in cylinder z r, g y ^ 2 ∂volume) := hsmallSq
        _ = 64 * cylinderExcess f z r := by rw [hbig]
        _ ≤ 64 * (M * r ^ (2 * a)) := by
          exact mul_le_mul_of_nonneg_left (hcamp r hr hrr) (by norm_num)
    have hroot' := Real.sqrt_le_sqrt hbound
    have hrpow : 0 ≤ r ^ a := Real.rpow_nonneg (le_of_lt hr) a
    have hpow : r ^ (2 * a) = (r ^ a) ^ 2 := by
      calc
        r ^ (2 * a) = r ^ (a * 2) := by congr 1; ring
        _ = (r ^ a) ^ (2 : ℝ) := Real.rpow_mul (le_of_lt hr) a 2
        _ = (r ^ a) ^ 2 := Real.rpow_natCast (r ^ a) 2
    have hsqrt : Real.sqrt (64 * (M * r ^ (2 * a))) =
        8 * Real.sqrt M * r ^ a := by
      calc
        Real.sqrt (64 * (M * r ^ (2 * a))) =
            Real.sqrt (64 * M * (r ^ a) ^ 2) := by rw [hpow]; ring_nf
        _ = Real.sqrt (64 * M) * Real.sqrt ((r ^ a) ^ 2) := by
          rw [Real.sqrt_mul (mul_nonneg (by norm_num) hM)]
        _ = Real.sqrt 64 * Real.sqrt M * r ^ a := by
          rw [Real.sqrt_mul (by norm_num : 0 ≤ (64 : ℝ)),
            Real.sqrt_sq_eq_abs, abs_of_nonneg hrpow]
        _ = 8 * Real.sqrt M * r ^ a := by
          rw [show Real.sqrt (64 : ℝ) = 8 from
            (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)]
    rw [hsqrt] at hroot'
    exact hroot'
  calc
    |cylinderMean f z (r / 2) - cylinderMean f z r| =
        |⨍ y in cylinder z (r / 2), g y ∂volume| := by rw [hshift]
    _ ≤ Real.sqrt (⨍ y in cylinder z (r / 2), g y ^ 2 ∂volume) :=
      setAverage_abs_le_sqrt_setAverage_sq
        (cylinder_measure_ne_zero z (by positivity))
        (cylinder_measure_ne_top z (by positivity)) g hgSmall
    _ ≤ 8 * Real.sqrt M * r ^ a := hroot

theorem campanatoScale_tendsto : Tendsto campanatoScale atTop (𝓝[>] (0 : ℝ)) := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hzero : Tendsto campanatoScale atTop (𝓝 (0 : ℝ)) := by
    unfold campanatoScale
    convert (tendsto_const_nhds (x := (1 / 8 : ℝ))).mul hpow using 1
    · exact congrArg nhds (by norm_num)
  exact (tendsto_nhdsWithin_iff).2
    ⟨hzero, Filter.Eventually.of_forall campanatoScale_pos⟩

theorem campanatoScale_rpow (a : ℝ) (n : ℕ) :
    campanatoScale n ^ a = (1 / 8 : ℝ) ^ a * ((1 / 2 : ℝ) ^ a) ^ n := by
  unfold campanatoScale
  rw [Real.mul_rpow (by norm_num) (by positivity)]
  have hpow : ((1 / 2 : ℝ) ^ n) ^ a = ((1 / 2 : ℝ) ^ a) ^ n := by
    calc
      ((1 / 2 : ℝ) ^ n) ^ a = (1 / 2 : ℝ) ^ ((n : ℝ) * a) := by
        rw [← Real.rpow_natCast (1 / 2 : ℝ) n,
          ← Real.rpow_mul (by norm_num) (n : ℝ) a]
      _ = (1 / 2 : ℝ) ^ (a * n) := by congr 1; ring
      _ = ((1 / 2 : ℝ) ^ a) ^ n := Real.rpow_mul_natCast (by norm_num) a n
  rw [hpow]

def campanatoConstant (a : ℝ) : ℝ := 8 / (1 - (1 / 2 : ℝ) ^ a)

theorem campanatoConstant_pos {a : ℝ} (ha : 0 < a) : 0 < campanatoConstant a := by
  unfold campanatoConstant
  have hq : (1 / 2 : ℝ) ^ a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha
  positivity

/-- The means on the fixed dyadic sequence of backward cylinders. -/
def campanatoAverages (f : ℝ × Vec 2 → ℝ) (z : ℝ × Vec 2) (n : ℕ) : ℝ :=
  cylinderMean f z (campanatoScale n)

/-- The limiting representative selected by backward-cylinder averages. -/
def campanatoRepresentative (f : ℝ × Vec 2 → ℝ) (z : ℝ × Vec 2) : ℝ :=
  limUnder atTop (campanatoAverages f z)

private def campanatoRatio (a : ℝ) : ℝ := (1 / 2 : ℝ) ^ a

private def campanatoStepConstant (a M : ℝ) : ℝ :=
  8 * Real.sqrt M * (1 / 8 : ℝ) ^ a

private theorem campanatoRatio_pos {a : ℝ} : 0 < campanatoRatio a := by
  unfold campanatoRatio
  exact Real.rpow_pos_of_pos (by norm_num) a

private theorem campanatoRatio_lt_one {a : ℝ} (ha : 0 < a) : campanatoRatio a < 1 := by
  unfold campanatoRatio
  exact Real.rpow_lt_one (by norm_num) (by norm_num) ha

private theorem campanatoAverages_step
    {f : ℝ × Vec 2 → ℝ} {z : ℝ × Vec 2} {a M : ℝ}
    (hf : MemLp f 2 volume) (hM : 0 ≤ M)
    (hcamp : ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess f z r ≤ M * r ^ (2 * a))
    (n : ℕ) :
    dist (campanatoAverages f z n) (campanatoAverages f z (n + 1)) ≤
      campanatoStepConstant a M * campanatoRatio a ^ n := by
  have hr := campanatoScale_pos n
  have hlt := campanatoScale_lt_quarter n
  have hstep := cylinderMean_dyadic_difference hf hM hcamp hr hlt
  rw [abs_sub_comm] at hstep
  have hscale := campanatoScale_rpow a n
  have habs : |campanatoAverages f z n - campanatoAverages f z (n + 1)| ≤
      8 * Real.sqrt M * campanatoScale n ^ a := by
    simpa [campanatoAverages, campanatoScale_succ] using hstep
  rw [Real.dist_eq]
  calc
    |campanatoAverages f z n - campanatoAverages f z (n + 1)| ≤
        8 * Real.sqrt M * campanatoScale n ^ a := habs
    _ = campanatoStepConstant a M * campanatoRatio a ^ n := by
      rw [campanatoStepConstant, campanatoRatio, hscale]
      ring

private theorem campanatoStep_summable {a M : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => campanatoStepConstant a M * campanatoRatio a ^ n) := by
  apply Summable.mul_left
  exact summable_geometric_of_lt_one campanatoRatio_pos.le (campanatoRatio_lt_one ha)

private theorem cylinder_abs_error_average_tendsto
    {f : ℝ × Vec 2 → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ z ∂(volume : Measure (ℝ × Vec 2)),
      Tendsto (fun n : ℕ =>
        ⨍ y in cylinder z (campanatoScale n), |f y - f z| ∂volume)
        atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_parabolic_ball_average_norm_sub hf] with z hz
  have hdelta := campanatoScale_tendsto
  have hmem : ∀ᶠ n : ℕ in atTop,
      z ∈ parabolicClosedBall z (2 * campanatoScale n) := by
    filter_upwards [] with n
    change parabolicDist z z ≤ 2 * campanatoScale n
    rw [parabolicDist_self]
    have hr := campanatoScale_pos n
    nlinarith
  have hball := hz (fun _ : ℕ => z) campanatoScale hdelta hmem
  have hball' : Tendsto (fun n : ℕ =>
      ⨍ y in parabolicClosedBall z (campanatoScale n), |f y - f z| ∂volume)
      atTop (𝓝 0) := by
    simpa using hball
  have hdiff : LocallyIntegrable (fun y => |f y - f z|) volume := by
    apply locallyIntegrableOn_univ.mp
    exact (locallyIntegrableOn_univ.mpr
      (hf.sub (locallyIntegrable_const (f z)))).norm
  have hbound : ∀ n : ℕ,
      (⨍ y in cylinder z (campanatoScale n), |f y - f z| ∂volume) ≤
        8 * (⨍ y in parabolicClosedBall z (campanatoScale n),
          |f y - f z| ∂volume) := by
    intro n
    let r := campanatoScale n
    have hr : 0 < r := campanatoScale_pos n
    have hsubset : cylinder z r ⊆ parabolicClosedBall z r :=
      cylinder_subset_parabolic_closedBall z hr
    have hfi : IntegrableOn (fun y => |f y - f z|)
        (parabolicClosedBall z r) volume :=
      hdiff.integrableOn_isCompact (parabolic_closedBall_isCompact z hr.le)
    have hballpos : 0 < (volume (parabolicClosedBall z r)).toReal := by
      rw [parabolic_closedBall_volume z hr.le,
        ENNReal.toReal_ofReal (by positivity)]
      exact mul_pos (by norm_num) (pow_pos hr 4)
    have hratio := setAverage_le_measure_ratio hsubset
      (cylinder_measureReal_pos z hr) hballpos hfi (fun y => abs_nonneg _)
    have hratio' := cylinder_parabolicBall_volume_ratio z hr
    calc
      ⨍ y in cylinder z r, |f y - f z| ∂volume ≤
          ((volume (parabolicClosedBall z r)).toReal /
            (volume (cylinder z r)).toReal) *
              (⨍ y in parabolicClosedBall z r, |f y - f z| ∂volume) := hratio
      _ ≤ 8 * (⨍ y in parabolicClosedBall z r, |f y - f z| ∂volume) := by
        apply mul_le_mul_of_nonneg_right hratio'
        exact setAverage_nonneg_of_nonneg (fun y => abs_nonneg _)
  exact squeeze_zero
    (fun n => setAverage_nonneg_of_nonneg (fun y => abs_nonneg _))
    hbound
    (by convert hball'.const_mul 8 using 1; simp [mul_comm])

theorem campanatoAverages_cauchy
    {f : ℝ × Vec 2 → ℝ} {z : ℝ × Vec 2} {a M : ℝ}
    (hf : MemLp f 2 volume) (hM : 0 ≤ M)
    (hcamp : ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess f z r ≤ M * r ^ (2 * a))
    (ha : 0 < a) : CauchySeq (campanatoAverages f z) := by
  apply cauchySeq_of_dist_le_of_summable
    (fun n => campanatoStepConstant a M * campanatoRatio a ^ n)
  · intro n
    exact campanatoAverages_step hf hM hcamp n
  · exact campanatoStep_summable ha

theorem campanatoAverages_tendsto_representative
    {f : ℝ × Vec 2 → ℝ} {z : ℝ × Vec 2} {a M : ℝ}
    (hf : MemLp f 2 volume) (hM : 0 ≤ M)
    (hcamp : ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess f z r ≤ M * r ^ (2 * a))
    (ha : 0 < a) :
    Tendsto (campanatoAverages f z) atTop (𝓝 (campanatoRepresentative f z)) :=
  (campanatoAverages_cauchy hf hM hcamp ha).tendsto_limUnder

theorem campanatoRepresentative_ae_eq
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 volume)
    {z₀ : ℝ × Vec 2} {a M : ℝ} (hM : 0 ≤ M) (ha : 0 < a)
    (hcamp : ∀ z ∈ halfWindow z₀, ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess f z r ≤ M * r ^ (2 * a)) :
    ∀ᵐ z ∂(volume.restrict (halfWindow z₀)),
      campanatoRepresentative f z = f z := by
  rw [ae_restrict_iff' (halfWindow_measurable z₀)]
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  filter_upwards [cylinder_abs_error_average_tendsto hloc] with z hz hzDomain
  have hmean : Tendsto (campanatoAverages f z) atTop (𝓝 (f z)) := by
    have hnonneg : ∀ n : ℕ,
        0 ≤ |campanatoAverages f z n - f z| := fun _ => abs_nonneg _
    have hbound : ∀ n : ℕ,
        |campanatoAverages f z n - f z| ≤
          ⨍ y in cylinder z (campanatoScale n), |f y - f z| ∂volume := by
      intro n
      let s := cylinder z (campanatoScale n)
      let μ : Measure (ℝ × Vec 2) := volume.restrict s
      have hr : 0 < campanatoScale n := campanatoScale_pos n
      have hμtop : volume s ≠ ∞ := cylinder_measure_ne_top z hr
      have hμ : IsFiniteMeasure μ := by
        refine ⟨?_⟩
        simpa [μ] using hμtop.lt_top
      have hfμ : MemLp f 2 μ := by
        simpa [μ] using (MemLp.restrict s hf)
      have hcμ : MemLp (fun _ : ℝ × Vec 2 => f z) 2 μ :=
        @memLp_const (ℝ × Vec 2) ℝ _ 2 μ _ (f z) hμ
      have hsubμ : MemLp (fun y => f y - f z) 2 μ := hfμ.sub hcμ
      have hshift := setAverage_sub_const_of_memLp
        (cylinder_measure_ne_zero z hr) hμtop f hf (f z)
      have habs := setAverage_abs_le_setAverage_abs
        (cylinder_measure_ne_zero z hr) hμtop (fun y => f y - f z) hsubμ
      have hrewrite : campanatoAverages f z n - f z =
          ⨍ y in s, (f y - f z) ∂volume := by
        simpa [s, campanatoAverages, cylinderMean] using hshift.symm
      rw [hrewrite]
      exact habs
    have herr : Tendsto (fun n : ℕ =>
        |campanatoAverages f z n - f z|) atTop (𝓝 0) :=
      squeeze_zero hnonneg hbound hz
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa [Real.dist_eq] using herr
  have hrep := campanatoAverages_tendsto_representative hf hM
    (hcamp z hzDomain) ha
  exact tendsto_nhds_unique hrep hmean

theorem campanatoRepresentative_tail
    {f : ℝ × Vec 2 → ℝ} {z : ℝ × Vec 2} {a M : ℝ}
    (hf : MemLp f 2 volume) (hM : 0 ≤ M)
    (hcamp : ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess f z r ≤ M * r ^ (2 * a))
    (ha : 0 < a) (n : ℕ) :
    |campanatoRepresentative f z - campanatoAverages f z n| ≤
      campanatoConstant a * Real.sqrt M * campanatoScale n ^ a := by
  let d := fun k : ℕ => campanatoStepConstant a M * campanatoRatio a ^ k
  have hstep : ∀ k, dist (campanatoAverages f z k) (campanatoAverages f z (k + 1)) ≤ d k :=
    fun k => campanatoAverages_step hf hM hcamp k
  have hsum : Summable d := campanatoStep_summable ha
  have hlim := campanatoAverages_tendsto_representative hf hM hcamp ha
  have hbound := dist_le_tsum_of_dist_le_of_tendsto d hstep hsum hlim n
  have htail : (∑' m : ℕ, d (n + m)) =
      campanatoStepConstant a M * campanatoRatio a ^ n *
        (1 - campanatoRatio a)⁻¹ := by
    dsimp [d]
    calc
      (∑' m : ℕ, campanatoStepConstant a M * campanatoRatio a ^ (n + m)) =
          ∑' m : ℕ, (campanatoStepConstant a M * campanatoRatio a ^ n) *
            campanatoRatio a ^ m := by
        congr 1
        funext m
        rw [pow_add]
        ring
      _ = (campanatoStepConstant a M * campanatoRatio a ^ n) *
          (∑' m : ℕ, campanatoRatio a ^ m) := by
        exact (summable_geometric_of_lt_one campanatoRatio_pos.le
          (campanatoRatio_lt_one ha)).tsum_mul_left _
      _ = campanatoStepConstant a M * campanatoRatio a ^ n *
          (1 - campanatoRatio a)⁻¹ := by
        rw [tsum_geometric_of_lt_one campanatoRatio_pos.le (campanatoRatio_lt_one ha)]
  have hdist : dist (campanatoAverages f z n) (campanatoRepresentative f z) ≤
      campanatoStepConstant a M * campanatoRatio a ^ n *
        (1 - campanatoRatio a)⁻¹ := by
    rw [← htail]
    exact hbound
  rw [Real.dist_eq] at hdist
  have hcomm : |campanatoAverages f z n - campanatoRepresentative f z| =
      |campanatoRepresentative f z - campanatoAverages f z n| := abs_sub_comm _ _
  rw [hcomm] at hdist
  rw [campanatoConstant]
  have hscale := campanatoScale_rpow a n
  calc
    |campanatoRepresentative f z - campanatoAverages f z n| ≤
        8 * Real.sqrt M * (1 / 8 : ℝ) ^ a *
          ((1 / 2 : ℝ) ^ a) ^ n * (1 - (1 / 2 : ℝ) ^ a)⁻¹ := by
      simpa [campanatoRatio, campanatoStepConstant] using hdist
    _ = (8 / (1 - (1 / 2 : ℝ) ^ a)) *
          Real.sqrt M * campanatoScale n ^ a := by
      rw [hscale]
      field_simp

end AVRegularity.External.Campanato
end
