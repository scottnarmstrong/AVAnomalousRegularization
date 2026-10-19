-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.LocalEnergy.MolEnergy
import AVRegularity.Applications.LocalEnergy.FluxAux.Slice
public import Mathlib.MeasureTheory.Function.L2Space
import AVRegularity.Applications.LocalEnergy.DivFreeMollify.Slice

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology Convolution
namespace AVRegularity.Applications.LocalEnergy

/-! # Energy estimates for the mollified functions

A single mollified function with window kernel satisfies
`sup_{τ ∈ [a,b]} ∫ ζ² w(τ)² ≤ c ∫_{[a,b] × tsupport ζ} qd`, where `qd` is the quadratic density of
the mollified data (`energy_sup_estimate`). This is the key estimate for the uniform Cauchy
property of the time mollifications. -/

section
open AVRegularity.Applications

/-- Quadratic density of the data `(w, D, P, g)`. -/
def qd (w g : ℝ × Vec 2 → ℝ) (D P : ℝ × Vec 2 → Vec 2) (p : ℝ × Vec 2) : ℝ :=
  w p ^ 2 + D p 0 ^ 2 + D p 1 ^ 2 + P p 0 ^ 2 + P p 1 ^ 2 + g p ^ 2

theorem abs_mul_le_half_sq (x y : ℝ) : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]

theorem prod_bound (x y u Uu : ℝ) (hu : |u| ≤ Uu) : |x * (u * y)| ≤ Uu * ((x ^ 2 + y ^ 2) / 2) := by
  have h1 : |x * (u * y)| = |u| * |x * y| := by
    rw [abs_mul, abs_mul, abs_mul]; ring
  rw [h1]
  exact mul_le_mul hu (abs_mul_le_half_sq x y) (abs_nonneg _) ((abs_nonneg u).trans hu)

theorem abs_flux_le {ζ : Vec 2 → ℝ} {Z Zg : ℝ} (hZ : ∀ y, |ζ y| ≤ Z)
    (hZg : ∀ y i, |spGrad ζ y i| ≤ Zg) (w g : ℝ × Vec 2 → ℝ) (D P : ℝ × Vec 2 → Vec 2)
    (p : ℝ × Vec 2) :
    |fluxIntegrand ζ w P D g p| ≤ (Z ^ 2 + 2 * Z * Zg) * qd w g D P p := by
  have hZ0 : 0 ≤ Z := (abs_nonneg _).trans (hZ 0)
  have hZg0 : 0 ≤ Zg := (abs_nonneg _).trans (hZg 0 0)
  set a := ζ p.2 with ha
  have hsq : |a ^ 2| ≤ Z ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hZ _) 2
  have hc : ∀ i, |2 * a * spGrad ζ p.2 i| ≤ 2 * Z * Zg := by
    intro i
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul (hZ p.2) (hZg p.2 i) (abs_nonneg _) hZ0
    nlinarith
  have t1_0 := prod_bound (P p 0) (D p 0) (a ^ 2) (Z ^ 2) hsq
  have t1_1 := prod_bound (P p 1) (D p 1) (a ^ 2) (Z ^ 2) hsq
  have t2_0 := prod_bound (P p 0) (w p) (2 * a * spGrad ζ p.2 0) (2 * Z * Zg) (hc 0)
  have t2_1 := prod_bound (P p 1) (w p) (2 * a * spGrad ζ p.2 1) (2 * Z * Zg) (hc 1)
  have t3 := prod_bound (g p) (w p) (a ^ 2) (Z ^ 2) hsq
  have heq : fluxIntegrand ζ w P D g p =
      P p 0 * (a ^ 2 * D p 0) + P p 0 * (2 * a * spGrad ζ p.2 0 * w p) +
      (P p 1 * (a ^ 2 * D p 1) + P p 1 * (2 * a * spGrad ζ p.2 1 * w p)) -
      g p * (a ^ 2 * w p) := by
    simp only [fluxIntegrand, vecDot, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha]
    ring
  rw [heq]
  have h2 : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    simpa [sub_eq_add_neg] using abs_add_le x (-y)
  have h3 : ∀ x y z u : ℝ, |x + y + (z + u)| ≤ |x| + |y| + (|z| + |u|) := fun x y z u => by
    calc |x + y + (z + u)| ≤ |x + y| + |z + u| := abs_add_le _ _
      _ ≤ |x| + |y| + (|z| + |u|) := add_le_add (abs_add_le _ _) (abs_add_le _ _)
  refine (h2 _ _).trans ?_
  refine (add_le_add (h3 _ _ _ _) le_rfl).trans ?_
  unfold qd
  have hZ2 : 0 ≤ Z ^ 2 := sq_nonneg _
  have hZZ : 0 ≤ 2 * Z * Zg := by positivity
  nlinarith [mul_nonneg hZ2 (sq_nonneg (P p 0)), mul_nonneg hZ2 (sq_nonneg (P p 1)),
    mul_nonneg hZ2 (sq_nonneg (D p 0)), mul_nonneg hZ2 (sq_nonneg (D p 1)),
    mul_nonneg hZ2 (sq_nonneg (g p)), mul_nonneg hZ2 (sq_nonneg (w p)),
    mul_nonneg hZZ (sq_nonneg (P p 0)), mul_nonneg hZZ (sq_nonneg (P p 1)),
    mul_nonneg hZZ (sq_nonneg (w p))]


theorem sup_le_avg {a b : ℝ} (hab : a < b) {e : ℝ → ℝ} (he : ContinuousOn e (Set.Icc a b)) {Λ : ℝ}
    (hid : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, e t ≤ e s + Λ) :
    ∀ τ ∈ Set.Icc a b, e τ ≤ (∫ s in a..b, e s) / (b - a) + Λ := by
  intro τ hτ
  have hint : IntervalIntegrable e MeasureTheory.volume a b :=
    (he.mono (by rw [Set.uIcc_of_le hab.le])).intervalIntegrable
  have hle : ∫ s in a..b, e τ ≤ ∫ s in a..b, (e s + Λ) := by
    refine intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
      (hint.add intervalIntegrable_const) fun s hs => ?_
    exact hid s hs τ hτ
  rw [intervalIntegral.integral_add hint intervalIntegrable_const] at hle
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hle
  have hba : 0 < b - a := sub_pos.2 hab
  rw [div_add' _ _ _ hba.ne', le_div_iff₀ hba]
  nlinarith


theorem continuous_energy {ζ : Vec 2 → ℝ} (hζc : HasCompactSupport ζ) (hζ : Continuous ζ)
    {B : Set (Vec 2)} (hB : MeasurableSet B) (hζB : tsupport ζ ⊆ B) {w : ℝ × Vec 2 → ℝ}
    (hw : Continuous w) : Continuous fun τ => ∫ y in B, ζ y ^ 2 * w (τ, y) ^ 2 := by
  have hz : ∀ y, y ∉ tsupport ζ → ζ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have h1 : ∀ τ, (∫ y in B, ζ y ^ 2 * w (τ, y) ^ 2) =
      ∫ y in tsupport ζ, ζ y ^ 2 * w (τ, y) ^ 2 := by
    intro τ
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hB hζB fun y hy => ?_
    simp [hz y hy.2]
  simp only [h1]
  exact continuous_parametric_integral_of_continuous
    (f := fun τ y => ζ y ^ 2 * w (τ, y) ^ 2)
    (by
      have : Continuous fun q : ℝ × Vec 2 => ζ q.2 := hζ.comp continuous_snd
      show Continuous fun q : ℝ × Vec 2 => ζ q.2 ^ 2 * w (q.1, q.2) ^ 2
      fun_prop) hζc.isCompact

/-- The flux integral over a time slab is controlled by the quadratic density on the compact
region. -/
theorem flux_integral_le {ζ : Vec 2 → ℝ} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ)
    {B : Set (Vec 2)} (hB : MeasurableSet B) (hζB : tsupport ζ ⊆ B) {Z Zg : ℝ}
    (hZ : ∀ y, |ζ y| ≤ Z) (hZg : ∀ y i, |spGrad ζ y i| ≤ Zg)
    {w g : ℝ × Vec 2 → ℝ} {D P : ℝ × Vec 2 → Vec 2}
    (hw : Continuous w) (hP : ∀ i, Continuous fun p => P p i)
    (hD : ∀ i, Continuous fun p => D p i) (hg : Continuous g) {a b τ₁ τ₂ : ℝ}
    (h1 : a ≤ τ₁) (h2 : τ₂ ≤ b) :
    |∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ w P D g p| ≤
      (Z ^ 2 + 2 * Z * Zg) * ∫ p in Set.Icc a b ×ˢ tsupport ζ, qd w g D P p := by
  have hfc : Continuous (fluxIntegrand ζ w P D g) := continuous_flux hζ hw hP hD hg
  have hqc : Continuous (qd w g D P) := by
    have := fun i => hP i; have := fun i => hD i
    unfold qd; fun_prop
  have hRc : IsCompact (Set.Icc a b ×ˢ tsupport ζ) := isCompact_Icc.prod hζc
  have hint1 : IntegrableOn (fun p => |fluxIntegrand ζ w P D g p|) (Set.Icc a b ×ˢ tsupport ζ) :=
    (hfc.abs).continuousOn.integrableOn_compact hRc
  have hint2 : IntegrableOn (qd w g D P) (Set.Icc a b ×ˢ tsupport ζ) :=
    hqc.continuousOn.integrableOn_compact hRc
  calc |∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ w P D g p|
      ≤ ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, |fluxIntegrand ζ w P D g p| := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc τ₁ τ₂ ×ˢ B))
            (fluxIntegrand ζ w P D g)
    _ = ∫ p in Set.Ioc τ₁ τ₂ ×ˢ tsupport ζ, |fluxIntegrand ζ w P D g p| := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_Ioc.prod hB)
          (Set.prod_mono subset_rfl hζB) fun p hp => ?_
        rw [flux_zero_off p fun h => hp.2 ⟨hp.1.1, h⟩]; simp
    _ ≤ ∫ p in Set.Icc a b ×ˢ tsupport ζ, |fluxIntegrand ζ w P D g p| := by
        refine setIntegral_mono_set hint1 (Eventually.of_forall fun p => abs_nonneg _) ?_
        refine Eventually.of_forall fun p hp => ⟨⟨?_, ?_⟩, hp.2⟩
        · exact h1.trans hp.1.1.le
        · exact hp.1.2.trans h2
    _ ≤ ∫ p in Set.Icc a b ×ˢ tsupport ζ, (Z ^ 2 + 2 * Z * Zg) * qd w g D P p := by
        refine integral_mono hint1 (hint2.const_mul _) fun p => ?_
        exact abs_flux_le hZ hZg w g D P p
    _ = _ := integral_const_mul _ _


theorem integral_B_eq_T {ζ : Vec 2 → ℝ} {B : Set (Vec 2)} (hB : MeasurableSet B)
    (hζB : tsupport ζ ⊆ B) {f : Vec 2 → ℝ} (hf : ∀ y, y ∉ tsupport ζ → f y = 0) :
    ∫ y in B, f y = ∫ y in tsupport ζ, f y :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hB hζB fun y hy => hf y hy.2

theorem qd_nonneg (w g : ℝ × Vec 2 → ℝ) (D P : ℝ × Vec 2 → Vec 2) (p : ℝ × Vec 2) :
    0 ≤ qd w g D P p := by
  unfold qd; positivity

theorem energy_sup_estimate {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B) {U g : ℝ × Vec 2 → ℝ}
    {DU P : ℝ × Vec 2 → Vec 2} (h : WeakEq ta tb B U g DU P) {ζ : Vec 2 → ℝ}
    (hζ : IsSpTest B ζ) {K : ℝ × Vec 2 → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hKc : HasCompactSupport K) {a b : ℝ} (hab : a < b)
    (hwin : Window (Set.Ioo ta tb ×ˢ B) K (Set.Icc a b) (tsupport ζ)) {Z Zg : ℝ}
    (hZ : ∀ y, |ζ y| ≤ Z) (hZg : ∀ y i, |spGrad ζ y i| ≤ Zg) :
    ∀ τ ∈ Set.Icc a b,
      ∫ y in B, ζ y ^ 2 * (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) K (τ, y)) ^ 2 ≤
        (Z ^ 2 / (b - a) + 2 * (Z ^ 2 + 2 * Z * Zg)) *
          ∫ p in Set.Icc a b ×ˢ tsupport ζ,
            qd (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) K)
              (mollify ((Set.Ioo ta tb ×ˢ B).indicator g) K)
              (molVec (Set.Ioo ta tb ×ˢ B) DU K) (molVec (Set.Ioo ta tb ×ˢ B) P K) p := by
  intro τ hτ
  have hS : MeasurableSet (Set.Ioo ta tb ×ˢ B) := measurableSet_Ioo.prod hB.measurableSet
  have hζ1 : ContDiff ℝ 1 ζ := hζ.1.of_le (by exact_mod_cast le_top)
  set w := mollify ((Set.Ioo ta tb ×ˢ B).indicator U) K with hw
  set gK := mollify ((Set.Ioo ta tb ×ˢ B).indicator g) K with hgK
  set PK := molVec (Set.Ioo ta tb ×ˢ B) P K with hPK
  set DK := molVec (Set.Ioo ta tb ×ˢ B) DU K with hDK
  have hwc : Continuous w := mollify_continuous hK.continuous hKc (locallyIntegrable_indicator hS h.hU)
  have hgc : Continuous gK :=
    mollify_continuous hK.continuous hKc (locallyIntegrable_indicator hS h.hg)
  have hPc : ∀ i, Continuous fun p => PK p i := fun i =>
    mollify_continuous hK.continuous hKc (locallyIntegrable_indicator hS (h.hP i))
  have hDc : ∀ i, Continuous fun p => DK p i := fun i =>
    mollify_continuous hK.continuous hKc (locallyIntegrable_indicator hS (h.hDU i))
  have hqc : Continuous (qd w gK DK PK) := by
    have := fun i => hPc i; have := fun i => hDc i
    unfold qd; fun_prop
  set Q := ∫ p in Set.Icc a b ×ˢ tsupport ζ, qd w gK DK PK p with hQ
  have hRc : IsCompact (Set.Icc a b ×ˢ tsupport ζ) := isCompact_Icc.prod hζ.2.1
  have hQ0 : 0 ≤ Q := setIntegral_nonneg (isCompact_Icc.prod hζ.2.1).measurableSet
    fun p _ => qd_nonneg _ _ _ _ p
  set C := Z ^ 2 + 2 * Z * Zg with hC
  set e : ℝ → ℝ := fun τ => ∫ y in B, ζ y ^ 2 * w (τ, y) ^ 2 with he
  have hec : Continuous e := continuous_energy hζ.2.1 hζ.1.continuous hB.measurableSet hζ.2.2 hwc
  have hflux : ∀ s t, s ∈ Set.Icc a b → t ∈ Set.Icc a b → s ≤ t →
      |e t - e s| ≤ 2 * (C * Q) := by
    intro s t hs ht hst
    have hid := mollified_energy_identity hB h hζ hK hKc Set.ordConnected_Icc hwin hs ht hst
    have hb := flux_integral_le hζ1 hζ.2.1 hB.measurableSet hζ.2.2 hZ hZg hwc hPc hDc hgc
      hs.1 ht.2
    have : e t - e s = -2 * ∫ p in Set.Ioc s t ×ˢ B, fluxIntegrand ζ w PK DK gK p := hid
    rw [this, abs_mul]
    simp only [abs_neg, abs_two]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have hsup : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, e t ≤ e s + 2 * (C * Q) := by
    intro s hs t ht
    rcases le_total s t with hst | hts
    · have := hflux s t hs ht hst
      linarith [(abs_le.1 this).2]
    · have := hflux t s ht hs hts
      linarith [(abs_le.1 this).1]
  have havg := sup_le_avg hab hec.continuousOn hsup τ hτ
  set q : ℝ → ℝ := fun s => ∫ y in tsupport ζ, qd w gK DK PK (s, y) with hq
  have hqcont : Continuous q :=
    continuous_parametric_integral_of_continuous
      (f := fun s y => qd w gK DK PK (s, y)) (hqc.comp continuous_id) hζ.2.1.isCompact
  have hpt : ∀ s, e s ≤ Z ^ 2 * q s := by
    intro s
    have hz : ∀ y, y ∉ tsupport ζ → ζ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
    have hcs : Continuous fun y : Vec 2 => w (s, y) := hwc.comp (continuous_const.prodMk continuous_id)
    have hcq : Continuous fun y : Vec 2 => qd w gK DK PK (s, y) :=
      hqc.comp (continuous_const.prodMk continuous_id)
    simp only [he, hq]
    rw [integral_B_eq_T hB.measurableSet hζ.2.2 (f := fun y => ζ y ^ 2 * w (s, y) ^ 2)
      (fun y hy => by simp [hz y hy]), ← integral_const_mul]
    refine setIntegral_mono_on ?_ ?_ hζ.2.1.isCompact.measurableSet fun y _ => ?_
    · exact (((hζ.1.continuous.pow 2).mul (hcs.pow 2)).continuousOn).integrableOn_compact hζ.2.1.isCompact
    · exact (hcq.const_mul _).continuousOn.integrableOn_compact hζ.2.1.isCompact
    · have h1 : ζ y ^ 2 ≤ Z ^ 2 := by
        rw [← sq_abs (ζ y)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hZ y) 2
      have h2 : w (s, y) ^ 2 ≤ qd w gK DK PK (s, y) := by
        unfold qd
        nlinarith [sq_nonneg (DK (s, y) 0), sq_nonneg (DK (s, y) 1), sq_nonneg (PK (s, y) 0),
          sq_nonneg (PK (s, y) 1), sq_nonneg (gK (s, y))]
      calc ζ y ^ 2 * w (s, y) ^ 2 ≤ Z ^ 2 * w (s, y) ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ ≤ Z ^ 2 * qd w gK DK PK (s, y) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hQeq : ∫ s in a..b, q s = Q := by
    rw [hQ, Measure.volume_eq_prod, setIntegral_prod _ (by
      rw [← Measure.volume_eq_prod]; exact hqc.continuousOn.integrableOn_compact hRc),
      intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]
  have hint : ∫ s in a..b, e s ≤ Z ^ 2 * Q := by
    calc ∫ s in a..b, e s ≤ ∫ s in a..b, Z ^ 2 * q s :=
          intervalIntegral.integral_mono_on hab.le (hec.intervalIntegrable _ _)
            ((hqcont.const_mul _).intervalIntegrable _ _) fun s _ => hpt s
      _ = Z ^ 2 * Q := by rw [intervalIntegral.integral_const_mul, hQeq]
  have hba : 0 < b - a := sub_pos.2 hab
  calc e τ ≤ (∫ s in a..b, e s) / (b - a) + 2 * (C * Q) := by linarith [havg]
    _ ≤ Z ^ 2 * Q / (b - a) + 2 * (C * Q) := by
        gcongr
    _ = (Z ^ 2 / (b - a) + 2 * C) * Q := by ring
end

/-! # Uniform Cauchy property of the time mollifications

For a mollifier sequence `k n` whose translated supports stay inside `(ta,tb) × B` on `[a,b]`,
the functions `τ ↦ ζ · mollify (1_S U) (k n) (τ,·)` are uniformly Cauchy in `L²` on `[a,b]`
(`cauchy_sup`), by the energy estimate applied to the difference of two mollifications. -/

section
open AVRegularity.Applications
open scoped ENNReal

/-- A mollifier sequence: smooth compactly supported kernels approximating the identity in `L²`. -/
structure MollSeq (k : ℕ → ℝ × Vec 2 → ℝ) : Prop where
  contDiff : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (k n)
  compact : ∀ n, HasCompactSupport (k n)
  conv : ∀ f : ℝ × Vec 2 → ℝ, MemLp f 2 volume →
    Tendsto (fun n => eLpNorm (fun x => mollify f (k n) x - f x) 2 volume) atTop (𝓝 0)

theorem memLp_mollify_sub_restrict {k : ℕ → ℝ × Vec 2 → ℝ} (hk : MollSeq k)
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 volume) {R : Set (ℝ × Vec 2)} (hRc : IsCompact R) (n : ℕ) :
    MemLp (fun p => mollify f (k n) p - f p) 2 (volume.restrict R) := by
  have : IsFiniteMeasure (volume.restrict R) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hRc.measure_lt_top⟩
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hcont : Continuous (mollify f (k n)) :=
    mollify_continuous (hk.contDiff n).continuous (hk.compact n) hloc
  have h1 : MemLp (mollify f (k n)) 2 (volume.restrict R) := by
    obtain ⟨C, hC⟩ := hRc.exists_bound_of_continuousOn hcont.continuousOn
    exact MemLp.of_bound hcont.aestronglyMeasurable C
      ((ae_restrict_iff' hRc.measurableSet).2 (Eventually.of_forall hC))
  exact h1.sub (hf.restrict R)

theorem tendsto_setIntegral_sq_mollify {k : ℕ → ℝ × Vec 2 → ℝ} (hk : MollSeq k)
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 volume) {R : Set (ℝ × Vec 2)} (hRc : IsCompact R) :
    Tendsto (fun n => ∫ p in R, (mollify f (k n) p - f p) ^ 2) atTop (𝓝 0) := by
  set μ : Measure (ℝ × Vec 2) := volume.restrict R with hμ
  have hmem : ∀ n, MemLp (fun p => mollify f (k n) p - f p) 2 μ :=
    memLp_mollify_sub_restrict hk hf hRc
  have hlim : Tendsto (fun n => eLpNorm (fun p => (mollify f (k n) p - f p) - (0 : ℝ × Vec 2 → ℝ) p)
      2 μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hk.conv f hf) (fun n => bot_le) ?_
    intro n
    simpa using eLpNorm_mono_measure (fun p => mollify f (k n) p - f p)
      (Measure.restrict_le_self (μ := volume) (s := R)) (p := 2)
  have := tendsto_integral_mul_of_L2 (μ := μ) (fn := fun n p => mollify f (k n) p - f p)
    (hn := fun n p => mollify f (k n) p - f p) (f := (0 : ℝ × Vec 2 → ℝ)) (h := (0 : ℝ × Vec 2 → ℝ))
    hmem hmem MemLp.zero MemLp.zero hlim hlim
  simpa [sq] using this


theorem sq_sub_le_two (a b c : ℝ) : (a - b) ^ 2 ≤ 2 * (a - c) ^ 2 + 2 * (b - c) ^ 2 := by
  nlinarith [sq_nonneg (a + b - 2 * c)]

theorem exists_bounds {ζ : Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) :
    ∃ Z Zg : ℝ, 0 ≤ Z ∧ 0 ≤ Zg ∧ (∀ y, |ζ y| ≤ Z) ∧ (∀ y i, |spGrad ζ y i| ≤ Zg) := by
  obtain ⟨Z, hZ⟩ := hζc.exists_bound_of_continuous hζ.continuous
  have hd : ∀ i : Fin 2, ∃ C, ∀ y, ‖fderiv ℝ ζ y (basisVec i)‖ ≤ C := fun i => by
    have hc : Continuous fun y => fderiv ℝ ζ y (basisVec i) :=
      (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).continuous.comp
        ((hζ.of_le (by exact_mod_cast le_top)).continuous_fderiv one_ne_zero)
    have hs : HasCompactSupport fun y => fderiv ℝ ζ y (basisVec i) :=
      (hζc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) (by simp)
    exact hs.exists_bound_of_continuous hc
  obtain ⟨C0, hC0⟩ := hd 0
  obtain ⟨C1, hC1⟩ := hd 1
  refine ⟨max Z 0, max (max C0 C1) 0, le_max_right _ _, le_max_right _ _, fun y => ?_, fun y i => ?_⟩
  · have := hZ y; rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · fin_cases i
    · have := hC0 y; rw [Real.norm_eq_abs] at this
      exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
    · have := hC1 y; rw [Real.norm_eq_abs] at this
      exact this.trans ((le_max_right _ _).trans (le_max_left _ _))


theorem tendsto_integral_add_fun {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : ℕ → X → ℝ} {a b : ℝ} (hf : ∀ n, Integrable (f n) μ) (hg : ∀ n, Integrable (g n) μ)
    (h1 : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 a))
    (h2 : Tendsto (fun n => ∫ x, g n x ∂μ) atTop (𝓝 b)) :
    Tendsto (fun n => ∫ x, (f n x + g n x) ∂μ) atTop (𝓝 (a + b)) := by
  simp_rw [integral_add (hf _) (hg _)]
  exact h1.add h2

/-- Defect of the mollified data on a compact region. -/
def defectDensity (S : Set (ℝ × Vec 2)) (U g : ℝ × Vec 2 → ℝ) (DU P : ℝ × Vec 2 → Vec 2)
    (K : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  (mollify (S.indicator U) K p - S.indicator U p) ^ 2 +
  (molVec S DU K p 0 - S.indicator (fun q => DU q 0) p) ^ 2 +
  (molVec S DU K p 1 - S.indicator (fun q => DU q 1) p) ^ 2 +
  (molVec S P K p 0 - S.indicator (fun q => P q 0) p) ^ 2 +
  (molVec S P K p 1 - S.indicator (fun q => P q 1) p) ^ 2 +
  (mollify (S.indicator g) K p - S.indicator g p) ^ 2


theorem tendsto_integral_six {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f1 f2 f3 f4 f5 f6 : ℕ → X → ℝ}
    (i1 : ∀ n, Integrable (f1 n) μ) (i2 : ∀ n, Integrable (f2 n) μ)
    (i3 : ∀ n, Integrable (f3 n) μ) (i4 : ∀ n, Integrable (f4 n) μ)
    (i5 : ∀ n, Integrable (f5 n) μ) (i6 : ∀ n, Integrable (f6 n) μ)
    (t1 : Tendsto (fun n => ∫ x, f1 n x ∂μ) atTop (𝓝 0))
    (t2 : Tendsto (fun n => ∫ x, f2 n x ∂μ) atTop (𝓝 0))
    (t3 : Tendsto (fun n => ∫ x, f3 n x ∂μ) atTop (𝓝 0))
    (t4 : Tendsto (fun n => ∫ x, f4 n x ∂μ) atTop (𝓝 0))
    (t5 : Tendsto (fun n => ∫ x, f5 n x ∂μ) atTop (𝓝 0))
    (t6 : Tendsto (fun n => ∫ x, f6 n x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (f1 n x + f2 n x + f3 n x + f4 n x + f5 n x + f6 n x) ∂μ)
      atTop (𝓝 0) := by
  have h12 := tendsto_integral_add_fun i1 i2 t1 t2
  have h123 := tendsto_integral_add_fun (fun n => (i1 n).add (i2 n)) i3 (f := fun n x => f1 n x + f2 n x) h12 t3
  have h1234 := tendsto_integral_add_fun (fun n => ((i1 n).add (i2 n)).add (i3 n)) i4
    (f := fun n x => f1 n x + f2 n x + f3 n x) h123 t4
  have h12345 := tendsto_integral_add_fun (fun n => (((i1 n).add (i2 n)).add (i3 n)).add (i4 n)) i5
    (f := fun n x => f1 n x + f2 n x + f3 n x + f4 n x) h1234 t5
  have h6 := tendsto_integral_add_fun
    (fun n => ((((i1 n).add (i2 n)).add (i3 n)).add (i4 n)).add (i5 n)) i6
    (f := fun n x => f1 n x + f2 n x + f3 n x + f4 n x + f5 n x) h12345 t6
  simpa using h6

theorem tendsto_defect {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B) {U g : ℝ × Vec 2 → ℝ}
    {DU P : ℝ × Vec 2 → Vec 2} (h : WeakEq ta tb B U g DU P) {k : ℕ → ℝ × Vec 2 → ℝ}
    (hk : MollSeq k) {R : Set (ℝ × Vec 2)} (hRc : IsCompact R) :
    (∀ n, IntegrableOn (defectDensity (Set.Ioo ta tb ×ˢ B) U g DU P (k n)) R) ∧
    Tendsto (fun n => ∫ p in R, defectDensity (Set.Ioo ta tb ×ˢ B) U g DU P (k n) p) atTop (𝓝 0) := by
  have hS : MeasurableSet (Set.Ioo ta tb ×ˢ B) := measurableSet_Ioo.prod hB.measurableSet
  have mU : MemLp ((Set.Ioo ta tb ×ˢ B).indicator U) 2 volume := (memLp_indicator_iff_restrict hS).2 h.hU
  have mg : MemLp ((Set.Ioo ta tb ×ˢ B).indicator g) 2 volume := (memLp_indicator_iff_restrict hS).2 h.hg
  have mD : ∀ i, MemLp ((Set.Ioo ta tb ×ˢ B).indicator (fun q => DU q i)) 2 volume := fun i =>
    (memLp_indicator_iff_restrict hS).2 (h.hDU i)
  have mP : ∀ i, MemLp ((Set.Ioo ta tb ×ˢ B).indicator (fun q => P q i)) 2 volume := fun i =>
    (memLp_indicator_iff_restrict hS).2 (h.hP i)
  have iU := fun n => (memLp_mollify_sub_restrict hk mU hRc n).integrable_sq
  have ig := fun n => (memLp_mollify_sub_restrict hk mg hRc n).integrable_sq
  have iD := fun i n => (memLp_mollify_sub_restrict hk (mD i) hRc n).integrable_sq
  have iP := fun i n => (memLp_mollify_sub_restrict hk (mP i) hRc n).integrable_sq
  have tU := tendsto_setIntegral_sq_mollify hk mU hRc
  have tg := tendsto_setIntegral_sq_mollify hk mg hRc
  have tD := fun i => tendsto_setIntegral_sq_mollify hk (mD i) hRc
  have tP := fun i => tendsto_setIntegral_sq_mollify hk (mP i) hRc
  constructor
  · intro n
    unfold defectDensity molVec
    exact ((((((iU n).add (iD 0 n)).add (iD 1 n)).add (iP 0 n)).add (iP 1 n)).add (ig n))
  · exact tendsto_integral_six iU (iD 0) (iD 1) (iP 0) (iP 1) ig tU (tD 0) (tD 1) (tP 0) (tP 1) tg

theorem qd_sub_le_defect {S : Set (ℝ × Vec 2)} {U g : ℝ × Vec 2 → ℝ} {DU P : ℝ × Vec 2 → Vec 2}
    {f₁ f₂ : ℝ × Vec 2 → ℝ} (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hc₁ : HasCompactSupport f₁) (hc₂ : HasCompactSupport f₂)
    (hU : LocallyIntegrable (S.indicator U) volume) (hg : LocallyIntegrable (S.indicator g) volume)
    (hD : ∀ i : Fin 2, LocallyIntegrable (S.indicator (fun q => DU q i)) volume)
    (hP : ∀ i : Fin 2, LocallyIntegrable (S.indicator (fun q => P q i)) volume)
    (p : ℝ × Vec 2) :
    qd (mollify (S.indicator U) (f₁ - f₂)) (mollify (S.indicator g) (f₁ - f₂))
      (molVec S DU (f₁ - f₂)) (molVec S P (f₁ - f₂)) p ≤
    2 * defectDensity S U g DU P f₁ p + 2 * defectDensity S U g DU P f₂ p := by
  have e : ∀ F : ℝ × Vec 2 → ℝ, LocallyIntegrable F volume →
      mollify F (f₁ - f₂) p = mollify F f₁ p - mollify F f₂ p := fun F hF => by
    rw [mollify_sub_right hf₁ hf₂ hc₁ hc₂ hF]; rfl
  unfold qd defectDensity molVec
  simp only [e _ hU, e _ hg, e _ (hD 0), e _ (hD 1), e _ (hP 0), e _ (hP 1)]
  have := fun a b c => sq_sub_le_two a b c
  have h1 := this (mollify (S.indicator U) f₁ p) (mollify (S.indicator U) f₂ p) (S.indicator U p)
  have h2 := this (mollify (S.indicator fun q => DU q 0) f₁ p) (mollify (S.indicator fun q => DU q 0) f₂ p) (S.indicator (fun q => DU q 0) p)
  have h3 := this (mollify (S.indicator fun q => DU q 1) f₁ p) (mollify (S.indicator fun q => DU q 1) f₂ p) (S.indicator (fun q => DU q 1) p)
  have h4 := this (mollify (S.indicator fun q => P q 0) f₁ p) (mollify (S.indicator fun q => P q 0) f₂ p) (S.indicator (fun q => P q 0) p)
  have h5 := this (mollify (S.indicator fun q => P q 1) f₁ p) (mollify (S.indicator fun q => P q 1) f₂ p) (S.indicator (fun q => P q 1) p)
  have h6 := this (mollify (S.indicator g) f₁ p) (mollify (S.indicator g) f₂ p) (S.indicator g p)
  linarith

theorem cauchy_sup {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B) {U g : ℝ × Vec 2 → ℝ}
    {DU P : ℝ × Vec 2 → Vec 2} (h : WeakEq ta tb B U g DU P) {ζ : Vec 2 → ℝ}
    (hζ : IsSpTest B ζ) {k : ℕ → ℝ × Vec 2 → ℝ} (hk : MollSeq k) {a b : ℝ} (hab : a < b)
    {N0 : ℕ} (hwin : ∀ n ≥ N0, Window (Set.Ioo ta tb ×ˢ B) (k n) (Set.Icc a b) (tsupport ζ)) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ τ ∈ Set.Icc a b,
      ∫ y in B, (ζ y * mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k n) (τ, y) -
        ζ y * mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k m) (τ, y)) ^ 2 ≤ ε := by
  intro ε hε
  have hS : MeasurableSet (Set.Ioo ta tb ×ˢ B) := measurableSet_Ioo.prod hB.measurableSet
  obtain ⟨Z, Zg, hZ0, hZg0, hZ, hZg⟩ := exists_bounds hζ.1 hζ.2.1
  set R := Set.Icc a b ×ˢ tsupport ζ with hR
  have hRc : IsCompact R := isCompact_Icc.prod hζ.2.1
  obtain ⟨hint, hlim⟩ := tendsto_defect hB h hk hRc
  set c : ℝ := Z ^ 2 / (b - a) + 2 * (Z ^ 2 + 2 * Z * Zg) with hc
  have hba : 0 < b - a := sub_pos.2 hab
  have hc0 : 0 ≤ c := by positivity
  set η : ℝ := ε / (4 * (c + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.1 hlim) η hη0
  refine ⟨max N0 N1, fun n hn m hm τ hτ => ?_⟩
  have hn0 : N0 ≤ n := (le_max_left _ _).trans hn
  have hm0 : N0 ≤ m := (le_max_left _ _).trans hm
  have hδn : ∫ p in R, defectDensity (Set.Ioo ta tb ×ˢ B) U g DU P (k n) p < η := by
    have := hN1 n ((le_max_right _ _).trans hn)
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hδm : ∫ p in R, defectDensity (Set.Ioo ta tb ×ˢ B) U g DU P (k m) p < η := by
    have := hN1 m ((le_max_right _ _).trans hm)
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hlocU := locallyIntegrable_indicator hS h.hU
  have hlocg := locallyIntegrable_indicator hS h.hg
  have hlocD := fun i => locallyIntegrable_indicator hS (h.hDU i)
  have hlocP := fun i => locallyIntegrable_indicator hS (h.hP i)
  -- the difference kernel
  set κ : ℝ × Vec 2 → ℝ := k n - k m with hκ
  have hκd : ContDiff ℝ (⊤ : ℕ∞) κ := (hk.contDiff n).sub (hk.contDiff m)
  have hκc : HasCompactSupport κ := (hk.compact n).sub (hk.compact m)
  have hwκ : Window (Set.Ioo ta tb ×ˢ B) κ (Set.Icc a b) (tsupport ζ) := by
    intro σ hσ y hy q hq
    have := tsupport_sub (k n) (k m) hq
    rcases this with h1 | h1
    · exact hwin n hn0 σ hσ y hy q h1
    · exact hwin m hm0 σ hσ y hy q h1
  have hest := energy_sup_estimate hB h hζ hκd hκc hab hwκ hZ hZg τ hτ
  -- bound the right side
  have hqd : ∫ p in R, qd (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) κ)
        (mollify ((Set.Ioo ta tb ×ˢ B).indicator g) κ) (molVec (Set.Ioo ta tb ×ˢ B) DU κ)
        (molVec (Set.Ioo ta tb ×ˢ B) P κ) p ≤
      2 * (∫ p in R, defectDensity (Set.Ioo ta tb ×ˢ B) U g DU P (k n) p) +
        2 * ∫ p in R, defectDensity (Set.Ioo ta tb ×ˢ B) U g DU P (k m) p := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hint n).const_mul 2)
      ((hint m).const_mul 2)]
    refine setIntegral_mono_on ?_ (((hint n).const_mul 2).add ((hint m).const_mul 2))
      hRc.measurableSet fun p _ => ?_
    · have hc1 : ∀ F : ℝ × Vec 2 → ℝ, LocallyIntegrable F volume → Continuous (mollify F κ) :=
        fun F hF => mollify_continuous hκd.continuous hκc hF
      have hqc : Continuous (qd (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) κ)
          (mollify ((Set.Ioo ta tb ×ˢ B).indicator g) κ) (molVec (Set.Ioo ta tb ×ˢ B) DU κ)
          (molVec (Set.Ioo ta tb ×ˢ B) P κ)) := by
        have := hc1 _ hlocU; have := hc1 _ hlocg
        have := fun i => hc1 _ (hlocD i); have := fun i => hc1 _ (hlocP i)
        unfold qd molVec; fun_prop
      exact hqc.continuousOn.integrableOn_compact hRc
    · exact qd_sub_le_defect (hk.contDiff n).continuous (hk.contDiff m).continuous (hk.compact n)
        (hk.compact m) hlocU hlocg hlocD hlocP p
  have hweq : ∀ y, (ζ y * mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k n) (τ, y) -
        ζ y * mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k m) (τ, y)) ^ 2 =
      ζ y ^ 2 * (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) κ (τ, y)) ^ 2 := by
    intro y
    rw [hκ, mollify_sub_right (hk.contDiff n).continuous (hk.contDiff m).continuous (hk.compact n)
      (hk.compact m) hlocU]
    simp only [Pi.sub_apply]
    ring
  simp_rw [hweq]
  refine hest.trans ?_
  have hQ : 2 * (∫ p in R, defectDensity (Set.Ioo ta tb ×ˢ B) U g DU P (k n) p) +
      2 * ∫ p in R, defectDensity (Set.Ioo ta tb ×ˢ B) U g DU P (k m) p ≤ 4 * η := by
    linarith
  calc c * ∫ p in R, qd _ _ _ _ p ≤ c * (4 * η) :=
        mul_le_mul_of_nonneg_left (hqd.trans hQ) hc0
    _ = ε * (c / (c + 1)) := by rw [hη]; field_simp
    _ ≤ ε * 1 := by
        gcongr
        rw [div_le_one (by positivity)]
        linarith
    _ = ε := mul_one ε
end

end AVRegularity.Applications.LocalEnergy
end
end
end

section
public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
open AVRegularity.Applications.LocalEnergy.Moll AVRegularity.Applications.LocalEnergy.Flux
namespace AVRegularity.Applications

/-! # The flux form of the skew-drift equation

For a weak solution of `∂τU - div((I+K)∇U) + d·∇U = 0` in `Q₁` with `d` divergence free, the term
`∫∫ (d·∇U) φ` can be rewritten as `-∬ (U - c) d·∇φ`, so that the weak formulation holds with flux `(I+K)∇U - (U - c) d`. -/

theorem skewDrift_flux_form {K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {d : ℝ × Vec 2 → Vec 2}
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2} {kK kd : ℝ}
    (hKm : ∀ i j : Fin 2, AEStronglyMeasurable (fun p => K p i j) (volume.restrict (openCyl 0 1)))
    (hdm : ∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1)))
    (hbound : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)),
      (∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ kK ^ 2 * vecNormSq e) ∧ vecNormSq (d p) ≤ kd ^ 2)
    (hdiv : IsDivFreeQ1 d) (hU : IsEnergyClassQ1 U DU) (hw : IsSkewDriftWeak K d U DU)
    (c : ℝ) (φ : ℝ × Vec 2 → ℝ) (hφ : IsSTTest (openCyl 0 1) φ) :
    ∫ p in openCyl 0 1, (-(U p * stTimeDeriv φ p)
      + vecDot ((1 + K p).mulVec (DU p) - (U p - c) • d p) (stSpaceGrad φ p)) = 0 := by
  obtain ⟨hU2, hDU2, hweak, -⟩ := hU
  obtain ⟨iT1, iT2, iT3, iT4⟩ := flux_terms_integrable hKm hdm hbound hU2 hDU2 c hφ
  have hw' := hw φ hφ
  have hbd : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)), vecNormSq (d p) ≤ kd ^ 2 :=
    hbound.mono fun p hp => hp.2
  -- Fubini: the integral of `(d·DU) φ + (U - c) d·∇φ` vanishes
  have hF : ∫ p in openCyl 0 1, (vecDot (d p) (DU p) * φ p +
      (U p - c) * vecDot (d p) (stSpaceGrad φ p)) = 0 := by
    have iF : Integrable (fun p => vecDot (d p) (DU p) * φ p +
        (U p - c) * vecDot (d p) (stSpaceGrad φ p)) (volume.restrict (openCyl 0 1)) :=
      iT3.add iT4
    rw [restrict_openCyl] at iF ⊢
    rw [integral_prod _ iF]
    refine integral_eq_zero_of_ae ?_
    have hsU := ae_slice_memLp hU2
    have hs0 := ae_slice_memLp (hDU2 0)
    have hs1 := ae_slice_memLp (hDU2 1)
    have hdd := divFree_integral_grad hdm hbd hdiv
    filter_upwards [hsU, hs0, hs1, hweak, hdd] with τ a0 a1 a2 a3 a4
    exact flux_slice_identity c hφ a0 (fun i => by fin_cases i <;> assumption) a3 a4
  have e : (fun p => -(U p * stTimeDeriv φ p)
      + vecDot ((1 + K p).mulVec (DU p) - (U p - c) • d p) (stSpaceGrad φ p)) =
      fun p => (-(U p * stTimeDeriv φ p) + vecDot ((1 + K p).mulVec (DU p)) (stSpaceGrad φ p)
        + vecDot (d p) (DU p) * φ p) - (vecDot (d p) (DU p) * φ p +
          (U p - c) * vecDot (d p) (stSpaceGrad φ p)) := by
    ext p
    simp only [vecDot, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have iA : Integrable (fun p => -(U p * stTimeDeriv φ p)
      + vecDot ((1 + K p).mulVec (DU p)) (stSpaceGrad φ p) + vecDot (d p) (DU p) * φ p)
      (volume.restrict (openCyl 0 1)) := (iT1.add iT2).add iT3
  have iB : Integrable (fun p => vecDot (d p) (DU p) * φ p +
      (U p - c) * vecDot (d p) (stSpaceGrad φ p)) (volume.restrict (openCyl 0 1)) :=
    iT3.add iT4
  rw [e, integral_sub iA iB, hw', hF]
  simp

end AVRegularity.Applications
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology Convolution
namespace AVRegularity.Applications.LocalEnergy

/-! # The cutoff-weighted slices as `L²(B)`-valued functions of time

`phiLp B ζ w τ` is the class of `ζ · w(τ, ·)` in `L²(B)`; `dist_phiLp_sq` computes distances by
the integral formula, and `continuous_phiLp` shows continuity in `τ` for continuous `w`. -/

section
open AVRegularity.Applications
open scoped ENNReal

theorem inner_toLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx1 hx2
  rw [hx1, hx2]
  simp [mul_comm]

theorem dist_toLp_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    dist (hf.toLp f) (hg.toLp g) ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [dist_eq_norm, ← MemLp.toLp_sub hf hg]
  have hfg : MemLp (f - g) 2 μ := hf.sub hg
  rw [← real_inner_self_eq_norm_sq, inner_toLp hfg hfg]
  simp [sq]

theorem memLp_phi {ζ : Vec 2 → ℝ} (hζ : Continuous ζ) (hζc : HasCompactSupport ζ)
    {w : ℝ × Vec 2 → ℝ} (hw : Continuous w) (τ : ℝ) (μ : Measure (Vec 2))
    [IsFiniteMeasureOnCompacts μ] : MemLp (fun y => ζ y * w (τ, y)) 2 μ := by
  refine Continuous.memLp_of_hasCompactSupport (hζ.mul (hw.comp (continuous_const.prodMk continuous_id))) ?_
  refine HasCompactSupport.intro hζc fun y hy => ?_
  simp [image_eq_zero_of_notMem_tsupport hy]

open Classical in
/-- The cutoff-weighted slice `ζ · w(τ,·)` as an element of `L²(B)` (zero if not in `L²`). -/
def phiLp (B : Set (Vec 2)) (ζ : Vec 2 → ℝ) (w : ℝ × Vec 2 → ℝ) (τ : ℝ) :
    Lp ℝ 2 (volume.restrict B) :=
  if h : MemLp (fun y => ζ y * w (τ, y)) 2 (volume.restrict B) then h.toLp _ else 0

theorem phiLp_eq {B : Set (Vec 2)} {ζ : Vec 2 → ℝ} {w : ℝ × Vec 2 → ℝ} {τ : ℝ}
    (h : MemLp (fun y => ζ y * w (τ, y)) 2 (volume.restrict B)) :
    phiLp B ζ w τ = h.toLp _ := by simp [phiLp, h]

theorem dist_phiLp_sq {ζ : Vec 2 → ℝ} {B : Set (Vec 2)} (hB : MeasurableSet B)
    (hζB : tsupport ζ ⊆ B) (hζ : Continuous ζ) (hζc : HasCompactSupport ζ)
    {w w' : ℝ × Vec 2 → ℝ} (hw : Continuous w) (hw' : Continuous w') (τ τ' : ℝ) :
    dist (phiLp B ζ w τ) (phiLp B ζ w' τ') ^ 2 =
      ∫ y in tsupport ζ, (ζ y * w (τ, y) - ζ y * w' (τ', y)) ^ 2 := by
  rw [phiLp_eq (memLp_phi hζ hζc hw τ _), phiLp_eq (memLp_phi hζ hζc hw' τ' _), dist_toLp_sq]
  refine integral_B_eq_T hB hζB fun y hy => ?_
  simp [image_eq_zero_of_notMem_tsupport hy]

theorem continuous_phiLp {ζ : Vec 2 → ℝ} {B : Set (Vec 2)} (hB : MeasurableSet B)
    (hζB : tsupport ζ ⊆ B) (hζ : Continuous ζ) (hζc : HasCompactSupport ζ)
    {w : ℝ × Vec 2 → ℝ} (hw : Continuous w) : Continuous (phiLp B ζ w) := by
  rw [continuous_iff_continuousAt]
  intro τ
  have hG : Continuous fun σ : ℝ => ∫ y in tsupport ζ, (ζ y * w (σ, y) - ζ y * w (τ, y)) ^ 2 := by
    refine continuous_parametric_integral_of_continuous
      (f := fun σ y => (ζ y * w (σ, y) - ζ y * w (τ, y)) ^ 2) ?_ hζc.isCompact
    show Continuous fun q : ℝ × Vec 2 => (ζ q.2 * w (q.1, q.2) - ζ q.2 * w (τ, q.2)) ^ 2
    have h1 : Continuous fun q : ℝ × Vec 2 => ζ q.2 := hζ.comp continuous_snd
    have h2 : Continuous fun q : ℝ × Vec 2 => w (τ, q.2) := hw.comp (by fun_prop)
    fun_prop
  have hs : Tendsto (fun σ => Real.sqrt (∫ y in tsupport ζ, (ζ y * w (σ, y) - ζ y * w (τ, y)) ^ 2))
      (𝓝 τ) (𝓝 0) := by
    have h2 := (Real.continuous_sqrt.comp hG).tendsto τ
    have h3 : (Real.sqrt ∘ fun σ : ℝ => ∫ y in tsupport ζ, (ζ y * w (σ, y) - ζ y * w (τ, y)) ^ 2) τ
        = 0 := by simp
    rw [h3] at h2
    exact h2
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine hs.congr fun σ => ?_
  rw [← dist_phiLp_sq hB hζB hζ hζc hw hw σ τ]
  exact (Real.sqrt_sq dist_nonneg)
end

/-! # Convergence of the flux integrals

If the mollified data converge in `L²`, the flux integrals over a slab converge
(`tendsto_flux_integral`); this passes the mollified energy identity to the limit. -/

section
open AVRegularity.Applications
open scoped ENNReal

theorem tendsto_weighted_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ : α → ℝ}
    (hφm : Measurable φ) {C : ℝ} (hφ : ∀ x, |φ x| ≤ C) {fn hn : ℕ → α → ℝ} {f h : α → ℝ}
    (hfn : ∀ n, MemLp (fn n) 2 μ) (hhn : ∀ n, MemLp (hn n) 2 μ) (hf : MemLp f 2 μ)
    (hh : MemLp h 2 μ)
    (hf_lim : Tendsto (fun n => eLpNorm (fun x => fn n x - f x) 2 μ) atTop (𝓝 0))
    (hh_lim : Tendsto (fun n => eLpNorm (fun x => hn n x - h x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, φ x * (fn n x * hn n x) ∂μ) atTop (𝓝 (∫ x, φ x * (f x * h x) ∂μ)) := by
  have hmem : ∀ (u : α → ℝ), MemLp u 2 μ → MemLp (fun x => φ x * u x) 2 μ := by
    intro u hu
    refine hu.of_le_mul (c := C) (hφm.aestronglyMeasurable.mul hu.aestronglyMeasurable) ?_
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hφ x) (abs_nonneg _) |>.trans_eq' rfl
  have hlim' : Tendsto (fun n => eLpNorm (fun x => φ x * fn n x - φ x * f x) 2 μ) atTop (𝓝 0) := by
    have hb : ∀ n, eLpNorm (fun x => φ x * fn n x - φ x * f x) 2 μ ≤
        ENNReal.ofReal C * eLpNorm (fun x => fn n x - f x) 2 μ := fun n => by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ (Eventually.of_forall fun x => ?_) 2
      · exact ((hmem _ (hfn n)).sub (hmem _ hf)).aestronglyMeasurable
      · rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hφ x) (abs_nonneg _) |>.trans_eq' rfl
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le) hb
    simpa using ENNReal.Tendsto.const_mul hf_lim (Or.inr ENNReal.ofReal_ne_top)
  have := tendsto_integral_mul_of_L2 (μ := μ) (fn := fun n x => φ x * fn n x) (hn := hn)
    (f := fun x => φ x * f x) (h := h) (fun n => hmem _ (hfn n)) hhn (hmem _ hf) hh hlim' hh_lim
  simpa [mul_assoc] using this

theorem integrable_weighted_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ : α → ℝ}
    (hφm : Measurable φ) {C : ℝ} (hφ : ∀ x, |φ x| ≤ C) {f h : α → ℝ}
    (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) : Integrable (fun x => φ x * (f x * h x)) μ := by
  have hmem : MemLp (fun x => φ x * f x) 2 μ := by
    refine hf.of_le_mul (c := C) (hφm.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hφ x) (abs_nonneg _) |>.trans_eq' rfl
  exact (hmem.integrable_mul hh).congr (Eventually.of_forall fun x => by simp [mul_assoc])

theorem tendsto_flux_abstract {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ₁ φ₂ φ₃ : α → ℝ} (m₁ : Measurable φ₁) (m₂ : Measurable φ₂) (m₃ : Measurable φ₃)
    {C : ℝ} (b₁ : ∀ x, |φ₁ x| ≤ C) (b₂ : ∀ x, |φ₂ x| ≤ C) (b₃ : ∀ x, |φ₃ x| ≤ C)
    {w P0 P1 D0 D1 g : ℕ → α → ℝ} {w' P0' P1' D0' D1' g' : α → ℝ}
    (hw : ∀ n, MemLp (w n) 2 μ) (hP0 : ∀ n, MemLp (P0 n) 2 μ) (hP1 : ∀ n, MemLp (P1 n) 2 μ)
    (hD0 : ∀ n, MemLp (D0 n) 2 μ) (hD1 : ∀ n, MemLp (D1 n) 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (hw' : MemLp w' 2 μ) (hP0' : MemLp P0' 2 μ) (hP1' : MemLp P1' 2 μ) (hD0' : MemLp D0' 2 μ)
    (hD1' : MemLp D1' 2 μ) (hg' : MemLp g' 2 μ)
    (tw : Tendsto (fun n => eLpNorm (fun x => w n x - w' x) 2 μ) atTop (𝓝 0))
    (tP0 : Tendsto (fun n => eLpNorm (fun x => P0 n x - P0' x) 2 μ) atTop (𝓝 0))
    (tP1 : Tendsto (fun n => eLpNorm (fun x => P1 n x - P1' x) 2 μ) atTop (𝓝 0))
    (tD0 : Tendsto (fun n => eLpNorm (fun x => D0 n x - D0' x) 2 μ) atTop (𝓝 0))
    (tD1 : Tendsto (fun n => eLpNorm (fun x => D1 n x - D1' x) 2 μ) atTop (𝓝 0))
    (tg : Tendsto (fun n => eLpNorm (fun x => g n x - g' x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (φ₁ x * (P0 n x * D0 n x) + φ₁ x * (P1 n x * D1 n x) +
        φ₂ x * (P0 n x * w n x) + φ₃ x * (P1 n x * w n x) - φ₁ x * (g n x * w n x)) ∂μ)
      atTop (𝓝 (∫ x, (φ₁ x * (P0' x * D0' x) + φ₁ x * (P1' x * D1' x) +
        φ₂ x * (P0' x * w' x) + φ₃ x * (P1' x * w' x) - φ₁ x * (g' x * w' x)) ∂μ)) := by
  have t1 := tendsto_weighted_mul m₁ b₁ hP0 hD0 hP0' hD0' tP0 tD0
  have t2 := tendsto_weighted_mul m₁ b₁ hP1 hD1 hP1' hD1' tP1 tD1
  have t3 := tendsto_weighted_mul m₂ b₂ hP0 hw hP0' hw' tP0 tw
  have t4 := tendsto_weighted_mul m₃ b₃ hP1 hw hP1' hw' tP1 tw
  have t5 := tendsto_weighted_mul m₁ b₁ hg hw hg' hw' tg tw
  have i1 := fun n => integrable_weighted_mul m₁ b₁ (hP0 n) (hD0 n)
  have i2 := fun n => integrable_weighted_mul m₁ b₁ (hP1 n) (hD1 n)
  have i3 := fun n => integrable_weighted_mul m₂ b₂ (hP0 n) (hw n)
  have i4 := fun n => integrable_weighted_mul m₃ b₃ (hP1 n) (hw n)
  have i5 := fun n => integrable_weighted_mul m₁ b₁ (hg n) (hw n)
  have t12 := tendsto_integral_add_fun i1 i2 t1 t2
  have t123 := tendsto_integral_add_fun (fun n => (i1 n).add (i2 n)) i3 t12 t3
  have t1234 := tendsto_integral_add_fun (fun n => ((i1 n).add (i2 n)).add (i3 n)) i4 t123 t4
  have t5' : Tendsto (fun n => ∫ x, -(φ₁ x * (g n x * w n x)) ∂μ) atTop
      (𝓝 (∫ x, -(φ₁ x * (g' x * w' x)) ∂μ)) := by
    simp_rw [integral_neg]; exact t5.neg
  have t12345 := tendsto_integral_add_fun
    (fun n => (((i1 n).add (i2 n)).add (i3 n)).add (i4 n)) (fun n => (i5 n).neg) t1234 t5'
  simp only [sub_eq_add_neg]
  have j1 := integrable_weighted_mul m₁ b₁ hP0' hD0'
  have j2 := integrable_weighted_mul m₁ b₁ hP1' hD1'
  have j3 := integrable_weighted_mul m₂ b₂ hP0' hw'
  have j4 := integrable_weighted_mul m₃ b₃ hP1' hw'
  have j5 := integrable_weighted_mul m₁ b₁ hg' hw'
  have e1 := integral_add j1 j2
  have e2 := integral_add (j1.add j2) j3
  have e3 := integral_add ((j1.add j2).add j3) j4
  have e4 := integral_add (((j1.add j2).add j3).add j4) j5.neg
  simp only [Pi.add_apply, Pi.neg_apply] at e1 e2 e3 e4 t12345
  rw [e4, e3, e2, e1]
  exact t12345

/-- Zero extension of a vector field off `S`. -/
def zeroExt (S : Set (ℝ × Vec 2)) (P : ℝ × Vec 2 → Vec 2) : ℝ × Vec 2 → Vec 2 :=
  fun p i => S.indicator (fun q => P q i) p

theorem flux_expand (ζ : Vec 2 → ℝ) (w g : ℝ × Vec 2 → ℝ) (P D : ℝ × Vec 2 → Vec 2)
    (p : ℝ × Vec 2) :
    fluxIntegrand ζ w P D g p =
      (ζ p.2 ^ 2) * (P p 0 * D p 0) + (ζ p.2 ^ 2) * (P p 1 * D p 1) +
      (2 * ζ p.2 * spGrad ζ p.2 0) * (P p 0 * w p) + (2 * ζ p.2 * spGrad ζ p.2 1) * (P p 1 * w p) -
      (ζ p.2 ^ 2) * (g p * w p) := by
  simp only [fluxIntegrand, vecDot, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem memLp_mollify_restrict {k : ℕ → ℝ × Vec 2 → ℝ} (hk : MollSeq k)
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 volume) {R : Set (ℝ × Vec 2)} (hRc : IsCompact R) (n : ℕ) :
    MemLp (mollify f (k n)) 2 (volume.restrict R) := by
  have := (memLp_mollify_sub_restrict hk hf hRc n).add (hf.restrict R)
  have e : mollify f (k n) = (fun p => mollify f (k n) p - f p) + f := by
    funext p; simp
  rw [e]; exact this

theorem tendsto_flux_integral {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B)
    {U g : ℝ × Vec 2 → ℝ} {DU P : ℝ × Vec 2 → Vec 2} (h : WeakEq ta tb B U g DU P)
    {ζ : Vec 2 → ℝ} (hζ : IsSpTest B ζ) {k : ℕ → ℝ × Vec 2 → ℝ} (hk : MollSeq k) (τ₁ τ₂ : ℝ) :
    Tendsto (fun n => ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ
        (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k n))
        (molVec (Set.Ioo ta tb ×ˢ B) P (k n)) (molVec (Set.Ioo ta tb ×ˢ B) DU (k n))
        (mollify ((Set.Ioo ta tb ×ˢ B).indicator g) (k n)) p) atTop
      (𝓝 (∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ ((Set.Ioo ta tb ×ˢ B).indicator U)
        (zeroExt (Set.Ioo ta tb ×ˢ B) P) (zeroExt (Set.Ioo ta tb ×ˢ B) DU)
        ((Set.Ioo ta tb ×ˢ B).indicator g) p)) := by
  have hS : MeasurableSet (Set.Ioo ta tb ×ˢ B) := measurableSet_Ioo.prod hB.measurableSet
  set S := Set.Ioo ta tb ×ˢ B with hSdef
  obtain ⟨Z, Zg, hZ0, hZg0, hZ, hZg⟩ := exists_bounds hζ.1 hζ.2.1
  have hT : tsupport ζ ⊆ B := hζ.2.2
  set R := Set.Icc τ₁ τ₂ ×ˢ tsupport ζ with hR
  have hRc : IsCompact R := isCompact_Icc.prod hζ.2.1
  set μ : Measure (ℝ × Vec 2) := volume.restrict (Set.Ioc τ₁ τ₂ ×ˢ tsupport ζ) with hμ
  have hμR : μ ≤ volume.restrict R :=
    Measure.restrict_mono (Set.prod_mono Set.Ioc_subset_Icc_self subset_rfl) le_rfl
  have hμv : μ ≤ volume := Measure.restrict_le_self
  have mU : MemLp (S.indicator U) 2 volume := (memLp_indicator_iff_restrict hS).2 h.hU
  have mg : MemLp (S.indicator g) 2 volume := (memLp_indicator_iff_restrict hS).2 h.hg
  have mD : ∀ i, MemLp (S.indicator (fun q => DU q i)) 2 volume := fun i =>
    (memLp_indicator_iff_restrict hS).2 (h.hDU i)
  have mP : ∀ i, MemLp (S.indicator (fun q => P q i)) 2 volume := fun i =>
    (memLp_indicator_iff_restrict hS).2 (h.hP i)
  have lim : ∀ {f : ℝ × Vec 2 → ℝ}, MemLp f 2 volume →
      Tendsto (fun n => eLpNorm (fun x => mollify f (k n) x - f x) 2 μ) atTop (𝓝 0) :=
    fun hf => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hk.conv _ hf)
      (fun n => bot_le) (fun n => eLpNorm_mono_measure _ hμv)
  have mem : ∀ {f : ℝ × Vec 2 → ℝ}, MemLp f 2 volume → ∀ n, MemLp (mollify f (k n)) 2 μ :=
    fun hf n => (memLp_mollify_restrict hk hf hRc n).mono_measure hμR
  have m₁ : Measurable fun p : ℝ × Vec 2 => ζ p.2 ^ 2 :=
    ((hζ.1.continuous.comp continuous_snd).pow 2).measurable
  have mφ : ∀ i : Fin 2, Measurable fun p : ℝ × Vec 2 => 2 * ζ p.2 * spGrad ζ p.2 i := fun i => by
    have h1 : Continuous fun p : ℝ × Vec 2 => ζ p.2 := hζ.1.continuous.comp continuous_snd
    have h2 : Continuous fun p : ℝ × Vec 2 => spGrad ζ p.2 i :=
      (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).continuous.comp
        ((hζ.1.of_le (by exact_mod_cast le_top)).continuous_fderiv one_ne_zero |>.comp continuous_snd)
    exact ((continuous_const.mul h1).mul h2).measurable
  have hcore := tendsto_flux_abstract (μ := μ) (φ₁ := fun p : ℝ × Vec 2 => ζ p.2 ^ 2)
    (φ₂ := fun p : ℝ × Vec 2 => 2 * ζ p.2 * spGrad ζ p.2 0)
    (φ₃ := fun p : ℝ × Vec 2 => 2 * ζ p.2 * spGrad ζ p.2 1) m₁ (mφ 0) (mφ 1)
    (C := Z ^ 2 + 2 * Z * Zg + 1)
    (fun p => by
      rw [abs_pow]
      have := pow_le_pow_left₀ (abs_nonneg _) (hZ p.2) 2
      nlinarith [mul_nonneg hZ0 hZg0])
    (fun p => by
      rw [abs_mul, abs_mul, abs_two]
      have := mul_le_mul (hZ p.2) (hZg p.2 0) (abs_nonneg _) hZ0
      nlinarith [mul_nonneg hZ0 hZg0])
    (fun p => by
      rw [abs_mul, abs_mul, abs_two]
      have := mul_le_mul (hZ p.2) (hZg p.2 1) (abs_nonneg _) hZ0
      nlinarith [mul_nonneg hZ0 hZg0])
    (w := fun n => mollify (S.indicator U) (k n)) (P0 := fun n => mollify (S.indicator fun q => P q 0) (k n))
    (P1 := fun n => mollify (S.indicator fun q => P q 1) (k n))
    (D0 := fun n => mollify (S.indicator fun q => DU q 0) (k n))
    (D1 := fun n => mollify (S.indicator fun q => DU q 1) (k n))
    (g := fun n => mollify (S.indicator g) (k n))
    (mem mU) (mem (mP 0)) (mem (mP 1)) (mem (mD 0)) (mem (mD 1)) (mem mg)
    (mU.mono_measure hμv)
    ((mP 0).mono_measure hμv) ((mP 1).mono_measure hμv) ((mD 0).mono_measure hμv)
    ((mD 1).mono_measure hμv) (mg.mono_measure hμv)
    (lim mU) (lim (mP 0)) (lim (mP 1)) (lim (mD 0)) (lim (mD 1)) (lim mg)
  have hrew : ∀ (w g' : ℝ × Vec 2 → ℝ) (P' D' : ℝ × Vec 2 → Vec 2),
      ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ w P' D' g' p =
        ∫ p, (ζ p.2 ^ 2 * (P' p 0 * D' p 0) + ζ p.2 ^ 2 * (P' p 1 * D' p 1) +
          (2 * ζ p.2 * spGrad ζ p.2 0) * (P' p 0 * w p) +
          (2 * ζ p.2 * spGrad ζ p.2 1) * (P' p 1 * w p) - ζ p.2 ^ 2 * (g' p * w p)) ∂μ := by
    intro w g' P' D'
    have h1 : ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ w P' D' g' p =
        ∫ p in Set.Ioc τ₁ τ₂ ×ˢ tsupport ζ, fluxIntegrand ζ w P' D' g' p := by
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_Ioc.prod hB.measurableSet)
        (Set.prod_mono subset_rfl hT) fun p hp => ?_
      exact flux_zero_off p fun h' => hp.2 ⟨hp.1.1, h'⟩
    rw [h1, hμ]
    simp_rw [flux_expand]
  simp only [hrew]
  exact hcore
end

/-! # The `L²(B)` limit of the mollified cutoff slices

`phiLim` is the uniform limit on `[a,b]` of the mollified slices `ζ · w_n(τ,·)`, hence continuous
into `L²(B)` (`phi_tendsto_and_continuous`). -/

section
open AVRegularity.Applications
open scoped ENNReal

/-- The `L²(B)` limit of the mollified cutoff slices. -/
def phiLim (B : Set (Vec 2)) (ζ : Vec 2 → ℝ) (S : Set (ℝ × Vec 2)) (U : ℝ × Vec 2 → ℝ)
    (k : ℕ → ℝ × Vec 2 → ℝ) (τ : ℝ) : Lp ℝ 2 (volume.restrict B) :=
  limUnder atTop (fun n => phiLp B ζ (mollify (S.indicator U) (k n)) τ)

theorem phi_tendsto_and_continuous {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B)
    {U g : ℝ × Vec 2 → ℝ} {DU P : ℝ × Vec 2 → Vec 2} (h : WeakEq ta tb B U g DU P)
    {ζ : Vec 2 → ℝ} (hζ : IsSpTest B ζ) {k : ℕ → ℝ × Vec 2 → ℝ} (hk : MollSeq k) {a b : ℝ}
    (hab : a < b) {N0 : ℕ}
    (hwin : ∀ n ≥ N0, Window (Set.Ioo ta tb ×ˢ B) (k n) (Set.Icc a b) (tsupport ζ)) :
    (∀ τ ∈ Set.Icc a b, Tendsto (fun n => phiLp B ζ (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k n)) τ)
      atTop (𝓝 (phiLim B ζ (Set.Ioo ta tb ×ˢ B) U k τ))) ∧
    ContinuousOn (phiLim B ζ (Set.Ioo ta tb ×ˢ B) U k) (Set.Icc a b) := by
  have hS : MeasurableSet (Set.Ioo ta tb ×ˢ B) := measurableSet_Ioo.prod hB.measurableSet
  have hcw : ∀ n, Continuous (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k n)) := fun n =>
    mollify_continuous (hk.contDiff n).continuous (hk.compact n)
      (locallyIntegrable_indicator hS h.hU)
  have huc : UniformCauchySeqOn
      (fun n τ => phiLp B ζ (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k n)) τ) atTop
      (Set.Icc a b) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := cauchy_sup hB h hζ hk hab hwin (ε ^ 2 / 4) (by positivity)
    refine ⟨N, fun m hm n hn τ hτ => ?_⟩
    have h1 := hN m hm n hn τ hτ
    have h2 := dist_phiLp_sq hB.measurableSet hζ.2.2 hζ.1.continuous hζ.2.1 (hcw m) (hcw n) τ τ
    rw [← integral_B_eq_T hB.measurableSet hζ.2.2 (fun y hy => by
      simp [image_eq_zero_of_notMem_tsupport hy])] at h2
    by_contra hcon
    push Not at hcon
    have := dist_nonneg (x := phiLp B ζ (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k m)) τ)
      (y := phiLp B ζ (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k n)) τ)
    nlinarith
  have hpt : ∀ τ ∈ Set.Icc a b, Tendsto
      (fun n => phiLp B ζ (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k n)) τ) atTop
      (𝓝 (phiLim B ζ (Set.Ioo ta tb ×ˢ B) U k τ)) := fun τ hτ =>
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (huc.cauchySeq hτ))
  refine ⟨hpt, ?_⟩
  exact (huc.tendstoUniformlyOn_of_tendsto hpt).continuousOn
    (Eventually.of_forall fun n =>
      (continuous_phiLp hB.measurableSet hζ.2.2 hζ.1.continuous hζ.2.1 (hcw n)).continuousOn).frequently

theorem norm_phiLp_sq {ζ : Vec 2 → ℝ} {B : Set (Vec 2)} (hζ : Continuous ζ)
    (hζc : HasCompactSupport ζ) {w : ℝ × Vec 2 → ℝ} (hw : Continuous w) (τ : ℝ) :
    ‖phiLp B ζ w τ‖ ^ 2 = ∫ y in B, ζ y ^ 2 * w (τ, y) ^ 2 := by
  rw [phiLp_eq (memLp_phi hζ hζc hw τ _), ← real_inner_self_eq_norm_sq, inner_toLp]
  congr 1
  funext y
  ring

theorem energy_identity_limit {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B)
    {U g : ℝ × Vec 2 → ℝ} {DU P : ℝ × Vec 2 → Vec 2} (h : WeakEq ta tb B U g DU P)
    {ζ : Vec 2 → ℝ} (hζ : IsSpTest B ζ) {k : ℕ → ℝ × Vec 2 → ℝ} (hk : MollSeq k) {a b : ℝ}
    (hab : a < b) {N0 : ℕ}
    (hwin : ∀ n ≥ N0, Window (Set.Ioo ta tb ×ˢ B) (k n) (Set.Icc a b) (tsupport ζ))
    {τ₁ τ₂ : ℝ} (h1 : τ₁ ∈ Set.Icc a b) (h2 : τ₂ ∈ Set.Icc a b) (h12 : τ₁ ≤ τ₂) :
    ‖phiLim B ζ (Set.Ioo ta tb ×ˢ B) U k τ₂‖ ^ 2 - ‖phiLim B ζ (Set.Ioo ta tb ×ˢ B) U k τ₁‖ ^ 2 =
      -2 * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ ((Set.Ioo ta tb ×ˢ B).indicator U)
        (zeroExt (Set.Ioo ta tb ×ˢ B) P) (zeroExt (Set.Ioo ta tb ×ˢ B) DU)
        ((Set.Ioo ta tb ×ˢ B).indicator g) p := by
  have hS : MeasurableSet (Set.Ioo ta tb ×ˢ B) := measurableSet_Ioo.prod hB.measurableSet
  obtain ⟨hpt, -⟩ := phi_tendsto_and_continuous hB h hζ hk hab hwin
  have hcw : ∀ n, Continuous (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k n)) := fun n =>
    mollify_continuous (hk.contDiff n).continuous (hk.compact n)
      (locallyIntegrable_indicator hS h.hU)
  have hL : Tendsto (fun n =>
      ‖phiLp B ζ (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k n)) τ₂‖ ^ 2 -
      ‖phiLp B ζ (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (k n)) τ₁‖ ^ 2) atTop
      (𝓝 (‖phiLim B ζ (Set.Ioo ta tb ×ˢ B) U k τ₂‖ ^ 2 -
        ‖phiLim B ζ (Set.Ioo ta tb ×ˢ B) U k τ₁‖ ^ 2)) :=
    ((hpt τ₂ h2).norm.pow 2).sub ((hpt τ₁ h1).norm.pow 2)
  have hR := (tendsto_flux_integral hB h hζ hk τ₁ τ₂).const_mul (-2)
  refine tendsto_nhds_unique_of_eventuallyEq hL hR ?_
  filter_upwards [Filter.eventually_ge_atTop N0] with n hn
  rw [norm_phiLp_sq hζ.1.continuous hζ.2.1 (hcw n), norm_phiLp_sq hζ.1.continuous hζ.2.1 (hcw n)]
  exact mollified_energy_identity hB h hζ (hk.contDiff n) (hk.compact n) Set.ordConnected_Icc
    (hwin n hn) h1 h2 h12
end

/-! # The limit slice is the cutoff datum

For almost every time the `L²(B)` limit `phiLim` of the mollified slices agrees with
`ζ · U(τ, ·)` (`phiLim_ae_eq`), by extracting an almost everywhere convergent subsequence from the
`L¹`-in-time convergence of the slice defects. -/

section
open AVRegularity.Applications
open scoped ENNReal

/-- Time-slice defect of the mollification relative to the zero-extended datum. -/
def sliceDefect (ζ : Vec 2 → ℝ) (f : ℝ × Vec 2 → ℝ) (K : ℝ × Vec 2 → ℝ) (τ : ℝ) : ℝ :=
  ∫ y in tsupport ζ, (ζ y * (mollify f K (τ, y) - f (τ, y))) ^ 2

theorem tendsto_integral_sliceDefect {k : ℕ → ℝ × Vec 2 → ℝ} (hk : MollSeq k) {ζ : Vec 2 → ℝ}
    (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 volume)
    {a b : ℝ} :
    (∀ n, Integrable (sliceDefect ζ f (k n)) (volume.restrict (Set.Icc a b))) ∧
    Tendsto (fun n => ∫ τ in Set.Icc a b, sliceDefect ζ f (k n) τ) atTop (𝓝 0) := by
  set R := Set.Icc a b ×ˢ tsupport ζ with hR
  have hRc : IsCompact R := isCompact_Icc.prod hζc
  obtain ⟨Z, hZ⟩ := hζc.exists_bound_of_continuous hζ
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ 0)
  set u : ℕ → ℝ × Vec 2 → ℝ := fun n p => ζ p.2 * (mollify f (k n) p - f p) with hu
  have hmem : ∀ n, MemLp (u n) 2 (volume.restrict R) := by
    intro n
    refine (memLp_mollify_sub_restrict hk hf hRc n).of_le_mul (c := Z) ?_ ?_
    · exact ((hζ.comp continuous_snd).aestronglyMeasurable).mul
        (memLp_mollify_sub_restrict hk hf hRc n).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      simp only [hu, norm_mul]
      exact mul_le_mul_of_nonneg_right (hZ p.2) (norm_nonneg _)
  have hprod : volume.restrict R =
      (volume.restrict (Set.Icc a b)).prod (volume.restrict (tsupport ζ)) := by
    rw [hR, Measure.volume_eq_prod, Measure.prod_restrict]
  have hint : ∀ n, Integrable (fun p => u n p ^ 2) ((volume.restrict (Set.Icc a b)).prod
      (volume.restrict (tsupport ζ))) := fun n => by
    rw [← hprod]; exact (hmem n).integrable_sq
  have hsd : ∀ n, sliceDefect ζ f (k n) = fun τ => ∫ y, u n (τ, y) ^ 2 ∂(volume.restrict (tsupport ζ)) := by
    intro n; funext τ; simp [sliceDefect, hu]
  refine ⟨fun n => ?_, ?_⟩
  · rw [hsd]; exact (hint n).integral_prod_left
  · have hfub : ∀ n, ∫ τ in Set.Icc a b, sliceDefect ζ f (k n) τ = ∫ p in R, u n p ^ 2 := by
      intro n
      rw [hsd]
      show (∫ τ in Set.Icc a b, ∫ y, u n (τ, y) ^ 2 ∂(volume.restrict (tsupport ζ))) = _
      rw [← integral_prod (fun p => u n p ^ 2) (hint n), ← hprod]
    simp_rw [hfub]
    have hbound := tendsto_setIntegral_sq_mollify hk hf hRc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hbound.const_mul (Z ^ 2)) (fun n => setIntegral_nonneg hRc.measurableSet
        fun p _ => sq_nonneg _) (fun n => ?_)
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hmem n).integrable_sq
      (((memLp_mollify_sub_restrict hk hf hRc n).integrable_sq).const_mul _) hRc.measurableSet
      fun p _ => ?_
    simp only [hu]
    rw [mul_pow]
    have : ζ p.2 ^ 2 ≤ Z ^ 2 := by
      rw [← sq_abs (ζ p.2)]
      exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using hZ p.2) 2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

theorem exists_seq_ae_sliceDefect {k : ℕ → ℝ × Vec 2 → ℝ} (hk : MollSeq k) {ζ : Vec 2 → ℝ}
    (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 volume)
    {a b : ℝ} :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ τ ∂(volume.restrict (Set.Icc a b)),
      Tendsto (fun j => sliceDefect ζ f (k (ns j)) τ) atTop (𝓝 0) := by
  obtain ⟨hint, hlim⟩ := tendsto_integral_sliceDefect hk hζ hζc hf (a := a) (b := b)
  have hnn : ∀ n τ, 0 ≤ sliceDefect ζ f (k n) τ := fun n τ =>
    setIntegral_nonneg hζc.isCompact.measurableSet fun y _ => sq_nonneg _
  have h1 : Tendsto (fun n => eLpNorm (sliceDefect ζ f (k n) - fun _ => (0 : ℝ)) 1
      (volume.restrict (Set.Icc a b))) atTop (𝓝 0) := by
    have : ∀ n, eLpNorm (sliceDefect ζ f (k n) - fun _ => (0 : ℝ)) 1 (volume.restrict (Set.Icc a b)) =
        ENNReal.ofReal (∫ τ in Set.Icc a b, sliceDefect ζ f (k n) τ) := by
      intro n
      have e : (sliceDefect ζ f (k n) - fun _ => (0 : ℝ)) = sliceDefect ζ f (k n) := by
        funext τ; simp
      rw [e, eLpNorm_one_eq_lintegral_enorm (hint n).aestronglyMeasurable,
        ofReal_integral_eq_lintegral_ofReal (hint n) (Eventually.of_forall (hnn n))]
      refine lintegral_congr fun τ => ?_
      rw [← ofReal_norm, Real.norm_of_nonneg (hnn n τ)]
    simp_rw [this]
    simpa using ENNReal.tendsto_ofReal hlim
  exact (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) h1).exists_seq_tendsto_ae

theorem phiLim_ae_eq {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B)
    {U g : ℝ × Vec 2 → ℝ} {DU P : ℝ × Vec 2 → Vec 2} (h : WeakEq ta tb B U g DU P)
    {ζ : Vec 2 → ℝ} (hζ : IsSpTest B ζ) {k : ℕ → ℝ × Vec 2 → ℝ} (hk : MollSeq k) {a b : ℝ}
    (hab : a < b) {N0 : ℕ}
    (hwin : ∀ n ≥ N0, Window (Set.Ioo ta tb ×ˢ B) (k n) (Set.Icc a b) (tsupport ζ)) :
    ∀ᵐ τ ∂(volume.restrict (Set.Icc a b)),
      (phiLim B ζ (Set.Ioo ta tb ×ˢ B) U k τ : Vec 2 → ℝ) =ᵐ[volume.restrict B]
        fun y => ζ y * (Set.Ioo ta tb ×ˢ B).indicator U (τ, y) := by
  have hS : MeasurableSet (Set.Ioo ta tb ×ˢ B) := measurableSet_Ioo.prod hB.measurableSet
  set f := (Set.Ioo ta tb ×ˢ B).indicator U with hfdef
  have hf : MemLp f 2 volume := (memLp_indicator_iff_restrict hS).2 h.hU
  obtain ⟨hpt, -⟩ := phi_tendsto_and_continuous hB h hζ hk hab hwin
  obtain ⟨ns, hns, hae⟩ := exists_seq_ae_sliceDefect hk hζ.1.continuous hζ.2.1 hf (a := a) (b := b)
  set R := Set.Icc a b ×ˢ tsupport ζ with hR
  have hRc : IsCompact R := isCompact_Icc.prod hζ.2.1
  have hprod : volume.restrict R =
      (volume.restrict (Set.Icc a b)).prod (volume.restrict (tsupport ζ)) := by
    rw [hR, Measure.volume_eq_prod, Measure.prod_restrict]
  obtain ⟨Z, hZ⟩ := hζ.2.1.exists_bound_of_continuous hζ.1.continuous
  have hmemR : MemLp (fun p : ℝ × Vec 2 => ζ p.2 * f p) 2 (volume.restrict R) := by
    refine (hf.restrict R).of_le_mul (c := Z) ?_ ?_
    · exact ((hζ.1.continuous.comp continuous_snd).aestronglyMeasurable).mul
        (hf.restrict R).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hZ p.2) (norm_nonneg _)
  have hintR : Integrable (fun p : ℝ × Vec 2 => (ζ p.2 * f p) ^ 2)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (tsupport ζ))) := by
    rw [← hprod]; exact hmemR.integrable_sq
  have hslice1 := hintR.prod_right_ae
  have hslice2 : ∀ᵐ τ ∂(volume.restrict (Set.Icc a b)),
      AEStronglyMeasurable (fun y => f (τ, y)) volume := by
    have := hf.aestronglyMeasurable
    rw [Measure.volume_eq_prod] at this
    exact ae_restrict_of_ae (this.prodMk_left)
  filter_upwards [hae, hslice1, hslice2, ae_restrict_mem measurableSet_Icc] with τ h1 h2 h3 hτ
  have hmemτ : MemLp (fun y => ζ y * f (τ, y)) 2 (volume.restrict B) := by
    refine (memLp_two_iff_integrable_sq
      ((hζ.1.continuous.aestronglyMeasurable.mul h3.restrict))).2 ?_
    have h2' : IntegrableOn (fun y => (ζ y * f (τ, y)) ^ 2) (tsupport ζ) volume := h2
    exact h2'.of_forall_sdiff_eq_zero hB.measurableSet fun y hy => by
      simp [image_eq_zero_of_notMem_tsupport hy.2]
  have hcw : ∀ n, Continuous (mollify f (k n)) := fun n =>
    mollify_continuous (hk.contDiff n).continuous (hk.compact n)
      (locallyIntegrable_indicator hS h.hU)
  have hdist : ∀ n, dist (phiLp B ζ (mollify f (k n)) τ) (hmemτ.toLp _) =
      Real.sqrt (sliceDefect ζ f (k n) τ) := by
    intro n
    rw [← Real.sqrt_sq dist_nonneg, phiLp_eq (memLp_phi hζ.1.continuous hζ.2.1 (hcw n) τ _),
      dist_toLp_sq]
    congr 1
    rw [integral_B_eq_T hB.measurableSet hζ.2.2 (fun y hy => by
      simp [image_eq_zero_of_notMem_tsupport hy])]
    simp only [sliceDefect]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  have hsub : Tendsto (fun j => phiLp B ζ (mollify f (k (ns j))) τ) atTop
      (𝓝 (hmemτ.toLp _)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simp_rw [hdist]
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    simpa [Function.comp_def] using this
  have hlim2 := (hpt τ hτ).comp hns.tendsto_atTop
  have heq := tendsto_nhds_unique hlim2 hsub
  rw [heq]
  exact hmemτ.coeFn_toLp
end

end AVRegularity.Applications.LocalEnergy
end
end
end
