-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Coarse.Defect.CovCommute
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The bracket of the coarse defect bound is at most the bill factor `𝔱`**.
The coarse defect bound (`cycle_coarse_defect_bound`) bounds the coarse flux by `F₀` times the bracket
`(ω^{p+1}(q₀+q₁) + k₀ω^p) Σ + q₀ ∑_h binom(J+h,J)(4q₀)^J(4q₁)^h`, with
`Σ = ∑_{i≤J, h≤H} binom(i+h,i)(4q₀)^i(4q₁)^h`. With `q₀ ≤ A E^{2δ}`, `q₁ ≤ Q`,
`ω ≤ W E^δ` and `k₀ ≤ K` the bracket is at most `C (E^{2δ(J+1)} + E^{δp})`
(`coarse_bracket_le`), the factor `𝔱` of the bill. Abstract reals only. -/

/-- The binomial sum `Σ` of the coarse defect bound. -/
def coarseSig (q₀ q₁ : ℝ) (J H : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (J + 1), ∑ j ∈ Finset.range (H + 1),
    (Nat.choose (i + j) i : ℝ) * (4 * q₀) ^ i * (4 * q₁) ^ j

/-- The constant of the bracket bound. -/
def coarseBracketConst (A Q W K : ℝ) (J p H : ℕ) : ℝ :=
  (W ^ (p + 1) * (A + Q) + K * W ^ p) * coarseSig A Q J H +
    4 ^ J * A ^ (J + 1) * ∑ j ∈ Finset.range (H + 1), (Nat.choose (J + j) J : ℝ) * (4 * Q) ^ j

theorem coarseSig_nonneg {q₀ q₁ : ℝ} (h₀ : 0 ≤ q₀) (h₁ : 0 ≤ q₁) (J H : ℕ) :
    0 ≤ coarseSig q₀ q₁ J H := by
  unfold coarseSig
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _))
      (pow_nonneg (by linarith) _)

theorem coarseSig_mono {q₀ q₁ A Q : ℝ} (h₀ : 0 ≤ q₀) (h₁ : 0 ≤ q₁) (hA : q₀ ≤ A) (hQ : q₁ ≤ Q)
    (J H : ℕ) : coarseSig q₀ q₁ J H ≤ coarseSig A Q J H := by
  unfold coarseSig
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h4 : (4 * q₀) ^ i ≤ (4 * A) ^ i := pow_le_pow_left₀ (by linarith) (by linarith) i
  have h5 : (4 * q₁) ^ j ≤ (4 * Q) ^ j := pow_le_pow_left₀ (by linarith) (by linarith) j
  have hc : (0 : ℝ) ≤ (Nat.choose (i + j) i : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul (mul_le_mul_of_nonneg_left h4 hc) h5 (pow_nonneg (by linarith) _)
    (mul_nonneg hc (pow_nonneg (by linarith) _))

/-- **The coarse bracket is at most `C 𝔱`.** -/
theorem coarse_bracket_le {E δ A Q W K : ℝ} (hE : 0 < E) (hE1 : E ≤ 1) (hδ : 0 < δ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) {q₀ q₁ ω k₀ : ℝ} (hq₀ : 0 ≤ q₀) (hq₀' : q₀ ≤ A * E ^ (2 * δ)) (hq₁ : 0
        ≤ q₁)
    (hq₁' : q₁ ≤ Q) (hω : 0 ≤ ω) (hω' : ω ≤ W * E ^ δ) (hk₀ : 0 ≤ k₀) (hk₀' : k₀ ≤ K)
    (J p H : ℕ) :
    (ω ^ (p + 1) * (q₀ + q₁) + k₀ * ω ^ p) * coarseSig q₀ q₁ J H +
        q₀ * ∑ j ∈ Finset.range (H + 1), (Nat.choose (J + j) J : ℝ) * (4 * q₀) ^ J * (4 * q₁) ^ j
      ≤ coarseBracketConst A Q W K J p H *
          (E ^ (2 * δ * ((J : ℝ) + 1)) + E ^ (δ * (p : ℝ))) := by
  have hEδ0 : 0 ≤ E ^ δ := Real.rpow_nonneg hE.le δ
  have hEδ1 : E ^ δ ≤ 1 := Real.rpow_le_one hE.le hE1 hδ.le
  have hE2δ0 : 0 ≤ E ^ (2 * δ) := Real.rpow_nonneg hE.le _
  have hE2δ1 : E ^ (2 * δ) ≤ 1 := Real.rpow_le_one hE.le hE1 (by linarith)
  have hQ : 0 ≤ Q := hq₁.trans hq₁'
  have hK : 0 ≤ K := hk₀.trans hk₀'
  have hq₀A : q₀ ≤ A := hq₀'.trans (by nlinarith)
  -- powers of `E^δ`
  have hpow : ∀ n : ℕ, (E ^ δ) ^ n = E ^ (δ * (n : ℝ)) := fun n => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le]
  have hp1 : E ^ (δ * ((p + 1 : ℕ) : ℝ)) ≤ E ^ (δ * (p : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hE hE1 (by push_cast; nlinarith)
  have hωp : ω ^ p ≤ W ^ p * E ^ (δ * (p : ℝ)) := by
    calc ω ^ p ≤ (W * E ^ δ) ^ p := pow_le_pow_left₀ hω hω' p
      _ = W ^ p * E ^ (δ * (p : ℝ)) := by rw [mul_pow, hpow]
  have hωp1 : ω ^ (p + 1) ≤ W ^ (p + 1) * E ^ (δ * (p : ℝ)) := by
    calc ω ^ (p + 1) ≤ (W * E ^ δ) ^ (p + 1) := pow_le_pow_left₀ hω hω' (p + 1)
      _ = W ^ (p + 1) * E ^ (δ * ((p + 1 : ℕ) : ℝ)) := by rw [mul_pow, hpow]
      _ ≤ W ^ (p + 1) * E ^ (δ * (p : ℝ)) := mul_le_mul_of_nonneg_left hp1 (by positivity)
  have hSig := coarseSig_mono hq₀ hq₁ hq₀A hq₁' J H
  have hSig0 := coarseSig_nonneg hq₀ hq₁ J H
  have hSigA := coarseSig_nonneg hA hQ J H
  -- the first part
  have h1 : (ω ^ (p + 1) * (q₀ + q₁) + k₀ * ω ^ p) * coarseSig q₀ q₁ J H ≤
      (W ^ (p + 1) * (A + Q) + K * W ^ p) * coarseSig A Q J H * E ^ (δ * (p : ℝ)) := by
    have hEp : 0 ≤ E ^ (δ * (p : ℝ)) := Real.rpow_nonneg hE.le _
    have ha : ω ^ (p + 1) * (q₀ + q₁) ≤ W ^ (p + 1) * E ^ (δ * (p : ℝ)) * (A + Q) :=
      mul_le_mul hωp1 (add_le_add hq₀A hq₁') (add_nonneg hq₀ hq₁)
        (mul_nonneg (pow_nonneg hW _) hEp)
    have hb : k₀ * ω ^ p ≤ K * (W ^ p * E ^ (δ * (p : ℝ))) :=
      mul_le_mul hk₀' hωp (pow_nonneg hω _) hK
    calc (ω ^ (p + 1) * (q₀ + q₁) + k₀ * ω ^ p) * coarseSig q₀ q₁ J H
        ≤ (W ^ (p + 1) * E ^ (δ * (p : ℝ)) * (A + Q) + K * (W ^ p * E ^ (δ * (p : ℝ)))) *
            coarseSig A Q J H :=
          mul_le_mul (add_le_add ha hb) hSig hSig0
            (add_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hW _) hEp) (add_nonneg hA hQ))
              (mul_nonneg hK (mul_nonneg (pow_nonneg hW _) hEp)))
      _ = (W ^ (p + 1) * (A + Q) + K * W ^ p) * coarseSig A Q J H * E ^ (δ * (p : ℝ)) := by
          ring
  -- the second part
  have h2 : q₀ * ∑ j ∈ Finset.range (H + 1), (Nat.choose (J + j) J : ℝ) * (4 * q₀) ^ J *
      (4 * q₁) ^ j ≤ 4 ^ J * A ^ (J + 1) * (∑ j ∈ Finset.range (H + 1),
        (Nat.choose (J + j) J : ℝ) * (4 * Q) ^ j) * E ^ (2 * δ * ((J : ℝ) + 1)) := by
    have hq0J : q₀ * (4 * q₀) ^ J ≤ 4 ^ J * A ^ (J + 1) * E ^ (2 * δ * ((J : ℝ) + 1)) := by
      have hq : q₀ ^ (J + 1) ≤ (A * E ^ (2 * δ)) ^ (J + 1) := pow_le_pow_left₀ hq₀ hq₀' (J + 1)
      have he : (E ^ (2 * δ)) ^ (J + 1) = E ^ (2 * δ * ((J : ℝ) + 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le]
        push_cast
        ring_nf
      calc q₀ * (4 * q₀) ^ J = 4 ^ J * q₀ ^ (J + 1) := by ring
        _ ≤ 4 ^ J * (A * E ^ (2 * δ)) ^ (J + 1) :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ = 4 ^ J * A ^ (J + 1) * E ^ (2 * δ * ((J : ℝ) + 1)) := by rw [mul_pow, he]; ring
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj : (4 * q₁) ^ j ≤ (4 * Q) ^ j := pow_le_pow_left₀ (by linarith) (by linarith) j
    have hc : (0 : ℝ) ≤ (Nat.choose (J + j) J : ℝ) := Nat.cast_nonneg _
    have hEJ' : 0 ≤ E ^ (2 * δ * ((J : ℝ) + 1)) := Real.rpow_nonneg hE.le _
    calc q₀ * ((Nat.choose (J + j) J : ℝ) * (4 * q₀) ^ J * (4 * q₁) ^ j)
        = (Nat.choose (J + j) J : ℝ) * (q₀ * (4 * q₀) ^ J) * (4 * q₁) ^ j := by ring
      _ ≤ (Nat.choose (J + j) J : ℝ) * (4 ^ J * A ^ (J + 1) * E ^ (2 * δ * ((J : ℝ) + 1))) *
            (4 * Q) ^ j :=
          mul_le_mul (mul_le_mul_of_nonneg_left hq0J hc) hj (pow_nonneg (by linarith) _)
            (mul_nonneg hc (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hA _)) hEJ'))
      _ = 4 ^ J * A ^ (J + 1) * ((Nat.choose (J + j) J : ℝ) * (4 * Q) ^ j) *
            E ^ (2 * δ * ((J : ℝ) + 1)) := by ring
  have hEJ : 0 ≤ E ^ (2 * δ * ((J : ℝ) + 1)) := Real.rpow_nonneg hE.le _
  have hEp : 0 ≤ E ^ (δ * (p : ℝ)) := Real.rpow_nonneg hE.le _
  have hc1 : 0 ≤ (W ^ (p + 1) * (A + Q) + K * W ^ p) * coarseSig A Q J H :=
    mul_nonneg (add_nonneg (mul_nonneg (pow_nonneg hW _) (add_nonneg hA hQ))
      (mul_nonneg hK (pow_nonneg hW _))) hSigA
  have hc2 : 0 ≤ 4 ^ J * A ^ (J + 1) * ∑ j ∈ Finset.range (H + 1),
      (Nat.choose (J + j) J : ℝ) * (4 * Q) ^ j :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hA _))
      (Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _))
  unfold coarseBracketConst
  nlinarith [mul_nonneg hc1 hEJ, mul_nonneg hc2 hEp]

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Topology
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Measurability of an `L¹` limit.** A function that is approximated by a.e. strongly measurable
functions up to errors dominated by integrable functions whose integrals tend to zero is a.e.
strongly measurable (`aestronglyMeasurable_of_integral_bound_tendsto`): the dominating functions
tend to zero in measure, hence a.e. along a subsequence, along which the approximants converge
a.e. This gives the time measurability of the tested right side of a weak identity obtained as a
limit (the integrated identity of the solution class), without joint
measurability of the limit. -/

/-- **An `L¹`-dominated limit of a.e. strongly measurable functions is a.e. strongly
measurable.** -/
theorem aestronglyMeasurable_of_integral_bound_tendsto {α E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] {r : ℕ → α → E} {r' : α → E} {c : ℕ → α → ℝ}
    (hr : ∀ M, AEStronglyMeasurable (r M) μ) (hc : ∀ M, Integrable (c M) μ)
    (hbound : ∀ M, ∀ᵐ s ∂μ, ‖r M s - r' s‖ ≤ c M s)
    (hc0 : Tendsto (fun M => ∫ s, c M s ∂μ) atTop (𝓝 0)) : AEStronglyMeasurable r' μ := by
  have hnn : ∀ M, 0 ≤ᵐ[μ] c M := fun M => by
    filter_upwards [hbound M] with s hs
    exact (norm_nonneg _).trans hs
  -- the dominating functions tend to zero in `L¹`, hence in measure
  have hL1 : Tendsto (fun M => eLpNorm (c M - fun _ => (0 : ℝ)) 1 μ) atTop (𝓝 0) := by
    have he : ∀ M, eLpNorm (c M - fun _ => (0 : ℝ)) 1 μ = ENNReal.ofReal (∫ s, c M s ∂μ) := by
      intro M
      have h0 : c M - (fun _ => (0 : ℝ)) = c M := by
        funext s
        simp
      rw [h0, eLpNorm_one_eq_lintegral_enorm (hc M).aestronglyMeasurable,
        ofReal_integral_eq_lintegral_ofReal (hc M) (hnn M)]
      refine lintegral_congr_ae ?_
      filter_upwards [hnn M] with s hs
      rw [Real.enorm_eq_ofReal hs]
    simp only [he]
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp hc0
    rw [ENNReal.ofReal_zero] at h
    exact h
  obtain ⟨ns, -, hns⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hL1).exists_seq_tendsto_ae
  refine aestronglyMeasurable_of_tendsto_ae atTop (fun j => hr (ns j)) ?_
  filter_upwards [hns, ae_all_iff.2 hbound] with s hs hb
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun j => norm_nonneg _) (fun j => hb (ns j)) hs

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Integrals of limits split into three parts**. If `a_n(s) → F(s)` at every
point of `I` and `a_n ≤ β + b_n + c_n` with `β` integrable, `b_n(s) → 0` pointwise and the
`c_n` a.e. measurable with integrals at most `P`, then `∫_I F ≤ ∫_I β + P`
(`integral_le_of_limit_split`, Fatou's lemma on the `c_n`). This is how the forcing residual of
the reconstruction inherits the bill of the glued residual force (the part `β`), of the
commutator remainders (the part `b_n → 0`) and of the partition term (the part `c_n`). -/

/-- `ofReal a ≤ ofReal b + ofReal (a - b)` for `0 ≤ b`. -/
theorem ofReal_le_ofReal_add_sub {a b : ℝ} (hb : 0 ≤ b) :
    ENNReal.ofReal a ≤ ENNReal.ofReal b + ENNReal.ofReal (a - b) := by
  rcases le_total a b with hab | hab
  · exact (ENNReal.ofReal_le_ofReal hab).trans le_self_add
  · rw [← ENNReal.ofReal_add hb (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **The integral of a limit split into an integrable part, a vanishing part and a part with
bounded integrals.** -/
theorem integral_le_of_limit_split {I : Set ℝ} (hI : MeasurableSet I)
    {Fq : ℝ → ℝ} (hFq0 : ∀ s, 0 ≤ Fq s) (hFqm : AEStronglyMeasurable Fq (volume.restrict I))
    (an bn cn : ℕ → ℝ → ℝ) {β : ℝ → ℝ} (hβ0 : ∀ s, 0 ≤ β s) (hβ : IntegrableOn β I)
    (hlim : ∀ s ∈ I, Tendsto (fun n => an n s) atTop (𝓝 (Fq s)))
    (hsplit : ∀ n, ∀ s ∈ I, an n s ≤ β s + bn n s + cn n s)
    (hb : ∀ s ∈ I, Tendsto (fun n => bn n s) atTop (𝓝 0))
    (hcm : ∀ n, AEMeasurable (cn n) (volume.restrict I)) {P : ℝ} (hP : 0 ≤ P)
    (hc : ∀ n, ∫⁻ s in I, ENNReal.ofReal (cn n s) ≤ ENNReal.ofReal P) :
    ∫ s in I, Fq s ≤ (∫ s in I, β s) + P := by
  -- the pointwise bound
  have hpt : ∀ s ∈ I, ENNReal.ofReal (Fq s) ≤
      ENNReal.ofReal (β s) + liminf (fun n => ENNReal.ofReal (cn n s)) atTop := by
    intro s hs
    have hg : Tendsto (fun n => ENNReal.ofReal (an n s - β s - bn n s)) atTop
        (𝓝 (ENNReal.ofReal (Fq s - β s - 0))) :=
      ENNReal.tendsto_ofReal (((hlim s hs).sub tendsto_const_nhds).sub (hb s hs))
    have hle : liminf (fun n => ENNReal.ofReal (an n s - β s - bn n s)) atTop ≤
        liminf (fun n => ENNReal.ofReal (cn n s)) atTop :=
      liminf_le_liminf (Eventually.of_forall fun n => ENNReal.ofReal_le_ofReal (by
        have := hsplit n s hs
        linarith))
    rw [hg.liminf_eq, sub_zero] at hle
    exact (ofReal_le_ofReal_add_sub (hβ0 s)).trans (add_le_add le_rfl hle)
  -- integrate
  have hlint : ∫⁻ s in I, ENNReal.ofReal (Fq s) ≤ ENNReal.ofReal (∫ s in I, β s) +
      ENNReal.ofReal P := by
    calc ∫⁻ s in I, ENNReal.ofReal (Fq s)
        ≤ ∫⁻ s in I, (ENNReal.ofReal (β s) + liminf (fun n => ENNReal.ofReal (cn n s)) atTop) :=
          setLIntegral_mono' hI hpt
      _ = (∫⁻ s in I, ENNReal.ofReal (β s)) +
            ∫⁻ s in I, liminf (fun n => ENNReal.ofReal (cn n s)) atTop :=
          lintegral_add_left' hβ.aemeasurable.ennreal_ofReal _
      _ ≤ ENNReal.ofReal (∫ s in I, β s) +
            liminf (fun n => ∫⁻ s in I, ENNReal.ofReal (cn n s)) atTop := by
          refine add_le_add (le_of_eq ?_) (lintegral_liminf_le' fun n => (hcm n).ennreal_ofReal)
          exact (ofReal_integral_eq_lintegral_ofReal hβ
            (Eventually.of_forall fun s => hβ0 s)).symm
      _ ≤ ENNReal.ofReal (∫ s in I, β s) + ENNReal.ofReal P := by
          refine add_le_add le_rfl ((liminf_le_limsup).trans ?_)
          exact limsup_le_of_le (h := Eventually.of_forall hc)
  have hβi : 0 ≤ ∫ s in I, β s := integral_nonneg hβ0
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hFq0) hFqm]
  refine (ENNReal.toReal_mono (by simp) hlint).trans (le_of_eq ?_)
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hβi, ENNReal.toReal_ofReal hP]

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Set
open scoped InnerProductSpace
namespace AVRegularity.CycleComparison.Reconstruction

/-! Functions of integral type on an interval (`g s = g a + ∫_a^s dg`) and their calculus: images
under continuous linear maps, finite sums, products with scalar functions of integral type, and the
application of a family of linear maps of integral type to a vector of integral type (finite
dimensional inner product spaces; coordinates in orthonormal bases reduce to the scalar product
rule `Coarse.product_rule_integral`). This is the time calculus of the lift coefficients applied to
the time-dependent jets of a coarse field. -/

/-- `g` is of integral type on `[a, b]` with density `dg`. -/
def IsPrimOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a b : ℝ) (g dg : ℝ → F) :
    Prop :=
  IntervalIntegrable dg volume a b ∧ ∀ s ∈ Icc a b, g s = g a + ∫ σ in a..s, dg σ

section Basic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {a b : ℝ}

omit [CompleteSpace F] in
theorem IsPrimOn.intervalIntegrable_sub {g dg : ℝ → F} (hg : IsPrimOn a b g dg) {s : ℝ}
    (hs : s ∈ Icc a b) : IntervalIntegrable dg volume a s :=
  hg.1.mono_set (by
    rw [uIcc_of_le hs.1, uIcc_of_le (hs.1.trans hs.2)]
    exact Icc_subset_Icc le_rfl hs.2)

omit [CompleteSpace F] in
theorem IsPrimOn.continuousOn {g dg : ℝ → F} (hab : a ≤ b) (hg : IsPrimOn a b g dg) :
    ContinuousOn g (Icc a b) := by
  have hc := (intervalIntegral.continuousOn_primitive_interval' hg.1 (left_mem_uIcc (a := a) (b := b))).const_add
    (g a)
  rw [uIcc_of_le hab] at hc
  exact hc.congr fun s hs => hg.2 s hs

theorem IsPrimOn.map_clm {g dg : ℝ → F} (hg : IsPrimOn a b g dg) (L : F →L[ℝ] G) :
    IsPrimOn a b (fun s => L (g s)) (fun s => L (dg s)) := by
  refine ⟨⟨L.integrable_comp hg.1.1, L.integrable_comp hg.1.2⟩, fun s hs => ?_⟩
  beta_reduce
  rw [hg.2 s hs, map_add, L.intervalIntegral_comp_comm (hg.intervalIntegrable_sub hs)]

omit [CompleteSpace F] in
theorem IsPrimOn.add {g dg g' dg' : ℝ → F} (hg : IsPrimOn a b g dg)
    (hg' : IsPrimOn a b g' dg') :
    IsPrimOn a b (fun s => g s + g' s) (fun s => dg s + dg' s) := by
  refine ⟨hg.1.add hg'.1, fun s hs => ?_⟩
  beta_reduce
  rw [hg.2 s hs, hg'.2 s hs, intervalIntegral.integral_add (hg.intervalIntegrable_sub hs)
    (hg'.intervalIntegrable_sub hs)]
  abel

omit [CompleteSpace F] in
theorem IsPrimOn.sum {κ : Type*} (S : Finset κ) {g dg : κ → ℝ → F}
    (hg : ∀ i ∈ S, IsPrimOn a b (g i) (dg i)) :
    IsPrimOn a b (fun s => ∑ i ∈ S, g i s) (fun s => ∑ i ∈ S, dg i s) := by
  refine ⟨?_, fun s hs => ?_⟩
  · have he : (∑ i ∈ S, dg i) = fun s => ∑ i ∈ S, dg i s := by
      funext s; simp only [Finset.sum_apply]
    rw [← he]
    exact IntervalIntegrable.sum S fun i hi => (hg i hi).1
  · rw [intervalIntegral.integral_finsetSum fun i hi => (hg i hi).intervalIntegrable_sub hs,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => (hg i hi).2 s hs

omit [CompleteSpace F] in
theorem IsPrimOn.congr {g dg g' dg' : ℝ → F} (hab : a ≤ b) (hg : IsPrimOn a b g dg)
    (hgg : ∀ s ∈ Icc a b, g s = g' s) (hd : ∀ s ∈ Icc a b, dg s = dg' s) :
    IsPrimOn a b g' dg' := by
  refine ⟨hg.1.congr fun σ hσ => ?_, fun s hs => ?_⟩
  · rw [uIoc_of_le hab] at hσ
    exact hd σ (Ioc_subset_Icc_self hσ)
  · rw [← hgg s hs, ← hgg a (left_mem_Icc.2 hab), hg.2 s hs]
    congr 1
    refine intervalIntegral.integral_congr fun σ hσ => hd σ ?_
    rw [uIcc_of_le hs.1] at hσ
    exact ⟨hσ.1, hσ.2.trans hs.2⟩

omit [CompleteSpace F] in
theorem IsPrimOn.const_smul {g dg : ℝ → F} (hg : IsPrimOn a b g dg) (c : ℝ) :
    IsPrimOn a b (fun s => c • g s) (fun s => c • dg s) := by
  refine ⟨hg.1.smul c, fun s hs => ?_⟩
  beta_reduce
  rw [hg.2 s hs, smul_add, intervalIntegral.integral_smul]

omit [CompleteSpace F] in
theorem IsPrimOn.zero : IsPrimOn a b (fun _ => (0 : F)) (fun _ => 0) :=
  ⟨intervalIntegrable_const, fun s _ => by simp⟩

/-- **Product rule** for scalar functions of integral type. -/
theorem IsPrimOn.mul {c dc g dg : ℝ → ℝ} (hab : a ≤ b) (hc : IsPrimOn a b c dc)
    (hg : IsPrimOn a b g dg) :
    IsPrimOn a b (fun s => c s * g s) (fun s => dc s * g s + c s * dg s) := by
  have hdc : IntegrableOn dc (Ioc a b) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hc.1
  have hdg : IntegrableOn dg (Ioc a b) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hg.1
  have hc' : ∀ s ∈ Icc a b, c s = c a + ∫ σ in Ioc a s, dc σ := fun s hs => by
    rw [hc.2 s hs, intervalIntegral.integral_of_le hs.1]
  have hg' : ∀ s ∈ Icc a b, g s = g a + ∫ σ in Ioc a s, dg σ := fun s hs => by
    rw [hg.2 s hs, intervalIntegral.integral_of_le hs.1]
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    (Coarse.product_rule_integral hab hdc hdg hc' hg').1, fun s hs => ?_⟩
  have h := Coarse.prod_prim hdc hdg hc' hg' s hs
  beta_reduce
  rw [h, intervalIntegral.integral_of_le hs.1]

end Basic

section Smul

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {a b : ℝ}

/-- **Product rule** for a scalar function times a vector function of integral type. -/
theorem IsPrimOn.smul {c dc : ℝ → ℝ} {g dg : ℝ → F} (hab : a ≤ b) (hc : IsPrimOn a b c dc)
    (hg : IsPrimOn a b g dg) :
    IsPrimOn a b (fun s => c s • g s) (fun s => dc s • g s + c s • dg s) := by
  have hint : IntervalIntegrable (fun s => dc s • g s + c s • dg s) volume a b := by
    refine (hc.1.smul_continuousOn ?_).add (hg.1.continuousOn_smul ?_)
    · rw [uIcc_of_le hab]; exact hg.continuousOn hab
    · rw [uIcc_of_le hab]; exact hc.continuousOn hab
  refine ⟨hint, fun s hs => ?_⟩
  let e := stdOrthonormalBasis ℝ F
  refine InnerProductSpace.ext_inner_left_basis e.toBasis fun j => ?_
  simp only [OrthonormalBasis.coe_toBasis]
  have hj := (hc.mul hab (hg.map_clm (innerSL ℝ (e j)))).2 s hs
  have hints : IntervalIntegrable (fun s => dc s • g s + c s • dg s) volume a s :=
    hint.mono_set (by
      rw [uIcc_of_le hs.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl hs.2)
  have hcomm := (innerSL ℝ (e j)).intervalIntegral_comp_comm hints
  simp only [innerSL_apply_apply] at hj hcomm
  rw [inner_add_right, inner_smul_right, inner_smul_right, hj, ← hcomm]
  simp only [inner_add_right, inner_smul_right]

/-- **Linear maps of integral type applied to a vector of integral type.** If `s ↦ C s ξ` has
density `Gd s ξ` for every `ξ` (with `Gd s` linear) and `J` has density `dJ`, then
`s ↦ C s (J s)` has density `Gd s (J s) + C s (dJ s)`. -/
theorem IsPrimOn.clm_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hab : a ≤ b) (C : ℝ → E →L[ℝ] F) (Gd : ℝ → E → F)
    (hGd : ∀ s ∈ Icc a b, IsLinearMap ℝ (Gd s))
    (hC : ∀ ξ, IsPrimOn a b (fun s => C s ξ) (fun s => Gd s ξ))
    {J dJ : ℝ → E} (hJ : IsPrimOn a b J dJ) :
    IsPrimOn a b (fun s => C s (J s)) (fun s => Gd s (J s) + C s (dJ s)) := by
  let bE := stdOrthonormalBasis ℝ E
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
      IsPrimOn a b (fun s => inner ℝ (bE i) (J s) • C s (bE i))
        (fun s => inner ℝ (bE i) (dJ s) • C s (bE i) + inner ℝ (bE i) (J s) • Gd s (bE i)) :=
    fun i _ => IsPrimOn.smul hab (by simpa using hJ.map_clm (innerSL ℝ (bE i))) (hC (bE i))
  refine (IsPrimOn.sum Finset.univ hterm).congr hab (fun s _ => ?_) (fun s hs => ?_)
  · conv_rhs => rw [← bE.sum_repr' (J s)]
    rw [map_sum]
    simp only [map_smul]
  · conv_rhs => rw [← bE.sum_repr' (J s), ← bE.sum_repr' (dJ s)]
    let Gl : E →ₗ[ℝ] F := (hGd s hs).mk' (Gd s)
    have hGl : ∀ x, Gd s x = Gl x := fun _ => rfl
    rw [hGl, map_sum, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, ← hGl, add_comm]

end Smul

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Gluing weighted primitives in time.** A `C¹` weight `ϖ` supported in `[α, β]` times a
function of integral type on the window `[α, β] ∩ [A, B]` is of integral type on all of `[A, B]`,
with the product-rule density `ϖ' g + ϖ ġ` (extension by zero: off the open interval `(α, β)` the
weight and its derivative both vanish, so the product is constant and its density vanishes on the
two outer pieces of `[A, B]`). Summing over a finite family of weights glues the pieces into one
function of integral type on `[A, B]`. The product rule with a scalar factor is proved in a general
Banach space by testing against continuous linear functionals, which separate points. -/

/-- A `C¹` scalar function is the primitive of its derivative on any interval. -/
theorem isPrimOn_of_contDiff {ϖ : ℝ → ℝ} (hϖ : ContDiff ℝ 1 ϖ) (a b : ℝ) :
    IsPrimOn a b ϖ (deriv ϖ) := by
  have hc : Continuous (deriv ϖ) := hϖ.continuous_deriv_one
  refine ⟨hc.intervalIntegrable a b, fun s _ => ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => (hϖ.differentiable_one x).hasDerivAt) (hc.intervalIntegrable a s)]
  abel

/-- A continuous function vanishing off `[α, β]` vanishes off `(α, β)`. -/
theorem eq_zero_of_notMem_Ioo {f : ℝ → ℝ} (hf : Continuous f) {α β : ℝ}
    (h : ∀ t, t ∉ Icc α β → f t = 0) {t : ℝ} (ht : t ∉ Ioo α β) : f t = 0 := by
  have hcl : IsClosed {x : ℝ | f x = 0} := isClosed_eq hf continuous_const
  rcases le_or_gt t α with hta | hta
  · have hsub : Iio α ⊆ {x : ℝ | f x = 0} := fun x hx =>
      h x fun hx' => (not_le.2 (Set.mem_Iio.1 hx)) hx'.1
    have hmem : t ∈ closure (Iio α) := by
      rw [closure_Iio]
      exact hta
    exact hcl.closure_subset_iff.2 hsub hmem
  · have htb : β ≤ t := not_lt.1 fun hb => ht ⟨hta, hb⟩
    have hsub : Ioi β ⊆ {x : ℝ | f x = 0} := fun x hx =>
      h x fun hx' => (not_le.2 (Set.mem_Ioi.1 hx)) hx'.2
    have hmem : t ∈ closure (Ioi β) := by
      rw [closure_Ioi]
      exact htb
    exact hcl.closure_subset_iff.2 hsub hmem

section Banach

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Product rule in a Banach space** for a scalar function of integral type times a vector
function of integral type (tested against continuous linear functionals, which separate points;
each test reduces to the scalar product rule `IsPrimOn.mul`). -/
theorem IsPrimOn.smul_banach {a b : ℝ} {c dc : ℝ → ℝ} {g dg : ℝ → F} (hab : a ≤ b)
    (hc : IsPrimOn a b c dc) (hg : IsPrimOn a b g dg) :
    IsPrimOn a b (fun s => c s • g s) (fun s => dc s • g s + c s • dg s) := by
  have hint : IntervalIntegrable (fun s => dc s • g s + c s • dg s) volume a b := by
    refine (hc.1.smul_continuousOn ?_).add (hg.1.continuousOn_smul ?_)
    · rw [uIcc_of_le hab]; exact hg.continuousOn hab
    · rw [uIcc_of_le hab]; exact hc.continuousOn hab
  refine ⟨hint, fun s hs => ?_⟩
  have hints : IntervalIntegrable (fun σ => dc σ • g σ + c σ • dg σ) volume a s :=
    hint.mono_set (by
      rw [uIcc_of_le hs.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl hs.2)
  beta_reduce
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun L => ?_
  have hj := (hc.mul hab (hg.map_clm L)).2 s hs
  beta_reduce at hj
  rw [map_add, ← L.intervalIntegral_comp_comm hints]
  simp only [map_add, map_smul, smul_eq_mul]
  exact hj

omit [CompleteSpace F] in
/-- **Extension by constants.** A function of integral type on `[a', b'] ⊆ [A, B]` that is
constant on `[A, a']` and on `[b', B]`, with a density vanishing on `(A, a']` and on `(b', B]`, is
of integral type on `[A, B]`. -/
theorem IsPrimOn.extend {A B a' b' : ℝ} (hA : A ≤ a') (hab' : a' ≤ b') (hB : b' ≤ B)
    {P D : ℝ → F} (hP : IsPrimOn a' b' P D)
    (hPA : ∀ t ∈ Icc A a', P t = P a') (hDA : ∀ t ∈ Ioc A a', D t = 0)
    (hPB : ∀ t ∈ Icc b' B, P t = P b') (hDB : ∀ t ∈ Ioc b' B, D t = 0) :
    IsPrimOn A B P D := by
  -- the density vanishes on the two outer pieces
  have hintA : ∀ t ∈ Icc A a', IntervalIntegrable D volume A t := fun t ht =>
    (intervalIntegrable_const (c := (0 : F))).congr fun σ hσ => by
      rw [uIoc_of_le ht.1] at hσ
      exact (hDA σ ⟨hσ.1, hσ.2.trans ht.2⟩).symm
  have hzA : ∀ t ∈ Icc A a', ∫ σ in A..t, D σ = 0 := fun t ht => by
    rw [intervalIntegral.integral_of_le ht.1]
    exact setIntegral_eq_zero_of_forall_eq_zero fun σ hσ => hDA σ ⟨hσ.1, hσ.2.trans ht.2⟩
  have hintB : ∀ t ∈ Icc b' B, IntervalIntegrable D volume b' t := fun t ht =>
    (intervalIntegrable_const (c := (0 : F))).congr fun σ hσ => by
      rw [uIoc_of_le ht.1] at hσ
      exact (hDB σ ⟨hσ.1, hσ.2.trans ht.2⟩).symm
  have hzB : ∀ t ∈ Icc b' B, ∫ σ in b'..t, D σ = 0 := fun t ht => by
    rw [intervalIntegral.integral_of_le ht.1]
    exact setIntegral_eq_zero_of_forall_eq_zero fun σ hσ => hDB σ ⟨hσ.1, hσ.2.trans ht.2⟩
  have hA' : a' ∈ Icc A a' := ⟨hA, le_rfl⟩
  have hint : IntervalIntegrable D volume A B :=
    ((hintA a' hA').trans hP.1).trans (hintB B ⟨hB, le_rfl⟩)
  refine ⟨hint, fun s hs => ?_⟩
  have hP0 : P A = P a' := hPA A ⟨le_rfl, hA⟩
  rcases le_total s a' with hsa | hsa
  · -- `s ∈ [A, a']`
    rw [hzA s ⟨hs.1, hsa⟩, add_zero, hPA s ⟨hs.1, hsa⟩, hP0]
  rcases le_total s b' with hsb | hsb
  · -- `s ∈ [a', b']`
    have hs' : s ∈ Icc a' b' := ⟨hsa, hsb⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (hintA a' hA')
      (hP.intervalIntegrable_sub hs'), hzA a' hA', zero_add, hP0]
    exact hP.2 s hs'
  · -- `s ∈ [b', B]`
    have hs' : s ∈ Icc b' B := ⟨hsb, hs.2⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals ((hintA a' hA').trans hP.1)
      (hintB s hs'), hzB s hs', add_zero,
      ← intervalIntegral.integral_add_adjacent_intervals (hintA a' hA') hP.1, hzA a' hA',
      zero_add, hPB s hs', hP0]
    exact hP.2 b' ⟨hab', le_rfl⟩

/-- **Weighted extension by zero.** A `C¹` weight supported in `[α, β]` times a primitive on
`[α, β] ∩ [A, B]` is a primitive on `[A, B]` with the product-rule density. -/
theorem IsPrimOn.weight_extend {A B α β : ℝ} (hAB : A ≤ B) {ϖ : ℝ → ℝ} (hϖ : ContDiff ℝ 1 ϖ)
    (hsupp : ∀ t, ϖ t ≠ 0 → t ∈ Icc α β) {g dg : ℝ → F}
    (hg : IsPrimOn (max α A) (min β B) g dg) :
    IsPrimOn A B (fun t => ϖ t • g t) (fun t => deriv ϖ t • g t + ϖ t • dg t) := by
  have hz : ∀ t, t ∉ Icc α β → ϖ t = 0 := fun t ht =>
    Classical.byContradiction fun h => ht (hsupp t h)
  have hdz : ∀ t, t ∉ Icc α β → deriv ϖ t = 0 := fun t ht => by
    have hev : ϖ =ᶠ[nhds t] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (isClosed_Icc.isOpen_compl.mem_nhds (Set.mem_compl ht))
        fun x hx => hz x (Set.notMem_of_mem_compl hx)
    rw [hev.deriv_eq]
    exact deriv_const t 0
  -- off the open interval `(α, β)` the weight and its derivative vanish
  have hw : ∀ t, t ∉ Ioo α β →
      ϖ t • g t = 0 ∧ deriv ϖ t • g t + ϖ t • dg t = 0 := fun t ht => by
    have h1 : ϖ t = 0 := eq_zero_of_notMem_Ioo hϖ.continuous hz ht
    have h2 : deriv ϖ t = 0 := eq_zero_of_notMem_Ioo hϖ.continuous_deriv_one hdz ht
    refine ⟨?_, ?_⟩
    · rw [h1, zero_smul]
    · rw [h1, h2, zero_smul, zero_smul, add_zero]
  rcases lt_or_ge (min β B) (max α A) with hlt | hle
  · -- the window is empty: the weight and its derivative vanish on `[A, B]`
    have hout : ∀ t ∈ Icc A B, t ∉ Ioo α β := fun t ht hto =>
      (not_le.2 hlt) ((max_le hto.1.le ht.1).trans (le_min hto.2.le ht.2))
    refine IsPrimOn.congr hAB IsPrimOn.zero (fun s hs => ?_) (fun s hs => ?_)
    · exact (hw s (hout s hs)).1.symm
    · exact (hw s (hout s hs)).2.symm
  -- the window `[max α A, min β B]` is nonempty
  have hPA : ∀ t ∈ Icc A (max α A), ϖ t • g t = ϖ (max α A) • g (max α A) := by
    intro t ht
    rcases ht.2.eq_or_lt with heq | hlt
    · rw [heq]
    have htα : t < α := (lt_max_iff.1 hlt).resolve_right (not_lt.2 ht.1)
    rw [max_eq_left (ht.1.trans htα.le), (hw t fun h => (not_lt.2 htα.le) h.1).1,
      (hw α fun h => lt_irrefl α h.1).1]
  have hDA : ∀ t ∈ Ioc A (max α A), deriv ϖ t • g t + ϖ t • dg t = 0 := by
    intro t ht
    have htα : t ≤ α := (le_max_iff.1 ht.2).resolve_right (not_le.2 ht.1)
    exact (hw t fun h => (not_lt.2 htα) h.1).2
  have hPB : ∀ t ∈ Icc (min β B) B, ϖ t • g t = ϖ (min β B) • g (min β B) := by
    intro t ht
    rcases ht.1.eq_or_lt with heq | hlt
    · rw [heq]
    have hβt : β < t := (min_lt_iff.1 hlt).resolve_right (not_lt.2 ht.2)
    rw [min_eq_left (hβt.le.trans ht.2), (hw t fun h => (not_lt.2 hβt.le) h.2).1,
      (hw β fun h => lt_irrefl β h.2).1]
  have hDB : ∀ t ∈ Ioc (min β B) B, deriv ϖ t • g t + ϖ t • dg t = 0 := by
    intro t ht
    have hβt : β < t := (min_lt_iff.1 ht.1).resolve_right (not_lt.2 ht.2)
    exact (hw t fun h => (not_lt.2 hβt.le) h.2).2
  exact ((isPrimOn_of_contDiff hϖ (max α A) (min β B)).smul_banach hle hg).extend
    (le_max_right α A) hle (min_le_right β B) hPA hDA hPB hDB

/-- **Gluing weighted primitives.** A finite sum of `C¹` weights `ϖ k` supported in
`[α k, β k]`, each multiplying a primitive on its window `[α k, β k] ∩ [A, B]`, is a primitive on
`[A, B]` with the summed product-rule densities. -/
theorem IsPrimOn.glue {κ : Type*} (S : Finset κ) {A B : ℝ} (hAB : A ≤ B) (ϖ : κ → ℝ → ℝ)
    (α β : κ → ℝ) (g dg : κ → ℝ → F) (hϖ : ∀ k ∈ S, ContDiff ℝ 1 (ϖ k))
    (hsupp : ∀ k ∈ S, ∀ t, ϖ k t ≠ 0 → t ∈ Icc (α k) (β k))
    (hg : ∀ k ∈ S, IsPrimOn (max (α k) A) (min (β k) B) (g k) (dg k)) :
    IsPrimOn A B (fun t => ∑ k ∈ S, ϖ k t • g k t)
      (fun t => ∑ k ∈ S, (deriv (ϖ k) t • g k t + ϖ k t • dg k t)) :=
  IsPrimOn.sum S fun k hk => (hg k hk).weight_extend hAB (hϖ k hk) (hsupp k hk)

end Banach

end AVRegularity.CycleComparison.Reconstruction
end
