-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Velocity.Port.AppB2Smoothness
import AVenhance.Infra.FaaDiBruno.Composition
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open Homogenization AVenhance MeasureTheory Filter Topology
open scoped ContDiff BigOperators
namespace AVRegularity.Velocity.Port.RecursionIncrement

/-! The first all-order stream increment estimate, copied from the upstream
Section 2 proof and expressed using the OC recursion and scale record. -/

open AVRegularity.Velocity.Port.Section2Scales
open AVRegularity.Velocity.Port.Section2Induction
open AVRegularity.Velocity.Port.Section2FlowIdentities
open AVRegularity.Velocity.Port.ExplicitBarNorm

/-- The fast cutoff of the recursion. -/
def streamRecursionCutoff {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) (k : ℤ) (t : ℝ) : ℝ :=
  slowEnvelope α q Λ m (ocLabel α q Λ m k) t *
    ζ ((t - (k : ℝ) * D.tau m) / D.tau m)

/-- A nonzero fast-profile value lies within its support radius. -/
theorem zeta_nonzero_distance {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) (k : ℤ) (t : ℝ)
    (hne : ζ ((t - (k : ℝ) * D.tau m) / D.tau m) ≠ 0) :
    |t - (k : ℝ) * D.tau m| ≤ (2 / 3 : ℝ) * D.tau m := by
  have hτ : 0 < D.tau m := by
    rw [D.tau_eq_oc]
    exact AVRegularity.Construction.Stream.ocTau_pos (by
      have hΛ := D.hΛ
      omega)
  have hmem : ((t - (k : ℝ) * D.tau m) / D.tau m) ∈
      Set.Ioo (-(2 / 3 : ℝ)) (2 / 3) := by
    have hsupp : ((t - (k : ℝ) * D.tau m) / D.tau m) ∈ Function.support ζ := by
      change ζ ((t - (k : ℝ) * D.tau m) / D.tau m) ≠ 0
      exact hne
    have hts : ((t - (k : ℝ) * D.tau m) / D.tau m) ∈ tsupport ζ :=
      subset_tsupport ζ hsupp
    exact D.hζ.2.2.1 hts
  have habs : |(t - (k : ℝ) * D.tau m) / D.tau m| ≤ 2 / 3 :=
    abs_le.mpr ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
  rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at habs
  simpa [abs_of_pos hτ] using habs

/-- A nonzero fast cutoff can only have either of the two adjacent integer
labels at a fixed time. -/
theorem active_recursion_index {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) (k : ℤ) (r t : ℝ)
    (hclose : |r - t| < D.tau m / 6)
    (hactive : streamRecursionCutoff D m k r ≠ 0) :
    k ∈ Set.Icc (⌊t / D.tau m⌋ : ℤ) ((⌊t / D.tau m⌋ : ℤ) + 1) := by
  have hτ : 0 < D.tau m := by
    rw [D.tau_eq_oc]
    exact AVRegularity.Construction.Stream.ocTau_pos (by
      have hΛ := D.hΛ
      omega)
  have hζ : ζ ((r - (k : ℝ) * D.tau m) / D.tau m) ≠ 0 := by
    intro hz
    apply hactive
    simp [streamRecursionCutoff, hz]
  have hdist := zeta_nonzero_distance D m k r hζ
  have htriangle : |t - (k : ℝ) * D.tau m| < (5 / 6 : ℝ) * D.tau m := by
    calc
      |t - (k : ℝ) * D.tau m| =
          |(t - r) + (r - (k : ℝ) * D.tau m)| := by congr 1; ring
      _ ≤ |t - r| + |r - (k : ℝ) * D.tau m| := abs_add_le _ _
      _ < D.tau m / 6 + (2 / 3) * D.tau m := by
        have hclose' : |t - r| < D.tau m / 6 := by
          simpa [abs_sub_comm] using hclose
        nlinarith [hclose', hdist]
      _ = (5 / 6 : ℝ) * D.tau m := by ring
  have hquot : |t / D.tau m - (k : ℝ)| < 1 := by
    have hscaled : |t / D.tau m - (k : ℝ)| < 5 / 6 := by
      have hEq : t / D.tau m - (k : ℝ) =
          (t - (k : ℝ) * D.tau m) / D.tau m := by field_simp
      rw [hEq, abs_div, abs_of_pos hτ]
      exact (div_lt_iff₀ hτ).2 htriangle
    linarith
  have hquot' := abs_lt.mp hquot
  have hfloorle : (⌊t / D.tau m⌋ : ℝ) ≤ t / D.tau m :=
    Int.floor_le (t / D.tau m)
  have hfloorlt : t / D.tau m < (⌊t / D.tau m⌋ : ℝ) + 1 :=
    Int.lt_floor_add_one (t / D.tau m)
  simp only [Set.mem_Icc]
  constructor
  · by_contra hnot
    have hk : k < ⌊t / D.tau m⌋ := lt_of_not_ge hnot
    have hk' : (k : ℝ) + 1 ≤ (⌊t / D.tau m⌋ : ℝ) := by
      exact_mod_cast (show k + 1 ≤ ⌊t / D.tau m⌋ by omega)
    linarith [hquot'.2, hfloorle]
  · by_contra hnot
    have hk : ⌊t / D.tau m⌋ + 2 ≤ k := by omega
    have hk' : (⌊t / D.tau m⌋ : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hk
    have hquotlow : (k : ℝ) - 1 < t / D.tau m := by linarith [hquot'.1]
    linarith [hfloorlt]

/-- The radius and jet-size sequences are positive. -/
theorem section2_radius_nonneg {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) : 0 ≤ D.radius m := by
  induction m with
  | zero => rw [D.radius_zero]; norm_num
  | succ m ih =>
    rw [D.radius_step m]
    have he : 0 < D.epsilon (m + 1) := D.epsilon_pos _
    positivity

theorem section2_radius_pos {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) : 0 < D.radius m :=
  AVRegularity.Velocity.Port.Section2Scales.section2_radius_pos D m

theorem section2_amplitude_pos {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) : 0 < D.jetSize m :=
  AVRegularity.Velocity.Port.Section2Scales.section2_amplitude_pos D m

/-- The source composition radius identity is independent of the construction. -/
theorem composition_radius_identity {R e : ℝ} (hR : 0 < R) (he : 0 < e) :
    ((9 / 8 : ℝ) * R) *
        (1 + 2 * (5 * (8 / 9 : ℝ) * R⁻¹) * (2 * Real.pi / e)) =
      (9 / 8) * R + 20 * Real.pi / e := by
  field_simp [ne_of_gt hR, ne_of_gt he]
  ring

/-- The Section 2 radius remains bounded by the next wavelength scale. -/
theorem section2_recursion_radius_bound {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) (hm : 1 ≤ m) :
    (9 / 8) * D.radius (m - 1) + 20 * Real.pi * (D.epsilon m)⁻¹ ≤
      2 ^ 7 * (D.epsilon m)⁻¹ := by
  have hR : D.radius (m - 1) ≤ 131 * (D.epsilon (m - 1))⁻¹ := by
    by_cases hm1 : m = 1
    · subst m
      rw [D.radius_zero, D.epsilon_zero]
      norm_num
    · have hmPrev : 1 ≤ m - 1 := by omega
      exact AVRegularity.Velocity.Port.Scalars.radius_recurrence_bound D hmPrev
  have hePrev : 0 < D.epsilon (m - 1) := D.epsilon_pos _
  have he : 0 < D.epsilon m := D.epsilon_pos _
  have hsep : D.epsilon m ≤ (1 / 128 : ℝ) * D.epsilon (m - 1) := by
    have hratio := D.epsilon_ratio m hm
    have hΛ : (128 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast D.hΛ
    have hmul : D.epsilon m * (Λ : ℝ) ≤ D.epsilon (m - 1) := by
      simpa [mul_comm] using (le_div_iff₀ he).mp hratio
    have h128 : D.epsilon m * 128 ≤ D.epsilon (m - 1) :=
      (mul_le_mul_of_nonneg_left hΛ he.le).trans hmul
    have hdiv : D.epsilon m ≤ D.epsilon (m - 1) / 128 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 128)).2 h128
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  have hRscaled : D.epsilon m * D.radius (m - 1) ≤ (131 : ℝ) / 128 := by
    calc
      D.epsilon m * D.radius (m - 1) ≤
          D.epsilon m * (131 * (D.epsilon (m - 1))⁻¹) :=
        mul_le_mul_of_nonneg_left hR he.le
      _ = 131 * (D.epsilon m / D.epsilon (m - 1)) := by
        field_simp [he.ne', hePrev.ne']
      _ ≤ 131 / 128 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply (div_le_iff₀ hePrev).2
        nlinarith [hsep]
  have htarget : (9 / 8 : ℝ) * ((131 : ℝ) / 128) + 20 * Real.pi ≤ 128 := by
    nlinarith [Real.pi_lt_four]
  have hscaled : D.epsilon m *
      ((9 / 8) * D.radius (m - 1) + 20 * Real.pi * (D.epsilon m)⁻¹) ≤ 128 := by
    have hcancel : D.epsilon m *
        (20 * Real.pi * (D.epsilon m)⁻¹) = 20 * Real.pi := by field_simp [he.ne']
    calc
      _ = (9 / 8) * (D.epsilon m * D.radius (m - 1)) +
          D.epsilon m * (20 * Real.pi * (D.epsilon m)⁻¹) := by ring
      _ = (9 / 8) * (D.epsilon m * D.radius (m - 1)) + 20 * Real.pi := by rw [hcancel]
      _ ≤ (9 / 8) * ((131 : ℝ) / 128) + 20 * Real.pi := by
        gcongr
      _ ≤ 128 := htarget
  apply (le_div_iff₀ he).2
  simpa [show (2 : ℝ) ^ 7 = 128 by norm_num, mul_comm] using hscaled

/-- The shear has the sine seminorm estimate at every order. -/
theorem ocShear_barNorm_le {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) (k : ℤ) (n : ℕ) :
    AVenhance.barNorm n (2 * Real.pi / D.epsilon m)
      (ocShear α q Λ m k) ≤
      ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) := by
  let E := D.epsilon m
  have hE : 0 < E := D.epsilon_pos m
  have hA : 0 ≤ E ^ (1 + α) := Real.rpow_nonneg hE.le _
  have hω : 0 ≤ 2 * Real.pi / E := by positivity
  have heq : ocShear α q Λ m k = fun x => E ^ (1 + α) *
      (if k % 4 = 1 then Real.sin ((2 * Real.pi / E) * x 0)
       else if k % 4 = 3 then Real.sin ((2 * Real.pi / E) * x 1) else 0) := by
    funext x
    dsimp [E, ocShear]
    rw [D.epsilon_eq_oc m]
    unfold AVenhance.psi0
    have hcoord (i : Fin 2) :
        2 * Real.pi * ((ocEpsilon q Λ m)⁻¹ * x i) =
          (2 * Real.pi / ocEpsilon q Λ m) * x i := by
      rw [div_eq_mul_inv]
      ring
    by_cases h1 : k % 4 = 1
    · simp only [ite_eq_left h1]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hcoord 0]
    · by_cases h3 : k % 4 = 3
      · simp only [ite_eq_right h1, ite_eq_left h3]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hcoord 1]
      · simp only [ite_eq_right h1, ite_eq_right h3]
  rw [heq]
  by_cases h1 : k % 4 = 1
  · simp only [h1, ite_true]
    simpa [E, mul_assoc] using
      AVRegularity.Velocity.Port.ExplicitBarNorm.barNorm_sine_le
        (E ^ (1 + α)) (2 * Real.pi / E) hA hω 0 n (by positivity) le_rfl
  · by_cases h3 : k % 4 = 3
    · simp only [ite_eq_right h1, ite_eq_left h3]
      simpa [E, mul_assoc] using
        AVRegularity.Velocity.Port.ExplicitBarNorm.barNorm_sine_le
          (E ^ (1 + α)) (2 * Real.pi / E) hA hω 1 n (by positivity) le_rfl
    · simp only [ite_eq_right h1, ite_eq_right h3]
      simp [AVenhance.barNorm]

/-- Smoothness of the shear profile at every spatial order. -/
theorem ocShear_contDiff {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (_D : JetRecursionData α s q Λ ζ) (m : ℕ) (k : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (ocShear α q Λ m k) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 =>
    ocEpsilon q Λ m ^ (1 + α) *
      AVenhance.psi0 k ((ocEpsilon q Λ m)⁻¹ • x))
  have hcoord (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => Real.sin
        (2 * Real.pi * (((ocEpsilon q Λ m)⁻¹ • x) j))) := by
    fun_prop
  have hconst : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec 2 => ocEpsilon q Λ m ^ (1 + α)) := contDiff_const
  by_cases h1 : k % 4 = 1
  · simpa [AVenhance.psi0, h1] using hconst.mul (hcoord 0)
  · by_cases h3 : k % 4 = 3
    · simpa [AVenhance.psi0, h1, h3] using hconst.mul (hcoord 1)
    · simp [AVenhance.psi0, h1, h3]
      exact contDiff_const

/-- Nonzero slow envelopes lie in the renewal interval used by the source
inverse-flow window estimate. -/
theorem slowEnvelope_nonzero_distance {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) (hm : 1 ≤ m)
    (l : ℤ) (t : ℝ)
    (hne : slowEnvelope α q Λ m l t ≠ 0) :
    |t - (l : ℝ) * ocTauPP α q Λ m| ≤ ocTauPP α q Λ m / 2 := by
  have hτP : 0 < ocTauP α q Λ m := by
    rw [← D.tauP_eq_oc m]
    exact D.tauP_pos m hm
  have hleft : Real.smoothTransition
      ((t - ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) /
        ocTauP α q Λ m) ≠ 0 := by
    intro hz
    apply hne
    rw [slowEnvelope, hz]
    simp
  have hright : Real.smoothTransition
      ((((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m - t) /
        ocTauP α q Λ m) ≠ 0 := by
    intro hz
    apply hne
    rw [slowEnvelope, hz]
    simp
  have hleftArg : 0 <
      (t - ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) /
        ocTauP α q Λ m := by
    by_contra hnot
    exact hleft (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hnot))
  have hrightArg : 0 <
      (((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m - t) /
        ocTauP α q Λ m := by
    by_contra hnot
    exact hright (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hnot))
  have hleftNum : 0 <
      t - ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m :=
    (div_pos_iff_of_pos_right hτP).mp hleftArg
  have hrightNum : 0 <
      ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m - t :=
    (div_pos_iff_of_pos_right hτP).mp hrightArg
  have hτPP : 0 < ocTauPP α q Λ m := by
    rw [← D.tauPP_eq_oc m]
    exact D.tauPP_pos m hm
  rw [abs_le]
  constructor <;> nlinarith [hleftNum, hrightNum, hτP, hτPP]

/-- The composed shear profile estimate in the source composition radius. -/
theorem section2_composed_profile_barNorm_bound
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (happB2 : AppB2InverseFlowData D Φ hseq)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2StreamInductionHypothesis D Φ (m - 1))
    (s u : ℝ) (hu : |u| ≤ (2 : ℝ) ^ (-6 : ℤ) * (D.jetSize (m - 1))⁻¹)
    (k : ℤ) (n : ℕ) :
    AVenhance.barNorm n ((9 / 8) * D.radius (m - 1) +
      20 * Real.pi / D.epsilon m)
      (fun x : Vec 2 => ocShear α q Λ m k
        (constructionFlowInv D hseq (m - 1) (s + u) x s)) ≤
      ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) := by
  let g : Vec 2 → Vec 2 := fun x =>
    constructionFlowInv D hseq (m - 1) (s + u) x s
  let Rh : ℝ := 2 * Real.pi / D.epsilon m
  let Rg : ℝ := (9 / 8) * D.radius (m - 1)
  let Cg : ℝ := 5 * (8 / 9 : ℝ) * (D.radius (m - 1))⁻¹
  let Ch : ℝ := 5 * D.epsilon m ^ (1 + α)
  have hRprev : 0 < D.radius (m - 1) := section2_radius_pos D _
  have he : 0 < D.epsilon m := D.epsilon_pos _
  have hRh : 0 < Rh := by dsimp [Rh]; positivity
  have hRg : 0 < Rg := by dsimp [Rg]; positivity
  have hCg : 0 < Cg := by dsimp [Cg]; positivity
  have hCh : 0 < Ch := by dsimp [Ch]; positivity
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (ocShear α q Λ m k) :=
    ocShear_contDiff D m k
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    dsimp [g]
    exact happB2.inverse_spatial_smooth m hm s u
  have hH : ∀ j : ℕ, j ≤ n →
      FaaDiBruno.snorm (ocShear α q Λ m k) j Rh ≤ ENNReal.ofReal Ch := by
    intro j hj
    rw [← barNorm_eq_snorm (f := ocShear α q Λ m k)
      (hψ.of_le (by simp))]
    dsimp [Rh, Ch]
    exact ocShear_barNorm_le D m k j
  have hG : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      FaaDiBruno.snorm g j Rg ≤ ENNReal.ofReal Cg := by
    intro j hj1 hjn
    dsimp [g, Rg, Cg]
    exact happB2.inverse_transport_estimate m hm hprev s u hu j hj1
  have hcomp := FaaDiBruno.compositionEstimate10528
    (d := 2) (m := n) (ocShear α q Λ m k) g
    (hψ.of_le (by simp)) (hg.of_le (by simp))
    hCh hCg hRh hRg hH hG n le_rfl
  have hcompRadius := composition_radius_identity hRprev he
  have hradius : Rg * (1 + (2 : ℝ) * Cg * Rh) =
      (9 / 8) * D.radius (m - 1) + 20 * Real.pi / D.epsilon m := by
    dsimp [Rg, Cg, Rh]
    exact hcompRadius
  have hcomp' :
      FaaDiBruno.snorm (ocShear α q Λ m k ∘ g) n
        ((9 / 8) * D.radius (m - 1) + 20 * Real.pi / D.epsilon m) ≤
        ENNReal.ofReal Ch := by
    change FaaDiBruno.snorm (ocShear α q Λ m k ∘ g) n
      (Rg * (1 + (2 : ℝ) * Cg * Rh)) ≤ ENNReal.ofReal Ch at hcomp
    rw [hradius] at hcomp
    exact hcomp
  have hcompSmooth : ContDiff ℝ n (ocShear α q Λ m k ∘ g) :=
    (hψ.comp hg).of_le (by simp)
  change AVenhance.barNorm n ((9 / 8) * D.radius (m - 1) +
      20 * Real.pi / D.epsilon m) (ocShear α q Λ m k ∘ g) ≤ _
  rw [barNorm_eq_snorm (f := ocShear α q Λ m k ∘ g) hcompSmooth]
  simpa [g, Ch, Function.comp_def] using hcomp'

/-- Multiplication by a spatially constant cutoff in `[0,1]` cannot increase
the barred seminorm. -/
theorem barNorm_mul_const_Icc_le {f : Vec 2 → ℝ} {n : ℕ} {R c : ℝ}
    (hf : ContDiff ℝ n f) (hc : c ∈ Set.Icc 0 1) :
    AVenhance.barNorm n R (fun x => c * f x) ≤ AVenhance.barNorm n R f := by
  have hcf : ContDiff ℝ n (fun x : Vec 2 => c * f x) := contDiff_const.mul hf
  rw [barNorm_eq_pointwise _ n R hcf, barNorm_eq_pointwise f n R hf]
  have hderiv (J : Fin n → Fin 2) (x : Vec 2) :
      ‖iteratedFDeriv ℝ n (fun y : Vec 2 => c * f y) x
          (fun j => basisVec (J j))‖ₑ =
        ENNReal.ofReal c *
          ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ := by
    rw [show (fun y : Vec 2 => c * f y) = fun y => c • f y by
      funext y
      simp [smul_eq_mul]]
    rw [iteratedFDeriv_const_smul_apply' hf.contDiffAt]
    simp [Real.enorm_of_nonneg hc.1, smul_eq_mul]
  have hinner :
      (⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
        ‖iteratedFDeriv ℝ n (fun y : Vec 2 => c * f y) x
          (fun j => basisVec (J j))‖ₑ) ≤
      ENNReal.ofReal c * (⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
        ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ) := by
    apply iSup_le
    intro J
    apply iSup_le
    intro x
    rw [hderiv]
    exact mul_le_mul_of_nonneg_left
      (le_iSup_of_le J (le_iSup_of_le x le_rfl)) (by positivity)
  have hcENN : ENNReal.ofReal c ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hc.2
  calc
    _ ≤ ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
          (ENNReal.ofReal R)⁻¹ ^ n *
            (ENNReal.ofReal c * (⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
              ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ)) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
          (ENNReal.ofReal R)⁻¹ ^ n * ENNReal.ofReal c) *
            (⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
              ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ) := by ac_rfl
    _ ≤ (ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
          (ENNReal.ofReal R)⁻¹ ^ n * 1) *
            (⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
              ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcENN (by positivity)) (by positivity)
    _ = _ := by simp

/-- Enlarging the radius decreases the barred seminorm. -/
theorem barNorm_radius_monotone {f : Vec 2 → ℝ} {n : ℕ} {R S : ℝ}
    (hf : ContDiff ℝ n f) (hR : 0 < R) (hRS : R ≤ S) :
    AVenhance.barNorm n S f ≤ AVenhance.barNorm n R f := by
  by_cases hS : 0 < S
  · rw [barNorm_radius_change hf hR hS]
    have hratio : 0 ≤ R / S ∧ R / S ≤ 1 := by
      constructor
      · exact (div_pos hR hS).le
      · exact (div_le_one hS).2 hRS
    have hq : ENNReal.ofReal (R / S) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hratio.2
    have hq0 : 0 ≤ ENNReal.ofReal (R / S) := by positivity
    have hpAll (k : ℕ) : ENNReal.ofReal (R / S) ^ k ≤ 1 := by
      induction k with
      | zero => simp
      | succ k ih => exact pow_le_one₀ hq0 hq
    have hp : ENNReal.ofReal (R / S) ^ n ≤ 1 := hpAll n
    calc
      AVenhance.barNorm n R f * ENNReal.ofReal (R / S) ^ n ≤
          AVenhance.barNorm n R f * 1 :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = AVenhance.barNorm n R f := by simp
  · have hS' : S ≤ 0 := le_of_not_gt hS
    linarith

/-- The finite-overlap `ocNextStream` recursion gives the
composition-radius increment estimate and the Section 2 scale-radius bound. -/
theorem stream_increment_bounds_at_scale
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (happB2 : AppB2InverseFlowData D Φ hseq)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2StreamInductionHypothesis D Φ (m - 1))
    (t : ℝ) (n : ℕ) :
    AVenhance.barNorm n ((9 / 8) * D.radius (m - 1) +
        20 * Real.pi / D.epsilon m) (Φ m t - Φ (m - 1) t) ≤
      ENNReal.ofReal (10 * D.epsilon m ^ (1 + α)) ∧
    AVenhance.barNorm n (2 ^ 7 * (D.epsilon m)⁻¹)
        (Φ m t - Φ (m - 1) t) ≤
      ENNReal.ofReal (10 * D.epsilon m ^ (1 + α)) := by
  classical
  obtain ⟨hφ, hrec⟩ := hseq.2 m hm
  have hφeq : hφ = AVRegularity.Velocity.streamSeq_admissible
      D.hζ D.hΛ hseq (m - 1) := Subsingleton.elim _ _
  let S : Finset ℤ :=
    {(⌊t / D.tau m⌋ : ℤ), (⌊t / D.tau m⌋ : ℤ) + 1}
  let d : ℤ → Vec 2 → ℝ := fun k x =>
    streamRecursionCutoff D m k t *
      ocShear α q Λ m k
        (constructionFlowInv D hseq (m - 1) t x
          ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m))
  have hzero (k : ℤ) (hk : k ∉ S) (x : Vec 2) : d k x = 0 := by
    have hcut : streamRecursionCutoff D m k t = 0 := by
      by_contra hne
      have hpair := active_recursion_index D m k t t
        (by have hτ : 0 < D.tau m := by
              rw [D.tau_eq_oc]
              exact AVRegularity.Construction.Stream.ocTau_pos (by
                have hΛ := D.hΛ
                omega)
            simp [hτ]) hne
      have hpair' : ⌊t / D.tau m⌋ ≤ k ∧ k ≤ ⌊t / D.tau m⌋ + 1 := by
        simpa using hpair
      have heq : k = ⌊t / D.tau m⌋ ∨
          k = ⌊t / D.tau m⌋ + 1 := by omega
      have hmem : k ∈ S := by
        rcases heq with h | h <;> simp [S, h]
      exact hk hmem
    dsimp [d]
    rw [hcut]
    simp
  have hincrement :
      (fun x : Vec 2 => Φ m t x - Φ (m - 1) t x) = ∑ k ∈ S, d k := by
    funext x
    have htsum : (∑' k : ℤ, d k x) = ∑ k ∈ S, d k x :=
      tsum_eq_sum (s := S) (fun k hk => hzero k hk x)
    have hrecPoint : Φ m t x = Φ (m - 1) t x + ∑' k : ℤ, d k x := by
      have hpoint := congrArg (fun f : ℝ → Vec 2 → ℝ => f t x) hrec
      have hflow (k : ℤ) (y : Vec 2) :
          AVRegularity.Velocity.Port.Section2FlowIdentities.constructionFlowInv
              D hseq (m - 1) t y ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m) =
            AVenhance.flowInv (streamVel (Φ (m - 1))) hφ.vel_continuous
              hφ.vel_lipschitz t y ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m) := by
        dsimp [AVRegularity.Velocity.Port.Section2FlowIdentities.constructionFlowInv,
          AVRegularity.Velocity.Port.Section2FlowIdentities.streamFlowInv,
          AVRegularity.Velocity.Port.Section2FlowIdentities.streamFlow]
      rw [AVRegularity.ocNextStream] at hpoint
      have htermRec (k : ℤ) :
          slowEnvelope α q Λ m (ocLabel α q Λ m k) t *
            ζ ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) *
            ocShear α q Λ m k
              (AVenhance.flowInv (streamVel (Φ (m - 1))) hφ.vel_continuous
                hφ.vel_lipschitz t x
                ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m)) = d k x := by
        dsimp [d, streamRecursionCutoff]
        rw [D.tau_eq_oc m, hflow k x]
      have hsumRec :
          (∑' k : ℤ, slowEnvelope α q Λ m (ocLabel α q Λ m k) t *
            ζ ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) *
            ocShear α q Λ m k
              (AVenhance.flowInv (streamVel (Φ (m - 1))) hφ.vel_continuous
                hφ.vel_lipschitz t x
                ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m))) =
          ∑' k : ℤ, d k x := tsum_congr htermRec
      rw [hsumRec] at hpoint
      exact hpoint
    rw [hrecPoint, htsum]
    simp [Finset.sum_apply, sub_eq_add_neg, add_assoc]
  let E : ℝ := D.epsilon m
  let Rcomp : ℝ := (9 / 8) * D.radius (m - 1) + 20 * Real.pi / E
  let Rout : ℝ := 2 ^ 7 * E⁻¹
  have hE : 0 < E := by dsimp [E]; exact D.epsilon_pos m
  have hRcomp : 0 < Rcomp := by
    have hRprev := section2_radius_nonneg D (m - 1)
    dsimp [Rcomp]
    positivity
  have hRout : 0 < Rout := by dsimp [Rout, E]; positivity
  have hRcompOut : Rcomp ≤ Rout := by
    have h := section2_recursion_radius_bound D m hm
    simpa [Rcomp, Rout, E, div_eq_mul_inv] using h
  have hcutIcc (k : ℤ) : streamRecursionCutoff D m k t ∈ Set.Icc 0 1 := by
    have hslow : slowEnvelope α q Λ m (ocLabel α q Λ m k) t ∈ Set.Icc 0 1 := by
      dsimp [slowEnvelope]
      refine ⟨mul_nonneg (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.nonneg _), ?_⟩
      calc
        _ ≤ 1 * Real.smoothTransition _ :=
          mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
            (Real.smoothTransition.nonneg _)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left
          (Real.smoothTransition.le_one _) (by norm_num)
        _ = 1 := by ring
    have hfast : ζ ((t - (k : ℝ) * D.tau m) / D.tau m) ∈ Set.Icc 0 1 :=
      D.hζ.2.2.2.1 _
    constructor
    · exact mul_nonneg hslow.1 hfast.1
    · have htmp := mul_le_mul_of_nonneg_right hslow.2 hfast.1
      calc
        slowEnvelope α q Λ m (ocLabel α q Λ m k) t *
            ζ ((t - (k : ℝ) * D.tau m) / D.tau m) ≤ 1 * ζ _ := htmp
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hfast.2 (by norm_num)
        _ = 1 := by ring
  have htermSmooth (k : ℤ) : ContDiff ℝ n (d k) := by
    let sₖ : ℝ := (ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m
    let uₖ : ℝ := t - sₖ
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 =>
        constructionFlowInv D hseq (m - 1) (sₖ + uₖ) x sₖ) := by
      exact happB2.inverse_spatial_smooth m hm sₖ uₖ
    have hprofileTop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 =>
        ocShear α q Λ m k
          (constructionFlowInv D hseq (m - 1) (sₖ + uₖ) x sₖ)) :=
      (ocShear_contDiff D m k).comp hg
    have hst : sₖ + uₖ = t := by dsimp [sₖ, uₖ]; ring
    have htermEq : d k = fun x : Vec 2 =>
        streamRecursionCutoff D m k t *
          ocShear α q Λ m k
            (constructionFlowInv D hseq (m - 1) t x sₖ) := by
      funext x
      dsimp [d]
    rw [htermEq]
    have hprof : ContDiff ℝ n (fun x : Vec 2 =>
        ocShear α q Λ m k
          (constructionFlowInv D hseq (m - 1) t x sₖ)) := by
      have hprofile' : ContDiff ℝ n (fun x : Vec 2 =>
          ocShear α q Λ m k
            (constructionFlowInv D hseq (m - 1) (sₖ + uₖ) x sₖ)) :=
        hprofileTop.of_le (by simp)
      simpa only [hst] using hprofile'
    exact contDiff_const.mul hprof
  have hprofileBound (k : ℤ) : AVenhance.barNorm n Rcomp (d k) ≤
      ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) := by
    let sₖ : ℝ := (ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m
    let uₖ : ℝ := t - sₖ
    by_cases hcut : streamRecursionCutoff D m k t = 0
    · have hd : d k = 0 := by
        funext x
        dsimp [d]
        rw [hcut]
        simp
      rw [hd]
      simp [AVenhance.barNorm]
    · have hslow : slowEnvelope α q Λ m (ocLabel α q Λ m k) t ≠ 0 := by
        intro hz
        apply hcut
        simp [streamRecursionCutoff, hz]
      have hdist := slowEnvelope_nonzero_distance D m hm
        (ocLabel α q Λ m k) t hslow
      have hMbound := AVRegularity.Velocity.Port.Scalars.full_amplitude_recurrence_bound D
        (m - 1)
      have hMpos := section2_amplitude_pos D (m - 1)
      have hwindow := AVRegularity.Velocity.Port.Scalars.tauPP_induction_window
        D m hm hMpos hMbound
      have hu : |uₖ| ≤ (2 : ℝ) ^ (-6 : ℤ) * (D.jetSize (m - 1))⁻¹ := by
        have hu0 : |uₖ| = |t - (ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m| := by
          dsimp [uₖ, sₖ]
        rw [hu0]
        have hdist' : |t - (ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m| ≤
            (2 : ℝ) ^ (-6 : ℤ) * (D.jetSize (m - 1))⁻¹ := by
          have hhalf : ocTauPP α q Λ m / 2 ≤
              (2 : ℝ) ^ (-6 : ℤ) * (D.jetSize (m - 1))⁻¹ := by
            have hsmall := hwindow.2
            rw [D.tauPP_eq_oc m] at hsmall
            norm_num at hsmall ⊢
            nlinarith [hsmall]
          exact hdist.trans hhalf
        exact hdist'
      have hpsi := section2_composed_profile_barNorm_bound D hseq happB2 m hm
        hprev sₖ uₖ hu k n
      have hprof' : AVenhance.barNorm n Rcomp
          (fun x : Vec 2 => ocShear α q Λ m k
            (constructionFlowInv D hseq (m - 1) t x sₖ)) ≤
          ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) := by
        have hst : sₖ + uₖ = t := by dsimp [sₖ, uₖ]; ring
        simpa [Rcomp, E, hst] using hpsi
      have hcoeff : streamRecursionCutoff D m k t ∈ Set.Icc 0 1 := hcutIcc k
      have hprofileSmooth : ContDiff ℝ n (fun x : Vec 2 =>
          ocShear α q Λ m k
            (constructionFlowInv D hseq (m - 1) t x sₖ)) := by
        have hg := happB2.inverse_spatial_smooth m hm sₖ uₖ
        have hst : sₖ + uₖ = t := by dsimp [sₖ, uₖ]; ring
        have hprofile' : ContDiff ℝ n (fun x : Vec 2 =>
            ocShear α q Λ m k
              (constructionFlowInv D hseq (m - 1) (sₖ + uₖ) x sₖ)) :=
          ((ocShear_contDiff D m k).comp hg).of_le (by simp)
        simpa only [hst] using hprofile'
      have htermEq : d k = fun x : Vec 2 =>
          streamRecursionCutoff D m k t *
            ocShear α q Λ m k
              (constructionFlowInv D hseq (m - 1) t x sₖ) := by
        funext x
        dsimp [d]
      rw [htermEq]
      exact (barNorm_mul_const_Icc_le hprofileSmooth hcoeff).trans hprof'
  have hsum := AVRegularity.Velocity.Port.ExplicitBarNorm.barNorm_sum_le S d n Rout
    (fun k hk => (htermSmooth k).of_le le_rfl)
  have hsumComp := AVRegularity.Velocity.Port.ExplicitBarNorm.barNorm_sum_le S d n Rcomp
    (fun k hk => (htermSmooth k).of_le le_rfl)
  have hsumCompBound : AVenhance.barNorm n Rcomp (∑ k ∈ S, d k) ≤
      ENNReal.ofReal (10 * D.epsilon m ^ (1 + α)) := by
    calc
      AVenhance.barNorm n Rcomp (∑ k ∈ S, d k) ≤
          ∑ k ∈ S, AVenhance.barNorm n Rcomp (d k) := hsumComp
      _ ≤ ∑ k ∈ S, ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hprofileBound k
      _ ≤ ENNReal.ofReal (10 * D.epsilon m ^ (1 + α)) := by
        have hcard : S.card ≤ 2 := by simp [S]
        have hsumConst : (∑ _k ∈ S,
            ENNReal.ofReal (5 * D.epsilon m ^ (1 + α))) =
            (S.card : ENNReal) * ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        rw [hsumConst]
        have hcard' : (S.card : ENNReal) ≤ 2 := by exact_mod_cast hcard
        calc
          (S.card : ENNReal) * ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) ≤
              2 * ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) :=
            mul_le_mul_of_nonneg_right hcard' (by positivity)
          _ = ENNReal.ofReal (10 * D.epsilon m ^ (1 + α)) := by
            calc
              2 * ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) =
                  ENNReal.ofReal 2 * ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) := by norm_num
              _ = ENNReal.ofReal (2 * (5 * D.epsilon m ^ (1 + α))) :=
                (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
              _ = ENNReal.ofReal (10 * D.epsilon m ^ (1 + α)) := by congr 1; ring
  have hsumBound : AVenhance.barNorm n Rout (∑ k ∈ S, d k) ≤
      ENNReal.ofReal (10 * D.epsilon m ^ (1 + α)) := by
    calc
      AVenhance.barNorm n Rout (∑ k ∈ S, d k) ≤
          ∑ k ∈ S, AVenhance.barNorm n Rout (d k) := hsum
      _ ≤ ∑ k ∈ S, ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (barNorm_radius_monotone (htermSmooth k) hRcomp hRcompOut).trans
          (hprofileBound k)
      _ ≤ ENNReal.ofReal (10 * D.epsilon m ^ (1 + α)) := by
        have hcard : S.card ≤ 2 := by simp [S]
        have hsumConst : (∑ _k ∈ S,
            ENNReal.ofReal (5 * D.epsilon m ^ (1 + α))) =
            (S.card : ENNReal) * ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        rw [hsumConst]
        have hcard' : (S.card : ENNReal) ≤ 2 := by exact_mod_cast hcard
        calc
          (S.card : ENNReal) * ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) ≤
              2 * ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) :=
            mul_le_mul_of_nonneg_right hcard' (by positivity)
          _ = ENNReal.ofReal (10 * D.epsilon m ^ (1 + α)) := by
            calc
              2 * ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) =
                  ENNReal.ofReal 2 * ENNReal.ofReal (5 * D.epsilon m ^ (1 + α)) := by norm_num
              _ = ENNReal.ofReal (2 * (5 * D.epsilon m ^ (1 + α))) :=
                (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
              _ = ENNReal.ofReal (10 * D.epsilon m ^ (1 + α)) := by congr 1; ring
  have hrawComp : AVenhance.barNorm n Rcomp (Φ m t - Φ (m - 1) t) ≤
      ENNReal.ofReal (10 * D.epsilon m ^ (1 + α)) := by
    have hpoint : Φ m t - Φ (m - 1) t = ∑ k ∈ S, d k := by
      funext x
      exact congrFun hincrement x
    rw [hpoint]
    exact hsumCompBound
  have hraw : AVenhance.barNorm n Rout (Φ m t - Φ (m - 1) t) ≤
      ENNReal.ofReal (10 * D.epsilon m ^ (1 + α)) := by
    have hpoint : Φ m t - Φ (m - 1) t = ∑ k ∈ S, d k := by
      funext x
      exact congrFun hincrement x
    rw [hpoint]
    exact hsumBound
  exact ⟨by simpa [Rcomp] using hrawComp,
    by simpa [Rout] using hraw⟩

/-- The first stream-regularity increment display follows from the stronger
composition-radius estimate. -/
theorem stream_increment_bound_at_scale
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (happB2 : AppB2InverseFlowData D Φ hseq)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2StreamInductionHypothesis D Φ (m - 1))
    (t : ℝ) (n : ℕ) :
    AVenhance.barNorm n (2 ^ 7 * (D.epsilon m)⁻¹)
        (Φ m t - Φ (m - 1) t) ≤
      ENNReal.ofReal (10 * D.epsilon m ^ (1 + α)) := by
  exact (stream_increment_bounds_at_scale D hseq happB2 m hm hprev t n).2

end AVRegularity.Velocity.Port.RecursionIncrement
end

section
open MeasureTheory Homogenization Topology
open scoped ContDiff
namespace AVRegularity.Velocity.Port

/-! The analytic induction behind the first stream-regularity increment estimate. -/

open AVenhance AVRegularity.Velocity.Port.Section2Induction
open AVRegularity.Velocity.Port.RecursionIncrement
open AVRegularity.Velocity.Port.ExplicitBarNorm

def Section2JointInduction.section2Weight (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3

theorem Section2JointInduction.nat_add_three_le_three_mul_two_pow (k : ℕ) :
    k + 3 ≤ 3 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc
        k + 1 + 3 ≤ 2 * (k + 3) := by omega
        _ ≤ 2 * (3 * 2 ^ k) := Nat.mul_le_mul_left 2 ih
        _ = 3 * 2 ^ (k + 1) := by rw [pow_succ]; omega

theorem Section2JointInduction.section2_weight_half_power (n : ℕ) (hn : 2 ≤ n) :
    (1 / 2 : ℝ) ^ (n - 2) ≤ 3 * Section2JointInduction.section2Weight n := by
  let k := n - 2
  have hidx : k + 2 = n := by dsimp [k]; omega
  have hnat := Section2JointInduction.nat_add_three_le_three_mul_two_pow k
  have hnatR : (n : ℝ) + 1 ≤ 3 * (2 : ℝ) ^ k := by
    calc
      (n : ℝ) + 1 = ((k + 2 : ℕ) : ℝ) + 1 := by rw [← hidx]
      _ = (k : ℝ) + 3 := by push_cast; ring
      _ ≤ 3 * (2 : ℝ) ^ k := by exact_mod_cast hnat
  have hp : 0 < (2 : ℝ) ^ k := by positivity
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hleft : (1 : ℝ) / (2 : ℝ) ^ k ≤ 3 / ((n : ℝ) + 1) := by
    apply (div_le_iff₀ hp).2
    field_simp [ne_of_gt hn1]
    nlinarith [hnatR]
  have hweight : 3 / ((n : ℝ) + 1) ≤ 3 * Section2JointInduction.section2Weight n := by
    apply (div_le_iff₀ hn1).2
    dsimp [Section2JointInduction.section2Weight]
    have hnreal : 2 ≤ (n : ℝ) := by exact_mod_cast hn
    have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
    field_simp
    nlinarith [hsq]
  have hpow : (1 / 2 : ℝ) ^ k = 1 / (2 : ℝ) ^ k := by
    rw [one_div_pow]
  simpa [k, hpow] using hleft.trans hweight

theorem Section2JointInduction.section2_stream_slice_smooth
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    {D : JetRecursionData α s q Λ ζ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (m : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) := by
  have hΦ := (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m).1
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => Function.uncurry (Φ m) (t, x))
  exact hΦ.comp hmap

theorem Section2JointInduction.section2_amplitude_increment_budget
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ) (m : ℕ) (hm : 1 ≤ m) :
    30 * D.velocityAmplitude m * D.epsilon m ^ 2 *
        ((9 / 8) * D.radius (m - 1) + 20 * Real.pi / D.epsilon m) ^ 2 ≤
      D.jetSize m - D.jetSize (m - 1) := by
  let E := D.epsilon m
  let Rp := D.radius (m - 1)
  let Rc := (9 / 8) * Rp + 20 * Real.pi / E
  have hE : 0 < E := by
    dsimp [E]
    exact D.epsilon_pos m
  have hRp : 0 ≤ Rp := RecursionIncrement.section2_radius_nonneg D (m - 1)
  have ha : 0 ≤ D.velocityAmplitude m := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_nonneg (le_of_lt hE) _
  have hpi : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hgeom : 30 * E ^ 2 * Rc ^ 2 ≤ 128 * E ^ 2 * Rp ^ 2 + 2 ^ 18 := by
    have hsum : E * Rc = (9 / 8 : ℝ) * (E * Rp) + 20 * Real.pi := by
      dsimp [Rc]
      field_simp [ne_of_gt hE]
    have hsq : (E * Rc) ^ 2 ≤
        2 * ((9 / 8 : ℝ) * (E * Rp)) ^ 2 + 2 * (20 * Real.pi) ^ 2 := by
      rw [hsum]
      nlinarith [sq_nonneg ((9 / 8 : ℝ) * (E * Rp) - 20 * Real.pi)]
    calc
      30 * E ^ 2 * Rc ^ 2 = 30 * (E * Rc) ^ 2 := by ring
      _ ≤
          60 * ((9 / 8 : ℝ) * (E * Rp)) ^ 2 + 60 * (20 * Real.pi) ^ 2 := by
        nlinarith [hsq]
      _ ≤ 128 * E ^ 2 * Rp ^ 2 + 2 ^ 18 := by
        nlinarith [sq_nonneg (E * Rp), hpi]
  have hMdiff : D.jetSize m - D.jetSize (m - 1) =
      2 ^ 7 * D.velocityAmplitude m * E ^ 2 * Rp ^ 2 +
        2 ^ 18 * D.velocityAmplitude m := by
    have hmidx : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have hstep := D.jetSize_step (m - 1)
    rw [hmidx] at hstep
    rw [hstep]
    dsimp [E, Rp]
    ring
  rw [hMdiff]
  have hmul := mul_le_mul_of_nonneg_left hgeom ha
  calc
    30 * D.velocityAmplitude m * E ^ 2 * Rc ^ 2 = D.velocityAmplitude m *
        (30 * E ^ 2 * Rc ^ 2) := by ring
    _ ≤ D.velocityAmplitude m * (128 * E ^ 2 * Rp ^ 2 + 2 ^ 18) := hmul
    _ = 2 ^ 7 * D.velocityAmplitude m * E ^ 2 * Rp ^ 2 +
        2 ^ 18 * D.velocityAmplitude m := by ring

/-- One induction step for `e.indyhyp`. The App. B.2 inverse estimate is
applied only after the previous-scale hypothesis has been established. -/
theorem section2_stream_induction_step {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    {D : JetRecursionData (β - 1) s q Λ ζ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ}
    (happB2 : RecursionIncrement.AppB2InverseFlowData D Φ hseq)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2StreamInductionHypothesis D Φ (m - 1)) :
    Section2StreamInductionHypothesis D Φ m := by
  let R := D.radius
  let M := D.jetSize
  intro t n hn
  let Rp := R (m - 1)
  let Rm := R m
  let Rc := (9 / 8) * Rp + 20 * Real.pi / D.epsilon m
  let E := D.epsilon m
  let P := Section2JointInduction.section2Weight n
  have hRp : 0 < Rp := Section2Scales.section2_radius_pos D (m - 1)
  have hRm : 0 < Rm := Section2Scales.section2_radius_pos D m
  have hE : 0 < E := by
    dsimp [E]
    exact D.epsilon_pos m
  have hRc : 0 < Rc := by
    dsimp [Rc]
    positivity
  have hMprev : 0 < M (m - 1) := Section2Scales.section2_amplitude_pos D (m - 1)
  have hM : 0 < M m := Section2Scales.section2_amplitude_pos D m
  have hMmono : M (m - 1) ≤ M m := by
    change D.jetSize (m - 1) ≤ D.jetSize m
    have hstep := D.jetSize_step (m - 1)
    have hmidx : m - 1 + 1 = m := Nat.sub_add_cancel hm
    rw [hmidx] at hstep
    rw [hstep]
    have he := D.epsilon_pos m
    have ha : 0 ≤ D.velocityAmplitude m := (by rw [D.velocityAmplitude_eq]; exact Real.rpow_nonneg he.le _)
    have hRnonneg := RecursionIncrement.section2_radius_nonneg D (m - 1)
    have hinc : 0 ≤ 2 ^ 7 * D.velocityAmplitude m * D.epsilon m ^ 2 *
        R (m - 1) ^ 2 + 2 ^ 18 * D.velocityAmplitude m := by positivity
    linarith
  have hP : 0 < P := by
    dsimp [P, Section2JointInduction.section2Weight]
    positivity
  have hRrecM : Rm = (9 / 4) * Rp + 2 ^ 7 * E⁻¹ := by
    have hmidx : m - 1 + 1 = m := Nat.sub_add_cancel hm
    simpa [Rm, Rp, E, hmidx] using D.radius_step (m - 1)
  have hRtwice : 2 * Rc ≤ Rm := by
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have hraw : 40 * Real.pi ≤ (128 : ℝ) := by norm_num at hpi ⊢; linarith
    rw [hRrecM]
    have hdiv : 40 * Real.pi / E ≤ 128 * E⁻¹ := by
      have hdiv' := div_le_div_of_nonneg_right hraw hE.le
      simpa [div_eq_mul_inv] using hdiv'
    dsimp [Rc]
    rw [show 2 * ((9 / 8 : ℝ) * Rp + 20 * Real.pi / E) =
      (9 / 4) * Rp + 40 * Real.pi / E by ring]
    nlinarith [hdiv]
  have hRple : Rp ≤ Rm := by
    have hRcompLower : (9 / 8 : ℝ) * Rp ≤ Rc := by
      dsimp [Rc]
      have hpos : 0 < 20 * Real.pi / E := by positivity
      linarith
    nlinarith
  have hRprevRatio : 0 ≤ Rp / Rm ∧ Rp / Rm ≤ 1 := by
    constructor
    · exact (div_pos hRp hRm).le
    · exact (div_le_one hRm).2 hRple
  have hRcompRatio : 0 ≤ Rc / Rm ∧ Rc / Rm ≤ 1 / 2 := by
    constructor
    · exact (div_pos hRc hRm).le
    · exact (div_le_iff₀ hRm).2 (by nlinarith [hRtwice])
  have hΦprev : ContDiff ℝ (⊤ : ℕ∞) (Φ (m - 1) t) :=
    Section2JointInduction.section2_stream_slice_smooth (D := D) hseq (m - 1) t
  have hΦm : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) :=
    Section2JointInduction.section2_stream_slice_smooth (D := D) hseq m t
  let Δ : Vec 2 → ℝ := fun x => Φ m t x - Φ (m - 1) t x
  have hΔ : ContDiff ℝ (⊤ : ℕ∞) Δ := by
    dsimp [Δ]
    exact hΦm.sub hΦprev
  have hprevBar : barNorm n Rp (Φ (m - 1) t) ≤
      ENNReal.ofReal (M (m - 1) * Rp⁻¹ ^ 2 * P) := by
    rw [barNorm_eq_snorm (hΦprev.of_le (by simp))]
    exact hprev t n hn
  have hincComp :=
    (RecursionIncrement.stream_increment_bounds_at_scale D hseq happB2 m hm hprev t n).1
  have hscale : D.velocityAmplitude m * D.epsilon m ^ 2 = D.epsilon m ^ β := by
    rw [D.velocityAmplitude_eq, ← Real.rpow_natCast, ← Real.rpow_add (D.epsilon_pos m)]
    congr 1
    ring
  have hβexp : 1 + (β - 1) = β := by ring
  have hincBar : barNorm n Rc Δ ≤ ENNReal.ofReal (10 * D.velocityAmplitude m * E ^ 2) := by
    change barNorm n Rc (Φ m t - Φ (m - 1) t) ≤ _
    calc
      _ ≤ ENNReal.ofReal (10 * D.epsilon m ^ β) := by
        simpa [Rc, E, Rp, hβexp] using hincComp
      _ = ENNReal.ofReal (10 * D.velocityAmplitude m * E ^ 2) := by
        congr 1
        calc
          10 * D.epsilon m ^ β = 10 * (D.velocityAmplitude m * D.epsilon m ^ 2) := by
            rw [← hscale]
          _ = 10 * D.velocityAmplitude m * E ^ 2 := by simp [E, mul_assoc]
  have hqprev_pow : (Rp / Rm) ^ (n - 2) ≤ 1 := by
    have hq := hRprevRatio
    exact pow_le_one₀ hq.1 hq.2
  have hqprev_id : Rp⁻¹ ^ 2 * (Rp / Rm) ^ n =
      Rm⁻¹ ^ 2 * (Rp / Rm) ^ (n - 2) := by
    have hnidx : n - 2 + 2 = n := by omega
    have hqpow : (Rp / Rm) ^ n =
        (Rp / Rm) ^ (n - 2) * (Rp / Rm) ^ 2 := by
      calc
        (Rp / Rm) ^ n = (Rp / Rm) ^ (n - 2 + 2) := by rw [hnidx]
        _ = (Rp / Rm) ^ (n - 2) * (Rp / Rm) ^ 2 := by rw [pow_add]
    rw [hqpow]
    have hqsq : (Rp / Rm) ^ 2 = Rp ^ 2 * Rm⁻¹ ^ 2 := by
      field_simp [hRm.ne']
    rw [hqsq]
    field_simp [hRp.ne', hRm.ne']
  have hprevReal : M (m - 1) * Rp⁻¹ ^ 2 * P * (Rp / Rm) ^ n ≤
      M (m - 1) * Rm⁻¹ ^ 2 * P := by
    have hcoef : 0 ≤ M (m - 1) * P * Rm⁻¹ ^ 2 := by positivity
    calc
      M (m - 1) * Rp⁻¹ ^ 2 * P * (Rp / Rm) ^ n =
          M (m - 1) * P * (Rp⁻¹ ^ 2 * (Rp / Rm) ^ n) := by ring
      _ = M (m - 1) * P * (Rm⁻¹ ^ 2 * (Rp / Rm) ^ (n - 2)) := by
        rw [hqprev_id]
      _ = (M (m - 1) * P * Rm⁻¹ ^ 2) * (Rp / Rm) ^ (n - 2) := by ring
      _ ≤
          M (m - 1) * P * Rm⁻¹ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hqprev_pow hcoef
      _ = M (m - 1) * Rm⁻¹ ^ 2 * P := by ring
  have hprevScaled : barNorm n Rm (Φ (m - 1) t) ≤
      ENNReal.ofReal (M (m - 1) * Rm⁻¹ ^ 2 * P) := by
    rw [barNorm_radius_change (hΦprev.of_le (by simp)) hRp hRm]
    have hqnonneg : 0 ≤ Rp / Rm := hRprevRatio.1
    have hKnonneg : 0 ≤ M (m - 1) * Rp⁻¹ ^ 2 * P := by positivity
    calc
      barNorm n Rp (Φ (m - 1) t) * ENNReal.ofReal (Rp / Rm) ^ n ≤
          ENNReal.ofReal (M (m - 1) * Rp⁻¹ ^ 2 * P) *
            ENNReal.ofReal (Rp / Rm) ^ n :=
        mul_le_mul_of_nonneg_right hprevBar (by positivity)
      _ = ENNReal.ofReal
          (M (m - 1) * Rp⁻¹ ^ 2 * P * (Rp / Rm) ^ n) := by
        rw [← ENNReal.ofReal_pow hqnonneg, ← ENNReal.ofReal_mul hKnonneg]
      _ ≤ ENNReal.ofReal (M (m - 1) * Rm⁻¹ ^ 2 * P) :=
        ENNReal.ofReal_le_ofReal hprevReal
  have hqcomp_pow : (Rc / Rm) ^ (n - 2) ≤ 3 * P := by
    have hsmall := Section2JointInduction.section2_weight_half_power n hn
    have hpow := pow_le_pow_left₀ hRcompRatio.1 hRcompRatio.2 (n - 2)
    exact hpow.trans hsmall
  have hqcomp_id : (Rc / Rm) ^ 2 = Rc ^ 2 * Rm⁻¹ ^ 2 := by
    field_simp [hRm.ne']
  have hbudget := Section2JointInduction.section2_amplitude_increment_budget D m hm
  have hincReal : 10 * D.velocityAmplitude m * E ^ 2 * (Rc / Rm) ^ n ≤
      (M m - M (m - 1)) * Rm⁻¹ ^ 2 * P := by
    have hnidx : n = (n - 2) + 2 := by omega
    rw [hnidx, pow_add, mul_comm ((Rc / Rm) ^ (n - 2)) ((Rc / Rm) ^ 2), hqcomp_id]
    have hfactor : 0 ≤ 10 * D.velocityAmplitude m * E ^ 2 * (Rc ^ 2 * Rm⁻¹ ^ 2) := by
      have ha : 0 ≤ D.velocityAmplitude m := by
        rw [D.velocityAmplitude_eq]
        exact Real.rpow_nonneg hE.le _
      positivity
    calc
      10 * D.velocityAmplitude m * E ^ 2 *
          ((Rc ^ 2 * Rm⁻¹ ^ 2) * (Rc / Rm) ^ (n - 2)) =
        (10 * D.velocityAmplitude m * E ^ 2 * (Rc ^ 2 * Rm⁻¹ ^ 2)) *
          (Rc / Rm) ^ (n - 2) := by ring
      _ ≤ (10 * D.velocityAmplitude m * E ^ 2 * (Rc ^ 2 * Rm⁻¹ ^ 2)) * (3 * P) :=
        mul_le_mul_of_nonneg_left hqcomp_pow hfactor
      _ = (30 * D.velocityAmplitude m * E ^ 2 * Rc ^ 2) * Rm⁻¹ ^ 2 * P := by ring
      _ ≤ (M m - M (m - 1)) * Rm⁻¹ ^ 2 * P := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hbudget' : 30 * D.velocityAmplitude m * E ^ 2 * Rc ^ 2 ≤ M m - M (m - 1) := by
          simpa [E, Rc, Rp] using hbudget
        exact hbudget'
  have hincScaled : barNorm n Rm Δ ≤
      ENNReal.ofReal ((M m - M (m - 1)) * Rm⁻¹ ^ 2 * P) := by
    rw [barNorm_radius_change (hΔ.of_le (by simp)) hRc hRm]
    have hqnonneg : 0 ≤ Rc / Rm := hRcompRatio.1
    have ha : 0 ≤ D.velocityAmplitude m := by
      rw [D.velocityAmplitude_eq]
      exact Real.rpow_nonneg hE.le _
    have hKnonneg : 0 ≤ 10 * D.velocityAmplitude m * E ^ 2 := by positivity
    calc
      barNorm n Rc Δ * ENNReal.ofReal (Rc / Rm) ^ n ≤
          ENNReal.ofReal (10 * D.velocityAmplitude m * E ^ 2) *
            ENNReal.ofReal (Rc / Rm) ^ n :=
        mul_le_mul_of_nonneg_right hincBar (by positivity)
      _ = ENNReal.ofReal
          (10 * D.velocityAmplitude m * E ^ 2 * (Rc / Rm) ^ n) := by
        rw [← ENNReal.ofReal_pow hqnonneg, ← ENNReal.ofReal_mul hKnonneg]
      _ ≤ ENNReal.ofReal ((M m - M (m - 1)) * Rm⁻¹ ^ 2 * P) :=
        ENNReal.ofReal_le_ofReal hincReal
  have hdecomp : Φ m t = Φ (m - 1) t + Δ := by
    funext x
    simp [Δ]
  have hbarFinal : barNorm n Rm (Φ m t) ≤ ENNReal.ofReal (M m * Rm⁻¹ ^ 2 * P) := by
    rw [hdecomp]
    calc
      barNorm n Rm (Φ (m - 1) t + Δ) ≤
        barNorm n Rm (Φ (m - 1) t) + barNorm n Rm Δ :=
        barNorm_add_le _ _ n Rm (hΦprev.of_le (by simp)) (hΔ.of_le (by simp))
      _ ≤ ENNReal.ofReal (M (m - 1) * Rm⁻¹ ^ 2 * P) +
        ENNReal.ofReal ((M m - M (m - 1)) * Rm⁻¹ ^ 2 * P) :=
        add_le_add hprevScaled hincScaled
      _ = ENNReal.ofReal (M m * Rm⁻¹ ^ 2 * P) := by
        calc
          _ = ENNReal.ofReal
              (M (m - 1) * Rm⁻¹ ^ 2 * P +
                (M m - M (m - 1)) * Rm⁻¹ ^ 2 * P) :=
            (ENNReal.ofReal_add
              (p := M (m - 1) * Rm⁻¹ ^ 2 * P)
              (q := (M m - M (m - 1)) * Rm⁻¹ ^ 2 * P)
              (by positivity)
              (mul_nonneg
                (mul_nonneg (sub_nonneg.mpr hMmono) (by positivity))
                (by positivity))).symm
          _ = ENNReal.ofReal (M m * Rm⁻¹ ^ 2 * P) := by congr 1; ring
  rw [← barNorm_eq_snorm (hΦm.of_le (by simp))]
  simpa [Rm, P, Section2JointInduction.section2Weight] using hbarFinal

/-- The joint `e.indyhyp` induction over every Section 2 scale. -/
theorem section2_stream_induction {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ}
    (happB2 : RecursionIncrement.AppB2InverseFlowData D Φ hseq) :
    ∀ m : ℕ, Section2StreamInductionHypothesis D Φ m := by
  let R := D.radius
  let M := D.jetSize
  intro m
  induction m with
  | zero =>
      intro t n hn
      rw [hseq.1]
      rw [D.jetSize_zero, D.radius_zero]
      have hn0 : n ≠ 0 := by omega
      have hLift : FaaDiBruno.liftVecOne (fun _ : Vec 2 => (0 : ℝ)) =
          fun _ => (0 : ℝ) := by
        funext x
        simp [FaaDiBruno.liftVecOne]
      have hIter : iteratedFDeriv ℝ n
          (FaaDiBruno.liftVecOne (fun _ : Vec 2 => (0 : ℝ))) = 0 := by
        rw [hLift]
        exact iteratedFDeriv_const_of_ne hn0 (0 : ℝ)
      have hpartial (J : Fin n → Fin 2) (x : Vec 2) :
          FaaDiBruno.orderedPartial n (fun _ : Vec 2 => (0 : ℝ)) x J = 0 := by
        change iteratedFDeriv ℝ n
          (FaaDiBruno.liftVecOne (fun _ : Vec 2 => (0 : ℝ)))
          (WithLp.toLp 1 x) (fun j => FaaDiBruno.coordinateVectorOne 2 (J j)) = 0
        rw [hIter]
        simp
      have hderiv : FaaDiBruno.derivativeSup n (fun _ : Vec 2 => (0 : ℝ)) = 0 := by
        unfold FaaDiBruno.derivativeSup
        apply le_antisymm
        · apply iSup_le
          intro J
          unfold FaaDiBruno.partialSup
          have hfun : (fun x : Vec 2 =>
              FaaDiBruno.orderedPartial n (fun _ : Vec 2 => (0 : ℝ)) x J) = 0 := by
            funext x
            exact hpartial J x
          rw [hfun]
          change eLpNormEssSup (0 : Vec 2 → ℝ) (FaaDiBruno.vecVolume 2) ≤ 0
          exact le_of_eq eLpNormEssSup_zero
        · exact bot_le
      simp only [FaaDiBruno.snorm, hderiv, mul_zero]
      exact bot_le
  | succ m ih =>
      exact section2_stream_induction_step (D := D) (hseq := hseq)
        happB2 (m + 1) (by omega)
        (by simpa using ih)

/-- The §2 induction proves every induction hypothesis and the first stream-regularity increment
display. Flow estimates are assembled separately from the preceding-scale
induction hypothesis in the namespace `Velocity.Port.Section2FlowBridge`. -/
theorem section2_joint_induction {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ}
    (happB2 : RecursionIncrement.AppB2InverseFlowData D Φ hseq) :
    (∀ m : ℕ, Section2StreamInductionHypothesis D Φ m) ∧
      Section2Induction.StreamIncrementBounds D Φ := by
  have hind := section2_stream_induction D happB2
  have hinc : Section2Induction.StreamIncrementBounds D Φ := by
    intro m hm t n
    exact RecursionIncrement.stream_increment_bound_at_scale D hseq happB2 m hm
      (hind (m - 1)) t n
  exact ⟨hind, hinc⟩

end AVRegularity.Velocity.Port
end
