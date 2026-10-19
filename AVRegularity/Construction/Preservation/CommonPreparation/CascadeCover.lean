-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.NeutralChainEnvelopes
public import AVRegularity.Construction.Preservation.CommonPreparation.KernelSuperposition
import AVRegularity.Construction.Preservation.RetainedEnergy.UniformInputs
public import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
public import AVRegularity.Construction.WindowCover.WindowCoverGen
import AVRegularity.Proofs.CascadeInvariants.Scales
public import AVRegularity.CycleJoint.PeriodizedCompactCoefficientPairingIntegrable
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.CycleJoint.PeriodizedFamilyGlobalReadout
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public noncomputable section

section
open Filter Topology
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Uniform scalar prices for the same copied model. The existing fine-renewal
ratio supplies a band-independent deep-level floor; only finite power and sum
monotonicity remain in the joint-model constant. -/

open CycleComparison.Reconstruction

private theorem model_const_mono {C S r R : ℝ} (H N : ℕ)
    (hS : 0 ≤ S) (hS1 : S ≤ 1) (hr : r ≤ R) :
    jointModelConst C S H N r ≤ jointModelConst C 1 H N R := by
  have hp : max 1 r ^ N ≤ max 1 R ^ N :=
    pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (max_le_max le_rfl hr) N
  have hs : (1 : ℝ) + ∑ j ∈ Finset.Icc 1 H, S ^ j ≤
      1 + ∑ j ∈ Finset.Icc 1 H, (1 : ℝ) ^ j :=
    add_le_add le_rfl (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hS hS1 j)
  exact mul_le_mul (mul_le_mul_of_nonneg_right hp (le_max_right C 0)) hs
    (add_nonneg zero_le_one (Finset.sum_nonneg fun j _ => pow_nonneg hS j))
    (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) N) (le_max_right C 0))

private theorem model_radius_ratio {e l p c cr : ℝ}
    (he : 0 ≤ e) (he1 : e ≤ 1) (hp : 1 ≤ p) (hl : 0 < l)
    (hel : e ≤ l) (hc : 0 < c) (hcr : 0 < cr) :
    cr * e ^ p / (c * l) ≤ cr / c := by
  calc
    cr * e ^ p / (c * l) ≤ cr * l / (c * l) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        ((Real.rpow_le_self_of_le_one he he1 hp).trans hel) hcr.le) (mul_pos hc hl).le
    _ = cr / c := by rw [mul_comm c l, ← div_div, mul_div_cancel_right₀ _ hl.ne']

/-- The fixed copied model has one uniform pair of scalar readout prices. -/
theorem preparation_copied_model_budget {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    PreparationCopiedModelBudgetStatement α q ζ := by
  obtain ⟨Cf, _, Λ₀, hΛ₀, hf⟩ := CycleReference.bandChain_fine_renewal_ratio
    hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨hγ, hδ, _⟩ := Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  have hq0 : 0 < q := zero_lt_one.trans hq.1
  have hdec : 0 < q * ocGamma α q + 3 * ocDelta α q :=
    add_pos (mul_pos hq0 hγ) (mul_pos (by norm_num) hδ)
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ c cr C CP Cbuf H Nout hc hcr hbuf
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  have hlim := (Buffer.preparation_parent_power_tendsto_zero hq.1 h128 hdec).const_mul Cf
  rw [mul_zero] at hlim
  obtain ⟨mf, hmf⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_le_nhds zero_lt_one))
  refine ⟨((H : ℝ) + 1) * (CP * Cbuf),
    ((H : ℝ) + 1) * (jointModelConst C 1 H Nout (cr / c) * Cbuf), max 2 mf,
    mul_nonneg (add_nonneg (Nat.cast_nonneg H) zero_le_one)
      (mul_nonneg (jointModelConst_nonneg C zero_le_one H Nout _) hbuf),
    le_max_left _ _, ?_⟩
  intro M κ hband m hm hmM S hS hS1
  have hm2 : 2 ≤ m := (le_max_left _ _).trans hm
  have hsmall := hmf m ((le_max_right _ _).trans hm)
  have hratio := (hf Λ hΛ M (by omega) κ hband m hm2 (by omega)).2
  have hκ := CycleReference.bandChain_pos (by omega : 1 ≤ Λ) hζ hband
    (by omega : m - 1 ≤ M)
  have hτ := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m)
    (by omega : 1 ≤ Λ)
  have hl : 0 < Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) :=
    Real.sqrt_pos.mpr (mul_pos hκ hτ)
  have hel : ocEpsilon q Λ m ≤ Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) :=
    (div_le_one hl).mp (hratio.trans hsmall)
  have he := Scales.epsilon_basic (m := m) hq.1 h128
  have hpower : 1 ≤ 1 + ocGamma α q / 2 + ocDelta α q :=
    (le_add_of_nonneg_right (div_nonneg hγ.le (by norm_num))).trans
      (le_add_of_nonneg_right hδ.le)
  have hr := model_radius_ratio he.1.le he.2.1 hpower hl hel hc hcr
  exact ⟨le_rfl, mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (model_const_mono H Nout hS hS1 hr) hbuf)
      (add_nonneg (Nat.cast_nonneg H) zero_le_one)⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The physical finite-expansion estimate from the source-operator energy bounds.
This is the algebraic part of (e.preservation.depth.bounds) and
(e.preservation.depth.identity). Constructing the scalar solution operators,
pricing their kernel defects, and proving the scalar price are separate inputs.

The degenerate cases are included: Hpr=0 has only the actual-solution tail; identical source
operators have zero defect; a zero datum or empty family needs no division by its norm.
The two weights use the same operators and endpoint. Identity geometry, an
edgeless seed and the smallest orders have the same finite identities. -/

section
/-- Strictly better powers pay both finite defect and tail constants at one
starting level. The constants are chosen before the level and all stage data.
Either constant may be zero; this scalar budget does not use components. -/
theorem finite_expansion_scalar_price {q Q L T : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hL : Q < L) (hT : Q < T) (A B : ℝ) :
    ∃ mStar : ℕ, 2 ≤ mStar ∧ ∀ m : ℕ, mStar ≤ m →
      A * ocEpsilon q Λ (m - 1) ^ L + B * ocEpsilon q Λ (m - 1) ^ T ≤
        ocEpsilon q Λ (m - 1) ^ Q := by
  obtain ⟨mStar, hmStar, hsmall⟩ := Buffer.preparation_parameters_eventually_small
    hq hΛ (sub_pos.mpr hL) (sub_pos.mpr hT) A B
  refine ⟨mStar, hmStar, ?_⟩
  intro m hm
  have hE := (Scales.epsilon_basic (m := m - 1) hq hΛ).1
  have heL : ocEpsilon q Λ (m - 1) ^ L =
      ocEpsilon q Λ (m - 1) ^ (L - Q) * ocEpsilon q Λ (m - 1) ^ Q := by
    rw [← Real.rpow_add hE, sub_add_cancel]
  have heT : ocEpsilon q Λ (m - 1) ^ T =
      ocEpsilon q Λ (m - 1) ^ (T - Q) * ocEpsilon q Λ (m - 1) ^ Q := by
    rw [← Real.rpow_add hE, sub_add_cancel]
  have hb : A * ocEpsilon q Λ (m - 1) ^ (L - Q) +
      B * ocEpsilon q Λ (m - 1) ^ (T - Q) ≤ 1 := by
    have h1 := (hsmall m hm).1
    have h2 := (hsmall m hm).2
    linarith only [h1, h2]
  calc
    _ = (A * ocEpsilon q Λ (m - 1) ^ (L - Q) +
        B * ocEpsilon q Λ (m - 1) ^ (T - Q)) * ocEpsilon q Λ (m - 1) ^ Q := by
      rw [heL, heT]; ring
    _ ≤ 1 * ocEpsilon q Λ (m - 1) ^ Q :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hE.le _)
    _ = _ := one_mul _

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- A trace-controlled path seminorm transfers the finite expansion estimate to
physical L2. The defect bound retains its input reserve in its PDE proof; no
higher regularity is asserted for the final error. -/
theorem finite_expansion_approximation_of_operator_bounds
    (F : Request hr D Dm bw j₀) {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (M : F.Model)
    (p : (CompIn F.G.comps → ℝ) → Seminorm ℝ X)
    (β Cfull Cdef Cexp L : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hrestart : F.ScalarRestartStatement R)
    (htrace : F.TraceEnergyStatement R M p)
    (hkernel : F.KernelSourceEnergyStatement R p β)
    (hfull : F.BufferedFullEnergyStatement R p Cfull)
    (hdefect : F.PlainSourceDefectStatement R p Cdef L)
    (hprice : (∑ h ∈ Finset.range (F.Hpr + 1), (h : ℝ)) *
        Cdef * D.eps (F.G.level - 1) ^ L + β ^ (F.Hpr + 1) * Cfull ≤
          Cexp * D.eps (F.G.level - 1) ^ F.Q) :
    F.FiniteExpansionApproximationStatement R M Cexp := by
  obtain ⟨hfixed, hlayer⟩ := hrestart
  refine ⟨hfixed, ?_⟩
  intro w hw f
  let Z := ∑ h ∈ Finset.range (F.Hpr + 1), R.layer h f
  have he : R.plainTrace M.tp f - R.trace M.tp (R.full f) =
      R.trace M.tp (-(R.full f - Z)) := by
    rw [map_neg, map_sub, neg_sub]
    rfl
  rw [he]
  refine (htrace w hw _).trans ?_
  rw [map_neg_eq_map]
  have hb := source_insertion_error_le (p w) R.kernel (fun h => R.layer h f) (R.full f)
    (R.initial f) (congrArg (fun L => L f) hlayer) (hfixed f) β
    (Cdef * D.eps (F.G.level - 1) ^ L * F.inputNorm w f)
    hβ hβ1 (hkernel w hw) (F.Hpr + 1) (fun h hh => hdefect w hw f h (by omega))
  have hs : (∑ h ∈ Finset.range (F.Hpr + 1),
      (h : ℝ) * (Cdef * D.eps (F.G.level - 1) ^ L * F.inputNorm w f)) =
      ((∑ h ∈ Finset.range (F.Hpr + 1), (h : ℝ)) *
        Cdef * D.eps (F.G.level - 1) ^ L) * F.inputNorm w f := by
    simp only [Finset.sum_mul, mul_assoc]
  calc p w (R.full f - Z) ≤ _ := hb
    _ ≤ (∑ h ∈ Finset.range (F.Hpr + 1),
        (h : ℝ) * (Cdef * D.eps (F.G.level - 1) ^ L * F.inputNorm w f)) +
        β ^ (F.Hpr + 1) * (Cfull * F.inputNorm w f) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hfull w hw f) (pow_nonneg hβ _))
    _ = ((∑ h ∈ Finset.range (F.Hpr + 1), (h : ℝ)) *
        Cdef * D.eps (F.G.level - 1) ^ L + β ^ (F.Hpr + 1) * Cfull) *
          F.inputNorm w f := by rw [hs]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hprice (Real.sqrt_nonneg _)
end

/-! Threshold adapter for the scalar price of the finite expansion: if the kernel
factor is `O(eps^b)` with `b * (Hpr + 1) > Q` and the defect reserve `L` exceeds `Q`,
then the price hypothesis holds with leading constant one from a level on that
depends only on the fixed constants, never on stage data.

The degenerate cases are included: `Hpr = 0` (needs `b > Q`), zero defect constant, `beta = 0`, and
negative constants (absolute values are used). -/

/-- The scalar price bound at one level, from the kernel decay `beta <= Cb * eps^b`. -/
theorem expansion_price_threshold {q Q L b : ℝ} {Λ : ℕ} (H : ℕ)
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hL : Q < L) (hH : Q < b * (H + 1))
    (S Cdef Cb Cfull : ℝ) :
    ∃ mStar : ℕ, 2 ≤ mStar ∧ ∀ m : ℕ, mStar ≤ m → ∀ β : ℝ, 0 ≤ β →
      β ≤ Cb * ocEpsilon q Λ (m - 1) ^ b →
      S * Cdef * ocEpsilon q Λ (m - 1) ^ L + β ^ (H + 1) * Cfull ≤
        1 * ocEpsilon q Λ (m - 1) ^ Q := by
  obtain ⟨mStar, h2, hm⟩ := finite_expansion_scalar_price (Λ := Λ) hq hΛ hL hH
    (S * Cdef) (|Cb| ^ (H + 1) * |Cfull|)
  refine ⟨mStar, h2, fun m hmm β hβ hβb => ?_⟩
  have hE := (Scales.epsilon_basic (m := m - 1) hq hΛ).1
  set e := ocEpsilon q Λ (m - 1)
  have hbe : β ≤ |Cb| * e ^ b :=
    hβb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hE.le _))
  have hp : β ^ (H + 1) ≤ (|Cb| * e ^ b) ^ (H + 1) := pow_le_pow_left₀ hβ hbe _
  have hrw : (|Cb| * e ^ b) ^ (H + 1) = |Cb| ^ (H + 1) * e ^ (b * (H + 1)) := by
    rw [mul_pow, ← Real.rpow_natCast (e ^ b) (H + 1), ← Real.rpow_mul hE.le]
    push_cast; rfl
  have h1 : β ^ (H + 1) * Cfull ≤ |Cb| ^ (H + 1) * |Cfull| * e ^ (b * (H + 1)) := by
    calc β ^ (H + 1) * Cfull ≤ β ^ (H + 1) * |Cfull| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hβ _)
      _ ≤ (|Cb| ^ (H + 1) * e ^ (b * (H + 1))) * |Cfull| := by
          rw [← hrw]; exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)
      _ = _ := by ring
  have := hm m hmm
  rw [one_mul]
  linarith only [this, h1]

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Scalar interface from the actual moment-defect coefficient to the
parent-wavelength power used by the finite expansion. The fixed constant
includes the rounded-scale factor 2^(sigma L). The actual path estimate is
proved separately; the scalar leaf below removes the level-dependent
width/incidence/rank factors.

The degenerate cases are included: L=0 uses 0^0=1 and claims no gain; H=0 removes the rank
factor. Zero width, source, incidence and constants are allowed. Empty and singleton families,
identity geometry, edgeless seeds and Dm=2 only affect the already proved
actual coefficient producer, not this scalar calculation. Constants and
the finite orders precede every level and every datum. -/

/-- Fixed scalar constants supplied by the uniform stage, sampled-price
and buffer producers; none depends on a datum or an actual kernel order. -/
structure PreparationMomentBudgetParameters where
  q : ℝ
  Λ : ℕ
  H : ℕ
  L : ℕ
  σ : ℝ
  θ : ℝ
  Cwid : ℝ
  Csample : ℝ
  CI : ℝ
  Cplain : ℝ
  Cbuf : ℝ
  q_pos : 1 < q
  q_lt : q < 17 / 16
  frequency : 128 ≤ Λ
  sigma_nonneg : 0 ≤ σ
  theta_nonneg : 0 ≤ θ
  width_nonneg : 0 ≤ Cwid
  sample_nonneg : 0 ≤ Csample
  ledger_nonneg : 0 ≤ CI
  plain_nonneg : 0 ≤ Cplain
  buffer_nonneg : 0 ≤ Cbuf

/-- The level-dependent numbers of the actual path estimate, with exactly
the bounds furnished by kernel widths, the sampled budget and the ledger. -/
structure PreparationMomentBudgetData (F : PreparationMomentBudgetParameters) (m : ℕ) where
  width : ℝ
  ν : ℝ
  source : ℝ
  incidence : ℝ
  width_nonneg : 0 ≤ width
  diffusivity_pos : 0 < ν
  incidence_nonneg : 0 ≤ incidence
  width_le : width ≤ F.Cwid * ocEpsilon F.q F.Λ m ^ F.σ
  incidence_le : incidence ≤ F.CI * ocEpsilon F.q F.Λ m ^ F.θ
  source_le : |source| ≤ ν * F.Csample * incidence

/-- The actual physical coefficient, with its literal factor 14 and rank power. -/
def preparationMomentDefectPrice (F : PreparationMomentBudgetParameters) {m : ℕ}
    (X : PreparationMomentBudgetData F m) : ℝ :=
  14 * (X.width ^ F.L * |X.source| / X.ν) *
    (8 * (F.Cplain * X.incidence) + 1) ^ F.H * F.Cbuf

/-- A fixed upper constant; the final factor pays rounded adjacent wavelengths. -/
def preparationMomentDefectConstant (F : PreparationMomentBudgetParameters) : ℝ :=
  14 * F.Cwid ^ F.L * F.Csample * F.CI *
    (8 * (F.Cplain * F.CI) + 1) ^ F.H * F.Cbuf * (2 : ℝ) ^ (F.σ * F.L)

/-- Bounded scalar leaf: the physical moment cost gains q sigma L parent powers. -/
def UniformMomentDefectPowerStatement : Prop :=
  ∀ (F : PreparationMomentBudgetParameters) (m : ℕ), 1 ≤ m →
    ∀ X : PreparationMomentBudgetData F m,
      preparationMomentDefectPrice F X ≤
        preparationMomentDefectConstant F * ocEpsilon F.q F.Λ (m - 1) ^ (F.q * F.σ * F.L)

/-! The fixed scalar moment-defect price. Nonnegative incidence decay bounds
the source and rank factors uniformly; the rounded adjacent wavelength bound
supplies exactly the factor 2^(sigma L) in the prescribed constant. -/

private theorem moment_price_algebra
    {width ν source incidence W Cs CI Cp Cb : ℝ} (L H : ℕ)
    (hν : 0 < ν) (hI0 : 0 ≤ incidence) (hI : incidence ≤ CI)
    (hW : 0 ≤ W) (hwidth : width ^ L ≤ W)
    (hsource : |source| ≤ ν * Cs * incidence)
    (hCs : 0 ≤ Cs) (hCp : 0 ≤ Cp) (hCb : 0 ≤ Cb) :
    14 * (width ^ L * |source| / ν) * (8 * (Cp * incidence) + 1) ^ H * Cb ≤
      14 * W * Cs * CI * (8 * (Cp * CI) + 1) ^ H * Cb := by
  have hCI : 0 ≤ CI := hI0.trans hI
  have hs : |source| / ν ≤ Cs * CI := by
    apply (div_le_iff₀ hν).mpr
    calc
      |source| ≤ ν * Cs * incidence := hsource
      _ ≤ ν * Cs * CI := mul_le_mul_of_nonneg_left hI (mul_nonneg hν.le hCs)
      _ = (Cs * CI) * ν := by ring
  have hfront : width ^ L * |source| / ν ≤ W * (Cs * CI) := by
    rw [mul_div_assoc]
    exact mul_le_mul hwidth hs (div_nonneg (abs_nonneg _) hν.le) hW
  have hbase0 : 0 ≤ 8 * (Cp * incidence) + 1 :=
    add_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCp hI0)) zero_le_one
  have hbase : 8 * (Cp * incidence) + 1 ≤ 8 * (Cp * CI) + 1 :=
    add_le_add (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hI hCp) (by norm_num : (0 : ℝ) ≤ 8)) le_rfl
  have hrank := pow_le_pow_left₀ hbase0 hbase H
  calc
    14 * (width ^ L * |source| / ν) * (8 * (Cp * incidence) + 1) ^ H * Cb ≤
        14 * (W * (Cs * CI)) * (8 * (Cp * incidence) + 1) ^ H * Cb :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfront (by norm_num)) (pow_nonneg hbase0 H)) hCb
    _ ≤ 14 * (W * (Cs * CI)) * (8 * (Cp * CI) + 1) ^ H * Cb :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrank
        (mul_nonneg (by norm_num) (mul_nonneg hW (mul_nonneg hCs hCI)))) hCb
    _ = 14 * W * Cs * CI * (8 * (Cp * CI) + 1) ^ H * Cb := by ring

/-- The actual physical moment coefficient gains the prescribed parent-scale power. -/
theorem uniform_moment_defect_power : UniformMomentDefectPowerStatement := by
  intro F m hm X
  have he := Scales.epsilon_basic (m := m) F.q_pos F.frequency
  have hE := Scales.epsilon_basic (m := m - 1) F.q_pos F.frequency
  have hinc : X.incidence ≤ F.CI := by
    calc
      X.incidence ≤ F.CI * ocEpsilon F.q F.Λ m ^ F.θ := X.incidence_le
      _ ≤ F.CI * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one he.1.le he.2.1 F.theta_nonneg) F.ledger_nonneg
      _ = F.CI := mul_one _
  have hexp : 0 ≤ F.σ * (F.L : ℝ) := mul_nonneg F.sigma_nonneg (Nat.cast_nonneg _)
  have hstep := Real.rpow_le_rpow he.1.le
    (Scales.epsilon_q_step F.q_pos F.q_lt F.frequency hm) hexp
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hE.1.le _),
    ← Real.rpow_mul hE.1.le] at hstep
  rw [← mul_assoc F.q F.σ (F.L : ℝ)] at hstep
  have hwidth0 := pow_le_pow_left₀ X.width_nonneg X.width_le F.L
  rw [mul_pow, ← Real.rpow_mul_natCast he.1.le F.σ F.L] at hwidth0
  have hwidth : X.width ^ F.L ≤ F.Cwid ^ F.L *
      ((2 : ℝ) ^ (F.σ * F.L) * ocEpsilon F.q F.Λ (m - 1) ^ (F.q * F.σ * F.L)) :=
    hwidth0.trans (mul_le_mul_of_nonneg_left hstep (pow_nonneg F.width_nonneg _))
  have hW : 0 ≤ F.Cwid ^ F.L *
      ((2 : ℝ) ^ (F.σ * F.L) * ocEpsilon F.q F.Λ (m - 1) ^ (F.q * F.σ * F.L)) :=
    mul_nonneg (pow_nonneg F.width_nonneg _) (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hE.1.le _))
  have hbound := moment_price_algebra F.L F.H X.diffusivity_pos X.incidence_nonneg
    hinc hW hwidth X.source_le F.sample_nonneg F.plain_nonneg F.buffer_nonneg
  refine hbound.trans_eq ?_
  unfold preparationMomentDefectConstant
  ring

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **Joint measurability of the edge coefficients on the whole window, by gluing**
(`LocalPreparationCoefficientDataStatement`). The edge coefficients are
jointly measurable on every short window carrying a preparation chart certificate
(`edgeCoefficient_joint_measurable`). The whole window `[a, b]` is covered by the countably many
windows `[a + kδ, min (a + (k+1)δ) b]` of length at most `δ = 2τ''`; the SAME function restricted
to each is measurable, so it is measurable on the union (`measurable_liftCover`).
- `measurable_icc_glue`: the gluing for any function of `(t, y)`;
- `isSmoothOn_window_mono`: the smoothness of the family restricts to subwindows;
- `edgeCoefficient_window_measurable`: the edge coefficients on the whole window.

For an empty window `b < a` every piece is empty, for a point window `a = b` there is one
piece, and for `δ ≥ b - a` there is one nonempty piece. -/

/-- **Gluing over a bounded window**: a function of `(t, y)` measurable on every subwindow of
length at most `δ` is measurable on the window. -/
theorem measurable_icc_glue {Y T : Type*} [MeasurableSpace Y] [MeasurableSpace T]
    {a b δ : ℝ} (hδ : 0 < δ) (g : ℝ → Y → T)
    (hloc : ∀ c d, a ≤ c → c ≤ d → d ≤ b → d - c ≤ δ →
      Measurable (fun z : Set.Icc c d × Y => g z.1 z.2)) :
    Measurable (fun z : Set.Icc a b × Y => g z.1 z.2) := by
  classical
  let t : ℕ → Set (Set.Icc a b × Y) := fun k =>
    {z | (z.1 : ℝ) ∈ Set.Icc (a + k * δ) (min (a + (k + 1) * δ) b)}
  have htm : ∀ k, MeasurableSet (t k) := fun k =>
    measurableSet_Icc.preimage (measurable_subtype_coe.comp measurable_fst)
  have htU : ⋃ k, t k = Set.univ := by
    refine Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 ?_
    obtain ⟨⟨s, hs1, hs2⟩, y⟩ := z
    have hq : 0 ≤ (s - a) / δ := div_nonneg (sub_nonneg.2 hs1) hδ.le
    refine ⟨⌊(s - a) / δ⌋₊, ?_, le_min ?_ hs2⟩
    · have h1 := (le_div_iff₀ hδ).1 (Nat.floor_le hq)
      show a + (⌊(s - a) / δ⌋₊ : ℝ) * δ ≤ s
      linarith
    · have h2 := (div_lt_iff₀ hδ).1 (Nat.lt_floor_add_one ((s - a) / δ))
      show s ≤ a + ((⌊(s - a) / δ⌋₊ : ℕ) + 1 : ℝ) * δ
      linarith
  let f : ∀ k, t k → T := fun _ z => g z.1.1 z.1.2
  have hagree : ∀ (i j : ℕ) (x : Set.Icc a b × Y) (hxi : x ∈ t i) (hxj : x ∈ t j),
      f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ := fun _ _ _ _ _ => rfl
  have hfm : ∀ k, Measurable (f k) := by
    intro k
    by_cases hk : a + k * δ ≤ b
    · have hkδ : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ.le
      have hloc' := hloc (a + k * δ) (min (a + (k + 1) * δ) b) (by linarith)
        (le_min (by nlinarith) hk) (min_le_right _ _)
        (by have := min_le_left (a + (k + 1) * δ) b; nlinarith)
      have hemb : Measurable (fun z : t k =>
          ((⟨(z.1.1 : ℝ), z.2⟩ : Set.Icc (a + k * δ) (min (a + (k + 1) * δ) b)), z.1.2)) :=
        ((measurable_subtype_coe.comp (measurable_fst.comp measurable_subtype_coe)).subtype_mk).prodMk
          (measurable_snd.comp measurable_subtype_coe)
      exact hloc'.comp hemb
    · have : IsEmpty (t k) := ⟨fun z => hk (z.2.1.trans z.1.1.2.2)⟩
      exact Subsingleton.measurable
  have hG : (fun z : Set.Icc a b × Y => g z.1 z.2) = Set.liftCover t f hagree htU := by
    funext z
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (htU ▸ Set.mem_univ z : z ∈ ⋃ k, t k)
    rw [Set.liftCover_of_mem hk]
  rw [hG]
  exact measurable_liftCover t htm f hfm hagree htU

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}

omit [Fintype ι] in
/-- The smoothness of a charted family on a window restricts to its subwindows. -/
theorem isSmoothOn_window_mono {F : ChartedFamily ι h D P' Ctx} {E : ℝ} {n : ι → ℕ}
    {a b c d : ℝ} (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (hac : a ≤ c) (hdb : d ≤ b) :
    F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc c d)) E n := by
  intro p pc v u γ k I tY htY z
  exact hs p pc v u γ k I tY
    ⟨⟨htY.1.1, le_trans hac htY.1.2.1, le_trans htY.1.2.2 hdb⟩, htY.2⟩ z

variable [∀ i, FiniteDimensional ℝ (h i)]

/-- **The edge coefficients are jointly measurable on the whole window**, from the chart
certificates of its short subwindows and the smoothness of the family on the window. -/
theorem edgeCoefficient_window_measurable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ}
    {hφ : IsAdmissibleStream φ} {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ}
    (F : ChartedFamily ι h D P' Ctx) (hτ : 0 < ocTauPP α q Λ m)
    (hcert : ∀ (c d : ℝ), a ≤ c → c ≤ d → d ≤ b → d - c ≤ 2 * ocTauPP α q Λ m →
      ∃ (l₀ : ℤ) (P : ℕ), IsPreparationChartCertificate α q Λ m φ hφ c d
        Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (v u : ι) (d : admissibleOrders K D v u) :
    Measurable (fun z : Set.Icc a b × Vec 2 =>
      edgeCoefficient F ν e E actual K v u d z.1 z.2) :=
  measurable_icc_glue (mul_pos two_pos hτ) (edgeCoefficient F ν e E actual K v u d)
    fun c d' hac hcd hdb hlen => by
      obtain ⟨l₀, P, hc⟩ := hcert c d' hac hcd hdb hlen
      exact CycleJointProofs.edgeCoefficient_joint_measurable F hc ν e E n
        (isSmoothOn_window_mono hs hac hdb) hmeas hwmeas actual K v u d

end Family

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The common preparation from the actual evolution, finite source expansion and
one mass-uniform neutral-chain model. The covariance and near-unit bounds are
proved here, rather than left as additional preparation inputs.

The degenerate cases are included: empty and singleton families, Hpr=0, p=0 and order zero;
zero datum, an edgeless seed and identity geometry require no division by a norm.
This is a conditional assembly at a fixed stage. -/

open CoupledEnergy.Variational CycleComparison.Coarse FullLift RetainedEnergy

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] in
private theorem preparation_weighted_norm_sub_triangle {S : Finset Comp} {K : ℕ}
    (ρ : ℝ) (π w : CompIn S → ℝ) (hπ : ∀ v, 0 < π v / w v ^ 2)
    (a b c : ∀ v : CompIn S, TorusHk K (hr v.1.root)) :
    weightedNorm ρ π w (a - c) ≤ weightedNorm ρ π w (a - b) + weightedNorm ρ π w (b - c) := by
  unfold weightedNorm
  rw [← massWeightedCarrierCLM_norm (fun _ => K) ρ _ hπ (a - c),
    ← massWeightedCarrierCLM_norm (fun _ => K) ρ _ hπ (a - b),
    ← massWeightedCarrierCLM_norm (fun _ => K) ρ _ hπ (b - c)]
  have he : a - c = (a - b) + (b - c) := (sub_add_sub_cancel a b c).symm
  rw [he, map_add]
  exact norm_add_le _ _

/-- Reuse the adjoint bound for any covariance image of a weighted family. -/
theorem preparation_covariance_bound {S : Finset Comp} {K R p : ℕ} {ρ : ℝ}
    (horder : K + 2 * p ≤ R) (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : fbCovConst ρ Hc R ≤ 1) (π w : CompIn S → ℝ)
    (hπ : ∀ v, 0 < π v / w v ^ 2)
    (Z : ∀ v : CompIn S, TorusHk R (hr v.1.root))
    (W : ∀ v : CompIn S, TorusHk K (hr v.1.root))
    (hW : ∀ v, IsCovImage (covPolyQ Hc p) (Z v) (W v)) :
    weightedNorm ρ π w W ≤ ((p : ℝ) + 1) * weightedNorm ρ π w Z := by
  have hv (v : CompIn S) : factorialNormSq ρ (W v).val ≤
      ((p : ℝ) + 1) ^ 2 * factorialNormSq ρ (Z v).val := by
    obtain ⟨V, hV, hb⟩ := covariance_trace_exists horder hρ Hc hM (Z v)
    have he : W v = V := covImage_unique (covPolyQ Hc p) (Z v) (W v) V (hW v) hV
    rw [← he] at hb
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
    simpa only [mul_pow, Real.sq_sqrt (factorialNormSq_nonneg _ _)] using hs
  unfold weightedNorm massNormSq
  have hs : (∑ v : CompIn S, (π v / w v ^ 2)⁻¹ * factorialNormSq ρ (W v).val) ≤
      ((p : ℝ) + 1) ^ 2 * ∑ v : CompIn S, (π v / w v ^ 2)⁻¹ * factorialNormSq ρ (Z v).val := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => (mul_le_mul_of_nonneg_left (hv v)
      (inv_nonneg.mpr (hπ v).le)).trans_eq (by ring)
  have hb := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ p + 1)] at hb
  exact hb

/-- The literal common-preparation clause at a fixed stage, with both endpoint outputs.
Only the three substantive route inputs and the preparation endpoint `M.tp` are assumed. -/
theorem common_preparation_of_insertion_route
    (F : Request hr D Dm bw j₀) {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (M : F.Model) (Cexp Cjoint Cjet : ℝ)
    (hπ : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      ∀ v, 0 < F.G.mass F.law v / w v ^ 2)
    (hjet : 0 ≤ Cjet) (horder : F.Naux + 2 * F.p ≤ F.Nout)
    (hρ : 0 < rhoEnh D F.cr F.G.level)
    (hcov : fbCovConst (rhoEnh D F.cr F.G.level) (covPrimitive D F.G.level M.tp) F.Nout ≤ 1)
    (hevol : F.EvolutionTraceStatement R M)
    (hexp : F.FiniteExpansionApproximationStatement R M Cexp)
    (hmodel : F.NeutralChainModelStatement R M Cjoint Cjet)
    (hend : F.EndpointStatement M) :
    IsCommonPreparation F.law F.P F.seedK F.freshK F.φ₀ F.hφ₀ F.G F.cr F.Q
      (max (Cjoint + Cexp) Cjet) (((F.p : ℝ) + 1) * Cjet)
      F.p F.Nout F.Naux F.s F.tf M.tp M.map ∧
    F.bufferEnd ≤ M.tp ∧
    Set.Icc (M.tp - ocTauP D.α D.q D.Λ F.G.level)
      (M.tp + ocTauP D.α D.q D.Λ F.G.level) ⊆
        ocQuietTimes D.α D.q D.Λ D.ζ F.G.level := by
  have htime : M.tp ≤ F.s + 4 * ocTauPP D.α D.q D.Λ F.G.level := by
    have h1 := hend.2.1
    have h2 := hend.2.2.1.2
    linarith only [h1, h2]
  refine ⟨⟨hend.2.2.2.1, hend.1.trans hend.2.2.1.1, htime, hmodel.1, ?_⟩,
    hend.2.2.1.1, hend.2.2.2.2⟩
  intro w hw f
  have hmass := hπ w hw
  have hinput : 0 ≤ F.inputNorm w f := Real.sqrt_nonneg _
  have heps : 0 ≤ D.eps (F.G.level - 1) := by
    unfold OCData.eps ocEpsilon
    split_ifs <;> positivity
  have hE : 0 ≤ D.eps (F.G.level - 1) ^ F.Q := Real.rpow_nonneg heps _
  have herror : F.inputNorm w ((fun v => truncateTorusHk (Nat.zero_le F.Nout) (M.map f v)) -
      R.trace M.tp (R.full f)) ≤
      max (Cjoint + Cexp) Cjet * D.eps (F.G.level - 1) ^ F.Q * F.inputNorm w f := by
    calc _ ≤ F.inputNorm w ((fun v => truncateTorusHk (Nat.zero_le F.Nout) (M.map f v)) -
          R.plainTrace M.tp f) + F.inputNorm w (R.plainTrace M.tp f - R.trace M.tp (R.full f)) :=
        preparation_weighted_norm_sub_triangle 1 _ _ hmass _ _ _
      _ ≤ Cjoint * D.eps (F.G.level - 1) ^ F.Q * F.inputNorm w f +
          Cexp * D.eps (F.G.level - 1) ^ F.Q * F.inputNorm w f :=
        add_le_add (hmodel.2 w hw f).1 (hexp.2 w hw f)
      _ = (Cjoint + Cexp) * D.eps (F.G.level - 1) ^ F.Q * F.inputNorm w f := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hE) hinput
  refine ⟨?_, ?_, (hmodel.2 w hw f).2.trans ?_, ?_⟩
  · intro U W Y hsol
    have he := (hevol w hw f).2 U W Y hsol
    change F.inputNorm w _ ≤ _
    have he' : R.trace M.tp (R.full f) = fun v => U v M.tp := he
    rw [he'] at herror
    exact herror
  · have ht := preparation_weighted_norm_sub_triangle 1 _ _ hmass
      (fun v => truncateTorusHk (Nat.zero_le F.Nout) (M.map f v))
      (R.trace M.tp (R.full f)) 0
    simp only [sub_zero] at ht
    change F.inputNorm w _ ≤ _
    exact (ht.trans (add_le_add herror (hevol w hw f).1)).trans_eq (by
      dsimp only [Request.inputNorm]
      ring)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hinput
  · intro Ain hA Qh hQh
    have hb := preparation_covariance_bound horder hρ (covPrimitive D F.G.level M.tp)
      hcov (F.G.mass F.law) w hmass (M.map f) Qh hQh
    exact (hb.trans (mul_le_mul_of_nonneg_left (hmodel.2 w hw f).2 (by positivity))).trans
      ((by ring : ((F.p : ℝ) + 1) * (Cjet * F.inputNorm w f) =
        (((F.p : ℝ) + 1) * Cjet) * F.inputNorm w f).le.trans
          (mul_le_mul_of_nonneg_left hA (mul_nonneg (by positivity) hjet)))

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Extend the positive sampling budget from short preparation charts to a
whole bounded time window. The SAME full-window pointwise envelope bounds
the identity sums; a decomposition may not sum independent window prices.
The degenerate cases are included: a point or empty window, empty and singleton components,
zero identities, identity geometry and D=2 keep the same positive budget. This is a genuine
local-to-global sampling leaf; no uniform whole-window chart-age is assumed. -/

/-- Certificates on every short contained interval suffice for the global
sampled coefficient seminorm, with the existing reserve-only constant. -/
def LocalPreparationSampledEnvelopeStatement : Prop :=
  ∀ (D Kmax Jchart Jm : ℕ), Kmax + D + 2 ≤ Jchart → Kmax + D + 2 ≤ Jm →
  ∀ Cm Cchart : ℕ → ℝ, ∃ Cprep : ℝ, 1 ≤ Cprep ∧
  ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (a b Cpad Cage : ℝ) (Npad : ℕ) (ν e ρ : ℝ),
    0 < ocTauPP α q Λ m → 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
  ∀ {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {Part : Type*} {Ctx : Part → Type*} (F : ChartedFamily ι h D Part Ctx)
    (π : ι → ℝ), (∀ i, 0 < π i) →
  ∀ (K : ι → ℕ), (∀ i, K i ≤ Kmax) → ∀ (actual : ∀ pc, Ctx pc) (B : ι → ι → ℝ),
    (∀ v u, 0 ≤ B v u) →
    (∀ (c d : ℝ), a ≤ c → c ≤ d → d ≤ b → d - c ≤ 2 * ocTauPP α q Λ m →
      ∃ (l₀ : ℤ) (P : ℕ), IsPreparationChartCertificate α q Λ m φ hφ c d
        Cpad Cage Npad Jchart Cchart l₀ P F) →
    IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
    IsSampledEnvelope F π K actual a b ν e (ocEpsilon q Λ (m - 1)) ρ Cprep B

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Conditional assembly of the exact local preparation sampling statement.
Every constituent keeps one full-window native budget before positive summation. -/

open CycleJointProofs
universe u v w z

/-- Short certificates control global constituent norms against full-window native jets. -/
def LocalPreparationLoweringBudgetStatement : Prop :=
  ∀ (D Kmax Jchart Jm : ℕ), Kmax + D + 2 ≤ Jchart → Kmax + D + 2 ≤ Jm →
  ∀ Cm Cchart : ℕ → ℝ,
  ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (a b Cpad Cage : ℝ) (Npad : ℕ) (ν e ρ : ℝ),
    0 < ocTauPP α q Λ m → 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
  ∀ {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {Part : Type w} {Ctx : Part → Type z} (F : ChartedFamily ι h D Part Ctx)
    (π : ι → ℝ), (∀ i, 0 < π i) →
  ∀ (K : ι → ℕ), (∀ i, K i ≤ Kmax) → ∀ (actual : ∀ pc, Ctx pc) (B : ι → ι → ℝ),
    (∀ v u, 0 ≤ B v u) →
    (∀ (c d : ℝ), a ≤ c → c ≤ d → d ≤ b → d - c ≤ 2 * ocTauPP α q Λ m →
      ∃ (l₀ : ℤ) (P : ℕ), IsPreparationChartCertificate α q Λ m φ hφ c d
        Cpad Cage Npad Jchart Cchart l₀ P F) →
    IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
    (∀ v u (γ : F.Γ v u) d, ∀ t ∈ Set.Icc a b,
      ContDiff ℝ (K v : ℕ) (constituentPhysical F ν e (ocEpsilon q Λ (m - 1))
        actual v u γ d t)) ∧
    ∀ v u (γ : F.Γ v u) dout, dout ∈ Finset.Icc 2 D →
      coefficientSeminorm ρ (K v) a b
        (constituentPhysical F ν e (ocEpsilon q Λ (m - 1)) actual v u γ dout) ≤
      ENNReal.ofReal (‖(F.identity v u γ).map‖ *
        preparationSamplingSeminormConstant D Kmax Jchart Cchart *
        (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (din - 1), (ocEpsilon q Λ (m - 1))⁻¹ ^ (din - dout) *
            (pointwiseMolecularJet ρ e (K v) 0
              (fun z : F.Index => ChartedFamily.Domain.onWindow F (Set.Icc a b) z.1 z.2)
              (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ din I)).toReal))

/-- Positive constituent budgets give the exact global sampling statement. -/
theorem local_sampling_of_lowering
    (hlocal : LocalPreparationLoweringBudgetStatement.{u, v, w, z}) :
    LocalPreparationSampledEnvelopeStatement.{u, v, w, z} := by
  intro D Kmax Jchart Jm hchart hmol Cm Cchart
  let C := preparationSamplingSeminormConstant D Kmax Jchart Cchart
  let Cbase := C * D * |Cm 0|
  refine ⟨max 1 Cbase, le_max_left _ _, ?_⟩
  intro α q Λ m φ hφ a b Cpad Cage Npad ν e ρ hτ hν hρ hρe heE
    ι h _ _ Part Ctx F π hπ K hK actual B hB hc henv
  obtain ⟨hs, hbudget⟩ := hlocal D Kmax Jchart Jm hchart hmol Cm Cchart
    α q Λ m φ hφ a b Cpad Cage Npad ν e ρ hτ hν hρ hρe heE
    F π hπ K hK actual B hB hc henv
  have hρE : ρ ≤ ocEpsilon q Λ (m - 1) := hρe.trans heE
  have hh := sampled_envelope_of_lowering_budget F π K
    (ChartedFamily.Domain.onWindow F (Set.Icc a b)) actual a b ν e
    (ocEpsilon q Λ (m - 1)) ρ C hν hρ (hρ.trans_le hρE) hρE
    (preparationSamplingSeminormConstant_nonnegative _ _ _ _) Cm Jm B hB henv hs hbudget
  refine ⟨hh.1, ?_⟩
  intro v u
  exact (hh.2 v u).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_right 1 Cbase) (hB v u)))

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Short chart certificates transfer the same full-window positive native budgets to global constituent seminorms. -/

open CycleJointProofs

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ}

private theorem constituent_smooth_at
    (F : ChartedFamily ι h D P' Ctx) {l : ℤ} {Q : ℕ} {t : ℝ}
    (hc : IsPreparationChartCertificate α q Λ m φ hφ t t
      Cpad Cage Npad Jchart Cchart l Q F)
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (ht : t ∈ Set.Icc tS tZ) :
    ContDiff ℝ (n v : ℕ) (constituentPhysical F ν e E actual v u γ d t) := by
  have hst : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc t t)) E n := by
    intro p c v u γ d I tY htY z
    exact hs p c v u γ d I tY
      ⟨⟨htY.1.1, ht.1.trans htY.1.2.1, htY.1.2.2.trans ht.2⟩, htY.2⟩ z
  exact constituentPhysical_spatial_smooth F hc ν e E n hst actual v u γ d t ⟨le_rfl, le_rfl⟩

private theorem constituent_lowering_budget (F : ChartedFamily ι h D P' Ctx)
    (hc : ∀ t ∈ Set.Icc tS tZ, ∃ (l₀ : ℤ) (P : ℕ),
      IsPreparationChartCertificate α q Λ m φ hφ t t Cpad Cage Npad Jchart Cchart l₀ P F)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hchart : Kmax + D + 2 ≤ Jchart)
    (ν e ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hρ : 0 < ρ)
    (hE : 0 < ocEpsilon q Λ (m - 1)) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (Cm : ℕ → ℝ) (Jm : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K
      (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm b)
    (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u)
    (dout : ℕ) (hdout : dout ∈ Finset.Icc 2 D) :
    coefficientSeminorm ρ (K v) tS tZ
      (constituentPhysical F ν e (ocEpsilon q Λ (m - 1)) actual v u γ dout) ≤
    ENNReal.ofReal (‖(F.identity v u γ).map‖ *
      preparationSamplingSeminormConstant D Kmax Jchart Cchart *
      (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (din - 1), (ocEpsilon q Λ (m - 1))⁻¹ ^ (din - dout) *
          (pointwiseMolecularJet ρ e (K v) 0
            (fun z : F.Index => ChartedFamily.Domain.onWindow F (Set.Icc tS tZ) z.1 z.2)
            (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ din I)).toReal)) := by
  classical
  let E := ocEpsilon q Λ (m - 1)
  let dom := ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)
  let M := fun din (I : DerivativeWord2 (din - 1)) =>
    pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
      (fun z => F.dimFlux ν e E z.1 z.2 v u γ din I)
  let S := ∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
    ∑ I : DerivativeWord2 (din - 1), E⁻¹ ^ (din - dout) * (M din I).toReal
  by_cases hγ : (F.identity v u γ).map = 0
  · have hz : constituentPhysical F ν e E actual v u γ dout = fun _ _ => 0 := by
      funext t x
      exact constituentPhysical_zero_map F ν e E actual v u γ hγ dout t x
    change coefficientSeminorm ρ (K v) tS tZ
      (constituentPhysical F ν e E actual v u γ dout) ≤ _
    rw [hz, coefficientSeminorm_zero_function]
    exact zero_le
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro din _
    apply Finset.sum_nonneg
    intro I _
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hE.le) _) ENNReal.toReal_nonneg
  let B := ‖(F.identity v u γ).map‖ * preparationSamplingJetConstant D Kmax Jchart Cchart * S
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (norm_nonneg _) (preparationSamplingJetConstant_nonnegative _ _ _ _)) hS
  have hs : ∀ t ∈ Set.Icc tS tZ,
      ContDiff ℝ (K v : ℕ) (constituentPhysical F ν e E actual v u γ dout t) := by
    intro t ht
    obtain ⟨l, Q, hct⟩ := hc t ht
    exact (constituent_smooth_at F hct ν e E (fun v => K v + Jm)
      henv.1 actual v u γ dout ht).of_le
        (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have hjets : ∀ t ∈ Set.Icc tS tZ, ∀ j, j ≤ K v → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (constituentPhysical F ν e E actual v u γ dout t) x‖ ≤ B := by
    intro t ht j hj x
    obtain ⟨l, Q, hct⟩ := hc t ht
    let ts : Set.Icc t t := ⟨t, le_rfl, le_rfl⟩
    let g := fun p y => nativeArrayAssembly (dout - 1) (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ (F.piece p).anchor t)
        (F.identity v u γ).maxOrder
        (fun din I => F.dimFlux ν e E p (actual p) v u γ din I t
          (streamFlow φ hφ (F.piece p).anchor y t)
          (e⁻¹ • streamFlow φ hφ (F.piece p).anchor y t)) (dout - 1) A y a)
    have hg p (hout : t ∈ (F.piece p).output) : ContDiff ℝ (K v : ℕ) (g p) := by
      exact (natural_constituent_operator_smooth F ν e E hE.ne' (fun v => K v + Jm)
        dom henv.1 p (actual p) v u γ (dout - 1) φ hφ (F.piece p).anchor t
        (fun Y => by
          change (t, Y) ∈ ((F.piece p).output ∩ Set.Icc tS tZ) ×ˢ Set.univ
          exact ⟨⟨hout, ht⟩, Set.mem_univ Y⟩)).of_le (by exact_mod_cast Nat.le_add_right (K v) Jm)
    apply positive_constituentPhysical_jet_assembly F hct ν e E actual v u γ dout j
      ρ B hρ.le hB ts g (fun _ _ => rfl)
      (fun p hout => (hg p hout).of_le (by exact_mod_cast hj)) _ x
    intro p hout y
    have hp : ((F.piece p).output ∩ Set.Icc t t).Nonempty := ⟨t, hout, le_rfl, le_rfl⟩
    obtain ⟨has, hat, hage⟩ := preparation_piece_flow_endpoints hct p hp t
      ((F.piece p).output_subset hout) (preparation_renewal_nonnegative α q Λ m)
    have hnchart : K v ≤ Jchart + 1 := by have hk := hK v; omega
    have hnN : j + (F.identity v u γ).maxOrder ≤ Kmax + D + 2 := by
      have hk := hK v
      have hd := (F.identity v u γ).le_D
      omega
    have hh := pointwise_molecular_native_transport_uniform_budget F π hπ K Kmax hK dom ν e ρ
      hν he hE hρE (preparation_amplitude_nonnegative α q Λ (m - 1) hE.le) hρ
      Cm Jm b henv v u γ hγ p (actual p) hct.flow hnchart (Kmax + D + 2) hchart
      (F.piece p).anchor t has hat (by simpa only [abs_sub_comm] using hage)
      (fun Y => by
        change (t, Y) ∈ ((F.piece p).output ∩ Set.Icc tS tZ) ×ˢ Set.univ
        exact ⟨⟨hout, ht⟩, Set.mem_univ Y⟩) j (dout - 1) hj (by have hh := (Finset.mem_Icc.mp hdout).1; omega)
      hnN (by have hh := Finset.mem_Icc.mp hdout; omega) y
    have hr : dout - 1 + 1 = dout := by have hh := (Finset.mem_Icc.mp hdout).1; omega
    have hediff din : din - 1 - (dout - 1) = din - dout := by
      have hh := (Finset.mem_Icc.mp hdout).1
      omega
    dsimp only at hh
    simp only [hr, hediff] at hh
    change ρ ^ j * ‖iteratedFDeriv ℝ j (g p) y‖ ≤
      ‖(F.identity v u γ).map‖ * preparationSamplingJetConstant D Kmax Jchart Cchart *
        (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (din - 1), (M din I).toReal * E⁻¹ ^ (din - dout)) at hh
    have heq : (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (din - 1), (M din I).toReal * E⁻¹ ^ (din - dout)) = S := by
      dsimp only [S]
      apply Finset.sum_congr rfl
      intro din _
      apply Finset.sum_congr rfl
      intro I _
      exact mul_comm _ _
    rw [heq] at hh
    exact hh
  have hh := uniform_pointwise_coefficient_seminorm ρ hρ (K v) Kmax (hK v) tS tZ
    (constituentPhysical F ν e E actual v u γ dout) hs B hB hjets
  apply hh.trans_eq
  congr 1
  dsimp only [preparationSamplingSeminormConstant, B]
  ring


/-- Short contained certificates give one full-window positive lowering budget. -/
theorem local_preparation_lowering_budget : LocalPreparationLoweringBudgetStatement := by
  intro D Kmax Jchart Jm hchart _hmol Cm Cchart
    α q Λ m φ hφ a b Cpad Cage Npad ν e ρ hτ hν hρ hρe heE
    ι h _ _ Part Ctx F π hπ K hK actual B _hB hc henv
  have hsingle : ∀ t ∈ Set.Icc a b, ∃ (l : ℤ) (Q : ℕ),
      IsPreparationChartCertificate α q Λ m φ hφ t t
        Cpad Cage Npad Jchart Cchart l Q F := by
    intro t ht
    exact hc t t ht.1 le_rfl ht.2 (by
      rw [sub_self]
      exact mul_nonneg (by norm_num) hτ.le)
  constructor
  · intro v u γ d t ht
    obtain ⟨l, Q, hct⟩ := hsingle t ht
    exact (constituent_smooth_at F hct ν e (ocEpsilon q Λ (m - 1))
      (fun v => K v + Jm) henv.1 actual v u γ d ht).of_le
        (by exact_mod_cast Nat.le_add_right (K v) Jm)
  · intro v u γ dout hdout
    have hρE := hρe.trans heE
    exact constituent_lowering_budget F hsingle π hπ K Kmax hK hchart ν e ρ
      hν (hρ.trans_le hρe) hρ (hρ.trans_le hρE) hρE Cm Jm B henv actual v u γ dout hdout

/-- The exact local-to-global preparation sampling bridge, with no further inputs. -/
theorem local_preparation_sampled_envelope : LocalPreparationSampledEnvelopeStatement :=
  local_sampling_of_lowering local_preparation_lowering_budget

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The cascade's scalar instantiation of the already proved generic
window cover. Its start is arbitrary, so it applies at the actual buffer
endpoint. The constants and late-level floor precede every band chain,
stream, start time, finite jet request and stage datum. Only the numeric
instance is new here; the metric, drift, flow and cover analysis is that of the generic cover.

The degenerate cases are included: empty and singleton families, identity geometry, edgeless seeds
and zero orders have the same cover. A seed at n<M is included; terminal m=M is
excluded. The start may be exactly a renewal boundary (two blocks) or
interior to it (three blocks). No nonempty family or datum is needed. -/

open AVRegularity.Construction.Preservation.Assembly WindowCover

/-- One full cascade cover, with the fixed shared constants and chart
anchor inequalities, uniformly in the buffer start and all finite orders. -/
def CascadePreparationCoverStatement (α q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∃ cmax : ℝ, 0 < cmax ∧
  ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ g₀ c₀ : ℝ, 0 < g₀ → 0 < c₀ → c₀ ≤ cmax →
  ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
  ∀ m : ℕ, m₀ ≤ m → m < M →
  ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ), IsOCStreamSeq α q Λ ζ Φ →
  ∀ (hφ : IsAdmissibleStream (Φ (m - 1))) (t₁ : ℝ) (qJ Kmax : ℕ),
  ∃ (l₀ : ℤ) (P : ℕ), 1 ≤ P ∧
    ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ t₁ ∧
    t₁ < ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m ∧
    t₁ + 2 * ocTauPP α q Λ m ≤ ((l₀ : ℝ) + P - 1 / 2) * ocTauPP α q Λ m ∧
    CommonPreparationWindowCoverStatement α q Λ m ζ Φ hφ (κ m) (κ (m - 1))
      t₁ 2 c₀ (windowCoverCg * (ocA α q Λ (m - 1) * ocTauPP α q Λ m)) g₀
      (windowCoverCd * ocA α q Λ m * ocEpsilon q Λ m ^ 2 / κ m)
      windowCoverB0 1 windowCoverCb qJ Kmax windowCoverCG l₀ P 0

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization AVenhance Filter
open scoped Topology
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The cascade's numeric instance of the shared two-renewal window cover.
The radius coefficient is fixed before all requests, and the late-level floor
precedes the terminal index, band chain, stream, start time and finite orders.
All metric, drift-jet and chart analysis is reused through `windowCoverGen`. -/

open AVRegularity.Construction.Preservation.Assembly WindowCover

private theorem normalized_molecular_drift_small {e ν A B ρ a : ℝ}
    (he : 0 < e) (hν : 0 < ν) (h : (A * a) * B * ρ ^ 2 ≤ ν / 8) :
    (A * a * e ^ 2 / ν) * B * (ρ / e) ^ 2 ≤ 1 / 8 := by
  have hident : (A * a * e ^ 2 / ν) * B * (ρ / e) ^ 2 =
      ((A * a) * B * ρ ^ 2) / ν := by
    field_simp
  rw [hident]
  exact (div_le_iff₀ hν).mpr (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using h)

/-- Every sufficiently late interior level has the full common preparation
cover, uniformly in its buffer start and every finite jet request. -/
theorem cascadePreparationCover {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    CascadePreparationCoverStatement α q ζ := by
  obtain ⟨ΛW, hΛW, hW⟩ := windowCoverGen α s q ζ hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λr, hΛr, hradius⟩ :=
    preparation_joint_radius_scales hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Cu, _, Λp, hΛp, hpass⟩ :=
    Providers.CascadeInvariants.exists_passScales hα₀ hα₁ hs₀ hs₁ hq hζ
  have hB0 : 1 ≤ windowCoverB0 := by
    unfold windowCoverB0
    linarith only [Real.pi_gt_three]
  have hBpos : 0 < windowCoverB0 := zero_lt_one.trans_le hB0
  have hCd : 0 < windowCoverCd := by
    unfold windowCoverCd
    exact mul_pos (by positivity) (lt_max_of_lt_left one_pos)
  have hcap : 0 < windowCoverRadiusCap := by
    unfold windowCoverRadiusCap
    exact lt_min one_pos (by positivity)
  have hCg : 0 < windowCoverCg := by
    unfold windowCoverCg
    have h := le_max_left (78000 : ℝ) (2 * CycleComparison.Charts.metricDevConst 0)
    linarith only [h]
  obtain ⟨cD, hcD, hsmall⟩ := Buffer.exists_drift_radius_constant windowCoverCd
    windowCoverB0 hCd.le hB0
  refine ⟨max ΛW (max Λr Λp), by omega, min windowCoverRadiusCap cD,
    lt_min hcap hcD, ?_⟩
  intro Λ hΛ g₀ c₀ hg₀ hc₀ hcmax
  have h128 : 128 ≤ Λ := by omega
  have hΛ1 : 1 ≤ Λ := by omega
  have hccap : c₀ ≤ windowCoverRadiusCap := hcmax.trans (min_le_left _ _)
  have hc1 : c₀ ≤ 1 := hccap.trans (min_le_left _ _)
  obtain ⟨hgeom, hstrain⟩ := hsmall c₀ hc₀ (hcmax.trans (min_le_right _ _))
  obtain ⟨_, _, _, _, mr, hmr2, hradius⟩ := hradius Λ (by omega) c₀ hc₀
  obtain ⟨mg, hmg2, hmg⟩ := EntryWeakProofs.weak_anchor_product_eventually_small
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ h128 windowCoverCg g₀ hg₀
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hlim : Tendsto (fun m : ℕ => Cu * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (Buffer.preparation_parent_power_tendsto_zero hq.1 h128
        (mul_pos (by norm_num : (0 : ℝ) < 3) hδ))
  obtain ⟨mp, hmp⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_le_nhds zero_lt_one))
  refine ⟨max mr (max mg mp), by omega, ?_⟩
  intro M κ hband m hm hmM Φ hΦ hφ t₁ qJ Kmax
  have hm2 : 2 ≤ m := by omega
  have he : 0 < ocEpsilon q Λ m := Stream.ocEpsilon_pos hΛ1
  have ha : 0 < ocA α q Λ m := Real.rpow_pos_of_pos he _
  have hν : 0 < κ m := CycleReference.bandChain_pos hΛ1 hζ hband (by omega)
  have ht : 0 < ocTauPP α q Λ m := Stream.ocTauPP_pos hΛ1
  have hap : 0 < ocA α q Λ (m - 1) :=
    Real.rpow_pos_of_pos (Stream.ocEpsilon_pos hΛ1) _
  have hrEq := (hradius M κ hband m (by omega) hmM).1
  have hr := Buffer.molecular_radius_bounds hc₀ he hν ha
  rw [hrEq] at hr
  have hd := Buffer.molecular_radius_drift_smallness hc₀ he hν ha hCd.le hBpos.le
    hgeom hstrain
  rw [hrEq] at hd
  have hρcap : ocRhoMol α q Λ m c₀ (κ m) ≤ windowCoverRadiusCap * ocEpsilon q Λ m :=
    hr.2.1.trans (mul_le_mul_of_nonneg_right hccap he.le)
  let D : OCData :=
    { α := α, q := q, Λ := Λ, ζ := ζ, Φ := Φ,
      hΦ := Velocity.streamSeq_admissible hζ h128 hΦ, κ := κ, term := M }
  have hpass' := hpass D rfl rfl rfl (by dsimp only [D]; omega) hband m hm2
    (by dsimp only [D]; omega)
  have hεlift : ocEpsilon q Λ m ≤ Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) :=
    hpass'.hεd.trans ((div_le_one hpass'.hρ0).mp
      (hpass'.hDρ.trans (hmp m (by omega))))
  have hρR : ocRhoMol α q Λ m c₀ (κ m) ≤ Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) :=
    hr.2.1.trans ((mul_le_of_le_one_left he.le hc1).trans hεlift)
  let F : WindowCoverFrame α s q ζ :=
    { hα₀ := hα₀, hα₁ := hα₁, hs₀ := hs₀, hs₁ := hs₁, hq := hq, hζ := hζ,
      Λ := Λ, hΛ := h128, M' := M, κ := κ, hband := hband, m := m, hm2 := hm2,
      hmM := by omega, ν := κ m, B := κ (m - 1), hν := rfl, hB := rfl,
      Φ := Φ, hΦ := hΦ, hφ := hφ, tS := t₁, ρs := ocRhoMol α q Λ m c₀ (κ m),
      g := windowCoverCg * (ocA α q Λ (m - 1) * ocTauPP α q Λ m), g₀ := g₀,
      a := windowCoverCd * ocA α q Λ m * ocEpsilon q Λ m ^ 2 / κ m,
      rho_pos := hr.1, rho_cap := hρcap, rho_R := hρR,
      g_nonneg := (mul_pos hCg (mul_pos hap ht)).le,
      g_upper := hmg m (by omega), g_lower := le_rfl,
      a_nonneg := div_nonneg (mul_nonneg (mul_nonneg hCd.le ha.le) (sq_nonneg _)) hν.le,
      a_lower := le_rfl, drift_scale := by simpa only [mul_div_assoc] using hd.1,
      drift_small := normalized_molecular_drift_small he hν hd.2 }
  have hblocks := windowCoverBlocks F
  refine ⟨windowCoverFirstBlock F, windowCoverBlockCount F, hblocks.pos,
    hblocks.window.1, hblocks.window.2.1, hblocks.window.2.2.2, ?_⟩
  exact hW F (by dsimp only [F]; omega) qJ Kmax 0

end AVRegularity.Construction.Preservation.CommonPreparation
end
