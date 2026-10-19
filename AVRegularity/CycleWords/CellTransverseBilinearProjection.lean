-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.DerivativeSourceDensity
import AVRegularity.CoupledEnergyPlane.Transport.CarrierTransport
public import AVRegularity.Weighted.WordPredecessorFluxIdentity
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Renewal bookkeeping at a fixed moment for each response level and graph
rank. The piece and transport estimates are instantiated by the geometry. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def responseGrade (n J H Ks j rank : ℕ) : ℕ := n + (J - j + H - rank) * Ks

theorem gradedResponse_renewal_mass_budget {P N : ℕ} (hP : P ≤ N) (H Ks J n : ℕ)
    (rank : ι → ℕ) (hrank : ∀ x, rank x ≤ H) (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (K : ι → ℕ) (ϖ ρ : ℝ) (left right : Fin P → ℝ)
    (F : ∀ x, PlaneHk Set.univ (K x) (h x))
    (f : ∀ (_ : Fin P) (_ : Fin (J + 1)) x, PlaneHk Set.univ (K x) (h x))
    (Z : ∀ (_ : Fin P) (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x) (h x))
    (Zw : ∀ (_ : Fin P) (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (R A L ε : ℝ≥0∞) (hR : 1 ≤ R) (hA : 1 ≤ A) (hL : 1 ≤ L)
    (hRf : R ≠ ⊤) (hAf : A ≠ ⊤) (hLf : L ≠ ⊤) (hεf : ε ≠ ⊤)
    (hF : (∑ x, ENNReal.ofReal ((π x)⁻¹) *
      weightedFactorialNormSq (n + (J + H) * Ks) ϖ 0 ρ (K x) (F x)) ≠ ⊤)
    (hfirst : ∀ i : Fin P, i.val = 0 → ∀ j x, f i j x = if j = 0 then F x else 0)
    (hrenew : ∀ i i' : Fin P, i'.val = i.val + 1 → ∀ j : Fin (J + 1), ∀ x,
      weightedFactorialNormSq (responseGrade n J H Ks j.val (rank x)) ϖ 0 ρ (K x) (f i' j x) ≤
        L * nativeComponentEnergy (responseGrade n J H Ks j.val (rank x)) ϖ ρ
          (left i) (right i) (Z i j x) (Zw i j x))
    (hpiece : ∀ i : Fin P,
      (∀ j x q, q + (j.val + rank x) * Ks ≤ n + (J + H) * Ks →
        weightedFactorialNormSq q ϖ 0 ρ (K x) (f i j x) ≠ ⊤) →
      ∀ j : Fin (J + 1),
      (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        nativeComponentEnergy (responseGrade n J H Ks j.val (rank x)) ϖ ρ
          (left i) (right i) (Z i j x) (Zw i j x)) ≤
        ennResponseMassMajorant R ε (fun l => A * ∑ x, ENNReal.ofReal ((π x)⁻¹) *
          weightedFactorialNormSq (responseGrade n J H Ks l (rank x)) ϖ 0 ρ (K x)
            (f i ⟨min l J, by omega⟩ x)) j.val) :
    ∀ i : Fin P, ∀ j : Fin (J + 1),
      (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        nativeComponentEnergy (responseGrade n J H Ks j.val (rank x)) ϖ ρ
          (left i) (right i) (Z i j x) (Zw i j x)) ≤
        ((2 * R * A * L) ^ N) ^ (j.val + 1) * ε ^ j.val *
          ∑ x, ENNReal.ofReal ((π x)⁻¹) *
            weightedFactorialNormSq (n + (J + H) * Ks) ϖ 0 ρ (K x) (F x) := by
  classical
  let ji := fun j : ℕ => (⟨min j J, by omega⟩ : Fin (J + 1))
  let data := fun i : Fin P => fun j : ℕ => ∑ x, ENNReal.ofReal ((π x)⁻¹) *
    weightedFactorialNormSq (responseGrade n J H Ks j (rank x)) ϖ 0 ρ (K x) (f i (ji j) x)
  let energy := fun i : Fin P => fun j : ℕ => ∑ x, ENNReal.ofReal ((π x)⁻¹) *
    nativeComponentEnergy (responseGrade n J H Ks j (rank x)) ϖ ρ (left i) (right i)
      (Z i (ji j) x) (Zw i (ji j) x)
  let D := ∑ x, ENNReal.ofReal ((π x)⁻¹) *
    weightedFactorialNormSq (n + (J + H) * Ks) ϖ 0 ρ (K x) (F x)
  have hfirstBound (i : Fin P) (hi : i.val = 0) : data i 0 ≤ D := by
    apply Finset.sum_le_sum
    intro x _
    simp only [ji, Nat.zero_min, hfirst i hi]
    apply mul_le_mul_right
    apply weightedFactorialNormSq_moment_mono
    unfold responseGrade
    exact Nat.add_le_add_left (Nat.mul_le_mul_right Ks (Nat.sub_le _ _)) n
  have hfirstZero (i : Fin P) (hi : i.val = 0) (j : ℕ) (hj : 1 ≤ j) (hjJ : j ≤ J) : data i j = 0 := by
    have hji : ji j ≠ 0 := by intro hz; have hh := congrArg Fin.val hz; dsimp [ji] at hh; omega
    simp only [data, hfirst i hi, ite_eq_right hji, Weighted.weightedFactorialNormSq_zero_carrier, mul_zero, Finset.sum_const_zero]
  have hr (i i' : Fin P) (hi : i'.val = i.val + 1) (j : ℕ) (hj : j ≤ J) :
      data i' j ≤ L * energy i j := by
    dsimp only [data, energy]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have hh := mul_le_mul_right (hrenew i i' hi (ji j) x) (ENNReal.ofReal ((π x)⁻¹))
    simpa only [ji, Nat.min_eq_left hj, mul_assoc, mul_comm L, mul_left_comm L] using hh
  have hdFromMass (i : Fin P) (hd : ∀ j ≤ J, data i j ≠ ⊤) :
      ∀ j x q, q + (j.val + rank x) * Ks ≤ n + (J + H) * Ks →
        weightedFactorialNormSq q ϖ 0 ρ (K x) (f i j x) ≠ ⊤ := by
    intro j x q hq
    have hj : j.val ≤ J := Nat.le_of_lt_succ j.isLt
    have hx := finitePositiveMass_ofReal_inv_component_ne_top π
      (fun x => weightedFactorialNormSq (responseGrade n J H Ks j.val (rank x)) ϖ 0 ρ (K x) (f i (ji j.val) x))
      hπ (hd j.val hj) x
    have hji : ji j.val = j := Fin.ext (Nat.min_eq_left hj)
    rw [hji] at hx
    have hg : q ≤ responseGrade n J H Ks j.val (rank x) := by
      have heq : responseGrade n J H Ks j.val (rank x) + (j.val + rank x) * Ks = n + (J + H) * Ks := by
        unfold responseGrade
        have hh := hrank x
        have hs : J - j.val + H - rank x + (j.val + rank x) = J + H := by omega
        rw [Nat.add_assoc, ← Nat.add_mul, hs]
      omega
    exact ne_top_of_le_ne_top hx (weightedFactorialNormSq_moment_mono hg ϖ 0 ρ (K x) (f i j x))
  have hb (i : Fin P) (hd : ∀ j ≤ J, data i j ≠ ⊤) (j : ℕ) (hj : j ≤ J) :
      energy i j ≤ ennResponseMassMajorant R ε (fun l => A * data i l) j := by
    have hh := hpiece i (hdFromMass i hd) (ji j)
    simpa only [energy, data, ji, Nat.min_eq_left hj] using hh
  have hdf : ∀ i : Fin P, ∀ j ≤ J, data i j ≠ ⊤ := by
    apply finite_response_renewal_data_ne_top J data energy L hLf
    · intro i hi j hj
      by_cases hz : j = 0
      · subst j
        exact ne_top_of_le_ne_top hF (hfirstBound i hi)
      · rw [hfirstZero i hi j (by omega) hj]
        exact ENNReal.zero_ne_top
    · exact hr
    · intro i hd j hj
      exact ne_top_of_le_ne_top
        (ennResponseMassMajorant_ne_top R ε hRf hεf (fun l => A * data i l) J
          (fun l hl => ENNReal.mul_ne_top hAf (hd l hl)) j hj) (hb i hd j hj)
  have hh := finite_response_renewal_budget hP J energy data D A R L ε hA hR hL
    hfirstBound hfirstZero hr (fun i j hj => hb i (hdf i) j hj)
  intro i j
  have hj : j.val ≤ J := Nat.le_of_lt_succ j.isLt
  have hji : ji j.val = j := Fin.ext (Nat.min_eq_left hj)
  simpa only [energy, D, hji] using hh i j.val hj

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.CycleWords

/-! Continuity closes the half-open quiet left buffer for every actual pulse extension. -/

theorem interiorOrientationExtensions_quiet_left {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    (hL : 0 < ocEll q Λ m ν ^ 2) (a b D : ℝ) (marks : Fin 2 → Finset ℝ)
    (hD : D ≤ (ocTau α q Λ m / ocEll q Λ m ν ^ 2) / 4)
    (hleft : Ico a (a + D) ⊆ interiorTrimmedQuiet (ocTau α q Λ m / ocEll q Λ m ν ^ 2)
      (ocCellDrift α q Λ ζ m ν y₀))
    (hright : Ioc (b - D) b ⊆ interiorTrimmedQuiet (ocTau α q Λ m / ocEll q Λ m ν ^ 2)
      (ocCellDrift α q Λ ζ m ν y₀)) :
    let reg := interiorBufferedBlockRegions (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b D
      (ocCellDrift α q Λ ζ m ν y₀) marks
    ∀ p : Fin reg.P, 0 < D → ∀ t ∈ Icc (reg.lo p - D) (reg.lo p), ∀ z,
      interiorOrientationExtensions α q Λ ζ m ν y₀ a b p t z = 0 := by
  classical
  let reg := interiorBufferedBlockRegions (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b D
    (ocCellDrift α q Λ ζ m ν y₀) marks
  have hq := interiorBufferedActualRegions_quiet_buffers hΛ hζ ν y₀ hL a b D marks
    hleft hright hD
  dsimp only
  intro p hDpos t ht z
  let n := interiorActivePulseRegionIndex (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b
    (ocCellDrift α q Λ ζ m ν y₀) p
  have hk : Odd (2 * n + 1) := ⟨n, by ring⟩
  exact interiorSinglePulseDrift_quiet_closed hΛ hζ ν y₀ hk (reg.lo p) D hDpos
    (fun s hs => interiorTrimmedQuiet_drift
      (div_pos (AVRegularity.Construction.Stream.ocTau_pos hΛ) hL).le ((hq p).1 hs)) t ht z

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The actual clipped compact energy estimate, retaining diffusion dissipation. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_planeWeak_clipped_compact_value_gronwall
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (M : ℝ) (hM : 0 ≤ M) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (hCell : IsCellMetric G)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (ha : t₀ ≤ a) (hb : b ≤ t₀ + S)
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (slice : ℝ → PlaneHk Set.univ 1 E) (F : ℝ → PlaneFluxL2 E)
    (H : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (h : PlaneWeakHilbertCurve a b u slice
      (fun t => planeValueForcedDual
        (planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) M hvb t)
        (cellMetricIntervalDiffusion a b hab G (fun t ht k j => (hG t ht k j).continuous)
          hCell t) (slice t) (F t) (H t)))
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (hdχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ η)
    (B : ℝ) (hB : 0 < B) (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hH : MemLp H 2 (volume.restrict (Icc a b))) :
    ∀ t ∈ Icc a b,
      (∫ x, χ x ^ 2 * clipWeight B (W.W m t x) * ‖u t x‖ ^ 2) +
      (∫ s in a..t, ∫ x, (1 / 2) * χ x ^ 2 * clipWeight B (W.W m s x) *
        ‖(WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) (slice s) i x) :
          PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ≤
      ((∫ x, χ x ^ 2 * clipWeight B (W.W m a x) * ‖u a x‖ ^ 2) +
        ∫ s in a..b,
          8 * (∫ x, clipWeight B (W.W m s x) *
            ‖(WithLp.toLp 2 (fun i => F s i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
          (4096 * η ^ 2 + 16 * M * η) *
            (∫ x, clipWeight B (W.W m s x) * ‖u s x‖ ^ 2) +
          2 * (∫ x, (χ x ^ 2 * clipWeight B (W.W m s x)) * (‖H s x‖ * ‖u s x‖))) *
        Real.exp (18 * W.lam m * (t - a)) := by
  obtain ⟨P, htime, hgrowth⟩ := cellMetric_planeWeak_clipped_value_energy_growth a b hab v hv hdiv M hM hvb
    G hG hCell hGs t₀ S ϖ zc N m Cw W hm ha hb u slice F H h χ hχ hsχ
    hχ0 hχ1 η hη hdχ B hB
  let q := fun t x => clipWeight B (W.W m t x)
  let force := fun t => ∫ x, q t x *
    ‖(WithLp.toLp 2 (fun i => F t i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  let val := fun t => ∫ x, (χ x ^ 2 * q t x) * (‖H t x‖ * ‖u t x‖)
  let mass := fun t => ∫ x, q t x * ‖u t x‖ ^ 2
  let d := fun t => ∫ x, (1 / 2) * χ x ^ 2 * q t x *
    ‖(WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) (slice t) i x) :
      PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  let c := 4096 * η ^ 2 + 16 * M * η
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hu : MemLp u 2 (volume.restrict (Icc a b)) :=
    (memLp_congr_ae h.agrees).2 ((planeHkValueOperator (E := E) 1).comp_memLp' h.state)
  have hvint : Integrable val (volume.restrict (Icc a b)) :=
    chartWeights_clipped_cutoff_value_product_integrable W m hm B hB χ hχ.continuous
      hχ0 hχ1 _ H u hH hu
  have hfint : Integrable force (volume.restrict (Icc a b)) :=
    chartWeights_clipped_finite_time_integrable W m hm B hB _ F hF
  have hmint : Integrable mass (volume.restrict (Icc a b)) :=
    chartWeights_clipped_scalar_time_integrable W m hm B hB _ u hu
  have hdint : Integrable d (volume.restrict (Icc a b)) := by
    have hi := chartWeights_clipped_cutoff_finite_time_integrable W m hm B hB χ
      hχ.continuous hχ0 hχ1 _
      (fun t => planeH1GradientOperator (E := E) (slice t))
      ((planeH1GradientOperator (E := E)).comp_memLp' h.state)
    simpa only [d, q, integral_const_mul, mul_assoc] using hi.const_mul (1 / 2 : ℝ)
  have hforce0 t : 0 ≤ force t := integral_nonneg (fun x => by
    exact mul_nonneg (clipWeight_pos hB (W.pos m hm t x)).le (sq_nonneg _))
  have hval0 t : 0 ≤ val t := integral_nonneg (fun x =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (clipWeight_pos hB (W.pos m hm t x)).le)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hmass0 t : 0 ≤ mass t := integral_nonneg (fun x =>
    mul_nonneg (clipWeight_pos hB (W.pos m hm t x)).le (sq_nonneg _))
  have hd0 t : 0 ≤ d t := integral_nonneg (fun x => by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (clipWeight_pos hB (W.pos m hm t x)).le) (sq_nonneg _))
  exact scalar_energy_dissipation_le_gronwall hab htime (18 * W.lam m)
    (mul_nonneg (by norm_num) (W.lam_bound m hm).1)
    (fun t => 8 * force t + c * mass t + 2 * val t) d
    (intervalIntegrable_of_integrable_Icc hab (((hfint.const_mul 8).add (hmint.const_mul c)).add (hvint.const_mul 2)))
    (intervalIntegrable_of_integrable_Icc hab hdint)
    (Filter.Eventually.of_forall (fun t => add_nonneg (add_nonneg (mul_nonneg (by norm_num) (hforce0 t))
      (mul_nonneg hc (hmass0 t))) (mul_nonneg (by norm_num) (hval0 t))))
    (Filter.Eventually.of_forall hd0) (by
      simpa only [d, force, c, mass, val, q, add_assoc] using hgrowth)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! Unshifted transport is energy neutral; the diagonal generator retains only normalized coupling. -/

theorem cellNormalizedGenerator_diagonal
    (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) :
    cellGeneratorForm ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
      hG V hv.1 hb t u u =
    cellDiffusionForm ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
      hG t u u -
      inner ℝ (cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t
        (torusHkValueCLM u))) (torusHkValueCLM u) +
      inner ℝ (cellScalarCLM (κ t) (torusHkValueCLM u))
        (torusHkValueCLM u) := by
  let C : CellCoefficients := ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
  let p := u
  have hd : (∑ j : Fin 2, inner ℝ
      (cellDriftEntryCLM C V hv.1 hb t j (cellDerivativeCLM j p)) (torusHkValueCLM u)) = 0 :=
    by
      simpa only [C, p, cellDriftEntryCLM, cellDriftForm, sum_apply, pullbackInnerCLM_apply,
        ContinuousLinearMap.comp_apply] using cellDriftForm_energy_zero hv V hb t u
  have hsft : (∑ j : Fin 2, inner ℝ
      (cellDriftEntryCLM C V hv.1 hb t j (cellShiftedDerivativeCLM C.θ j p))
        (torusHkValueCLM u)) =
      inner ℝ (cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t
        (torusHkValueCLM p))) (torusHkValueCLM u) := by
    simp only [cellShiftedDerivativeCLM, add_apply, ContinuousLinearMap.comp_apply,
      map_add, inner_add_left]
    rw [Finset.sum_add_distrib, hd, zero_add, ← sum_inner]
    exact congrArg (fun q : ComplexCellL2 => inner ℝ q (torusHkValueCLM u))
      (cellScaledDriftMultiplier_sum η Cw hCw hv hw C rfl V hb ξ t (torusHkValueCLM p))
  simp only [cellGeneratorForm, add_apply, sub_apply, sum_apply, pullbackInnerCLM_apply,
    ContinuousLinearMap.comp_apply]
  rw [hsft]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Every reserved native transport multiplier has a universal constant times Pe. -/

 def constructedEntryUniversalJetPrice (n : ℕ) : ℝ :=
  (Fintype.card (DerivativeWord2 n) : ℝ) * ‖realScalarMultiplierMap‖ * constructedSpatialJetPrice n

 def constructedEntryUniversalNativePrice (K : ℕ) : ℝ :=
  (∑ l : Fin (K + 1), factorialRootWeight 1 l.val * constructedEntryUniversalJetPrice l.val) *
    Real.sqrt (factorialWeightMax 1 K) / Real.sqrt (factorialWeightMin 1 K)

 theorem constructedEntryUniversalJetPrice_nonneg (n : ℕ) :
    0 ≤ constructedEntryUniversalJetPrice n := by
  unfold constructedEntryUniversalJetPrice
  exact mul_nonneg (by positivity) (constructedSpatialJetPrice_nonneg n)

 theorem constructedEntryUniversalNativePrice_nonneg (K : ℕ) :
    0 ≤ constructedEntryUniversalNativePrice K := by
  unfold constructedEntryUniversalNativePrice
  apply div_nonneg
  · exact mul_nonneg (Finset.sum_nonneg (fun l _ => mul_nonneg
      (by unfold factorialRootWeight; positivity) (constructedEntryUniversalJetPrice_nonneg l.val)))
      (Real.sqrt_nonneg _)
  · exact Real.sqrt_nonneg _

 theorem constructedDriftEntryJetPrice_polynomial
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (n : ℕ) :
    constructedDriftEntryJetPrice α q Λ m ν n ≤
      constructedEntryUniversalJetPrice n * peFactor (ν / ocMeanFlux α q Λ ζ m ν) := by
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (constructed_amplitude_polynomial_price hΛ hζ hν hr)
      (by positivity : 0 ≤ (2 * Real.pi) ^ n))
    (by positivity : 0 ≤ (Fintype.card (DerivativeWord2 n) : ℝ) * ‖realScalarMultiplierMap‖)
  exact h.trans_eq (by
    unfold constructedEntryUniversalJetPrice constructedSpatialJetPrice
    simp only [pow_zero, mul_one]
    ring)

 theorem constructedDriftEntryNativePrice_polynomial
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (K : ℕ) :
    constructedDriftEntryNativePrice α q Λ m ν K ≤
      constructedEntryUniversalNativePrice K * peFactor (ν / ocMeanFlux α q Λ ζ m ν) := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (K + 1))))
    (fun l _ => mul_le_mul_of_nonneg_left
      (constructedDriftEntryJetPrice_polynomial hΛ hζ hν hr l.val)
      (by unfold factorialRootWeight; positivity : 0 ≤ factorialRootWeight 1 l.val))
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (factorialWeightMax 1 K)))
    (Real.sqrt_nonneg (factorialWeightMin 1 K))
  exact h.trans_eq (by
    unfold constructedEntryUniversalNativePrice
    simp only [← mul_assoc, ← Finset.sum_mul]
    ring)

 theorem constructedDriftEntryNativeCLM_polynomial_bound (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (i : Fin 2) (t : ℝ) (U : TorusHk K ℂ) :
    ‖constructedDriftEntryNativeCLM K hΛ hζ ν y₀ hv i t U‖ ≤
      (constructedEntryUniversalNativePrice K * peFactor (ν / ocMeanFlux α q Λ ζ m ν)) * ‖U‖ :=
  (constructedDriftEntryNativeCLM_norm_bound K hΛ hζ ν y₀ hv i t U).trans
    (mul_le_mul_of_nonneg_right (constructedDriftEntryNativePrice_polynomial hΛ hζ hν hr K) (norm_nonneg U))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Taylor coefficients retain every original slow derivative price and constituent identity. -/

theorem familyMolecular_remainder_coefficient_uniform (Ks Kmax : ℕ) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀ {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      ∀ (dom : F.Domain) (ν e E ρ : ℝ), 0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks + 1 ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (γ : F.Γ v u), (F.identity v u γ).map ≠ 0 → ∀ d,
      d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder →
      ∀ (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2) (k : Fin 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      let cc := slowRemainderTimeCoefficient Ks
        (fun t X z => F.flux p c v u γ d I (s * t) X (z + φ) k) a b X0 (e / E)
      (∀ z, Measurable (fun t => cc t z)) ∧
        (∀ t, ContDiff ℝ (K v : ℕ) (cc t)) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j ≤ K v, ∀ z,
          (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (cc t) z‖ ≤
            CR * molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I (Ks + 1) /
                derivativeReserveFactor (ρ / e) (K v) (d - 2) * ζ ^ (Ks + 1) * polynomialMomentRoot ϖ z ^ (Ks + 1)) := by
  obtain ⟨CR, hCR, hRemainder⟩ := slowRemainder_time_coefficient_budget Ks Kmax
  refine ⟨CR, hCR, ?_⟩
  intro ι h _ _ D P Ctx F π hπ K hK dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u γ hγ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hδ X0 φ k hwindow
  let f := fun t X z => F.flux p c v u γ d I (s * t) X (z + φ) k
  have hm (X z : Vec 2) : Measurable (fun t => f t X z) :=
    ((measurable_pi_iff.mp (hmeas p c v u γ d I X (z + φ))) k).comp
      ((measurable_const (a := s)).mul measurable_id)
  have hf (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ContDiff ℝ (K v + (Ks + 1) : ℕ) (Function.uncurry (f t)) := by
    have h0 := molecular_joint_contDiff F dom E hE.ne' (fun v => K v + J)
      henv.1 p c (s * t) (hwindow t ht) v u γ d I
    have h1 : ContDiff ℝ (K v + (Ks + 1) : ℕ)
        (Function.uncurry (F.flux p c v u γ d I (s * t))) :=
      h0.of_le (by exact_mod_cast Nat.add_le_add_left hKs (K v))
    exact (ContinuousLinearMap.proj k).contDiff.comp
      (h1.comp (contDiff_fst.prodMk (contDiff_snd.add (contDiff_const (c := φ)))))
  let R := derivativeReserveFactor (ρ / e) (K v) (d - 2)
  let B := molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I (Ks + 1)
  have hR : 0 < R := by dsimp [R, derivativeReserveFactor]; positivity
  have hB : 0 ≤ B := by
    unfold B molecularTaylorPrefixPrice
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hE.le _))
      (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _)
  have hjet : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r j : ℕ, r + j ≤ K v → ∀ X z,
      (ρ / e) ^ (r + j) * |e / E| ^ r *
        ‖iteratedFDeriv ℝ (Ks + 1 + r) (fun X' => iteratedFDeriv ℝ j (f t X') z) X‖ ≤ B / R := by
    have hb := familyMolecular_ae_scalar_mixed_budget F π hπ K Kmax hK dom ν e E ρ
      hν he hE hρ C J b₀ henv v u γ hγ d hd I (Ks + 1) hKs p c
    have hb' := ae_restrict_of_ae (s := Set.Icc a b) (ae_real_time_dilation s hs _ hb)
    filter_upwards [hb', ae_restrict_mem measurableSet_Icc] with t ht htI
    intro r j hrj X z
    exact ht (hwindow t htI) φ k r j hrj X z
  have hh := hRemainder (K v) (hK v) f a b X0 ϖ (ρ / e) (e / E) ζ (B / R)
    hm hf hϖ (div_pos hρ he) hscale hζ (div_nonneg hB hR.le) hδ hjet
  refine ⟨hh.1, hh.2.1, ?_⟩
  filter_upwards [hh.2.2] with t ht
  intro j hj z
  simpa only [B, R, mul_div_assoc] using ht j hj z

/-! Literal native product readouts recover the actual source flux value. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem productReadout_planeValue_ae {K : ℕ}
    (U : PlaneHk Set.univ K E) (V : PlaneHk Set.univ K F) (C : Vec 2 → E →L[ℝ] F)
    (hr : ∀ a, Weighted.planeJetReadoutOperator K a V =ᵐ[volume]
      multiplicationRawJet C U.toFunction.jet a) :
    planeValue V =ᵐ[volume] (fun x => C x (planeValue U x)) := by
  have hh := (planeJetLpReadout_ae (Nat.zero_le K) V (fun i : Fin 0 => Fin.elim0 i)).symm.trans
    (hr (valueIndex2 K))
  filter_upwards [hh] with x hx
  change V.toFunction.jet (valueIndex2 K) x =
    multiplicationRawJet C U.toFunction.jet (valueIndex2 K) x at hx
  change V.toFunction.jet (valueIndex2 K) x = C x (U.toFunction.jet (valueIndex2 K) x)
  rwa [multiplicationRawJet_value] at hx

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
theorem derivativeSourceOperator_planeValue {K L r : ℕ} (hKL : K + r ≤ L + 1)
    (I : DerivativeWord2 r) (U : PlaneHk Set.univ (L + 1) E) :
    planeValue (Weighted.derivativeSourceOperator hKL I U) = planeJetOrder U r I := by
  change planeJetOrder (Weighted.derivativeSourceOperator hKL I U) 0 (fun i => Fin.elim0 i) = _
  rw [derivativeSourceOperator_word_readout hKL I U 0 (Nat.zero_le K)]
  simp only [Nat.add_zero, Fin.append_elim0]
  congr 1
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! On the genuine shear sector the cell generator has only bounded normalized drift coupling. -/

theorem cellTransverseH1Projection_reduced_generator
    (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (e : Fin 2) (hs : ∀ t x, v t x e.rev = 0)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellGeneratorForm ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
      hG V hv.1 hb t (cellTransverseH1Projection e u) z =
    cellDiffusionForm ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
      hG t (cellTransverseH1Projection e u) z -
      inner ℝ (cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t
        (torusHkValueCLM (cellTransverseH1Projection e u)))) (torusHkValueCLM z) +
      inner ℝ (cellScalarCLM (κ t) (torusHkValueCLM (cellTransverseH1Projection e u)))
        (torusHkValueCLM z) := by
  let C : CellCoefficients := ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
  let p := cellTransverseH1Projection e u
  have hd : (∑ j : Fin 2, inner ℝ
      (cellDriftEntryCLM C V hv.1 hb t j (cellDerivativeCLM j p)) (torusHkValueCLM z)) = 0 :=
    cellTransverseH1Projection_drift_zero v V hv.1 hb e hs t u z
  have hsft : (∑ j : Fin 2, inner ℝ
      (cellDriftEntryCLM C V hv.1 hb t j (cellShiftedDerivativeCLM C.θ j p))
        (torusHkValueCLM z)) =
      inner ℝ (cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t
        (torusHkValueCLM p))) (torusHkValueCLM z) := by
    simp only [cellShiftedDerivativeCLM, add_apply, ContinuousLinearMap.comp_apply,
      map_add, inner_add_left]
    rw [Finset.sum_add_distrib, hd, zero_add, ← sum_inner]
    exact congrArg (fun q : ComplexCellL2 => inner ℝ q (torusHkValueCLM z))
      (cellScaledDriftMultiplier_sum η Cw hCw hv hw C rfl V hb ξ t (torusHkValueCLM p))
  simp only [cellGeneratorForm, add_apply, sub_apply, sum_apply, pullbackInnerCLM_apply,
    ContinuousLinearMap.comp_apply]
  rw [hsft]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev Set AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Every actual stored source word satisfies the clipped weighted scalar estimate with its true residuals. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem storedWords_clipped_compact_lower_integral_bound {K : ℕ}
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (Mv : ℝ) (hMv : 0 ≤ Mv) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ Mv)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (ha : t₀ ≤ a) (hb : b ≤ t₀ + S)
    (U H : ℝ → PlaneHk Set.univ K E)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (Q : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hcurve : ∀ α : JetIndex2 K, PlaneWeakHilbertCurve a b
      (fun t => planeJetReadoutOperator K α (U t))
      (fun t => planeWordH1SliceOperator K α (W t))
      (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
        (planeJetFluxOperator K α (Q t))))
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (hdχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ η)
    (B : ℝ) (hB : 0 < B) (ρ : ℝ) :
    let q := fun t x => clipWeight B (C.W m t x)
    let T := planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) Mv hvb
    let D := planeIntervalDiffusion a b hab G
      (fun t ht k j => (hG t ht k j).continuous) g hg4 hGnear hGs
    let u := fun α t => planeJetReadoutOperator K α (U t)
    let slice := fun α t => planeWordH1SliceOperator K α (W t)
    let L := fun α t => planeJetFluxOperator K α (Q t) - D t (planeH1GradientOperator (slice α t))
    let R := fun α t => planeJetReadoutOperator K α (H t) + T t (planeH1GradientOperator (slice α t))
    let energy := fun t => ∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, χ x ^ 2 * q t x * ‖u α t x‖ ^ 2)
    let dissipation := fun t => ∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, χ x ^ 2 * q t x * ‖(WithLp.toLp 2
        (fun k => planeH1GradientOperator (slice α t) k x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)
    let force := fun t => 8 * (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, q t x * ‖(WithLp.toLp 2 (fun k => L α t k x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) +
      (4096 * η ^ 2 + 16 * Mv * η) * (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
        (∫ x, q t x * ‖u α t x‖ ^ 2)) +
      2 * (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
        (∫ x, χ x ^ 2 * q t x * (‖R α t x‖ * ‖u α t x‖)))
    ∀ t ∈ Icc a b,
      ENNReal.ofReal (energy t + ∫ s in a..t, dissipation s) ≤
        (ENNReal.ofReal (energy a) + ∫⁻ s in Icc a b, ENNReal.ofReal (force s)) *
          ENNReal.ofReal (Real.exp (18 * C.lam m * (t - a))) := by
  dsimp only
  obtain ⟨P, htime, hgrowth⟩ := storedWords_clipped_compact_energy_growth a b hab
    v hv hdiv Mv hMv hvb G hG g hg4 hGnear hGs t₀ S ϖ zc N m Cw C hm ha hb
    U H W Q hcurve χ hχ hsχ hχ0 hχ1 η hη hdχ B hB ρ
  have hq0 t x : 0 ≤ clipWeight B (C.W m t x) := (clipWeight_pos hB (C.pos m hm t x)).le
  have hdi (α : JetIndex2 K) := chartWeights_clipped_cutoff_finite_time_integrable
    C m hm B hB χ hχ.continuous hχ0 hχ1 (volume.restrict (Icc a b))
    (fun t => planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))
    ((planeH1GradientOperator (E := E)).comp_memLp' (hcurve α).state)
  have hd := integrable_finsetSum (Finset.univ : Finset (JetIndex2 K))
    (fun α _ => (hdi α).const_mul (factorialWeight ρ α.1.val))
  apply scalar_energy_lower_integral_gronwall hab htime (18 * C.lam m)
    (mul_nonneg (by norm_num) (C.lam_bound m hm).1) _ _
    (intervalIntegrable_of_integrable_Icc hab hd)
  · intro t
    apply add_nonneg
    · apply add_nonneg
      · apply mul_nonneg (by norm_num)
        exact Finset.sum_nonneg (fun α _ => mul_nonneg (factorialWeight_nonneg ρ _)
          (integral_nonneg (fun x => mul_nonneg (hq0 t x) (sq_nonneg _))))
      · apply mul_nonneg (by positivity)
        exact Finset.sum_nonneg (fun α _ => mul_nonneg (factorialWeight_nonneg ρ _)
          (integral_nonneg (fun x => mul_nonneg (hq0 t x) (sq_nonneg _))))
    · apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg (fun α _ => mul_nonneg (factorialWeight_nonneg ρ _)
        (integral_nonneg (fun x => mul_nonneg (mul_nonneg (sq_nonneg _) (hq0 t x))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)))))
  · exact Finset.sum_nonneg (fun α _ => mul_nonneg (factorialWeight_nonneg ρ _)
      (integral_nonneg (fun x => mul_nonneg (mul_nonneg (sq_nonneg _) (hq0 a x)) (sq_nonneg _))))
  · exact Filter.Eventually.of_forall (fun t => Finset.sum_nonneg (fun α _ =>
      mul_nonneg (factorialWeight_nonneg ρ _) (integral_nonneg (fun x =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (hq0 t x)) (sq_nonneg _)))))
  · simpa only [add_assoc] using hgrowth

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CycleWords

/-! The actual bounded-weight energy estimate on the whole plane, after spatial cutoff removal. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_planeWeak_clipped_value_energy_gronwall
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (M : ℝ) (hM : 0 ≤ M) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (hCell : IsCellMetric G)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (ha : t₀ ≤ a) (hb : b ≤ t₀ + S)
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (slice : ℝ → PlaneHk Set.univ 1 E) (F : ℝ → PlaneFluxL2 E)
    (H : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (h : PlaneWeakHilbertCurve a b u slice
      (fun t => planeValueForcedDual
        (planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) M hvb t)
        (cellMetricIntervalDiffusion a b hab G (fun t ht k j => (hG t ht k j).continuous)
          hCell t) (slice t) (F t) (H t)))
    (B : ℝ) (hB : 0 < B) (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hH : MemLp H 2 (volume.restrict (Icc a b))) :
    ∀ t ∈ Icc a b,
      (∫ x, clipWeight B (W.W m t x) * ‖u t x‖ ^ 2) +
      (∫ s in a..t, ∫ x, (1 / 2) * clipWeight B (W.W m s x) *
        ‖(WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) (slice s) i x) :
          PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ≤
      ((∫ x, clipWeight B (W.W m a x) * ‖u a x‖ ^ 2) +
        8 * (∫ s in a..b, ∫ x, clipWeight B (W.W m s x) *
          ‖(WithLp.toLp 2 (fun i => F s i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
        2 * (∫ s in a..b, ∫ x, clipWeight B (W.W m s x) * (‖H s x‖ * ‖u s x‖))) *
        Real.exp (18 * W.lam m * (t - a)) := by
  obtain ⟨χ, Cχ, hCχ, hχ, hχrange, hχlim, hdχ⟩ :=
    AVRegularity.CoupledEnergyPlane.Transport.exists_expanding_smooth_cutoffs
  let q := fun t x => clipWeight B (W.W m t x)
  let force := fun t => ∫ x, q t x *
    ‖(WithLp.toLp 2 (fun i => F t i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  let val := fun t => ∫ x, q t x * (‖H t x‖ * ‖u t x‖)
  let valc := fun n t => ∫ x, (χ n x ^ 2 * q t x) * (‖H t x‖ * ‖u t x‖)
  let mass := fun t => ∫ x, q t x * ‖u t x‖ ^ 2
  let η := fun n : ℕ => ((n : ℝ) + 1)⁻¹ * Cχ
  let c := fun n => 4096 * η n ^ 2 + 16 * M * η n
  have hu : MemLp u 2 (volume.restrict (Icc a b)) :=
    (memLp_congr_ae h.agrees).2 ((planeHkValueOperator (E := E) 1).comp_memLp' h.state)
  have hfint := intervalIntegrable_of_integrable_Icc hab
    (chartWeights_clipped_finite_time_integrable W m hm B hB _ F hF)
  have hmint := intervalIntegrable_of_integrable_Icc hab
    (chartWeights_clipped_scalar_time_integrable W m hm B hB _ u hu)
  obtain ⟨hqc, hqm, hqb⟩ := chartWeights_clipped_time_coefficient W m hm B hB
  have hvint := intervalIntegrable_of_integrable_Icc hab
    (weighted_spatial_value_product_time_integrable q hqc hqm hB.le hqb H u hH hu)
  have hH' : MemLp H 2 (volume.restrict (Ioc a b)) :=
    hH.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hu' : MemLp u 2 (volume.restrict (Ioc a b)) :=
    hu.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hvlim := value_product_spatial_cutoff_time_tendsto χ (fun n => (hχ n).1.continuous)
    hχrange hχlim q hqc hqm hB.le hqb (fun s x => (clipWeight_pos hB (W.pos m hm s x)).le)
    (volume.restrict (Ioc a b)) H u hH' hu'
  have hvlim' : Tendsto (fun n => ∫ s in a..b, valc n s) atTop
      (𝓝 (∫ s in a..b, val s)) := by
    simpa only [intervalIntegral.integral_of_le hab] using hvlim
  have hvnc n := intervalIntegrable_of_integrable_Icc hab
    (chartWeights_clipped_cutoff_value_product_integrable W m hm B hB (χ n)
      (hχ n).1.continuous (fun x => (hχrange n x).1) (fun x => (hχrange n x).2) _ H u hH hu)
  have hη n : 0 ≤ η n := by dsimp only [η]; positivity
  have hχ2 n : ContDiff ℝ 2 (χ n) := (hχ n).1.of_le (by simp)
  have hgr n := cellMetric_planeWeak_clipped_compact_value_gronwall a b hab v hv hdiv M hM hvb
    G hG hCell hGs t₀ S ϖ zc N m Cw W hm ha hb u slice F H h (χ n) (hχ2 n) (hχ n).2
    (fun x => (hχrange n x).1) (fun x => (hχrange n x).2) (η n) (hη n) (hdχ n) B hB hF hH
  have hqint t : Integrable (fun x => q t x * ‖u t x‖ ^ 2) volume :=
    bounded_scalar_Lp_normSq_integrable (u t) (q t)
      (chartWeights_clipped_spatial_regularity W m hm t B hB).1.continuous.aestronglyMeasurable
      (Eventually.of_forall (fun x => by
        rw [Real.norm_of_nonneg (clipWeight_pos hB (W.pos m hm t x)).le]
        exact clipWeight_le_bound hB (W.pos m hm t x)))
  have henergy t : Tendsto (fun n => ∫ x, χ n x ^ 2 * q t x * ‖u t x‖ ^ 2) atTop
      (𝓝 (mass t)) := by
    have hh := integral_spatial_cutoff_tendsto χ (fun x => q t x * ‖u t x‖ ^ 2)
      (fun n => (hχ n).1.continuous.aestronglyMeasurable) hχrange hχlim (hqint t)
    convert hh using 1
    funext n
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by ring)
  have hclim : Tendsto c atTop (𝓝 0) := cutoff_error_rate_tendsto_zero
  intro t ht
  have hsub : Ioc a t ⊆ Icc a b := Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2)
  have hdu : MemLp (fun s => planeH1GradientOperator (E := E) (slice s)) 2
      (volume.restrict (Ioc a t)) :=
    ((planeH1GradientOperator (E := E)).comp_memLp' h.state).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hdlim := finite_energy_spatial_cutoff_time_tendsto χ (fun n => (hχ n).1.continuous)
    hχrange hχlim q hqc hqm hB.le hqb (fun s x => (clipWeight_pos hB (W.pos m hm s x)).le)
    (volume.restrict (Ioc a t)) (fun s => planeH1GradientOperator (E := E) (slice s)) hdu
  have hdlim' : Tendsto (fun n => ∫ s in a..t, ∫ x, χ n x ^ 2 * q s x *
      ‖(WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) (slice s) i x) :
        PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) atTop
      (𝓝 (∫ s in a..t, ∫ x, q s x * ‖(WithLp.toLp 2
        (fun i => planeH1GradientOperator (E := E) (slice s) i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) := by
    simpa only [intervalIntegral.integral_of_le ht.1] using hdlim
  have hdhalf : Tendsto (fun n => ∫ s in a..t, ∫ x,
      (1 / 2) * χ n x ^ 2 * q s x *
        ‖(WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) (slice s) i x) :
          PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) atTop
      (𝓝 (∫ s in a..t, ∫ x, (1 / 2) * q s x *
        ‖(WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) (slice s) i x) :
          PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) := by
    simpa only [mul_assoc, integral_const_mul, intervalIntegral.integral_const_mul]
      using hdlim'.const_mul (1 / 2 : ℝ)
  have hl := (henergy t).add hdhalf
  have hsource := ((tendsto_const_nhds :
    Tendsto (fun _ : ℕ => 8 * (∫ s in a..b, force s)) atTop
      (𝓝 (8 * (∫ s in a..b, force s)))).add
    (hclim.mul_const (∫ s in a..b, mass s))).add (hvlim'.const_mul 2)
  have hr := ((henergy a).add hsource).mul_const
    (Real.exp (18 * W.lam m * (t - a)))
  have hbnd n := hgr n t ht
  have hrhs n : (∫ s in a..b, 8 * force s + c n * mass s + 2 * valc n s) =
      8 * (∫ s in a..b, force s) + c n * (∫ s in a..b, mass s) +
        2 * (∫ s in a..b, valc n s) := by
    rw [intervalIntegral.integral_add ((hfint.const_mul 8).add (hmint.const_mul (c n))) ((hvnc n).const_mul 2),
      intervalIntegral.integral_add (hfint.const_mul 8) (hmint.const_mul (c n)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  apply le_of_tendsto_of_tendsto hl (by simpa only [zero_mul, add_zero, add_assoc] using hr)
  exact Eventually.of_forall (fun n => by
    have hh := hbnd n
    change _ ≤ ((_ + ∫ s in a..b, 8 * force s + c n * mass s + 2 * valc n s) * _) at hh
    rw [hrhs] at hh
    simpa only [add_assoc] using hh)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The reduced shear generator has uniform bounds in the normalized drift amplitude. -/

theorem cellFibreDriftCouplingCLM_apply_norm_le (η Cw : ℝ) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : ComplexCellL2) :
    ‖cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t u‖ ≤ Cw * fibreNorm ξ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have h := cellCoefficientCLM_ae (fibreDriftCoupling η v ξ t)
    (cellBlochDriftCoupling_aestronglyMeasurable η hv ξ t) (Cw * fibreNorm ξ)
    (mul_nonneg hCw (fibreNorm_nonneg ξ)) (fibreDriftCoupling_norm_le η Cw v hw ξ t) u
  change (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t u : Vec 2 → ℂ) =ᵐ[
    volume.restrict AVenhance.unitCube] fun x => fibreDriftCoupling η v ξ t x * u x at h
  filter_upwards [h] with x hx
  rw [hx]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    (fibreDriftCoupling_norm_le η Cw v hw ξ t x) (norm_nonneg _))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleWords

/-! Empty edges allow the literal admissible flux to be summed over all orders. -/

variable {ι σ : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

def letterFullOrderFlux (L : CycleLetter ι h D) (κ : σ → ℕ) (b : ι → σ)
    (v : ι) (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (W : ∀ u, PlaneHk Set.univ (κ (b u) + 1) (h u)) (t : ℝ) (z : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => h v) :=
  ∑ u, ∑ o ∈ Finset.Icc 2 D,
    if ho : o ∈ Finset.Icc 2 D then
      slowEvalCoefficient (fun f z => taylorSlow lo L.slow f X₀ (δ • z))
        (L.edge v u ⟨o, ho⟩) t z
        (WithLp.toLp 2 fun w => planeJetOrder (W u) (o - 1) w z)
    else 0

theorem letterAdmissibleFlux_eq_fullOrderFlux (L : CycleLetter ι h D)
    (κ : σ → ℕ) (a : σ) (b : ι → σ) (v : ι)
    (hc : ∀ u (o : Finset.Icc 2 D), L.edge v u o ≠ [] → κ a + o.1 ≤ κ (b u) + 2)
    (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (W : ∀ u, PlaneHk Set.univ (κ (b u) + 1) (h u)) (t : ℝ) (z : Vec 2) :
    Weighted.letterAdmissibleFlux L κ a b v lo X₀ δ W t z =
      letterFullOrderFlux L κ b v lo X₀ δ W t z := by
  classical
  unfold Weighted.letterAdmissibleFlux letterFullOrderFlux
  apply Finset.sum_congr rfl
  intro u _
  let f (o : ℕ) : PiLp 2 (fun _ : Fin 2 => h v) :=
    if ho : o ∈ Finset.Icc 2 D then
      slowEvalCoefficient (fun f z => taylorSlow lo L.slow f X₀ (δ • z))
        (L.edge v u ⟨o, ho⟩) t z
        (WithLp.toLp 2 fun w => planeJetOrder (W u) (o - 1) w z)
    else 0
  have he : (∑ o : admissibleOrders κ D a (b u),
      slowEvalCoefficient (fun f z => taylorSlow lo L.slow f X₀ (δ • z))
        (L.edge v u (Weighted.admissibleLetterOrder κ D a (b u) o)) t z
        (WithLp.toLp 2 fun w => (W u).toFunction.jet
          (Weighted.admissibleLetterSourceIndex κ D a (b u) o w) z)) =
      ∑ o : admissibleOrders κ D a (b u), f o := by
    apply Finset.sum_congr rfl
    intro o _
    have ho := Finset.mem_filter.mp o.2
    have hr : o.1 - 1 ≤ κ (b u) + 1 :=
      (Nat.le_add_left _ _).trans (Weighted.admissible_letter_source_reserve κ D a (b u) o)
    simp only [f, dite_eq_left ho.1, planeJetOrder, dite_eq_left hr,
      Weighted.admissibleLetterOrder, Weighted.admissibleLetterSourceIndex,
      Weighted.sourceWordIndex]
    rfl
  rw [he, Finset.sum_coe_sort]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro o ho hn
  have hz : L.edge v u ⟨o, ho⟩ = [] := by
    by_contra hne
    exact hn (Finset.mem_filter.mpr ⟨ho, hc u ⟨o, ho⟩ hne⟩)
  simp only [f, dite_eq_left ho, hz, slowEvalCoefficient, List.map_nil, List.sum_nil,
    zero_apply]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Smooth periodic functions inherit all Sobolev gap bounds from small L2 and uniform polynomial high jets. -/

def smoothPeriodicGapPrice (C : ℕ → ℝ) (B : ℝ) (j : ℕ) : ℝ :=
  nativeSobolevWordPrice j * adjacentGapPrice
    (fun k => (Fintype.card (JetIndex2 k) : ℝ) * C k)
    ((Fintype.card (JetIndex2 0) : ℝ) * B) j

theorem smoothPeriodic_polynomial_gap_hierarchy (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : AVenhance.IsZ2Periodic f)
    (C : ℕ → ℝ) (B p x γ D : ℝ) (hC : ∀ j, 0 ≤ C j)
    (hB : 0 ≤ B) (hp : 0 ≤ p) (hx : 0 ≤ x)
    (hhigh : ∀ j, cellSobolevNorm j f ≤ ENNReal.ofReal (C j * p ^ (2 * j) * x))
    (hzero : cellL2Norm f ≤ ENNReal.ofReal (B * x * Real.exp (-γ * D))) :
    ∀ j, cellSobolevNorm j f ≤ ENNReal.ofReal
      (smoothPeriodicGapPrice C B j * p ^ (2 * j) * x *
        Real.exp (-(γ / (2 : ℝ) ^ j) * D)) := by
  let U : ∀ j, TorusHk j ℂ := fun j => finiteSmoothPeriodicHk j f (hf.of_le (by simp)) hper
  let CN : ℕ → ℝ := fun j => (Fintype.card (JetIndex2 j) : ℝ) * C j
  let BN : ℝ := (Fintype.card (JetIndex2 0) : ℝ) * B
  have hcoherent (j : ℕ) : torusHkValueCLM (U j) = torusHkValueCLM (U 0) := by
    apply Lp.ext
    exact (finiteSmoothPeriodicHk_value_ae j f _ hper).trans
      (finiteSmoothPeriodicHk_value_ae 0 f _ hper).symm
  have hCN (j : ℕ) : 0 ≤ CN j := mul_nonneg (Nat.cast_nonneg _) (hC j)
  have hBN : 0 ≤ BN := mul_nonneg (Nat.cast_nonneg _) hB
  have hnative (j : ℕ) : ‖U j‖ ≤ CN j * p ^ (2 * j) * x := by
    have he := finiteSmoothPeriodicHk_norm_le_of_budget j f (hf.of_le (by simp)) hper
      (C j * p ^ (2 * j) * x)
      (mul_nonneg (mul_nonneg (hC j) (pow_nonneg hp _)) hx) (hhigh j)
    convert he using 1
    dsimp only [CN]
    ring
  have hnativezero : ‖U 0‖ ≤ BN * x * Real.exp (-γ * D) := by
    have hz : cellSobolevNorm 0 f ≤ ENNReal.ofReal (B * x * Real.exp (-γ * D)) := by
      rw [cellSobolevNorm_zero_eq f hf.continuous]
      exact hzero
    have he := finiteSmoothPeriodicHk_norm_le_of_budget 0 f (hf.of_le (by simp)) hper
      (B * x * Real.exp (-γ * D)) (by positivity) hz
    convert he using 1
    dsimp only [BN]
    ring
  have hgaps := torusHigher_polynomial_gap_hierarchy U hcoherent CN BN p x γ D
    hCN hBN hp hx hnative hnativezero
  intro j
  have hread := torusHigher_smooth_cellSobolevNorm_le (U j) f (hf.of_le (by simp))
    (finiteSmoothPeriodicHk_value_ae j f _ hper)
  have hn : ‖U j‖ₑ ≤ ENNReal.ofReal (adjacentGapPrice CN BN j * p ^ (2 * j) * x *
      Real.exp (-(γ / (2 : ℝ) ^ j) * D)) := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hgaps j)
  have he := hread.trans (mul_le_mul' le_rfl hn)
  rw [nativeSobolevWordPrice_mul_ofReal] at he
  convert he using 1
  congr 1
  dsimp only [smoothPeriodicGapPrice, CN, BN]
  ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleWords

/-! The energy class already supplies the zero-moment budgets for actual bounded source fluxes. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem integrated_zero_moment_factorial_ne_top {K : ℕ}
    (ρ ϖ : ℝ) (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ) :
    (∫⁻ t, weightedFactorialNormSq 0 ϖ 0 ρ K (U t) ∂μ) ≠ ⊤ := by
  have he (a : JetIndex2 K) :
      (∫⁻ t, Weighted.chartScalarEnergy
        (fun x => (Weighted.planeMomentSquareRoot 0 ϖ 0 x) ^ 2)
        (Weighted.planeJetReadoutOperator K a (U t)) ∂μ) ≠ ⊤ := by
    let R := fun t => Weighted.planeJetReadoutOperator K a (U t)
    have hR : MemLp R 2 μ := (Weighted.planeJetReadoutOperator (E := E) K a).comp_memLp' hU
    have hh := unweightedSpatialLpTimeEnergy_ne_top μ R hR
    have hq : (fun x : Vec 2 => (Weighted.planeMomentSquareRoot 0 ϖ 0 x) ^ 2) =
        (fun _ : Vec 2 => (1 : ℝ)) := by
      funext x
      rw [Weighted.planeMomentSquareRoot_sq]
      simp only [Weighted.planeMomentPolynomial, pow_zero]
    rw [hq]
    exact hh
  exact Weighted.integrated_weightedFactorialNormSq_ne_top (E := E) (K := K)
    0 ϖ 0 ρ μ U hU he

theorem integrated_zero_moment_gradient_ne_top {K : ℕ}
    (ρ ϖ : ℝ) (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ (K + 1) E) (hU : MemLp U 2 μ) :
    (∫⁻ t, weightedGradFactorialNormSq 0 ϖ 0 ρ K (U t) ∂μ) ≠ ⊤ := by
  let G := fun t => planeGradientTensor (U t)
  have hG : MemLp G 2 μ := by
    simpa only [Function.comp_def, planeGradientTensorOperator_apply, G] using
      (planeGradientTensorOperator (E := E) K).comp_memLp' hU
  have hh := integrated_zero_moment_factorial_ne_top ρ ϖ μ G hG
  simpa only [G, planeGradientTensor_weightedFactorialNormSq] using hh

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open MeasureTheory UnitAddTorus AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The transverse projection is symmetric for the literal bilinear pairing. -/

local instance cellTransverseBilinearProjectionMeasureSpace : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

theorem cellFiberConj_fourier_mode (n : Fin 2 → ℤ) :
    cellFiberCLM Complex.conjCLE.toContinuousLinearMap (scalarTorusToCell (mFourierLp 2 n)) =
      scalarTorusToCell (mFourierLp 2 (-n)) := by
  apply Lp.ext
  have hn := (cellComplexFourierMode_memLp n).coeFn_toLp
  have hm := (cellComplexFourierMode_memLp (-n)).coeFn_toLp
  rw [← scalarTorusToCell_mode] at hn hm
  filter_upwards [cellFiberConj_ae (scalarTorusToCell (mFourierLp 2 n)), hn, hm] with x hc hn' hm'
  rw [hc, hn', hm', cellComplexFourierMode_eq, cellComplexFourierMode_eq, mFourier_neg]
  rfl

theorem cellTransverseProjection_fourier_mode (e : Fin 2) (n : Fin 2 → ℤ) :
    cellTransverseProjection e (scalarTorusToCell (mFourierLp 2 n)) =
      if n e = 0 then scalarTorusToCell (mFourierLp 2 n) else 0 := by
  rw [cellTransverseProjection_torus]
  unfold scalarTorusTransverseProjection
  rw [← coe_mFourierBasis]
  change scalarTorusToCell
    (hilbertBasisSectorProjection (mFourierBasis (d := Fin 2)) {k | k e = 0}
      (mFourierBasis (d := Fin 2) n)) = _
  rw [hilbertBasisSectorProjection_basis]
  simp only [Set.mem_ofPred_eq]
  split_ifs <;> simp only [map_zero]

theorem cellTransverseProjection_conjugate (e : Fin 2) (u : ComplexCellL2) :
    cellTransverseProjection e (cellFiberCLM Complex.conjCLE.toContinuousLinearMap u) =
      cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellTransverseProjection e u) := by
  let J := cellFiberCLM Complex.conjCLE.toContinuousLinearMap
  have hs := scalarTorusToCell_fourier_series (scalarCellToTorus u)
  rw [scalarTorusToCell_scalarCellToTorus] at hs
  have hl := hs.mapL ((cellTransverseProjection e).comp J)
  have hr := hs.mapL (J.comp (cellTransverseProjection e))
  apply hl.unique
  apply hr.congr_fun
  intro n
  simp only [ContinuousLinearMap.comp_apply, J, cellFiberConj_smul,
    cellTransverseProjection_complex_smul, cellFiberConj_fourier_mode,
    cellTransverseProjection_fourier_mode, Pi.neg_apply, neg_eq_zero]
  split_ifs <;> simp only [smul_zero, map_zero, cellFiberConj_fourier_mode]

end AVRegularity.CycleWords
end
end
