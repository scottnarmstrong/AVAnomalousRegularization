-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.ConstituentPhysicalOrderSupport
import AVRegularity.CycleJoint.PlaneWindowScalarDiffusion
import AVRegularity.CycleJoint.CoefficientSeminormAddition
import AVRegularity.CoupledEnergy.CouplingBounds
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow
public import AVRegularity.Definitions.CycleJoint.IsPointwiseMolecularEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseMolecularEnvelope
public import AVRegularity.CycleWords.JointDiagonalChainRule
public import AVRegularity.Statements.Intermediate.Families.IsSampledEnvelope
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

section
section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! The finite mixed response has the exact affine forcing with its terminal metric row retained. -/

variable {ι : Type*} {h V Q : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  [∀ i, AddCommGroup (Q i)] [∀ i, Module ℝ (Q i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem finiteNativeResponse_affine_forcing_identity
    (F : ChartedFamily ι h D P Ctx)
    (R : ∀ i, Q i →ₗ[ℝ] V i)
    (Lmetric Lsource : ∀ i, (∀ j, V j) →ₗ[ℝ] Q i)
    (hM : HasSourceDegreeOn F 0 (nativeComponentResponseOperator R Lmetric))
    (hS : HasSourceDegreeOn F 1 (nativeComponentResponseOperator R Lsource))
    (H J : ℕ) (hdepth : F.HasDepthAtMost H) (Z : ∀ i, V i) :
    let M := nativeComponentResponseOperator R Lmetric
    let S := nativeComponentResponseOperator R Lsource
    let U := finiteResponse 1 M S Z
    let W := ∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n
    let T := ∑ n ∈ Finset.range (H + 1), U J n
    W = Z + (fun i => R i (Lmetric i W + Lsource i W - Lmetric i T)) := by
  let M := nativeComponentResponseOperator R Lmetric
  let S := nativeComponentResponseOperator R Lsource
  let U := finiteResponse 1 M S Z
  let W := ∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n
  let T := ∑ n ∈ Finset.range (H + 1), U J n
  have he := finiteNativeResponse_fixedPoint_source_residual F M S hM hS H J hdepth Z
  change W - M W - S W = Z - M T at he
  change W = Z + (fun i => R i (Lmetric i W + Lsource i W - Lmetric i T))
  funext i
  have hi := congrFun he i
  change W i - R i (Lmetric i W) - R i (Lsource i W) =
    Z i - R i (Lmetric i T) at hi
  simp only [Pi.add_apply, map_sub, map_add]
  calc
    W i = (W i - R i (Lmetric i W) - R i (Lsource i W)) +
      R i (Lmetric i W) + R i (Lsource i W) := by abel
    _ = _ := by rw [hi]; abel

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Native and physical order indices match the molecular lowering normalization exactly. -/

theorem native_order_price_normalization (ν ρ E : ℝ)
    (hν : 0 < ν) (hρ : 0 < ρ) (hE : 0 < E) (hρE : ρ ≤ E)
    (K dout din : ℕ) (hdout : 2 ≤ dout) (horder : dout ≤ din) (M : ℝ≥0∞) :
    E⁻¹ ^ (din - dout) * M.toReal * (ν * ρ ^ (dout - 2))⁻¹ *
      (((K + dout - 2).factorial : ℝ) / (K.factorial : ℝ)) ≤
        molecularRealPrice ν ρ K (din - 2) M := by
  have hi : dout - 2 + (din - dout) = din - 2 := by omega
  have ho : K + (dout - 2) = K + dout - 2 := by omega
  simpa only [hi, ho] using molecular_order_lowering_normalization ν ρ E hν hρ hE hρE
    K (dout - 2) (din - dout) M

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Positive sums over lowered physical orders spend only a finite order multiplicity. -/

theorem positive_native_order_budget (ν ρ E : ℝ)
    (hν : 0 < ν) (hρ : 0 < ρ) (hE : 0 < E) (hρE : ρ ≤ E)
    (K D Dγ : ℕ) (M : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ≥0∞) :
    (∑ dout ∈ Finset.Icc 2 D, ∑ din ∈ Finset.Icc dout Dγ,
      ∑ I : DerivativeWord2 (din - 1),
        E⁻¹ ^ (din - dout) * (M din I).toReal * (ν * ρ ^ (dout - 2))⁻¹ *
          (((K + dout - 2).factorial : ℝ) / (K.factorial : ℝ))) ≤
    D * (∑ din ∈ Finset.Icc 2 Dγ, ∑ I : DerivativeWord2 (din - 1),
      molecularRealPrice ν ρ K (din - 2) (M din I)) := by
  let B := ∑ din ∈ Finset.Icc 2 Dγ, ∑ I : DerivativeWord2 (din - 1),
    molecularRealPrice ν ρ K (din - 2) (M din I)
  have hn din I : 0 ≤ molecularRealPrice ν ρ K (din - 2) (M din I) :=
    molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _
  have hB : 0 ≤ B := Finset.sum_nonneg (fun din _ => Finset.sum_nonneg (fun I _ => hn din I))
  have hb dout (hd : dout ∈ Finset.Icc 2 D) :
      (∑ din ∈ Finset.Icc dout Dγ, ∑ I : DerivativeWord2 (din - 1),
        E⁻¹ ^ (din - dout) * (M din I).toReal * (ν * ρ ^ (dout - 2))⁻¹ *
          (((K + dout - 2).factorial : ℝ) / (K.factorial : ℝ))) ≤ B := by
    have hd2 := (Finset.mem_Icc.mp hd).1
    apply (Finset.sum_le_sum (fun din hdin => Finset.sum_le_sum (fun I _ =>
      native_order_price_normalization ν ρ E hν hρ hE hρE K dout din hd2
        (Finset.mem_Icc.mp hdin).1 (M din I)))).trans
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro din hdin
      have hh := Finset.mem_Icc.mp hdin
      exact Finset.mem_Icc.mpr ⟨hd2.trans hh.1, hh.2⟩
    · intro din _ _
      exact Finset.sum_nonneg (fun I _ => hn din I)
  apply (Finset.sum_le_sum hb).trans
  have hc : (Finset.Icc 2 D).card ≤ D := by simp only [Nat.card_Icc]; omega
  calc
    (∑ _dout ∈ Finset.Icc 2 D, B) = ((Finset.Icc 2 D).card : ℝ) * B := by simp
    _ ≤ D * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hB

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Each radius-scaled native derivative is bounded by the actual finite factorial norm. -/

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  {μ : Measure (Vec 2)} {K : ℕ}

theorem scaled_jet_norm_le_factorial {ρ : ℝ} (hρ : 0 ≤ ρ) (D : JetL2 μ K E)
    (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) :
    ρ ^ n * ‖D ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩‖ ≤
      (n.factorial : ℝ) * Real.sqrt (factorialNormSq ρ D) := by
  let j : Fin (K + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have hc : ‖D ⟨j, w⟩‖ ^ 2 ≤ derivativeNormSq D j := by
    unfold derivativeNormSq
    exact Finset.single_le_sum (fun v _ => sq_nonneg ‖D ⟨j, v⟩‖) (Finset.mem_univ w)
  have hl : factorialWeight ρ n * derivativeNormSq D j ≤ factorialNormSq ρ D := by
    exact Finset.single_le_sum (fun k _ => mul_nonneg (factorialWeight_nonneg ρ k.val)
      (derivativeNormSq_nonneg D k)) (Finset.mem_univ j)
  have hs := (mul_le_mul_of_nonneg_left hc (factorialWeight_nonneg ρ n)).trans hl
  have he : (factorialRootWeight ρ n * ‖D ⟨j, w⟩‖) ^ 2 =
      factorialWeight ρ n * ‖D ⟨j, w⟩‖ ^ 2 := by
    rw [mul_pow, factorialRootWeight_sq]
  rw [← he] at hs
  have hr : 0 ≤ factorialRootWeight ρ n :=
    div_nonneg (pow_nonneg hρ _) (Nat.cast_nonneg _)
  have hnorm := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hr (norm_nonneg _))] at hnorm
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  change (ρ ^ n / (n.factorial : ℝ)) * ‖D ⟨j, w⟩‖ ≤ _ at hnorm
  rw [div_mul_eq_mul_div] at hnorm
  simpa only [mul_comm] using (div_le_iff₀ hf).mp hnorm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! The construction's fixed smooth profile supplies a positive lattice patch partition. -/

def spatialPatchCutoff (ζ : ℝ → ℝ) (N : ℕ) (k : Fin 2 → ℤ) (x : Vec 2) : ℝ :=
  ζ (N * x 0 - k 0) * ζ (N * x 1 - k 1)

theorem spatialPatchCutoff_nonneg {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (k : Fin 2 → ℤ) (x : Vec 2) : 0 ≤ spatialPatchCutoff ζ N k x :=
  mul_nonneg (hζ.2.2.2.1 _).1 (hζ.2.2.2.1 _).1

theorem spatialPatchCutoff_le_one {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (k : Fin 2 → ℤ) (x : Vec 2) : spatialPatchCutoff ζ N k x ≤ 1 := by
  exact (mul_le_mul (hζ.2.2.2.1 _).2 (hζ.2.2.2.1 _).2
    (hζ.2.2.2.1 _).1 (by norm_num)).trans_eq (one_mul 1)

theorem spatialPatchCutoff_smooth {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (k : Fin 2 → ℤ) : ContDiff ℝ (⊤ : ℕ∞) (spatialPatchCutoff ζ N k) := by
  have hs := hζ.1
  unfold spatialPatchCutoff
  fun_prop

theorem spatialPatchCutoff_partition {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (x : Vec 2) : ∑' k : Fin 2 → ℤ, spatialPatchCutoff ζ N k x = 1 := by
  have hprofile (y : ℝ) : Summable (fun k : ℤ => ζ (y - k)) := by
    by_contra hn
    have hz := tsum_eq_zero_of_not_summable hn
    rw [hζ.2.2.2.2.1] at hz
    norm_num at hz
  have h0 := hprofile (N * x 0)
  have h1 := hprofile (N * x 1)
  have hs := summable_mul_of_summable_norm h0.norm h1.norm
  have he := (finTwoArrowEquiv ℤ).tsum_eq
    (fun p : ℤ × ℤ => ζ (N * x 0 - p.1) * ζ (N * x 1 - p.2))
  rw [show (∑' k : Fin 2 → ℤ, spatialPatchCutoff ζ N k x) =
      ∑' p : ℤ × ℤ, ζ (N * x 0 - p.1) * ζ (N * x 1 - p.2) from he,
    ← h0.tsum_mul_tsum h1 hs, hζ.2.2.2.2.1, hζ.2.2.2.2.1, one_mul]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Positive auxiliary masses absorb any finite strictly triangular coefficient system. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

variable (ν ρ : ℝ) (K : ι → ℕ) (D : ℕ) (a b : ℝ)
  (A : ∀ v u, (d : admissibleOrders K D v u) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h v))

omit [Fintype ι] in
theorem schurMatrix_eq_massConjugated (π : ι → ℝ) :
    schurMatrix ν ρ π K D a b A =
      massConjugatedMatrix π (schurMatrix ν ρ (fun _ => 1) K D a b A) := by
  funext v u
  simp only [schurMatrix, massConjugatedMatrix, div_self (one_ne_zero : (1 : ℝ) ≠ 0),
    Real.sqrt_one, one_mul]

omit [Fintype ι] in
theorem schurMatrix_entry_zero (v u : ι) (hz : ∀ d, A v u d = 0) (π : ι → ℝ) :
    schurMatrix ν ρ π K D a b A v u = 0 := by
  unfold schurMatrix
  have hs : ∀ d, coefficientSeminorm ρ (K v) a b (A v u d) = 0 := by
    intro d
    rw [hz d]
    exact coefficientSeminorm_zero_function ρ (K v) a b
  simp only [hs, ENNReal.toReal_zero, zero_div, zero_mul, Finset.sum_const_zero, mul_zero]

theorem exists_triangularCoefficientSchur (hν : 0 < ν) (hρ : 0 < ρ)
    (hA : ∀ v u d, coefficientSeminorm ρ (K v) a b (A v u d) ≠ ⊤)
    (r : ι → ℕ) (hr : ∀ v u, ¬ r u < r v → ∀ d, A v u d = 0) :
    ∃ π : ι → ℝ, (∀ v, 0 < π v) ∧ SchurCondition (schurMatrix ν ρ π K D a b A) := by
  have hn (v u : ι) : 0 ≤ schurMatrix ν ρ (fun _ => 1) K D a b A v u :=
    CoupledEnergy.schurMatrix_nonneg ν ρ hν hρ (fun _ => 1) (fun _ => zero_lt_one)
      K D a b A hA v u
  have hs (v u : ι) (hne : schurMatrix ν ρ (fun _ => 1) K D a b A v u ≠ 0) :
      r u < r v := by
    by_contra hh
    exact hne (schurMatrix_entry_zero ν ρ K D a b A v u (hr v u hh) (fun _ => 1))
  obtain ⟨π, hπ, hp⟩ := exists_rankMass_schurCondition r
    (schurMatrix ν ρ (fun _ => 1) K D a b A) hn hs
  exact ⟨π, hπ, by rw [schurMatrix_eq_massConjugated]; exact hp⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! The actual physical coefficient preserves the strict source-depth rank. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem physicalCoefficient_zero_of_no_edge (F : ChartedFamily ι h D P Ctx)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (v u : ι) (d : ℕ)
    (he : ¬ Nonempty (F.Γ v u)) :
    physicalCoefficient F ν e E actual v u d = 0 := by
  classical
  let : IsEmpty (F.Γ v u) := not_nonempty_iff.mp he
  funext t x
  simp [physicalCoefficient]

theorem physicalCoefficient_zero_of_rank (F : ChartedFamily ι h D P Ctx)
    (H : ℕ) (hdepth : F.HasDepthAtMost H) (ν e E : ℝ) (actual : ∀ p, Ctx p)
    (v u : ι) (d : ℕ) (hr : ¬ sourceDepthRank F H u < sourceDepthRank F H v) :
    physicalCoefficient F ν e E actual v u d = 0 := by
  apply physicalCoefficient_zero_of_no_edge
  intro he
  exact hr (sourceDepthRank_edge_lt hdepth he)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Each lattice cutoff is supported in a fixed-size patch around its exact mesh center. -/

def spatialPatchCentre (N : ℕ) (k : Fin 2 → ℤ) : Vec 2 := fun i => (k i : ℝ) / N

theorem spatialPatchCutoff_coordinate_support {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (k : Fin 2 → ℤ) (x : Vec 2) (hn : spatialPatchCutoff ζ N k x ≠ 0)
    (i : Fin 2) : |(N : ℝ) * x i - k i| < 2 / 3 := by
  have hh := mul_ne_zero_iff.mp hn
  have hz : ζ (N * x i - k i) ≠ 0 := by
    fin_cases i
    · exact hh.1
    · exact hh.2
  have hb := CycleReference.profile_ne_support_interval hζ hz
  exact abs_lt.mpr hb

theorem spatialPatchCutoff_support_radius {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (k : Fin 2 → ℤ) (x : Vec 2)
    (hn : spatialPatchCutoff ζ N k x ≠ 0) :
    ‖x - spatialPatchCentre N k‖ ≤ (2 / 3 : ℝ) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hb := spatialPatchCutoff_coordinate_support hζ N k x hn i
  have he : x i - (k i : ℝ) / N = ((N : ℝ) * x i - k i) / N := by
    field_simp
  change ‖x i - (k i : ℝ) / N‖ ≤ _
  rw [Real.norm_eq_abs, he, abs_div, abs_of_pos hNr]
  exact div_le_div_of_nonneg_right hb.le hNr.le

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The full physical flux of one original identity is exactly the finite weighted sum of its transported native piece fluxes. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem constituentPhysical_flux_window_sum
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (a b t : ℝ) (ht : t ∈ Set.Icc a b)
    (v u : ι) (γ : F.Γ v u) (x : Vec 2)
    (g : ∀ d : ℕ, PiLp 2 (fun _ : DerivativeWord2 (d - 1) => h u)) :
    (∑ d : admissibleOrders K D v u, constituentPhysical F ν e E actual v u γ d t x (g d)) =
      ∑ p ∈ (F.locally_finite a b).toFinset, F.weight p t •
        (∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
          nativeArrayAssembly (d - 1) (F.identity v u γ).map
            (fun k A => transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
              (F.identity v u γ).maxOrder
              (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
                (((F.piece p).material t).symm x)
                (e⁻¹ • ((F.piece p).material t).symm x)) (d - 1) A x k) (g d)) := by
  classical
  rw [constituentPhysical_order_reindex F K hdesc ν e E actual v u γ t x g]
  simp_rw [constituentPhysical_eq_window_sum F ν e E actual a b t ht v u γ]
  simp only [sum_apply, smul_apply]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The original output-window molecular envelope bounds the inactive-time
extension on the entire preparation window, without changing any identity. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem inactiveTimeZeroFamily_smooth_window (F : ChartedFamily ι h D P Ctx)
    (W : Set ℝ) (E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F W) E n) :
    (inactiveTimeZeroFamily F).IsSmoothOn (fun _ _ => W ×ˢ Set.univ) E n := by
  classical
  intro p c v u γ d I tY htY z
  by_cases ht : F.weight p tY.1 = 0
  · simpa only [inactiveTimeZeroFamily, ht, ite_true] using
      (contDiffAt_const : ContDiffAt ℝ (n v : ℕ)
        (fun _ : Vec 2 × Vec 2 => (0 : Vec 2)) (E⁻¹ • tY.2, z))
  · simpa only [inactiveTimeZeroFamily, ht, ite_false] using
      hs p c v u γ d I tY
        ⟨⟨inactiveTimeZeroFamily_weight_ne_zero_mem_output F p tY.1 ht,
          htY.1⟩, Set.mem_univ tY.2⟩ z

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Every declared time and spatial label is controlled by the pointwise molecular jet. -/

theorem pointwiseMolecularJet_term_le {ι : Type*} (ρ e : ℝ) (k j : ℕ)
    (dom : ι → Set (ℝ × Vec 2)) (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2)
    (r q : ℕ) (hrq : r + q ≤ k) :
    ENNReal.ofReal (ρ ^ (r + q) / ((r.factorial : ℝ) * (q.factorial : ℝ) * e ^ q)) *
      pointwiseJetSupFam dom (r + j) q f ≤ pointwiseMolecularJet ρ e k j dom f := by
  unfold pointwiseMolecularJet
  apply le_trans _ (Finset.single_le_sum (fun _ _ => zero_le)
    (Finset.mem_range.mpr (by omega : r < k + 1)))
  exact Finset.single_le_sum
    (f := fun q => ENNReal.ofReal (ρ ^ (r + q) / ((r.factorial : ℝ) * (q.factorial : ℝ) * e ^ q)) *
      pointwiseJetSupFam dom (r + j) q f) (fun _ _ => zero_le)
    (Finset.mem_range.mpr (by omega : q < k + 1 - r))

theorem pointwiseMolecularJet_real_term {ι : Type*} (ρ e : ℝ) (hρ : 0 ≤ ρ) (he : 0 < e)
    (k j : ℕ) (dom : ι → Set (ℝ × Vec 2))
    (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2)
    (hM : pointwiseMolecularJet ρ e k j dom f ≠ ⊤) (i : ι)
    (a b : ℕ) (hab : a + b ≤ k) (t : ℝ) (Y : Vec 2) (hY : (t, Y) ∈ dom i) (z : Vec 2) :
    ρ ^ (a + b) / ((a.factorial : ℝ) * (b.factorial : ℝ) * e ^ b) *
      ‖iteratedFDeriv ℝ (a + j) (fun Y' => iteratedFDeriv ℝ b (f i t Y') z) Y‖ ≤
        (pointwiseMolecularJet ρ e k j dom f).toReal := by
  have hjet : ‖iteratedFDeriv ℝ (a + j) (fun Y' => iteratedFDeriv ℝ b (f i t Y') z) Y‖ₑ ≤
      pointwiseJetSupFam dom (a + j) b f := by
    apply le_iSup_of_le i
    apply le_iSup_of_le t
    apply le_iSup₂_of_le Y hY
    exact le_iSup (fun z : Vec 2 =>
      ‖iteratedFDeriv ℝ (a + j) (fun Y' => iteratedFDeriv ℝ b (f i t Y') z) Y‖ₑ) z
  have hterm := (mul_le_mul_of_nonneg_left hjet
    (show 0 ≤ ENNReal.ofReal (ρ ^ (a + b) /
      ((a.factorial : ℝ) * (b.factorial : ℝ) * e ^ b)) from zero_le)).trans
        (pointwiseMolecularJet_term_le ρ e k j dom f a b hab)
  have hh := ENNReal.toReal_mono hM hterm
  have hw : 0 ≤ ρ ^ (a + b) / ((a.factorial : ℝ) * (b.factorial : ℝ) * e ^ b) := by positivity
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hw, enorm_eq_nnnorm,
    ENNReal.coe_toReal, coe_nnnorm] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The molecular real price sum is controlled before collapsing any original constituent. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem pointwiseMolecularRealEnvelope_sum_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b)
    (v u : ι) (hb : 0 ≤ b v u) (j : ℕ) (hj : j ≤ J) :
    Real.sqrt (π u / π v) * ∑ γ : F.Γ v u, ‖(F.identity v u γ).map‖ *
      ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
        molecularRealPrice ν ρ (K v) (d - 2)
          (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) ≤
      |C j| * (E ^ j)⁻¹ * b v u := by
  classical
  have hn (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) :
      0 ≤ molecularRealPrice ν ρ (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) :=
    molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ |C j| * (E ^ j)⁻¹ * b v u)).mp
  apply le_trans _ ((henv.2 v u j hj).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self (C j)) (by positivity)) hb)))
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun γ _ => mul_nonneg (norm_nonneg _)
      (Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun I _ => hn γ d I))))]
  apply mul_le_mul_right
  apply Finset.sum_le_sum
  intro γ _
  rw [ENNReal.ofReal_mul (norm_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun d _ => Finset.sum_nonneg (fun I _ => hn γ d I))]
  apply mul_le_mul_right
  apply Finset.sum_le_sum
  intro d hd
  rw [ENNReal.ofReal_sum_of_nonneg (fun I _ => hn γ d I)]
  apply Finset.sum_le_sum
  intro I _
  have hkd : K v + (d - 2) = K v + d - 2 := by
    have hd2 := (Finset.mem_Icc.mp hd).1
    omega
  simpa only [hkd] using molecularRealPrice_ofReal_le ν ρ hν hρ (K v) (d - 2)
    (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))

theorem pointwiseMolecularRealEnvelope_scaled_sum_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b)
    (v u : ι) (hb : 0 ≤ b v u) (j : ℕ) (hj : j ≤ J) :
    Real.sqrt (π u / π v) * ∑ γ : F.Γ v u, ‖(F.identity v u γ).map‖ *
      ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
        E ^ j * molecularRealPrice ν ρ (K v) (d - 2)
          (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) ≤ |C j| * b v u := by
  classical
  have hh := mul_le_mul_of_nonneg_left
    (pointwiseMolecularRealEnvelope_sum_le F π K dom ν e E ρ hν hE hρ C J b henv v u hb j hj)
    (pow_nonneg hE.le j)
  have he : E ^ j * (|C j| * (E ^ j)⁻¹ * b v u) = |C j| * b v u := by
    have hn := (pow_pos hE j).ne'
    field_simp
  rw [he] at hh
  simp_rw [← Finset.mul_sum]
  conv_lhs =>
    arg 2
    arg 2
    intro γ
    rw [mul_left_comm ‖(F.identity v u γ).map‖ (E ^ j)]
  rw [← Finset.mul_sum]
  convert hh using 1
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual triangular coefficient row is absorbed using a depth discount of its original masses. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem triangularCoefficient_original_mass_schur_budget
    (ν ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ v u, (d : admissibleOrders K D v u) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h v))
    (hA : ∀ v u d, coefficientSeminorm ρ (K v) a b (A v u d) ≠ ⊤)
    (r : ι → ℕ) (hr : ∀ v u, ¬ r u < r v → ∀ d, A v u d = 0)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (L B : ℝ) (hL : 1 ≤ L)
    (hrow : ∀ v, ∑ u, schurMatrix ν ρ π K D a b A v u ≤ B)
    (hcol : ∀ u, ∑ v, schurMatrix ν ρ π K D a b A v u ≤ B) :
    (∀ v, ∑ u, schurMatrix ν ρ (fun i => π i * rankMass r L i) K D a b A v u ≤ B / L) ∧
    (∀ u, ∑ v, schurMatrix ν ρ (fun i => π i * rankMass r L i) K D a b A v u ≤ B / L) := by
  let M := schurMatrix ν ρ (fun _ => 1) K D a b A
  have hn (v u : ι) : 0 ≤ M v u :=
    CoupledEnergy.schurMatrix_nonneg ν ρ hν hρ (fun _ => 1) (fun _ => zero_lt_one)
      K D a b A hA v u
  have hs (v u : ι) (hne : M v u ≠ 0) : r u < r v := by
    by_contra hh
    exact hne (schurMatrix_entry_zero ν ρ K D a b A v u (hr v u hh) (fun _ => 1))
  rw [schurMatrix_eq_massConjugated ν ρ K D a b A π] at hrow hcol
  rw [schurMatrix_eq_massConjugated ν ρ K D a b A (fun i => π i * rankMass r L i)]
  exact originalMass_rank_schur_budget π hπ r L hL M hn hs B hrow hcol

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! A fixed slot reserve bounds every metric multiplication price independently of the component family. -/

def metricTaylorUniformDensityPrice (Kmax : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (Kmax + 1), (4 * Real.sqrt (multiplicationDensityBudget k)) ^ 2

theorem metricTaylorUniformDensityPrice_nonneg (Kmax : ℕ) :
    0 ≤ metricTaylorUniformDensityPrice Kmax :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem metricTaylor_density_price_le (K Kmax : ℕ) (hK : K ≤ Kmax) (c : ℝ) :
    (4 * Real.sqrt (multiplicationDensityBudget K) * c) ^ 2 ≤
      metricTaylorUniformDensityPrice Kmax * c ^ 2 := by
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg c)
  exact Finset.single_le_sum (fun k _ => sq_nonneg (4 * Real.sqrt (multiplicationDensityBudget k)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hK))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Positive order budgets extracted before cancellation from the sampled envelope. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem sampledEnvelope_order_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (actual : ∀ p, Ctx p)
    (t₀ t₁ ν e E ρ C : ℝ) (b : ι → ι → ℝ)
    (hfwd : IsSampledEnvelope F π K actual t₀ t₁ ν e E ρ C b)
    (v u : ι) (d : ℕ) (hd : d ∈ Finset.Icc 2 D) :
    ENNReal.ofReal (Real.sqrt (π u / π v)) *
      ((∑ γ : F.Γ v u, coefficientSeminorm ρ (K v) t₀ t₁
        (constituentPhysical F ν e E actual v u γ d)) *
        (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
        ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) ≤
      ENNReal.ofReal (C * b v u) := by
  apply le_trans _ (hfwd.2 v u)
  apply mul_le_mul_of_nonneg_left _ (show 0 ≤ ENNReal.ofReal (Real.sqrt (π u / π v)) from zero_le)
  simp only [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro γ _
  exact Finset.single_le_sum
    (f := fun d' => coefficientSeminorm ρ (K v) t₀ t₁
      (constituentPhysical F ν e E actual v u γ d') *
        (ENNReal.ofReal (ν * ρ ^ (d' - 2)))⁻¹ *
        ENNReal.ofReal (((K v + d' - 2).factorial : ℝ) / ((K v).factorial : ℝ)))
    (fun _ _ => zero_le) hd

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Translating the base patches through all torus images recovers the positive partition. -/

theorem spatialPatchCutoff_translate (ζ : ℝ → ℝ) (N : ℕ) (k n : Fin 2 → ℤ)
    (x : Vec 2) :
    spatialPatchCutoff ζ N k (x + AVenhance.latticeShift n) =
      spatialPatchCutoff ζ N (fun i => k i - (N : ℤ) * n i) x := by
  have he (i : Fin 2) : (N : ℝ) * (x + AVenhance.latticeShift n) i - k i =
      N * x i - ((k i - (N : ℤ) * n i : ℤ) : ℝ) := by
    simp only [Pi.add_apply, AVenhance.latticeShift, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    ring
  simp only [spatialPatchCutoff, he]

theorem spatialPatchCutoff_summable {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (x : Vec 2) : Summable (fun k => spatialPatchCutoff ζ N k x) := by
  by_contra hn
  have hz := tsum_eq_zero_of_not_summable hn
  rw [spatialPatchCutoff_partition hζ N x] at hz
  norm_num at hz

theorem spatialPatchCutoff_square_sum_le_one {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (x : Vec 2) : ∑' k, (spatialPatchCutoff ζ N k x) ^ 2 ≤ 1 := by
  have hle (k : Fin 2 → ℤ) : (spatialPatchCutoff ζ N k x) ^ 2 ≤
      spatialPatchCutoff ζ N k x := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left
      (spatialPatchCutoff_le_one hζ N k x) (spatialPatchCutoff_nonneg hζ N k x)
  have hs := (spatialPatchCutoff_summable hζ N x).of_nonneg_of_le (fun _ => sq_nonneg _) hle
  exact (hs.tsum_le_tsum hle (spatialPatchCutoff_summable hζ N x)).trans_eq
    (spatialPatchCutoff_partition hζ N x)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Each original constituent and word retains its positive molecular envelope budget. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem pointwiseMolecularEnvelope_constituent_term_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (dom : F.Domain) (ν e E ρ : ℝ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (hf : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b)
    (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (j : ℕ) (hj : j ≤ J) :
    ENNReal.ofReal (Real.sqrt (π u / π v)) * ENNReal.ofReal ‖(F.identity v u γ).map‖ *
      (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
          (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
            ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) ≤
      ENNReal.ofReal (C j * (E ^ j)⁻¹ * b v u) := by
  let term : ∀ γ : F.Γ v u, ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ≥0∞ := fun γ d I =>
    pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
        (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
          ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))
  have hb := hf.2 v u j hj
  have hh := CycleWords.positive_constituent_term_le
    (ENNReal.ofReal (Real.sqrt (π u / π v)))
    (fun γ : F.Γ v u => ENNReal.ofReal ‖(F.identity v u γ).map‖)
    (fun γ => Finset.Icc 2 (F.identity v u γ).maxOrder) term γ d hd I
  exact hh.trans hb

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Squared positive patch weights over every translated base patch have total at most one. -/

def negatePeriodImages (N : ℕ) :
    ((Fin 2 → Fin N) × (Fin 2 → ℤ)) ≃ ((Fin 2 → Fin N) × (Fin 2 → ℤ)) where
  toFun p := (p.1, -p.2)
  invFun p := (p.1, -p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem spatialPatch_image_square_budget {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (x : Vec 2) :
    (∑ j : Fin 2 → Fin N, ∑' n : Fin 2 → ℤ,
      ENNReal.ofReal ((spatialPatchCutoff ζ N (fun i => (j i : ℤ))
        (x + AVenhance.latticeShift n)) ^ 2)) ≤ 1 := by
  have hs := (spatialPatchCutoff_summable hζ N x).of_nonneg_of_le
    (fun _ => sq_nonneg _) (fun k => by
      simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left
        (spatialPatchCutoff_le_one hζ N k x) (spatialPatchCutoff_nonneg hζ N k x))
  have he := ((negatePeriodImages N).trans (periodImageLatticeEquiv N hN)).tsum_eq
    (fun k => ENNReal.ofReal ((spatialPatchCutoff ζ N k x) ^ 2))
  have ht : (∑ j : Fin 2 → Fin N, ∑' n : Fin 2 → ℤ,
      ENNReal.ofReal ((spatialPatchCutoff ζ N (fun i => (j i : ℤ))
        (x + AVenhance.latticeShift n)) ^ 2)) =
      ∑' k : Fin 2 → ℤ, ENNReal.ofReal ((spatialPatchCutoff ζ N k x) ^ 2) := by
    change (∑' p : (Fin 2 → Fin N) × (Fin 2 → ℤ),
      ENNReal.ofReal ((spatialPatchCutoff ζ N
        (fun i => (p.1 i : ℤ) + (N : ℤ) * (-p.2 i)) x) ^ 2)) = _ at he
    simpa only [ENNReal.tsum_prod', tsum_fintype, mul_neg,
      ← sub_eq_add_neg, spatialPatchCutoff_translate] using he
  rw [ht, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs]
  exact (ENNReal.ofReal_le_ofReal (spatialPatchCutoff_square_sum_le_one hζ N x)).trans_eq
    ENNReal.ofReal_one

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The exact coefficient factorial budget applies to scalar-weighted raw jet arrays. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [MeasurableSpace F]

/-- Scalar weighting retains the existing dimension-independent coefficient multiplier budget. -/
theorem multiplication_weighted_factorialNorm_le {K : ℕ} {U : Set (Vec 2)}
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    (D : RawJet2 K E) (q : Vec 2 → ℝ)
    (hD : JetMemL2On U (fun β y => q y • D β y))
    {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Real.sqrt (factorialNormSq ρ
      (jetToL2 (fun β y => q y • multiplicationRawJet C D β y)
        (multiplicationRawJet_weight_memL2On C hC D q hD hb))) ≤
      (∑ l : Fin (K + 1), factorialRootWeight ρ l.val * A l) *
        Real.sqrt (factorialNormSq ρ (jetToL2 (fun β y => q y • D β y) hD)) := by
  have he : multiplicationRawJet C (fun β y => q y • D β y) =
      (fun β y => q y • multiplicationRawJet C D β y) :=
    funext (fun β => funext (fun y => multiplicationRawJet_smul_weight C D q β y))
  simpa only [he] using (multiplication_factorialNorm_le_of_bounds hC hD hb hρ)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Exact cancellation of dimensional and reserve factors in the diagonal sample budget. -/

theorem molecular_sample_price_cancellation (ν e ρ L : ℝ)
    (hν : 0 < ν) (he : 0 < e) (hρ : 0 < ρ) (K d : ℕ) (M : ℝ≥0∞) :
    |ν * e ^ d| * (L * molecularRealPrice ν ρ K d M /
      derivativeReserveFactor (ρ / e) K d) = L * M.toReal := by
  rw [abs_of_pos (mul_pos hν (pow_pos he _))]
  unfold molecularRealPrice derivativeReserveFactor
  rw [div_pow]
  have hk : (K.factorial : ℝ) ≠ 0 := by positivity
  have hkd : ((K + d).factorial : ℝ) ≠ 0 := by positivity
  have hep : e ^ d ≠ 0 := pow_ne_zero _ he.ne'
  have hρp : ρ ^ d ≠ 0 := pow_ne_zero _ hρ.ne'
  field_simp [hν.ne']

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Nonzero original maps have finite molecular coefficient jets at every reserved total order. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem pointwiseMolecularEnvelope_constituent_jet_ne_top (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (_he : 0 < e) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (hf : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (j : ℕ) (hj : j ≤ J)
    : pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) ≠ ⊤ := by
  have hh := pointwiseMolecularEnvelope_constituent_term_le F π K dom ν e E ρ C J b hf v u γ d hd I j hj
  have hroot : ENNReal.ofReal (Real.sqrt (π u / π v)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (div_pos (hπ u) (hπ v)))).ne'
  have hmap : ENNReal.ofReal ‖(F.identity v u γ).map‖ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hγ)).ne'
  have hscale : ENNReal.ofReal (ν * ρ ^ (d - 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (mul_pos hν (pow_pos hρ _))).ne'
  have hinv : (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hratio : ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (div_pos (by positivity) (by positivity))).ne'
  have hterm := (ENNReal.lt_top_of_mul_ne_top_right
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hh) (mul_ne_zero hroot hmap)).ne
  have hfirst := (ENNReal.lt_top_of_mul_ne_top_left hterm hratio).ne
  have hm := (ENNReal.lt_top_of_mul_ne_top_left hfirst hinv).ne
  exact hm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs

/-! The preparation certificate supplies the existing scale-invariant chart transport API. -/

def preparationFlowJetConstant (Cchart : ℕ → ℝ) (p : ℕ) : ℝ :=
  if p = 1 then 1 + max (Cchart 0) 0 / 2 else
    max (Cchart (p - 1)) 0 * ((p - 1).factorial : ℝ) / 2

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem preparation_flow_positive_jets
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (p : ℕ) (hp : 1 ≤ p) (hpJ : p ≤ Jchart + 1) (y : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun z => streamFlow φ hφ r z σ) y‖ ≤
      preparationFlowJetConstant Cchart p * (ocEpsilon q Λ (m - 1))⁻¹ ^ (p - 1) := by
  by_cases hp1 : p = 1
  · subst p
    simpa [preparationFlowJetConstant] using
      preparation_flow_first_jet_bound hc ha r σ hr hσ hage y
  have hj : p - 1 ≤ Jchart := by omega
  have hj0 : p - 1 ≠ 0 := by omega
  have hh := preparation_flow_higher_jet_bound hc ha r σ hr hσ hage (p - 1) hj0 hj y
  rw [Nat.sub_add_cancel hp] at hh
  simpa only [preparationFlowJetConstant, ite_eq_right hp1, div_mul_eq_mul_div] using hh

theorem preparation_flow_jetBound
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (hE : 0 < ocEpsilon q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m) :
    JetBound (fun z => streamFlow φ hφ r z σ) (Jchart + 1)
      (1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|)
      (ocEpsilon q Λ (m - 1)) := by
  exact jetBound_of_Cχ hE (preparation_flow_positive_jets hc ha r σ hr hσ hage)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Pointwise bounds of the assembled physical coefficient, at every time
and point, obtained from the sampled positive constituent budgets. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem sampledEnvelope_physicalCoefficient_ennreal_bound (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (actual : ∀ p, Ctx p)
    (t₀ t₁ ν e E ρ C : ℝ) (b : ι → ι → ℝ)
    (hfwd : IsSampledEnvelope F π K actual t₀ t₁ ν e E ρ C b)
    (v u : ι) (d : ℕ) (hd : d ∈ Finset.Icc 2 D)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) (x : Vec 2) :
    ENNReal.ofReal (Real.sqrt (π u / π v)) *
      (ENNReal.ofReal ‖physicalCoefficient F ν e E actual v u d t x‖ *
        (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
        ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) ≤
      ENNReal.ofReal (C * b v u) := by
  have hp : ENNReal.ofReal ‖physicalCoefficient F ν e E actual v u d t x‖ ≤
      ∑ γ : F.Γ v u, coefficientSeminorm ρ (K v) t₀ t₁
        (constituentPhysical F ν e E actual v u γ d) := by
    calc
      _ ≤ ENNReal.ofReal (∑ γ : F.Γ v u, ‖constituentPhysical F ν e E actual v u γ d t x‖) :=
        ENNReal.ofReal_le_ofReal (norm_sum_le _ _)
      _ = ∑ γ : F.Γ v u, ENNReal.ofReal ‖constituentPhysical F ν e E actual v u γ d t x‖ :=
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)
      _ ≤ _ := Finset.sum_le_sum (fun γ _ =>
        coefficient_value_le_seminorm ρ (K v) t₀ t₁ _ t ht x)
  have hm := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ from zero_le)
  have hm' := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ)) from zero_le)
  exact (mul_le_mul_of_nonneg_left hm'
    (show 0 ≤ ENNReal.ofReal (Real.sqrt (π u / π v)) from zero_le)).trans
    (sampledEnvelope_order_budget F π K actual t₀ t₁ ν e E ρ C b hfwd v u d hd)

theorem sampledEnvelope_physicalCoefficient_normalized_bound (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (actual : ∀ p, Ctx p)
    (t₀ t₁ ν e E ρ C : ℝ) (b : ι → ι → ℝ)
    (hν : 0 < ν) (hρ : 0 < ρ)
    (hfwd : IsSampledEnvelope F π K actual t₀ t₁ ν e E ρ C b)
    (v u : ι) (hCb : 0 ≤ C * b v u) (d : ℕ) (hd : d ∈ Finset.Icc 2 D)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) (x : Vec 2) :
    Real.sqrt (π u / π v) *
      (‖physicalCoefficient F ν e E actual v u d t x‖ / (ν * ρ ^ (d - 2)) *
        (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) ≤ C * b v u := by
  have hden : 0 ≤ ν * ρ ^ (d - 2) := mul_nonneg hν.le (pow_nonneg hρ.le _)
  have hfac : 0 ≤ ((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ) := by positivity
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (sampledEnvelope_physicalCoefficient_ennreal_bound F π K actual t₀ t₁ ν e E ρ C b
      hfwd v u d hd t ht x)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_ofReal hden, ENNReal.toReal_ofReal hfac,
    ENNReal.toReal_ofReal hCb] at he
  simpa only [div_eq_mul_inv] using he

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Periodized localized initial data reconstruct the original periodic datum exactly. -/

theorem spatialPatch_images_summable {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (x : Vec 2) :
    Summable (fun p : (Fin 2 → Fin N) × (Fin 2 → ℤ) =>
      spatialPatchCutoff ζ N (fun i => (p.1 i : ℤ)) (x + AVenhance.latticeShift p.2)) := by
  have hs := (spatialPatchCutoff_summable hζ N x).comp_injective
    (((negatePeriodImages N).trans (periodImageLatticeEquiv N hN)).injective)
  change Summable (fun p : (Fin 2 → Fin N) × (Fin 2 → ℤ) =>
    spatialPatchCutoff ζ N (fun i => (p.1 i : ℤ) + (N : ℤ) * (-p.2 i)) x) at hs
  simpa only [mul_neg, ← sub_eq_add_neg, spatialPatchCutoff_translate] using hs

theorem spatialPatch_images_partition {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (x : Vec 2) :
    (∑' p : (Fin 2 → Fin N) × (Fin 2 → ℤ),
      spatialPatchCutoff ζ N (fun i => (p.1 i : ℤ)) (x + AVenhance.latticeShift p.2)) = 1 := by
  have he := ((negatePeriodImages N).trans (periodImageLatticeEquiv N hN)).tsum_eq
    (fun k => spatialPatchCutoff ζ N k x)
  change (∑' p : (Fin 2 → Fin N) × (Fin 2 → ℤ),
    spatialPatchCutoff ζ N (fun i => (p.1 i : ℤ) + (N : ℤ) * (-p.2 i)) x) = _ at he
  simpa only [mul_neg, ← sub_eq_add_neg, spatialPatchCutoff_translate,
    spatialPatchCutoff_partition hζ N x] using he

theorem periodic_spatialPatch_reconstruction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (f : Vec 2 → E) (hp : AVenhance.IsZ2Periodic f) (x : Vec 2) :
    (∑ j : Fin 2 → Fin N, ∑' n : Fin 2 → ℤ,
      spatialPatchCutoff ζ N (fun i => (j i : ℤ)) (x + AVenhance.latticeShift n) •
        f (x + AVenhance.latticeShift n)) = f x := by
  have hper (n : Fin 2 → ℤ) : f (x + AVenhance.latticeShift n) = f x := hp n x
  simp only [hper]
  have hs := (spatialPatch_images_summable hζ N hN x).smul_const (f x)
  have he := (spatialPatch_images_summable hζ N hN x).tsum_smul_const (f x)
  rw [hs.tsum_prod, tsum_fintype, spatialPatch_images_partition hζ N hN x, one_smul] at he
  exact he

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Native Piola order lowering is paid by the original Sobolev derivative reserve. -/

theorem derivativeReserveFactor_order_lowering_le (ρ R : ℝ)
    (hρ : 0 < ρ) (hR : 0 < R) (hρR : ρ ≤ R) (K low extra : ℕ) :
    R⁻¹ ^ extra * derivativeReserveFactor ρ K low ≤
      derivativeReserveFactor ρ K (low + extra) := by
  have hh := molecular_order_lowering_normalization 1 ρ R (by norm_num) hρ hR hρR
    K low extra 1
  simpa only [molecularRealPrice, derivativeReserveFactor, ENNReal.toReal_one,
    one_mul, mul_one, mul_assoc, div_eq_mul_inv] using hh

theorem derivativeReserveFactor_order_lowering_budget (ρ R : ℝ)
    (hρ : 0 < ρ) (hR : 0 < R) (hρR : ρ ≤ R) (K low extra : ℕ)
    (B : ℝ) (hB : 0 ≤ B) :
    (B / derivativeReserveFactor ρ K (low + extra)) * R⁻¹ ^ extra *
      derivativeReserveFactor ρ K low ≤ B := by
  have hhigh : 0 < derivativeReserveFactor ρ K (low + extra) := by
    unfold derivativeReserveFactor
    positivity
  have hh : R⁻¹ ^ extra * derivativeReserveFactor ρ K low /
      derivativeReserveFactor ρ K (low + extra) ≤ 1 :=
    (div_le_one hhigh).mpr (derivativeReserveFactor_order_lowering_le ρ R hρ hR hρR K low extra)
  calc
    _ = B * (R⁻¹ ^ extra * derivativeReserveFactor ρ K low /
        derivativeReserveFactor ρ K (low + extra)) := by ring
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left hh hB
    _ = _ := mul_one B

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs

/-! Certified chart sampling preserves a positive finite molecular jet budget. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem preparation_flow_sample_jet_bound
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (ρ : ℝ) (hρ : 0 < ρ)
    (hρE : ρ ≤ ocEpsilon q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (n : ℕ) (hn : n ≤ Jchart + 1) (f : Vec 2 → V) (hf : ContDiff ℝ (n : ℕ) f)
    (B : ℝ) (hb : ∀ j, j ≤ n → ∀ y, ρ ^ j * ‖iteratedFDeriv ℝ j f y‖ ≤ B)
    (x : Vec 2) :
    let C := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => f (streamFlow φ hφ r y σ)) x‖ ≤
      (n.factorial : ℝ) * C ^ n * ((n + 1 : ℕ) * B) := by
  dsimp only
  let C := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
  have hC : 1 ≤ C := one_le_jetConst _ _
  have hE := hρ.trans_le hρE
  have hΨ : ContDiff ℝ (n : ℕ∞) (fun y => streamFlow φ hφ r y σ) :=
    (hc.smooth r hr σ hσ).of_le (by exact_mod_cast hn)
  have hJ := preparation_flow_jetBound hc ha hE r σ hr hσ hage
  have hh := scaled_comp_bound hf hΨ hC hρ hρE x
    (fun p hp hpN => hJ p hp (hpN.trans hn) x)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ _j ∈ Finset.range (n + 1), B :=
      Finset.sum_le_sum (fun j hj => hb j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) _)
    _ = _ := by simp

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The original output-window molecular envelope bounds the inactive-time
extension on the entire preparation window, without changing any identity. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem inactiveTimeZeroFamily_dimFlux_pointwise_jet_le (F : ChartedFamily ι h D P Ctx)
    (W : Set ℝ) (ν e E : ℝ) (p : P) (c : Ctx p) (v u : ι)
    (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (r q : ℕ) :
    pointwiseJetSupOn (W ×ˢ Set.univ) r q
        ((inactiveTimeZeroFamily F).dimFlux ν e E p c v u γ d I) ≤
      pointwiseJetSupOn (ChartedFamily.Domain.onWindow F W p c) r q
        (F.dimFlux ν e E p c v u γ d I) := by
  classical
  have he : (inactiveTimeZeroFamily F).dimFlux ν e E p c v u γ d I =
      fun t Y z => if F.weight p t ≠ 0 then F.dimFlux ν e E p c v u γ d I t Y z
        else 0 := by
    funext t Y z
    by_cases ht : F.weight p t = 0
    · simp [ChartedFamily.dimFlux, ChartedFamily.slowFlux, inactiveTimeZeroFamily, ht]
    · simp [ChartedFamily.dimFlux, ChartedFamily.slowFlux, inactiveTimeZeroFamily, ht]
  rw [he]
  exact pointwiseJetSupOn_inactiveTimeZero_le W (F.piece p).output (fun t => F.weight p t ≠ 0)
    (F.dimFlux ν e E p c v u γ d I)
    (fun t ht => inactiveTimeZeroFamily_weight_ne_zero_mem_output F p t ht) r q

theorem inactiveTimeZeroFamily_pointwiseMolecularJet_le (F : ChartedFamily ι h D P Ctx)
    (W : Set ℝ) (ν e E ρ : ℝ) (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (k j : ℕ) :
    pointwiseMolecularJet ρ e k j (fun _ : F.Index => W ×ˢ Set.univ)
        (fun x => (inactiveTimeZeroFamily F).dimFlux ν e E x.1 x.2 v u γ d I) ≤
      pointwiseMolecularJet ρ e k j (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) := by
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ zero_le
  exact iSup_mono (fun x => inactiveTimeZeroFamily_dimFlux_pointwise_jet_le F W ν e E
    x.1 x.2 v u γ d I (r + j) q)

theorem inactiveTimeZeroFamily_pointwiseMolecularEnvelope (F : ChartedFamily ι h D P Ctx)
    (W : Set ℝ) (π : ι → ℝ) (K : ι → ℕ) (ν e E ρ : ℝ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (he : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b) :
    IsPointwiseMolecularEnvelope (inactiveTimeZeroFamily F) π K
      (fun _ _ => W ×ˢ Set.univ) ν e E ρ C J b := by
  refine ⟨inactiveTimeZeroFamily_smooth_window F W E _ he.1, ?_⟩
  intro v u j hj
  apply le_trans _ (he.2 v u j hj)
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply Finset.sum_le_sum
  intro γ _
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply Finset.sum_le_sum
  intro d _
  apply Finset.sum_le_sum
  intro I _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (inactiveTimeZeroFamily_pointwiseMolecularJet_le F W ν e E ρ v u γ d I (K v) j)
      zero_le) zero_le

end AVRegularity.CycleJointProofs
end
end
