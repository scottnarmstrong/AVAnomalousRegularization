-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.MeanNormalizedBlocks
import AVRegularity.CycleJoint.Assembly.PlaneModelExtension
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.EntryTerminal.Ingredients.CoarseFamily.CoarseFamily
import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
import AVRegularity.EntryTerminal.Ingredients.PrepAnchor.PrepAnchor
import AVRegularity.EntryTerminal.Ingredients.PrepInterp.PrepInterp
public import AVRegularity.EntryTerminal.Assembly.Prep.ModelAssembly
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.CycleJoint.Assembly.PeriodizedSum
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.EntryTerminal.Ingredients.PrepChart.Chart
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs AVRegularity.CycleJointProofs.Assembly
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The normalized preparation map** (`PrepNormPart`; the normalization pattern
`Π₀ + Q₀ T_m Q₀`). From a raw whole-family model `T_m` on order-zero data:
`P X = Π₀ X + Q₀ trunc T_m(Q₀ trunc₀ X)`.
- `P` fixes constant component vectors: `Q₀` kills constants and `T_m 0 = 0`.
- The value of `P X` is the mean of `X` plus a mean-free part.

For `X` constant, `P X = X` as constants at the output order. For `T_m = 0`, `P = Π₀` is the
projection to the means. -/

local instance prepNormOpTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance prepNormOpTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance prepNormOpTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance
local instance prepNormOpTorusPiAdd {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    AddCommMonoid (∀ i, TorusHk (K i) (h i)) := inferInstance
local instance prepNormOpTorusPiModule {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    Module ℝ (∀ i, TorusHk (K i) (h i)) := inferInstance

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The order-zero datum `trunc₀ trunc_K X`. -/
def normG (Kw : ℕ) (K : ι → ℕ) (hK : ∀ v, K v ≤ Kw) :
    (∀ v, TorusHk Kw (h v)) →ₗ[ℝ] (∀ v, TorusHk 0 (h v)) :=
  LinearMap.pi (R := ℝ) (φ := fun u => TorusHk 0 (h u)) fun u =>
    (truncateTorusHk (E := h u) (Nat.zero_le (K u))).toLinearMap.comp
      ((truncateTorusHk (E := h u) (hK u)).toLinearMap.comp (LinearMap.proj u))

/-- Its constant part `trunc₀ (mean X)`. -/
def normGc (Kw : ℕ) (K : ι → ℕ) : (∀ v, TorusHk Kw (h v)) →ₗ[ℝ] (∀ v, TorusHk 0 (h v)) :=
  LinearMap.pi (R := ℝ) (φ := fun u => TorusHk 0 (h u)) fun u =>
    (truncateTorusHk (E := h u) (Nat.zero_le (K u))).toLinearMap.comp
      ((torusConstantLinearMap (K u)).comp ((torusMeanLinearMap Kw).comp (LinearMap.proj u)))

/-- **The normalized map** `Π₀ + Q₀ trunc (T_m(trunc₀ X) - T_m(trunc₀ Π₀ X))`, i.e.
`Π₀ + Q₀ T_m Q₀` with `T_m` applied to the datum and to its constant part separately. -/
def normOp (Kw Kh : ℕ) (K : ι → ℕ) (hK : ∀ v, K v ≤ Kw)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v))) :
    (∀ v, TorusHk Kw (h v)) →ₗ[ℝ] (∀ v, TorusHk Kh (h v)) :=
  LinearMap.pi (R := ℝ) (φ := fun v => TorusHk Kh (h v))
      (fun v => (meanProjection Kw Kh).comp (LinearMap.proj v)) +
    LinearMap.pi (R := ℝ) (φ := fun v => TorusHk Kh (h v)) fun v => (meanComplement Kh).comp
      ((truncateTorusHk (E := h v) (le_max_left Kh (K v))).toLinearMap.comp
        ((LinearMap.proj v).comp (Tm.comp (normG Kw K hK)) -
          (LinearMap.proj v).comp (Tm.comp (normGc Kw K))))

omit [Fintype ι] in
theorem normOp_apply (Kw Kh : ℕ) (K : ι → ℕ) (hK : ∀ v, K v ≤ Kw)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v)))
    (X : ∀ v, TorusHk Kw (h v)) (v : ι) :
    normOp Kw Kh K hK Tm X v = torusConstantCarrier Kh (torusMean (X v)) +
      meanComplement Kh (truncateTorusHk (le_max_left Kh (K v))
        (Tm (normG Kw K hK X) v - Tm (normGc Kw K X) v)) := rfl

omit [Fintype ι] in
/-- The map with its two data written out (the form of the raw error clauses). -/
theorem normOp_apply_lam (Kw Kh : ℕ) (K : ι → ℕ) (hK : ∀ v, K v ≤ Kw)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v)))
    (X : ∀ v, TorusHk Kw (h v)) (v : ι) :
    normOp Kw Kh K hK Tm X v = torusConstantCarrier Kh (torusMean (X v)) +
      meanComplement Kh (truncateTorusHk (le_max_left Kh (K v))
        (Tm (fun u => truncateTorusHk (Nat.zero_le (K u)) (truncateTorusHk (hK u) (X u))) v -
          Tm (fun u => truncateTorusHk (Nat.zero_le (K u))
            (torusConstantCarrier (K u) (torusMean (X u)))) v)) := rfl

omit [Fintype ι] in
/-- On constant carriers the two data agree. -/
theorem normG_constant (Kw : ℕ) (K : ι → ℕ) (hK : ∀ v, K v ≤ Kw) (c : ∀ v, h v) :
    normG Kw K hK (fun u => torusConstantCarrier Kw (c u)) =
      normGc Kw K (fun u => torusConstantCarrier Kw (c u)) := by
  funext u
  show truncateTorusHk (Nat.zero_le (K u)) (truncateTorusHk (hK u) (torusConstantCarrier Kw (c u))) =
    truncateTorusHk (Nat.zero_le (K u)) (torusConstantCarrier (K u)
      (torusMean (torusConstantCarrier Kw (c u))))
  rw [torusConstantCarrier_truncate, torusMean_constant]

omit [Fintype ι] in
/-- The map fixes constant carriers. -/
theorem normOp_constant (Kw Kh : ℕ) (K : ι → ℕ) (hK : ∀ v, K v ≤ Kw)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v))) (c : ∀ v, h v)
    (v : ι) :
    normOp Kw Kh K hK Tm (fun u => torusConstantCarrier Kw (c u)) v =
      torusConstantCarrier Kh (c v) := by
  rw [normOp_apply, normG_constant, sub_self, map_zero, map_zero, add_zero, torusMean_constant]

/-- An element whose value is almost everywhere a constant is that constant carrier. -/
theorem torusHk_eq_constant_of_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}
    (X : TorusHk K E) (c : E)
    (hX : X.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube] fun _ => c) :
    X = torusConstantCarrier K c := by
  apply TorusHk.ext_value
  apply Lp.ext
  filter_upwards [periodicJetRepresentative_ae X.val (valueIndex2 K), hX,
    periodicJetRepresentative_ae (torusConstantCarrier K c).val (valueIndex2 K),
    torusConstantCarrier_raw_value_ae K c] with x h1 h2 h3 h4
  have e1 : X.val (valueIndex2 K) x = c := h1.symm.trans h2
  have e2 : (torusConstantCarrier K c).val (valueIndex2 K) x = c := h3.symm.trans h4
  rw [e1, e2]

omit [Fintype ι] in
/-- **The constants clause** of the normalized map. -/
theorem normOp_fixes_constants (Kw Kh : ℕ) (K : ι → ℕ) (hK : ∀ v, K v ≤ Kw)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v)))
    (cv : ∀ v, h v) (X : ∀ v, TorusHk Kw (h v))
    (hX : ∀ v, (X v).toFunction.jet (valueIndex2 Kw) =ᵐ[volume.restrict AVenhance.unitCube]
      fun _ => cv v) (v : ι) :
    (normOp Kw Kh K hK Tm X v).toFunction.jet (valueIndex2 Kh) =ᵐ[volume.restrict AVenhance.unitCube]
      fun _ => cv v := by
  have hXc : X = fun u => torusConstantCarrier Kw (cv u) :=
    funext fun u => torusHk_eq_constant_of_ae (X u) (cv u) (hX u)
  rw [hXc, normOp_constant]
  exact torusConstantCarrier_raw_value_ae Kh (cv v)

end AVRegularity.EntryTerminal.Ingredients
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs AVRegularity.CycleJointProofs.Assembly
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The error of the normalized map** (`PrepNormPart`; the normalization). Let `u` solve the
plain coupled system from `f₀ = trunc_K X`, with means conserved. Apply the raw error `IsRawMassError`
twice: to `f₀`, with the error `e`, and to its constant part `f_c` (a constant solution), with the
error `e_c`. At the order zero,
`trunc₀ u(t_p) - trunc₀ P X = trunc₀ Q e - trunc₀ Q e_c`
(`Q₀ f₀ = f₀ - f_c`, `T_m` linear, `Π₀ u(t_p) = Π₀ f₀`). Hence the order-zero error is at most
`2‖e‖ + 2‖e_c‖ ≤ 4 C_P E^P (∑ π⁻¹ F²)^{1/2}`.

For `X` constant, `u = X` and the error is `0`. For `T_m = 0`, the error is the mean-free part of
`u(t_p)`. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E'] [CompleteSpace E']

omit [Fintype ι] in
theorem trunc0_normOp_split (Kw Kh : ℕ) (K : ι → ℕ) (hK : ∀ v, K v ≤ Kw)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v)))
    (X : ∀ v, TorusHk Kw (h v)) (v : ι) :
    truncateTorusHk (Nat.zero_le Kh) (normOp Kw Kh K hK Tm X v) =
      torusConstantCarrier 0 (torusMean (X v)) +
        meanComplement 0 (truncateTorusHk (Nat.zero_le (max Kh (K v))) (Tm (fun u => truncateTorusHk (Nat.zero_le (K u)) (truncateTorusHk (hK u) (X u))) v) -
          truncateTorusHk (Nat.zero_le (max Kh (K v))) (Tm (fun u => truncateTorusHk (Nat.zero_le (K u)) (torusConstantCarrier (K u) (torusMean (X u)))) v)) := by
  rw [normOp_apply_lam]
  simp only [map_add, torusConstantCarrier_truncate, truncate_meanComplement, map_sub]
  rfl

omit [Fintype ι] in
/-- The abstract identity behind the error identity. -/
theorem abstract_error_identity (A B Bc : TorusHk 0 E') (c : E')
    (hA : meanComplement 0 A = A - torusConstantCarrier 0 c) :
    A - (torusConstantCarrier 0 c + meanComplement 0 (B - Bc)) =
      meanComplement 0 (A - B) - meanComplement 0 (torusConstantCarrier 0 c - Bc) := by
  simp only [map_sub, hA, meanComplement_constant]
  abel

omit [Fintype ι] in
/-- **The error identity at the order zero.** -/
theorem normOp_error_identity (Kw Kh : ℕ) (K : ι → ℕ) (hK : ∀ v, K v ≤ Kw)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v)))
    (X : ∀ v, TorusHk Kw (h v)) (U : ∀ v, TorusHk (K v) (h v))
    (hU : ∀ v, torusMean (U v) = torusMean (X v)) (v : ι) :
    truncateTorusHk (Nat.zero_le (K v)) (U v) -
        truncateTorusHk (Nat.zero_le Kh) (normOp Kw Kh K hK Tm X v) =
      meanComplement 0 (truncateTorusHk (Nat.zero_le (K v)) (U v) -
          truncateTorusHk (Nat.zero_le (max Kh (K v))) (Tm (fun u => truncateTorusHk (Nat.zero_le (K u)) (truncateTorusHk (hK u) (X u))) v)) -
        meanComplement 0 (torusConstantCarrier 0 (torusMean (X v)) -
          truncateTorusHk (Nat.zero_le (max Kh (K v))) (Tm (fun u => truncateTorusHk (Nat.zero_le (K u)) (torusConstantCarrier (K u) (torusMean (X u)))) v)) := by
  have hA : meanComplement 0 (truncateTorusHk (Nat.zero_le (K v)) (U v)) =
      truncateTorusHk (Nat.zero_le (K v)) (U v) - torusConstantCarrier 0 (torusMean (X v)) := by
    rw [meanComplement_apply, torusMean_truncate, hU v]
  rw [trunc0_normOp_split Kw Kh K hK Tm X v]
  exact abstract_error_identity _ _ _ _ hA

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The order-zero mass norm at radius one is at most the full mass norm at any radius. -/
theorem massNormSq_trunc0_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (ρ : ℝ)
    (e : ∀ v, TorusHk (K v) (h v)) :
    massNormSq (E := h) (K := fun _ => 0) 1 π
        (fun v => (truncateTorusHk (Nat.zero_le (K v)) (e v)).val) ≤
      massNormSq (E := h) (K := K) ρ π (fun v => (e v).val) :=
  Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
    ((factorialNormSq_zero_radius 1 ρ _).le.trans
      (CycleComparison.Error.factorialNormSq_truncateTorusHk_le _ ρ (e v)))
    (inv_nonneg.2 (hπ v).le)

/-- The mass norm of a difference of mean-free parts. -/
theorem complement_sub_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (a b : ∀ v, TorusHk 0 (h v)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π
        (fun v => (meanComplement 0 (a v) - meanComplement 0 (b v)).val)) ≤
      2 * Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π (fun v => (a v).val)) +
        2 * Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π (fun v => (b v).val)) := by
  rw [← massWeightedCarrierCLM_norm (E := h) (fun _ => 0) 1 π hπ
    (fun v => meanComplement 0 (a v) - meanComplement 0 (b v))]
  have hs : (fun v => meanComplement 0 (a v) - meanComplement 0 (b v)) =
      (fun v => meanComplement 0 (a v)) - fun v => meanComplement 0 (b v) := rfl
  rw [hs, (massWeightedCarrierCLM (E := h) (fun _ => 0) 1 π).map_sub]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [massWeightedCarrierCLM_norm (E := h) (fun _ => 0) 1 π hπ]
    exact meanComplement_mass_le (fun _ => 0) 1 π hπ a
  · rw [massWeightedCarrierCLM_norm (E := h) (fun _ => 0) 1 π hπ]
    exact meanComplement_mass_le (fun _ => 0) 1 π hπ b

end AVRegularity.EntryTerminal.Ingredients
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs AVRegularity.CycleJointProofs.Assembly
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The error bound of the normalized map** (E2, `PrepNormPart`). Combine the error identity
with the raw error of the datum `f₀ = trunc_K X`, the raw error of its constant part, and
`‖Q₀ a‖ ≤ 2‖a‖`. The order-zero error at `t_p` is at most `4 C_P E^P (∑ π⁻¹ ‖f₀‖²_{ρ_old})^{1/2}`.

Special cases:
- `X` constant: both raw errors are those of constants.
- `C_P = 0`: the error vanishes. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The order-zero part of a raw error is controlled by the raw error. -/
theorem trunc0_rawError_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (Kh : ℕ) (ρs : ℝ)
    (U : ∀ v, TorusHk (K v) (h v)) (Y : ∀ v, TorusHk (max Kh (K v)) (h v)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π
        (fun v => (truncateTorusHk (Nat.zero_le (K v)) (U v) -
          truncateTorusHk (Nat.zero_le (max Kh (K v))) (Y v)).val)) ≤
      Real.sqrt (massNormSq (E := h) (K := K) ρs π
        (fun v => (U v - truncateTorusHk (le_max_right Kh (K v)) (Y v)).val)) := by
  have he : (fun v => (truncateTorusHk (Nat.zero_le (K v)) (U v) -
      truncateTorusHk (Nat.zero_le (max Kh (K v))) (Y v)).val) =
      fun v => (truncateTorusHk (Nat.zero_le (K v))
        (U v - truncateTorusHk (le_max_right Kh (K v)) (Y v))).val := by
    funext v
    rw [(truncateTorusHk (E := h v) (Nat.zero_le (K v))).map_sub]
    rfl
  exact (congrArg (fun F => Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π F)) he).trans_le
    (Real.sqrt_le_sqrt (massNormSq_trunc0_le π hπ K ρs _))

/-- The raw error of the datum `trunc_K X`. -/
theorem rawError_datum (π : ι → ℝ) (K : ι → ℕ) {Kw Kh : ℕ} (hK : ∀ v, K v ≤ Kw)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v))) {D : ℕ}
    {ν tS tp ρs ρold E Pacc CP : ℝ} {b : ℝ → Vec 2 → Vec 2}
    {A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i))}
    (herr : IsRawMassError π K Kh D ν tS tp ρs ρold E Pacc CP b A Tm)
    (X : ∀ v, TorusHk Kw (h v)) (u : ∀ v, ℝ → TorusHk (K v) (h v))
    (w : ∀ v, ℝ → TorusHk (K v + 1) (h v))
    (hu : IsCoupledWeakSolutionTorus ν tS tp b D K A (fun v => truncateTorusHk (hK v) (X v))
      (fun _ _ => 0) (fun _ _ => 0) u w) :
    Real.sqrt (massNormSq (E := h) (K := K) ρs π
      (fun v => (u v tp - truncateTorusHk (le_max_right Kh (K v)) (Tm (fun u => truncateTorusHk (Nat.zero_le (K u)) (truncateTorusHk (hK u) (X u))) v)).val)) ≤
      CP * E ^ Pacc * Real.sqrt (∑ v, (π v)⁻¹ *
        torusHkNorm ρold (le_refl (K v)) (truncateTorusHk (hK v) (X v)) ^ 2) :=
  herr (fun v => truncateTorusHk (hK v) (X v))
    (fun v => torusHkNorm ρold (le_refl (K v)) (truncateTorusHk (hK v) (X v)))
    (fun _ => le_rfl) u w hu

/-- The raw error of the constant part of the datum. -/
theorem rawError_constant (π : ι → ℝ) (K : ι → ℕ) {Kw Kh : ℕ} (hK : ∀ v, K v ≤ Kw)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v))) {D : ℕ}
    {ν tS tp ρs ρold E Pacc CP : ℝ} {b : ℝ → Vec 2 → Vec 2}
    {A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i))}
    (herr : IsRawMassError π K Kh D ν tS tp ρs ρold E Pacc CP b A Tm)
    (X : ∀ v, TorusHk Kw (h v)) :
    Real.sqrt (massNormSq (E := h) (K := K) ρs π
      (fun v => (torusConstantCarrier (K v) (torusMean (X v)) -
        truncateTorusHk (le_max_right Kh (K v)) (Tm (fun u => truncateTorusHk (Nat.zero_le (K u)) (torusConstantCarrier (K u) (torusMean (X u)))) v)).val)) ≤
      CP * E ^ Pacc * Real.sqrt (∑ v, (π v)⁻¹ *
        torusHkNorm ρold (le_refl (K v)) (truncateTorusHk (hK v) (X v)) ^ 2) := by
  have hfc : ∀ v, torusHkNorm ρold (le_refl (K v))
      (torusConstantCarrier (K v) (torusMean (X v))) ≤
        torusHkNorm ρold (le_refl (K v)) (truncateTorusHk (hK v) (X v)) := by
    intro v
    rw [torusHkNorm_constant]
    exact torusMean_norm_le ρold (le_refl (K v)) (truncateTorusHk (hK v) (X v))
  exact herr (fun v => torusConstantCarrier (K v) (torusMean (X v)))
    (fun v => torusHkNorm ρold (le_refl (K v)) (truncateTorusHk (hK v) (X v))) hfc
    (fun v _ => torusConstantCarrier (K v) (torusMean (X v)))
    (fun v _ => torusConstantCarrier (K v + 1) (torusMean (X v)))
    (torusConstantCoupledSolution K D ν tS tp b A fun v => torusMean (X v))

/-- **The error bound of the normalized map.** -/
theorem normOp_error_bound (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) {Kw Kh : ℕ}
    (hK : ∀ v, K v ≤ Kw)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v))) {D : ℕ}
    {ν tS tp ρs ρold E Pacc CP : ℝ} {b : ℝ → Vec 2 → Vec 2}
    {A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i))}
    (herr : IsRawMassError π K Kh D ν tS tp ρs ρold E Pacc CP b A Tm)
    (X : ∀ v, TorusHk Kw (h v)) (u : ∀ v, ℝ → TorusHk (K v) (h v))
    (w : ∀ v, ℝ → TorusHk (K v + 1) (h v))
    (hu : IsCoupledWeakSolutionTorus ν tS tp b D K A (fun v => truncateTorusHk (hK v) (X v))
      (fun _ _ => 0) (fun _ _ => 0) u w)
    (hU : ∀ v, torusMean (u v tp) = torusMean (X v)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π
        (fun v => (truncateTorusHk (Nat.zero_le (K v)) (u v tp) -
          truncateTorusHk (Nat.zero_le Kh) (normOp Kw Kh K hK Tm X v)).val)) ≤
      4 * (CP * E ^ Pacc * Real.sqrt (∑ v, (π v)⁻¹ *
        torusHkNorm ρold (le_refl (K v)) (truncateTorusHk (hK v) (X v)) ^ 2)) := by
  have hfun : (fun v => (truncateTorusHk (Nat.zero_le (K v)) (u v tp) -
      truncateTorusHk (Nat.zero_le Kh) (normOp Kw Kh K hK Tm X v)).val) =
      fun v => (meanComplement 0 (truncateTorusHk (Nat.zero_le (K v)) (u v tp) -
          truncateTorusHk (Nat.zero_le (max Kh (K v))) (Tm (fun u => truncateTorusHk (Nat.zero_le (K u)) (truncateTorusHk (hK u) (X u))) v)) -
        meanComplement 0 (torusConstantCarrier 0 (torusMean (X v)) -
          truncateTorusHk (Nat.zero_le (max Kh (K v))) (Tm (fun u => truncateTorusHk (Nat.zero_le (K u)) (torusConstantCarrier (K u) (torusMean (X u)))) v))).val :=
    funext fun v => congrArg Subtype.val
      (normOp_error_identity Kw Kh K hK Tm X (fun v => u v tp) hU v)
  refine (le_of_eq (congrArg (fun F => Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π F))
    hfun)).trans ((complement_sub_le π hπ _ _).trans ?_)
  have h1 := trunc0_rawError_le π hπ K Kh ρs (fun v => u v tp) (Tm (fun u => truncateTorusHk (Nat.zero_le (K u)) (truncateTorusHk (hK u) (X u))))
  have h2 := trunc0_rawError_le π hπ K Kh ρs
    (fun v => torusConstantCarrier (K v) (torusMean (X v))) (Tm (fun u => truncateTorusHk (Nat.zero_le (K u)) (torusConstantCarrier (K u) (torusMean (X u)))))
  have hc0 : (fun v => (torusConstantCarrier 0 (torusMean (X v)) -
      truncateTorusHk (Nat.zero_le (max Kh (K v))) (Tm (fun u => truncateTorusHk (Nat.zero_le (K u)) (torusConstantCarrier (K u) (torusMean (X u)))) v)).val) =
      fun v => (truncateTorusHk (Nat.zero_le (K v))
        (torusConstantCarrier (K v) (torusMean (X v))) -
        truncateTorusHk (Nat.zero_le (max Kh (K v))) (Tm (fun u => truncateTorusHk (Nat.zero_le (K u)) (torusConstantCarrier (K u) (torusMean (X u)))) v)).val := by
    funext v
    rw [torusConstantCarrier_truncate]
  have h2' := le_trans (le_of_eq (congrArg (fun F => Real.sqrt (massNormSq (E := h)
    (K := fun _ => 0) 1 π F)) hc0)) h2
  linarith [h1.trans (rawError_datum π K hK Tm herr X u w hu),
    h2'.trans (rawError_constant π K hK Tm herr X)]

end AVRegularity.EntryTerminal.Ingredients
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs AVRegularity.CycleJointProofs.Assembly
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The model bound of the normalized map** (E2, `PrepNormPart`). At a radius `ρ ≤ A ρ_m`
(`A ≥ 1`), where `ρ_m` is the radius of the raw model bound `‖T_m f‖_{ρ_m} ≤ C_R ‖f‖`:
- the constant part costs `‖Π₀ X‖ ≤ ‖trunc₀ X‖`;
- each raw model costs `A^{K_h} C_R`, with the data `trunc₀ X` and its constant part, of norm at
  most `‖trunc₀ X‖`;
- `Q₀` costs `2`.
Hence `‖P X‖_ρ ≤ (1 + 4 A^{K_h} C_R) ‖trunc₀ X‖`. The data norms are at most the norms at any
radius.

Special cases:
- `C_R = 0` (`T_m = 0`): `P = Π₀` and the bound is `‖Π₀ X‖ ≤ ‖trunc₀ X‖`.
- `X` constant: `P X = X` and the bound holds with the factor `1`.
- `A = 1`: `ρ ≤ ρ_m`, with no radius cost. -/

section
attribute [local instance] prepNormOpTorusNormed prepNormOpTorusInner prepNormOpTorusSpace
  prepNormOpTorusPiAdd prepNormOpTorusPiModule

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The constant part: `‖Π₀ X‖_ρ ≤ ‖g‖` for any order-zero `g` with the means of `X`. -/
theorem constPart_mass_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i) {Kw : ℕ} (Kh : ℕ) (ρ : ℝ)
    (X : ∀ v, TorusHk Kw (h v)) (g : ∀ v, TorusHk 0 (h v))
    (hg : ∀ v, torusMean (g v) = torusMean (X v)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => Kh) ρ π
        (fun v => (torusConstantCarrier Kh (torusMean (X v))).val)) ≤
      Real.sqrt (∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (g u) ^ 2) := by
  unfold massNormSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_
    (inv_nonneg.2 (hπ v).le))
  rw [constant_factorialNormSq, ← hg v]
  exact pow_le_pow_left₀ (norm_nonneg _) (torusMean_norm_le 1 (le_refl 0) (g v)) 2

/-- The constant datum is no larger than any datum with the same means. -/
theorem constData_norm_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) {Kw : ℕ}
    (X : ∀ v, TorusHk Kw (h v)) (g gc : ∀ v, TorusHk 0 (h v))
    (hgc : gc = fun u => truncateTorusHk (Nat.zero_le (K u))
      (torusConstantCarrier (K u) (torusMean (X u))))
    (hg : ∀ v, torusMean (g v) = torusMean (X v)) :
    Real.sqrt (∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (gc u) ^ 2) ≤
      Real.sqrt (∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (g u) ^ 2) := by
  subst hgc
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_
    (inv_nonneg.2 (hπ u).le))
  beta_reduce
  rw [torusConstantCarrier_truncate, torusHkNorm_constant, ← hg u]
  exact pow_le_pow_left₀ (norm_nonneg _) (torusMean_norm_le 1 (le_refl 0) (g u)) 2

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- One raw model at the radius `ρ ≤ A ρ_m`. -/
theorem tmPart_mass_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (Kh : ℕ)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v)))
    {ρ ρm A CR : ℝ} (hρ : 0 ≤ ρ) (hA : 1 ≤ A) (hρA : ρ ≤ A * ρm) (hCR : 0 ≤ CR)
    (hmod : IsRawMassModel π K Kh ρm CR Tm) (f : ∀ u, TorusHk 0 (h u)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => Kh) ρ π
        (fun v => (truncateTorusHk (le_max_left Kh (K v)) (Tm f v)).val)) ≤
      A ^ Kh * CR * Real.sqrt (∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (f u) ^ 2) := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hs : massNormSq (E := h) (K := fun _ => Kh) ρ π
      (fun v => (truncateTorusHk (le_max_left Kh (K v)) (Tm f v)).val) ≤
      (A ^ Kh * CR) ^ 2 * ∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (f u) ^ 2 := by
    calc massNormSq (E := h) (K := fun _ => Kh) ρ π
          (fun v => (truncateTorusHk (le_max_left Kh (K v)) (Tm f v)).val)
        ≤ ∑ v, (π v)⁻¹ * (A ^ (2 * Kh) *
            torusHkNorm ρm (le_max_left Kh (K v)) (Tm f v) ^ 2) := by
          unfold massNormSq
          refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_
            (inv_nonneg.2 (hπ v).le)
          rw [torusHkNorm, Real.sq_sqrt (factorialNormSq_nonneg _ _)]
          exact (factorialNormSq_mono_radius hρ hρA _).trans
            (Construction.Preservation.FullLift.factorialNormSq_mul_radius_le hA ρm _)
      _ = A ^ (2 * Kh) * ∑ v, (π v)⁻¹ * torusHkNorm ρm (le_max_left Kh (K v)) (Tm f v) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ A ^ (2 * Kh) * (CR ^ 2 * ∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (f u) ^ 2) :=
          mul_le_mul_of_nonneg_left (hmod f) (by positivity)
      _ = (A ^ Kh * CR) ^ 2 * ∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (f u) ^ 2 := by
          rw [pow_mul]
          ring
  calc _ ≤ Real.sqrt ((A ^ Kh * CR) ^ 2 *
        ∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (f u) ^ 2) := Real.sqrt_le_sqrt hs
    _ = A ^ Kh * CR * Real.sqrt (∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (f u) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- The mean-free part `Q₀ trunc (T_m f - T_m f_c)`. -/
theorem compPart_mass_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (Kh : ℕ)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v)))
    {ρ ρm A CR : ℝ} (hρ : 0 ≤ ρ) (hA : 1 ≤ A) (hρA : ρ ≤ A * ρm) (hCR : 0 ≤ CR)
    (hmod : IsRawMassModel π K Kh ρm CR Tm) (f fc : ∀ u, TorusHk 0 (h u)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => Kh) ρ π
        (fun v => (meanComplement Kh
          (truncateTorusHk (le_max_left Kh (K v)) (Tm f v - Tm fc v))).val)) ≤
      2 * (A ^ Kh * CR * Real.sqrt (∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (f u) ^ 2) +
        A ^ Kh * CR * Real.sqrt (∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (fc u) ^ 2)) := by
  refine (meanComplement_mass_le (fun _ => Kh) ρ π hπ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [← massWeightedCarrierCLM_norm (E := h) (fun _ => Kh) ρ π hπ]
  have hs : (fun v => truncateTorusHk (le_max_left Kh (K v)) (Tm f v - Tm fc v)) =
      (fun v => truncateTorusHk (le_max_left Kh (K v)) (Tm f v)) -
        fun v => truncateTorusHk (le_max_left Kh (K v)) (Tm fc v) := by
    funext v
    exact (truncateTorusHk (E := h v) (le_max_left Kh (K v))).map_sub _ _
  rw [hs, (massWeightedCarrierCLM (E := h) (fun _ => Kh) ρ π).map_sub]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [massWeightedCarrierCLM_norm (E := h) (fun _ => Kh) ρ π hπ]
    exact tmPart_mass_le π hπ K Kh Tm hρ hA hρA hCR hmod f
  · rw [massWeightedCarrierCLM_norm (E := h) (fun _ => Kh) ρ π hπ]
    exact tmPart_mass_le π hπ K Kh Tm hρ hA hρA hCR hmod fc

/-- Combination of the constant part and the mean-free part. -/
theorem model_combine {a b N Nc Nx AC : ℝ} (hAC : 0 ≤ AC) (h1 : a ≤ N)
    (h2 : b ≤ 2 * (AC * N + AC * Nc)) (h3 : Nc ≤ N) (hN : N ≤ Nx) :
    a + b ≤ (1 + 4 * AC) * Nx := by
  have h4 := mul_le_mul_of_nonneg_left h3 hAC
  have h5 := mul_le_mul_of_nonneg_left hN (by linarith : (0 : ℝ) ≤ 1 + 4 * AC)
  linarith

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The order-zero data norm is at most the norm at any radius. -/
theorem dataNorm_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) {Kw : ℕ}
    (hK : ∀ v, K v ≤ Kw) (ρ : ℝ) (X : ∀ v, TorusHk Kw (h v)) (g : ∀ v, TorusHk 0 (h v))
    (hgd : g = fun u => truncateTorusHk (Nat.zero_le (K u)) (truncateTorusHk (hK u) (X u))) :
    Real.sqrt (∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (g u) ^ 2) ≤
      Real.sqrt (massNormSq (E := h) (K := fun _ => Kw) ρ π (fun v => (X v).val)) := by
  subst hgd
  unfold massNormSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_
    (inv_nonneg.2 (hπ u).le))
  rw [torusHkNorm, Real.sq_sqrt (factorialNormSq_nonneg _ _)]
  calc _ ≤ factorialNormSq 1 (truncateTorusHk (Nat.zero_le (K u))
        (truncateTorusHk (hK u) (X u))).val :=
        CycleComparison.Error.factorialNormSq_truncateTorusHk_le _ 1 _
    _ = factorialNormSq ρ (truncateTorusHk (Nat.zero_le (K u))
        (truncateTorusHk (hK u) (X u))).val := factorialNormSq_zero_radius 1 ρ _
    _ ≤ factorialNormSq ρ (truncateTorusHk (hK u) (X u)).val :=
        CycleComparison.Error.factorialNormSq_truncateTorusHk_le _ ρ _
    _ ≤ factorialNormSq ρ (X u).val :=
        CycleComparison.Error.factorialNormSq_truncateTorusHk_le _ ρ _

/-- **The model bound of the normalized map**, against the datum's norm at any radius `ρ'`. -/
theorem normOp_model_bound (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) {Kw Kh : ℕ}
    (hK : ∀ v, K v ≤ Kw)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v)))
    {ρ ρm A CR : ℝ} (hρ : 0 ≤ ρ) (hA : 1 ≤ A) (hρA : ρ ≤ A * ρm) (hCR : 0 ≤ CR)
    (hmod : IsRawMassModel π K Kh ρm CR Tm) (ρ' : ℝ) (X : ∀ v, TorusHk Kw (h v)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => Kh) ρ π
        (fun v => (normOp Kw Kh K hK Tm X v).val)) ≤
      (1 + 4 * (A ^ Kh * CR)) *
        Real.sqrt (massNormSq (E := h) (K := fun _ => Kw) ρ' π (fun v => (X v).val)) := by
  obtain ⟨g, hgd⟩ : ∃ g : ∀ u, TorusHk 0 (h u),
      g = fun u => truncateTorusHk (Nat.zero_le (K u)) (truncateTorusHk (hK u) (X u)) :=
    ⟨_, rfl⟩
  obtain ⟨gc, hgcd⟩ : ∃ gc : ∀ u, TorusHk 0 (h u),
      gc = fun u => truncateTorusHk (Nat.zero_le (K u))
        (torusConstantCarrier (K u) (torusMean (X u))) := ⟨_, rfl⟩
  have hg : ∀ v, torusMean (g v) = torusMean (X v) := fun v => by
    rw [hgd, torusMean_truncate, torusMean_truncate]
  have hsplit : normOp Kw Kh K hK Tm X =
      (fun v => torusConstantCarrier Kh (torusMean (X v))) + fun v => meanComplement Kh
        (truncateTorusHk (le_max_left Kh (K v)) (Tm g v - Tm gc v)) := by
    subst hgd hgcd
    exact funext fun v => normOp_apply_lam Kw Kh K hK Tm X v
  rw [← massWeightedCarrierCLM_norm (E := h) (fun _ => Kh) ρ π hπ, hsplit,
    (massWeightedCarrierCLM (E := h) (fun _ => Kh) ρ π).map_add]
  refine (norm_add_le _ _).trans ?_
  rw [massWeightedCarrierCLM_norm (E := h) (fun _ => Kh) ρ π hπ,
    massWeightedCarrierCLM_norm (E := h) (fun _ => Kh) ρ π hπ]
  exact model_combine (mul_nonneg (pow_nonneg (zero_le_one.trans hA) _) hCR)
    (constPart_mass_le π hπ Kh ρ X g hg)
    (compPart_mass_le π hπ K Kh Tm hρ hA hρA hCR hmod g gc)
    (constData_norm_le π hπ K X g gc hgcd hg) (dataNorm_le π hπ K hK ρ' X g hgd)

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The prepared-datum norm of the raw error is at most the norm of the datum at that radius. -/
theorem errData_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) {Kw : ℕ}
    (hK : ∀ v, K v ≤ Kw) (ρ : ℝ) (X : ∀ v, TorusHk Kw (h v)) :
    Real.sqrt (∑ v, (π v)⁻¹ * torusHkNorm ρ (le_refl (K v)) (truncateTorusHk (hK v) (X v)) ^ 2) ≤
      Real.sqrt (massNormSq (E := h) (K := fun _ => Kw) ρ π (fun v => (X v).val)) := by
  unfold massNormSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_
    (inv_nonneg.2 (hπ u).le))
  rw [torusHkNorm, Real.sq_sqrt (factorialNormSq_nonneg _ _)]
  exact (CycleComparison.Error.factorialNormSq_truncateTorusHk_le _ ρ _).trans
    (CycleComparison.Error.factorialNormSq_truncateTorusHk_le _ ρ _)
end

/-! **The normalized map at one level, abstractly** (E2, `PrepNormPart`). For a datum `X`, a
solution `u` of the plain coupled system from `trunc_K X` with conserved means, and any `Y`:
`‖trunc₀ Y - trunc₀ P X‖ ≤ ‖trunc₀ Y - trunc₀ u(t_p)‖ + 4 C_P E^P ‖X‖_{ρ'}` for every radius
`ρ' ≥ ρ_old`. The scale arithmetic of the terminal schedule is in abstract-real lemmas:
`x^{χ_w + σ_w L_t} ≤ 2^{e₀} E^{Q_T}` from `x ≤ 2E^q` and `q e₀ > 2Q_T + 4`, and the radius
comparison `c_r s ≤ max 1 (c_r/c_R) · c_R s`.

Special cases:
- `Y = u(t_p)`: the first term vanishes.
- `C_P = 0`: the normalized map reproduces `u(t_p)` at the order zero.
- `x = E^q`, `e = e₀`: the scale bound is `E^{q e₀} ≤ 2^{e₀} E^{Q_T}`. -/

section
attribute [local instance] prepNormOpTorusNormed prepNormOpTorusInner prepNormOpTorusSpace
  prepNormOpTorusPiAdd prepNormOpTorusPiModule

/-- The scale step of the core clause: `x^e ≤ 2^{e₀} E^Q`. -/
theorem prepNorm_scale_le {x E q e e0 Q : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hE0 : 0 < E)
    (hE1 : E ≤ 1) (hxE : x ≤ 2 * E ^ q) (he0 : 0 ≤ e0) (hee : e0 ≤ e) (hQ : Q ≤ q * e0) :
    x ^ e ≤ 2 ^ e0 * E ^ Q := by
  calc x ^ e ≤ x ^ e0 := Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 he0 hee
    _ ≤ (2 * E ^ q) ^ e0 := Real.rpow_le_rpow hx0 hxE he0
    _ = 2 ^ e0 * E ^ (q * e0) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hE0.le _), ← Real.rpow_mul hE0.le]
    _ ≤ 2 ^ e0 * E ^ Q := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hE0 hE1 hQ) (Real.rpow_nonneg (by norm_num) _)

/-- The output radius against the model radius: `c_r s ≤ max 1 (c_r/c_R) · (c_R s)`. -/
theorem prepNorm_radius_le {cr cR s : ℝ} (hcR : 0 < cR) (hs : 0 ≤ s) :
    cr * s ≤ max 1 (cr / cR) * (cR * s) := by
  have hc : cr * s = cr / cR * (cR * s) := by field_simp
  rw [hc]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hcR.le hs)

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The triangle inequality of the order-zero mass norm. -/
theorem mass_sub_triangle (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (a b c : ∀ v, TorusHk 0 (h v)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π (fun v => (a v - c v).val)) ≤
      Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π (fun v => (a v - b v).val)) +
        Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π (fun v => (b v - c v).val)) := by
  rw [← massWeightedCarrierCLM_norm (E := h) (fun _ => 0) 1 π hπ (fun v => a v - c v),
    ← massWeightedCarrierCLM_norm (E := h) (fun _ => 0) 1 π hπ (fun v => a v - b v),
    ← massWeightedCarrierCLM_norm (E := h) (fun _ => 0) 1 π hπ (fun v => b v - c v)]
  have hs : (fun v => a v - c v) = (fun v => a v - b v) + fun v => b v - c v := by
    funext v
    exact (sub_add_sub_cancel (a v) (b v) (c v)).symm
  rw [hs, (massWeightedCarrierCLM (E := h) (fun _ => 0) 1 π).map_add]
  exact norm_add_le _ _

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The mass norm grows with the radius. -/
theorem massNorm_mono_radius (π : ι → ℝ) (hπ : ∀ i, 0 < π i) {K : ℕ} {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r ≤ R) (X : ∀ v, TorusHk K (h v)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => K) r π (fun v => (X v).val)) ≤
      Real.sqrt (massNormSq (E := h) (K := fun _ => K) R π (fun v => (X v).val)) := by
  unfold massNormSq
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
    (factorialNormSq_mono_radius hr hrR _) (inv_nonneg.2 (hπ v).le))

/-- **The total order-zero error of the normalized map.** -/
theorem normOp_error_total (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) {Kw Kh : ℕ}
    (hK : ∀ v, K v ≤ Kw)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v))) {D : ℕ}
    {ν tS tp ρs ρold E Pacc CP : ℝ} {b : ℝ → Vec 2 → Vec 2}
    {A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i))}
    (herr : IsRawMassError π K Kh D ν tS tp ρs ρold E Pacc CP b A Tm)
    (hCP : 0 ≤ CP) (hE : 0 ≤ E ^ Pacc) {ρ' : ℝ} (hρ0 : 0 ≤ ρold) (hρ' : ρold ≤ ρ')
    (X : ∀ v, TorusHk Kw (h v)) (u : ∀ v, ℝ → TorusHk (K v) (h v))
    (w : ∀ v, ℝ → TorusHk (K v + 1) (h v))
    (hu : IsCoupledWeakSolutionTorus ν tS tp b D K A (fun v => truncateTorusHk (hK v) (X v))
      (fun _ _ => 0) (fun _ _ => 0) u w)
    (hU : ∀ v, torusMean (u v tp) = torusMean (X v)) (Y : ∀ v, TorusHk Kw (h v)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π
        (fun v => (truncateTorusHk (Nat.zero_le Kw) (Y v) -
          truncateTorusHk (Nat.zero_le Kh) (normOp Kw Kh K hK Tm X v)).val)) ≤
      Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π
        (fun v => (truncateTorusHk (Nat.zero_le Kw) (Y v) -
          truncateTorusHk (Nat.zero_le (K v)) (u v tp)).val)) +
        4 * (CP * E ^ Pacc *
          Real.sqrt (massNormSq (E := h) (K := fun _ => Kw) ρ' π (fun v => (X v).val))) := by
  refine (mass_sub_triangle π hπ _
    (fun v => truncateTorusHk (Nat.zero_le (K v)) (u v tp)) _).trans (add_le_add le_rfl ?_)
  refine (normOp_error_bound π hπ K hK Tm herr X u w hu hU).trans ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCP hE))
    (by norm_num)
  exact (errData_le π hπ K hK ρold X).trans (massNorm_mono_radius π hπ hρ0 hρ' X)
end

end AVRegularity.EntryTerminal.Ingredients
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs AVRegularity.CycleJointProofs.Assembly
open AVRegularity.EntryTerminal.Route
namespace AVRegularity.EntryTerminal.Ingredients

/-! **`PrepNormPart`** (the normalization `Π₀ + Q₀ T_m Q₀`). From the conclusion of the family
model bound for the weak family (`T_m` with the model bound at `c_R √(Bh)` and the raw error at `ϱ ≤ c_K x`), the
map `P = normOp T_m` fixes constants and, for every paired datum with the core clause:
- the model bound at `ρ_T = c_r √(Bh) ≤ max{1, c_r/c_R} c_R √(Bh)`:
  `‖P V(a_M)‖ ≤ (1 + 4 A^{K_h} C_R) ‖V(a_M)‖_{c_K x} ≤ (1 + 4 A^{K_h} C_R) C_K ‖f‖`
  (the weak strong energy at `a_M ≤ a + T₀`);
- the error: `‖V(t_p) - P V(a_M)‖ ≤ ‖V(t_p) - u(t_p)‖ + 4 C_P E^{Q_T} ‖V(a_M)‖_{c_K x}`. The core
  clause gives `C_core x^{χ_w + σ_w L_t} ‖f‖ ≤ C_core 2^{e₀} E^{Q_T} ‖f‖`, with
  `e₀ = χ_w + σ_w L_p^T`, `x ≤ 2E^q` and `q e₀ > 2Q_T + 4`. The means are conserved
  (`meanConservation`).

Design note (elaboration cost): the conclusion of the family model bound is stated over a generic family, so the component
set of `Gw.mass` carries the normed-space structure of the inner product, while `Gw.fam`, the core
clause and the slots carry the one found for `ℝ`. Mixing the two around large `TorusHk` types is
expensive, so the bounds are proved over an abstract component set (`prepNorm_S`, one structure) and
applied once with `S := Gw.comps`; the generic-family lemma `prepNorm_pair_gen` is stated in `ι, h`
like the family model bound.

A constant datum is fixed by `P` (`normOp_fixes_constants`). If `c_r ≤ c_R` then `A = 1` and there
is no radius cost. If `C_core ≤ 0`, the core term is bounded with `max C_core 0`. -/

attribute [local instance] prepNormOpTorusNormed prepNormOpTorusInner prepNormOpTorusSpace
  prepNormOpTorusPiAdd prepNormOpTorusPiModule

/-- The schedule facts used by the normalization. -/
theorem prepNorm_schedule {X : TermConstruction} {PA : PrepArgs X} (hPA : PA.Valid) :
    0 < PA.σw ∧ 0 ≤ PA.χw + PA.σw * PA.LpT ∧ PA.QT ≤ X.q * (PA.χw + PA.σw * PA.LpT) := by
  obtain ⟨-, -, -, ⟨-, -, -, -, hσ, -, hχ, -, -⟩, hPT, hS⟩ := hPA
  obtain ⟨-, hQ, -, -, -, -, -, -, -, -, -, -, -, hqe⟩ := hS
  have hq0 : 0 < X.q := zero_lt_one.trans X.hq.1
  have hpow : 0 ≤ X.q ^ (PA.Jw + 1) * (1 + X.s) :=
    mul_nonneg (pow_nonneg hq0.le _) (by linarith [X.hs₀])
  exact ⟨hσ, add_nonneg hχ.le (mul_nonneg hσ.le (Nat.cast_nonneg _)), by linarith⟩

/-- The arithmetic of the model bound. -/
theorem prepNorm_model_arith {B CK' F R N : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) (hF : 0 ≤ F)
    (hN : N ≤ CK' * F) : B * N ≤ (B * CK' + R) * F := by
  have h1 := mul_le_mul_of_nonneg_left hN hB
  have h2 := mul_nonneg hR hF
  have e : (B * CK' + R) * F = B * (CK' * F) + R * F := by ring
  rw [e]
  linarith

/-- The arithmetic of the error bound. -/
theorem prepNorm_err_arith {t s1 W Cc P2 EQ F CP CK' Cmod : ℝ}
    (hEQ : 0 ≤ EQ) (hF : 0 ≤ F) (hCP : 0 ≤ CP) (hCmod : 0 ≤ Cmod)
    (ht : t ≤ s1 + 4 * (CP * EQ * W)) (hs1 : s1 ≤ Cc * (P2 * EQ) * F) (hW : W ≤ CK' * F) :
    t ≤ (Cmod + (Cc * P2 + 4 * CP * CK')) * EQ * F := by
  have h1 : CP * EQ * W ≤ CP * EQ * (CK' * F) := mul_le_mul_of_nonneg_left hW (mul_nonneg hCP hEQ)
  have h2 : 0 ≤ Cmod * EQ * F := mul_nonneg (mul_nonneg hCmod hEQ) hF
  have e : (Cmod + (Cc * P2 + 4 * CP * CK')) * EQ * F =
      Cmod * EQ * F + Cc * (P2 * EQ) * F + 4 * (CP * EQ * (CK' * F)) := by ring
  rw [e]
  linarith

/-- The core term: `C_core x^{χ_w + σ_w L_t} ≤ max{C_core, 0} 2^{e₀} E^{Q_T}`. -/
theorem prepNorm_core_scale {s Cc x E q e e0 Q F : ℝ} (hF : 0 ≤ F) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hE0 : 0 < E) (hE1 : E ≤ 1) (hxE : x ≤ 2 * E ^ q) (he0 : 0 ≤ e0) (hee : e0 ≤ e)
    (hQ : Q ≤ q * e0) (hs : s ≤ Cc * x ^ e * F) :
    s ≤ max Cc 0 * (2 ^ e0 * E ^ Q) * F := by
  have hxe : 0 ≤ x ^ e := Real.rpow_nonneg hx0 _
  refine hs.trans (mul_le_mul_of_nonneg_right ?_ hF)
  exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hxe).trans
    (mul_le_mul_of_nonneg_left (prepNorm_scale_le hx0 hx1 hE0 hE1 hxE he0 hee hQ)
      (le_max_right _ _))

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The weighted norm with unit weights is the square root of the mass norm. -/
theorem weightedNorm_one_eq {S : Finset Comp} {k : ℕ} (ρ : ℝ) (π : CompIn S → ℝ)
    (X : ∀ v : CompIn S, TorusHk k (hr v.1.root)) :
    weightedNorm ρ π (fun _ => 1) X = Real.sqrt (massNormSq
      (E := fun v : CompIn S => hr v.1.root) (K := fun _ => k) ρ π (fun v => (X v).val)) := by
  unfold weightedNorm
  simp only [one_pow, div_one]

end Generic

section GenericFamily

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- **Both bounds at one level, for a generic family** (the form of the family model bound): from the raw model, the raw
error, the solution `u` from `trunc_K X`, the datum bound at `ρ'` and the core bound. -/
theorem prepNorm_pair_gen (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) {Kw Kh D' : ℕ}
    (hK : ∀ v, K v ≤ Kw)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Kh (K v)) (h v)))
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    {ν aM tp tp' ϱ ρm ρ ρ' E E' x QT CP CR A CK' Cc F q e e0 : ℝ}
    {Acoef : ∀ (i i' : ι) (d : admissibleOrders K D' i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i))}
    (hmod : IsRawMassModel π K Kh ρm CR Tm)
    (herr : IsRawMassError π K Kh D' ν aM tp ϱ ϱ E QT CP (streamVel φ) Acoef Tm)
    (X Y : ∀ v, TorusHk Kw (h v))
    (u : ∀ v, ℝ → TorusHk (K v) (h v)) (w : ∀ v, ℝ → TorusHk (K v + 1) (h v))
    (hu : IsCoupledWeakSolutionTorus ν aM tp (streamVel φ) D' K Acoef
      (fun v => truncateTorusHk (hK v) (X v)) (fun _ _ => 0) (fun _ _ => 0) u w)
    (haE : aM ≤ tp) (htp : tp' = tp) (hEE : E' = E)
    (hρ : 0 ≤ ρ) (hA : 1 ≤ A) (hρA : ρ ≤ A * ρm) (hCR : 0 ≤ CR) (hCP : 0 ≤ CP) (hCK : 0 ≤ CK')
    (hF : 0 ≤ F) (hϱ : 0 < ϱ) (hϱ' : ϱ ≤ ρ')
    (hV : Real.sqrt (massNormSq (E := h) (K := fun _ => Kw) ρ' π (fun v => (X v).val)) ≤ CK' * F)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hE0 : 0 < E') (hE1 : E' ≤ 1) (hxE : x ≤ 2 * E' ^ q)
    (he0 : 0 ≤ e0) (hee : e0 ≤ e) (hQ : QT ≤ q * e0)
    (hcore : Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π
      (fun v => (truncateTorusHk (Nat.zero_le Kw) (Y v) -
        truncateTorusHk (Nat.zero_le (K v)) (u v tp')).val)) ≤ Cc * x ^ e * F) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => Kh) ρ π
        (fun v => (normOp Kw Kh K hK Tm X v).val)) ≤
        ((1 + 4 * (A ^ Kh * CR)) * CK' + (max Cc 0 * 2 ^ e0 + 4 * CP * CK')) * F ∧
      Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π
        (fun v => (truncateTorusHk (Nat.zero_le Kw) (Y v) -
          truncateTorusHk (Nat.zero_le Kh) (normOp Kw Kh K hK Tm X v)).val)) ≤
        ((1 + 4 * (A ^ Kh * CR)) * CK' + (max Cc 0 * 2 ^ e0 + 4 * CP * CK')) * E' ^ QT * F := by
  subst hEE htp
  have hR : 0 ≤ max Cc 0 * 2 ^ e0 + 4 * CP * CK' :=
    add_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (mul_nonneg (by norm_num) hCP) hCK)
  have hAC : 0 ≤ A ^ Kh * CR := mul_nonneg (pow_nonneg (zero_le_one.trans hA) _) hCR
  refine ⟨(normOp_model_bound π hπ K hK Tm hρ hA hρA hCR hmod ρ' X).trans
    (prepNorm_model_arith (by linarith) hR hF hV), ?_⟩
  have hmem : tp' ∈ Set.Icc aM tp' := ⟨haE, le_rfl⟩
  have hU : ∀ v, torusMean (u v tp') = torusMean (X v) := fun v => by
    rw [meanConservation φ hφ ν aM tp' D' K Acoef _ u w hu v tp' hmem, torusMean_truncate]
  exact prepNorm_err_arith (Real.rpow_nonneg hE0.le _) hF hCP (mul_nonneg (by linarith) hCK)
    (normOp_error_total π hπ K hK Tm herr hCP (Real.rpow_nonneg hE0.le _) hϱ.le hϱ' X u w hu hU Y)
    (prepNorm_core_scale hF hx0 hx1 hE0 hE1 hxE he0 hee hQ hcore) hV

end GenericFamily

/-- The datum at `a_M`: `‖V(a_M)‖_{c_K x} ≤ max{C_K, 0} ‖f‖` from the weak strong energy. -/
theorem prepNorm_datum {X : TermConstruction} {PA : PrepArgs X} {M Kw Lt : ℕ} {nW : ℕ+}
    {D : OCData} {j₀ : ℕ} {lawW : BirthLaw} {PW : ProvParams}
    {Gw : GenStage D ScalarH (termD0bar PA.NT PA.pT PA.DW PA.dW) PA.bw j₀} {a aM cK CK : ℝ}
    {f : Vec 2 → ℝ} {U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)}
    {U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root)}
    {Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root)}
    {Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar PA.NT PA.pT PA.DW PA.dW) - 1)
      (ScalarH u.1.root)}
    (hπ : ∀ v, 0 < Gw.mass lawW v) (haT : aM ≤ a + PA.T₀)
    (hpair : IsWeakPaired PW PA.φ₀ PA.hφ₀ lawW M Kw Lt nW a PA.T₀ PA.σw PA.χw cK CK f Gw aM U₀ U V
      Uw Vw Uk Vk) :
    weightedNorm (D.termRStar cK M) (Gw.mass lawW) (fun _ => 1) (fun v => V v aM) ≤
      max CK 0 * Real.sqrt (l2NormSq f) := by
  have hF : 0 ≤ Real.sqrt (l2NormSq f) := Real.sqrt_nonneg _
  have hVSE : strongEnergy (D.termRStar cK M) (D.κ M) (Gw.mass lawW) aM (a + PA.T₀) V Vw ≤
      ENNReal.ofReal (max CK 0 * Real.sqrt (l2NormSq f)) :=
    le_add_self.trans (hpair.2.2.2.1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hF)))
  have hsT : aM ∈ Set.Icc aM (a + PA.T₀) := ⟨le_rfl, haT⟩
  exact weightedNorm_le_of_strongEnergy hπ hsT (mul_nonneg (le_max_right _ _) hF) V Vw hVSE

/-- The scales and radii of one level. -/
theorem prepNorm_scales {X : TermConstruction} {Λ M : ℕ} {D : OCData} {cK cr ϱ : ℝ}
    (hDα : D.α = X.α) (hDq : D.q = X.q) (hDΛ : D.Λ = Λ) (hΛ : 128 ≤ Λ) (hM : 1 ≤ M)
    (hϱK : ϱ ≤ cK * ocEpsilon X.q Λ M) :
    0 < D.eps M ∧ D.eps M ≤ 1 ∧ 0 < D.eps (M - 1) ∧ D.eps (M - 1) ≤ 1 ∧
      D.eps M ≤ 2 * D.eps (M - 1) ^ X.q ∧ D.eps (M - 1) = ocEpsilon X.q Λ (M - 1) ∧
      ϱ ≤ D.termRStar cK M ∧
      D.termRho cr M = cr * Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q Λ M) := by
  have hepsM : D.eps M = ocEpsilon X.q Λ M := by simp only [OCData.eps, hDq, hDΛ]
  have hepsM1 : D.eps (M - 1) = ocEpsilon X.q Λ (M - 1) := by simp only [OCData.eps, hDq, hDΛ]
  obtain ⟨hε, hε1, -⟩ := Scales.epsilon_basic (m := M) X.hq.1 hΛ
  obtain ⟨hE, hE1, -⟩ := Scales.epsilon_basic (m := M - 1) X.hq.1 hΛ
  have hstep := Scales.epsilon_q_step X.hq.1 X.hq.2.1 hΛ hM
  have hrS : D.termRStar cK M = cK * ocEpsilon X.q Λ M := by
    simp only [OCData.termRStar, hepsM]
  have hρ : D.termRho cr M = cr * Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q Λ M) := by
    simp only [OCData.termRho, OCData.termB, OCData.termH, hDα, hDq, hDΛ]
  rw [hepsM, hepsM1, hrS, hρ]
  exact ⟨hε, hε1, hE, hE1, hstep, rfl, hϱK, rfl⟩

/-- The preparation window: `a_M ≤ t_p` and `a_M ≤ a + T₀` at late levels. -/
theorem prepNorm_times {h6J h a aM T₀ : ℝ} {l₀ : ℤ} (hh : 0 < h)
    (hhi : aM < ((l₀ : ℝ) + 1 / 2) * h) (haM2 : aM ≤ a + h6J) (h6 : h6J + 3 * h ≤ T₀) :
    aM ≤ a + T₀ ∧ aM ≤ ((l₀ : ℝ) + 3 / 2) * h := by
  have htp : ((l₀ : ℝ) + 3 / 2) * h = ((l₀ : ℝ) + 1 / 2) * h + h := by ring
  rw [htp]
  constructor <;> linarith

section IPForm

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

/-- `edgeCoefficient` with the normed-space structure of the inner product (the form of the family model bound's
conclusion, which is stated over inner product spaces). -/
abbrev edgeCoefficientIP {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (K : ι → ℕ) :=
  edgeCoefficient F ν e E actual K

end IPForm

/-- The coupled system of the core clause (whose scalar normed-space structure is the one found
for `ℝ`) is the coupled system of the conclusion of the family model bound (the one of the inner product). -/
theorem prepNorm_ip_bridge {S : Finset Comp} {D' : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily (CompIn S) (fun v => ScalarH v.1.root) D' P Ctx) (ν e E : ℝ)
    (actual : ∀ p, Ctx p) (K : CompIn S → ℕ) {t₀ t₁ : ℝ} {b : ℝ → Vec 2 → Vec 2}
    {f : ∀ v : CompIn S, TorusHk (K v) (ScalarH v.1.root)}
    {u : ∀ v : CompIn S, ℝ → TorusHk (K v) (ScalarH v.1.root)}
    {w : ∀ v : CompIn S, ℝ → TorusHk (K v + 1) (ScalarH v.1.root)}
    (hu : IsCoupledWeakSolutionTorus ν t₀ t₁ b D' K (edgeCoefficient F ν e E actual K) f
      (fun _ _ => 0) (fun _ _ => 0) u w) :
    IsCoupledWeakSolutionTorus ν t₀ t₁ b D' K (edgeCoefficientIP F ν e E actual K) f
      (fun _ _ => 0) (fun _ _ => 0) u w := hu

/-- **Both bounds over an abstract component set** (one instance world): from the conclusion of the family model bound for
a family `F` on `CompIn S`, the solution `u` of the core clause, the datum bound and the core bound. -/
theorem prepNorm_S {S : Finset Comp} (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v) (K : CompIn S → ℕ)
    {Kw Kh D' : ℕ} (hK : ∀ v, K v ≤ Kw) {P' : Type*} {Ctx : P' → Type*}
    (F : ChartedFamily (CompIn S) (fun c => ScalarH c.1.root) D' P' Ctx) (actual : ∀ p, Ctx p)
    (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream (Φ m)) (ν B aM : ℝ)
    (l₀ : ℤ) {QT CR CP cR ϱ ρ ρ' A CK' Cc F0 x e e0 E' tp' : ℝ}
    (hraw : RawJointAbsConclusion α q Λ QT Kh D' CR CP cR π K Φ m ν B aM l₀ F actual ϱ ϱ)
    (V : ∀ v : CompIn S, ℝ → TorusHk Kw (ScalarH v.1.root))
    (u : ∀ v : CompIn S, ℝ → TorusHk (K v) (ScalarH v.1.root))
    (w : ∀ v : CompIn S, ℝ → TorusHk (K v + 1) (ScalarH v.1.root))
    (hu : IsCoupledWeakSolutionTorus ν aM (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) (streamVel (Φ m))
      D' K (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (fun v => truncateTorusHk (hK v) (V v aM)) (fun _ _ => 0) (fun _ _ => 0) u w)
    (haE : aM ≤ ((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m)
    (htp : tp' = ((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) (hEE : E' = ocEpsilon q Λ (m - 1))
    (hρ : 0 ≤ ρ) (hA : 1 ≤ A) (hρA : ρ ≤ A * (cR * Real.sqrt (B * ocTauPP α q Λ m)))
    (hCR : 0 ≤ CR) (hCP : 0 ≤ CP) (hCK : 0 ≤ CK') (hF : 0 ≤ F0) (hϱ : 0 < ϱ) (hϱ' : ϱ ≤ ρ')
    (hV : weightedNorm ρ' π (fun _ => 1) (fun v => V v aM) ≤ CK' * F0)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hE0 : 0 < E') (hE1 : E' ≤ 1) (hxE : x ≤ 2 * E' ^ q)
    (he0 : 0 ≤ e0) (hee : e0 ≤ e) (hQ : QT ≤ q * e0)
    (hcore : weightedNorm 1 π (fun _ => 1) (fun v => truncateTorusHk (Nat.zero_le Kw) (V v tp') -
      truncateTorusHk (Nat.zero_le (K v)) (u v tp')) ≤ Cc * x ^ e * F0) :
    weightedNorm ρ π (fun _ => 1) (normOp Kw Kh K hK (Classical.choose hraw) fun v => V v aM) ≤
        ((1 + 4 * (A ^ Kh * CR)) * CK' + (max Cc 0 * 2 ^ e0 + 4 * CP * CK')) * F0 ∧
      weightedNorm 1 π (fun _ => 1) (fun v => truncateTorusHk (Nat.zero_le Kw) (V v tp') -
          truncateTorusHk (Nat.zero_le Kh) (normOp Kw Kh K hK (Classical.choose hraw)
            (fun v => V v aM) v)) ≤
        ((1 + 4 * (A ^ Kh * CR)) * CK' + (max Cc 0 * 2 ^ e0 + 4 * CP * CK')) * E' ^ QT * F0 := by
  have hp := prepNorm_pair_gen (h := fun c => ScalarH c.1.root) π hπ K hK (Classical.choose hraw)
    hφ (Classical.choose_spec hraw).1 (Classical.choose_spec hraw).2.2 (fun v => V v aM)
    (fun v => V v tp') u w
    (prepNorm_ip_bridge F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K hu) haE htp hEE
    hρ hA hρA hCR hCP hCK hF hϱ hϱ' ((weightedNorm_one_eq (hr := ScalarH) _ _ _).symm.trans_le hV)
    hx0 hx1 hE0 hE1 hxE he0 hee hQ
    ((weightedNorm_one_eq (hr := ScalarH) _ _ _).symm.trans_le hcore)
  exact ⟨(weightedNorm_one_eq (hr := ScalarH) _ _ _).trans_le hp.1,
    (weightedNorm_one_eq (hr := ScalarH) _ _ _).trans_le hp.2⟩

/-- The two bounds at one level, from the solution of the core clause and the datum bound. -/
theorem prepNorm_clauses2 {X : TermConstruction} (PA : PrepArgs X) (hΛ : 128 ≤ PA.Λ)
    (Kout Kw Lt : ℕ) (cr cK CK : ℝ) (CR CP cR Ccore : ℝ)
    (M : ℕ) (hM : 2 ≤ M) (hcr : 0 < cr) (hcR : 0 < cR) (hCR : 0 ≤ CR) (hCP : 0 ≤ CP)
    (hσ : 0 < PA.σw) (he0 : 0 ≤ PA.χw + PA.σw * PA.LpT)
    (hQe : PA.QT ≤ X.q * (PA.χw + PA.σw * PA.LpT)) (hLt : PA.LpT ≤ Lt)
    {D : OCData} (hDα : D.α = X.α) (hDq : D.q = X.q) (hDΛ : D.Λ = PA.Λ) {j₀ : ℕ}
    (lawW : BirthLaw)
    (Gw : GenStage D ScalarH (termD0bar PA.NT PA.pT PA.DW PA.dW) PA.bw j₀) (aM : ℝ)
    (K : CompIn Gw.comps → ℕ) (hK : ∀ v, K v ≤ Kw) (ϱ : ℝ) (hϱ : 0 < ϱ)
    (hϱK : ϱ ≤ cK * ocEpsilon X.q PA.Λ M)
    (hraw : RawJointAbsConclusion X.α X.q PA.Λ PA.QT
      (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2)))
      (termD0bar PA.NT PA.pT PA.DW PA.dW) CR CP cR (Gw.mass lawW) K D.Φ M (D.κ M) (D.κ (M - 1)) aM
      (prepBlock (ocTauPP X.α X.q PA.Λ M) aM) Gw.actualFamily (fun _ => ()) ϱ ϱ)
    (hπ : ∀ v, 0 < Gw.mass lawW v) (f : Vec 2 → ℝ)
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
    (u : ∀ v : CompIn Gw.comps, ℝ → TorusHk (K v) (ScalarH v.1.root))
    (w : ∀ v : CompIn Gw.comps, ℝ → TorusHk (K v + 1) (ScalarH v.1.root))
    (hu : IsCoupledWeakSolutionTorus (D.κ M) aM
      (((prepBlock (ocTauPP X.α X.q PA.Λ M) aM : ℝ) + 3 / 2) * ocTauPP X.α X.q PA.Λ M)
      (streamVel (D.Φ M)) (termD0bar PA.NT PA.pT PA.DW PA.dW) K
      (edgeCoefficient Gw.fam (D.κ M) (ocEpsilon X.q PA.Λ M) (ocEpsilon X.q PA.Λ (M - 1))
        Gw.actual K)
      (fun v => truncateTorusHk (hK v) (V v aM)) (fun _ _ => 0) (fun _ _ => 0) u w)
    (hcoreb : weightedNorm 1 (Gw.mass lawW) (fun _ => 1)
        (fun v => truncateTorusHk (Nat.zero_le Kw) (V v (prepEndpoint (ocTauPP X.α X.q PA.Λ M) aM)) -
          truncateTorusHk (Nat.zero_le (K v)) (u v (prepEndpoint (ocTauPP X.α X.q PA.Λ M) aM))) ≤
      Ccore * D.eps M ^ (PA.χw + PA.σw * Lt) * Real.sqrt (l2NormSq f))
    (hV : weightedNorm (D.termRStar cK M) (Gw.mass lawW) (fun _ => 1) (fun v => V v aM) ≤
      max CK 0 * Real.sqrt (l2NormSq f))
    (haE : aM ≤ ((prepBlock (ocTauPP X.α X.q PA.Λ M) aM : ℝ) + 3 / 2) * ocTauPP X.α X.q PA.Λ M) :
      weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1)
          (normOp Kw _ K hK (Classical.choose hraw) fun v => V v aM) ≤
          ((1 + 4 * (max 1 (cr / cR) ^
        (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) * CR)) * max CK 0 +
        (max Ccore 0 * 2 ^ (PA.χw + PA.σw * PA.LpT) + 4 * CP * max CK 0)) * Real.sqrt (l2NormSq f) ∧
        weightedNorm 1 (Gw.mass lawW) (fun _ => 1)
            (fun v => truncateTorusHk (Nat.zero_le Kw) (V v (prepEndpoint (ocTauPP X.α X.q PA.Λ M) aM)) -
              truncateTorusHk (Nat.zero_le (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))))
                (normOp Kw _ K hK (Classical.choose hraw) (fun v => V v aM) v)) ≤
          ((1 + 4 * (max 1 (cr / cR) ^
        (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) * CR)) * max CK 0 +
        (max Ccore 0 * 2 ^ (PA.χw + PA.σw * PA.LpT) + 4 * CP * max CK 0)) * D.eps (M - 1) ^ PA.QT * Real.sqrt (l2NormSq f) := by
  have hF : 0 ≤ Real.sqrt (l2NormSq f) := Real.sqrt_nonneg _
  have hsc := prepNorm_scales (cr := cr) hDα hDq hDΛ hΛ (le_trans (by norm_num) hM) hϱK
  have hLtR : (PA.LpT : ℝ) ≤ Lt := Nat.cast_le.mpr hLt
  have hee : PA.χw + PA.σw * PA.LpT ≤ PA.χw + PA.σw * Lt :=
    add_le_add_right (mul_le_mul_of_nonneg_left hLtR hσ.le) PA.χw
  have hρ0 : 0 ≤ D.termRho cr M := by
    rw [hsc.2.2.2.2.2.2.2]
    exact mul_nonneg hcr.le (Real.sqrt_nonneg _)
  have hρA : D.termRho cr M ≤
      max 1 (cr / cR) * (cR * Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q PA.Λ M)) := by
    rw [hsc.2.2.2.2.2.2.2]
    exact prepNorm_radius_le hcR (Real.sqrt_nonneg _)
  have hu' : IsCoupledWeakSolutionTorus (D.κ M) aM
      (((prepBlock (ocTauPP X.α X.q PA.Λ M) aM : ℝ) + 3 / 2) * ocTauPP X.α X.q PA.Λ M)
      (streamVel (D.Φ M)) (termD0bar PA.NT PA.pT PA.DW PA.dW) K
      (edgeCoefficient Gw.actualFamily (D.κ M) (ocEpsilon X.q PA.Λ M)
        (ocEpsilon X.q PA.Λ (M - 1)) (fun _ => ()) K)
      (fun v => truncateTorusHk (hK v) (V v aM)) (fun _ _ => 0) (fun _ _ => 0) u w := by
    rw [Gw.edgeCoefficient_actualFamily]
    exact hu
  exact prepNorm_S (S := Gw.comps) (Gw.mass lawW) hπ K hK Gw.actualFamily (fun _ => ()) X.α X.q
    PA.Λ M D.Φ (D.hΦ M) (D.κ M)
    (D.κ (M - 1)) aM (prepBlock (ocTauPP X.α X.q PA.Λ M) aM) hraw V u w hu' haE rfl
    hsc.2.2.2.2.2.1 hρ0 (le_max_left _ _) hρA hCR hCP (le_max_right _ _) hF hϱ
    hsc.2.2.2.2.2.2.1 hV hsc.1.le hsc.2.1 hsc.2.2.1 hsc.2.2.2.1 hsc.2.2.2.2.1 he0 hee hQe hcoreb

/-- **The two bounds at one level**, for the raw model chosen from the conclusion of the family model bound. -/
theorem prepNorm_clauses {X : TermConstruction} (PA : PrepArgs X) (hΛ : 128 ≤ PA.Λ)
    (Kout Kw Lt : ℕ) (nW : ℕ+) (cr cK CK CL Cχ : ℝ) (kW : InvConsts) (CR CP cR Ccore : ℝ)
    (M : ℕ) (hM : 2 ≤ M) (hcr : 0 < cr) (hcR : 0 < cR) (hCR : 0 ≤ CR) (hCP : 0 ≤ CP)
    (hσ : 0 < PA.σw) (he0 : 0 ≤ PA.χw + PA.σw * PA.LpT)
    (hQe : PA.QT ≤ X.q * (PA.χw + PA.σw * PA.LpT)) (hLt : PA.LpT ≤ Lt)
    (hdead : 6 * PA.Jw * ocTauPP X.α X.q PA.Λ (M + 1) + 3 * ocTauPP X.α X.q PA.Λ M ≤ PA.T₀)
    {D : OCData} (hDα : D.α = X.α) (hDq : D.q = X.q) (hDΛ : D.Λ = PA.Λ) {j₀ : ℕ}
    (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH (termD0bar PA.NT PA.pT PA.DW PA.dW) PA.bw j₀) (aM : ℝ)
    (hW : IsWeakStage lawW PW PA.φ₀ PA.hφ₀ M (M + PA.Jw) PA.Jw PA.dW PA.DW nW kW a PA.T₀ PA.σw CL
      Cχ PA.χw Gw aM)
    (K : CompIn Gw.comps → ℕ) (hK : ∀ v, K v ≤ Kw) (ϱ : ℝ) (hϱ : 0 < ϱ)
    (hϱK : ϱ ≤ cK * ocEpsilon X.q PA.Λ M)
    (hraw : RawJointAbsConclusion X.α X.q PA.Λ PA.QT
      (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2)))
      (termD0bar PA.NT PA.pT PA.DW PA.dW) CR CP cR (Gw.mass lawW) K D.Φ M (D.κ M) (D.κ (M - 1)) aM
      (prepBlock (ocTauPP X.α X.q PA.Λ M) aM) Gw.actualFamily (fun _ => ()) ϱ ϱ) :
    ∀ (f : Vec 2 → ℝ)
      (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
      (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
      (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
      (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar PA.NT PA.pT PA.DW PA.dW) - 1)
        (ScalarH u.1.root)),
      IsWeakPaired PW PA.φ₀ PA.hφ₀ lawW M Kw Lt nW a PA.T₀ PA.σw PA.χw cK CK f Gw aM U₀ U V Uw Vw Uk
        Vk →
      PrepCoreClause PA Kw Lt M lawW Gw aM K hK V f Ccore →
      weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1)
          (normOp Kw _ K hK (Classical.choose hraw) fun v => V v aM) ≤
          ((1 + 4 * (max 1 (cr / cR) ^
        (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) * CR)) * max CK 0 +
        (max Ccore 0 * 2 ^ (PA.χw + PA.σw * PA.LpT) + 4 * CP * max CK 0)) * Real.sqrt (l2NormSq f) ∧
        weightedNorm 1 (Gw.mass lawW) (fun _ => 1)
            (fun v => truncateTorusHk (Nat.zero_le Kw) (V v (prepEndpoint (ocTauPP X.α X.q PA.Λ M) aM)) -
              truncateTorusHk (Nat.zero_le (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))))
                (normOp Kw _ K hK (Classical.choose hraw) (fun v => V v aM) v)) ≤
          ((1 + 4 * (max 1 (cr / cR) ^
        (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) * CR)) * max CK 0 +
        (max Ccore 0 * 2 ^ (PA.χw + PA.σw * PA.LpT) + 4 * CP * max CK 0)) * D.eps (M - 1) ^ PA.QT * Real.sqrt (l2NormSq f) := by
  intro f U₀ U V Uw Vw Uk Vk hpair hcore
  have hq1 : 1 < X.q := X.hq.1
  have hΛ1 : 1 ≤ PA.Λ := le_trans (by norm_num) hΛ
  have hπ : ∀ v, 0 < Gw.mass lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos (hDq ▸ hq1) (hDΛ ▸ hΛ) lawW v.1
  have hh : 0 < ocTauPP X.α X.q PA.Λ M := Construction.Stream.ocTauPP_pos hΛ1
  have haM2 : aM ≤ a + 6 * PA.Jw * ocTauPP X.α X.q PA.Λ (M + 1) := by
    have h := hW.2.1
    rwa [hDα, hDq, hDΛ] at h
  have htm := prepNorm_times hh (prepBlock_spec (aM := aM) hh).2 haM2 hdead
  exact prepNorm_clauses2 PA hΛ Kout Kw Lt cr cK CK CR CP cR Ccore M hM hcr hcR hCR hCP
    hσ he0 hQe hLt hDα hDq hDΛ lawW Gw aM K hK ϱ hϱ hϱK hraw hπ f V
    hcore.choose hcore.choose_spec.choose hcore.choose_spec.choose_spec.1
    hcore.choose_spec.choose_spec.2 (prepNorm_datum hπ htm.1 hpair) htm.2

/-- **Normalization at one level.** -/
theorem prepNormAtM_of {X : TermConstruction} (PA : PrepArgs X) (hΛ : 128 ≤ PA.Λ)
    (Kout Kw Lt : ℕ) (nW : ℕ+) (cr cK CK CL Cχ : ℝ) (kW : InvConsts) (CR CP cR Ccore : ℝ)
    (j₀ M : ℕ) (hM : 2 ≤ M) (hcr : 0 < cr) (hcR : 0 < cR) (hCR : 0 ≤ CR) (hCP : 0 ≤ CP)
    (hσ : 0 < PA.σw) (he0 : 0 ≤ PA.χw + PA.σw * PA.LpT)
    (hQe : PA.QT ≤ X.q * (PA.χw + PA.σw * PA.LpT)) (hLt : PA.LpT ≤ Lt)
    (hdead : 6 * PA.Jw * ocTauPP X.α X.q PA.Λ (M + 1) + 3 * ocTauPP X.α X.q PA.Λ M ≤ PA.T₀) :
    PrepNormAtM PA Kout Kw Lt nW cr cK CK CL Cχ kW CR CP cR Ccore
      ((1 + 4 * (max 1 (cr / cR) ^
        (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) * CR)) * max CK 0 +
        (max Ccore 0 * 2 ^ (PA.χw + PA.σw * PA.LpT) + 4 * CP * max CK 0)) j₀ M := by
  intro D hD a lawW PW Gw aM hW K hK ϱ hϱ hϱK hraw
  exact ⟨normOp Kw _ K hK (Classical.choose hraw),
    fun cv X' hX' v => normOp_fixes_constants Kw _ K hK _ cv X' hX' v,
    prepNorm_clauses PA hΛ Kout Kw Lt nW cr cK CK CL Cχ kW CR CP cR Ccore M hM hcr hcR hCR hCP hσ
      he0 hQe hLt hdead hD.1 hD.2.1 hD.2.2.1 a lawW PW Gw aM hW K hK ϱ hϱ hϱK hraw⟩

/-- **The normalization of the capped preparation.** -/
theorem prepNorm : PrepNormPart := by
  intro X
  refine ⟨128, le_rfl, fun PA hΛ hPA Kout => ⟨0, fun Kw Lt nW hk₀w cr _ hLt _ hcr _ cK CK CL Cχ
    kW hcK _ _ _ _ _ _ => ?_⟩⟩
  intro CR CP cR Ccore hcR hCR hCP
  have hT : 0 < PA.T₀ := hPA.2.2.2.1.2.1.trans hPA.2.2.2.1.2.2.1
  obtain ⟨M₀, hM₀⟩ := prepAnchor_deadline X hΛ PA.Jw hT
  obtain ⟨hσ, he0, hQe⟩ := prepNorm_schedule hPA
  exact ⟨_, fun j₀ => ⟨max M₀ 2, fun M hM => prepNormAtM_of PA hΛ Kout Kw Lt nW cr cK CK CL Cχ kW
    CR CP cR Ccore j₀ M (le_trans (le_max_right _ _) hM) hcr hcR hCR hCP hσ he0 hQe hLt
    (hM₀ M (le_trans (le_max_left _ _) hM))⟩⟩

end AVRegularity.EntryTerminal.Ingredients
end
end
end
