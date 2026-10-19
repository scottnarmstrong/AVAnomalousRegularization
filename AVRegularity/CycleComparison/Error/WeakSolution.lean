-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
public import AVRegularity.CycleJoint.TransitionJetTermDerivative
public import AVRegularity.Statements.Intermediate.CycleOutput.OcChartInv
import AVRegularity.CycleComparison.Charts.ChartDeviation
import AVRegularity.Applications.Transfer.TubeK
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionTorus
import AVRegularity.CycleComparison.Coarse.Defect.Final

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Error

/-! Rank-rescaled masses for the error clause of `cycle_comparison`. For a triangular coefficient
system (coefficients `A_{vu}` vanish unless `r_u < r_v`), the masses `π_v L^{2 r_v}` divide every
Schur entry by at least `L`; if the original entries are dominated by a matrix with row and column
sums at most `S` and `8S ≤ L`, the rescaled Schur matrix satisfies the Schur condition. The mass
norms at the rescaled masses are at most those at `π`, and conversely at most `L^{2H}` times them
when all ranks are at most `H`. The bound uses only row and column sums (no factor `card ι`). -/

/-- `π_v L^{2 r_v}`. -/
def rankScaledMass {ι : Type*} (π : ι → ℝ) (r : ι → ℕ) (L : ℝ) (v : ι) : ℝ :=
  π v * (L ^ r v) ^ 2

theorem rankScaledMass_pos {ι : Type*} {π : ι → ℝ} {r : ι → ℕ} {L : ℝ} (hπ : ∀ v, 0 < π v)
    (hL : 0 < L) (v : ι) : 0 < rankScaledMass π r L v := by
  unfold rankScaledMass
  exact mul_pos (hπ v) (pow_pos (pow_pos hL _) 2)

theorem le_rankScaledMass {ι : Type*} {π : ι → ℝ} (hπ : ∀ v, 0 < π v) (r : ι → ℕ) {L : ℝ}
    (hL : 1 ≤ L) (v : ι) : π v ≤ rankScaledMass π r L v := by
  unfold rankScaledMass
  exact le_mul_of_one_le_right (hπ v).le (one_le_pow₀ (one_le_pow₀ hL))

/-- `(π_v L^{2r_v})⁻¹ ≤ π_v⁻¹`. -/
theorem inv_rankScaledMass_le {ι : Type*} {π : ι → ℝ} (hπ : ∀ v, 0 < π v) (r : ι → ℕ) {L : ℝ}
    (hL : 1 ≤ L) (v : ι) : (rankScaledMass π r L v)⁻¹ ≤ (π v)⁻¹ :=
  inv_anti₀ (hπ v) (le_rankScaledMass hπ r hL v)

/-- `π_v⁻¹ ≤ L^{2H} (π_v L^{2r_v})⁻¹` when `r_v ≤ H`. -/
theorem inv_le_pow_mul_inv_rankScaledMass {ι : Type*} {π : ι → ℝ} (hπ : ∀ v, 0 < π v)
    (r : ι → ℕ) {L : ℝ} (hL : 1 ≤ L) (H : ℕ) {v : ι} (hrv : r v ≤ H) :
    (π v)⁻¹ ≤ L ^ (2 * H) * (rankScaledMass π r L v)⁻¹ := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hX : 0 < (L ^ r v) ^ 2 := pow_pos (pow_pos hL0 _) 2
  have e : (L ^ r v) ^ 2 * (rankScaledMass π r L v)⁻¹ = (π v)⁻¹ := by
    unfold rankScaledMass
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hX.ne', mul_one]
  have hXH : (L ^ r v) ^ 2 ≤ L ^ (2 * H) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hL (by omega)
  rw [← e]
  exact mul_le_mul_of_nonneg_right hXH (inv_nonneg.2 (rankScaledMass_pos hπ hL0 v).le)

/-! ### The Schur matrix at the rescaled masses -/

/-- `p s T ≤ p T / L` when `s ≤ 1/L`. -/
theorem rankScaled_mul_le_div {p s T L : ℝ} (hp : 0 ≤ p) (hT : 0 ≤ T)
    (hs : s ≤ 1 / L) : p * s * T ≤ p * T / L := by
  calc p * s * T ≤ p * (1 / L) * T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hp) hT
    _ = p * T / L := by rw [mul_one_div, div_mul_eq_mul_div]

/-- **The rescaled Schur entries.** For a strictly triangular coefficient system, the masses
`π_v L^{2r_v}` divide every Schur entry by at least `L`. -/
theorem schurMatrix_rankScaledMass_le {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    (ν ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (_hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (r : ι → ℕ) (hr : ∀ v u, ¬ r u < r v → ∀ d, A v u d = 0) (L : ℝ) (hL : 1 ≤ L)
    (v u : ι) :
    schurMatrix ν ρ (rankScaledMass π r L) K D a b A v u ≤
      schurMatrix ν ρ π K D a b A v u / L := by
  by_cases hvu : r u < r v
  · have hX : Real.sqrt ((L ^ r u) ^ 2 / (L ^ r v) ^ 2) ≤ 1 / L :=
      AVRegularity.CycleJointProofs.rankMass_sqrt_ratio_le_inv r L hL v u hvu
    have hsq : Real.sqrt (rankScaledMass π r L u / rankScaledMass π r L v) =
        Real.sqrt (π u / π v) * Real.sqrt ((L ^ r u) ^ 2 / (L ^ r v) ^ 2) := by
      unfold rankScaledMass
      rw [mul_div_mul_comm, Real.sqrt_mul (div_nonneg (hπ u).le (hπ v).le)]
    unfold schurMatrix
    rw [hsq]
    exact rankScaled_mul_le_div (Real.sqrt_nonneg _)
      (Finset.sum_nonneg fun d _ => mul_nonneg
        (div_nonneg ENNReal.toReal_nonneg (mul_pos hν (pow_pos hρ _)).le)
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) hX
  · have h1 := AVRegularity.CycleJointProofs.schurMatrix_entry_zero ν ρ K D a b A v u
      (hr v u hvu) (rankScaledMass π r L)
    have h2 := AVRegularity.CycleJointProofs.schurMatrix_entry_zero ν ρ K D a b A v u
      (hr v u hvu) π
    exact (h1.trans (by rw [h2, zero_div])).le

/-- **The Schur condition at the rescaled masses.** If the Schur entries at `π` are dominated by
`c` with row and column sums at most `S` and `8S ≤ L`, the rescaled matrix satisfies the Schur
condition. -/
theorem schurCondition_rankScaledMass {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    (ν ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (r : ι → ℕ) (hr : ∀ v u, ¬ r u < r v → ∀ d, A v u d = 0) (L : ℝ) (hL : 1 ≤ L)
    (c : ι → ι → ℝ) (S : ℝ) (hc : ∀ v u, schurMatrix ν ρ π K D a b A v u ≤ c v u)
    (hrow : ∀ v, ∑ u, c v u ≤ S) (hcol : ∀ u, ∑ v, c v u ≤ S) (hSL : 8 * S ≤ L) :
    SchurCondition (schurMatrix ν ρ (rankScaledMass π r L) K D a b A) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hent : ∀ v u, schurMatrix ν ρ (rankScaledMass π r L) K D a b A v u ≤ c v u / L :=
    fun v u => (schurMatrix_rankScaledMass_le ν ρ hν hρ π hπ K D a b A hA r hr L hL v u).trans
      (div_le_div_of_nonneg_right (hc v u) hL0.le)
  have hSdiv : S / L ≤ 1 / 8 := by
    rw [div_le_iff₀ hL0]
    linarith
  refine ⟨fun v => ?_, fun u => ?_⟩
  · calc ∑ u, schurMatrix ν ρ (rankScaledMass π r L) K D a b A v u
        ≤ ∑ u, c v u / L := Finset.sum_le_sum fun u _ => hent v u
      _ = (∑ u, c v u) / L := (Finset.sum_div _ _ _).symm
      _ ≤ S / L := div_le_div_of_nonneg_right (hrow v) hL0.le
      _ ≤ 1 / 8 := hSdiv
  · calc ∑ v, schurMatrix ν ρ (rankScaledMass π r L) K D a b A v u
        ≤ ∑ v, c v u / L := Finset.sum_le_sum fun v _ => hent v u
      _ = (∑ v, c v u) / L := (Finset.sum_div _ _ _).symm
      _ ≤ S / L := div_le_div_of_nonneg_right (hcol u) hL0.le
      _ ≤ 1 / 8 := hSdiv

/-! ### Mass norms at the rescaled masses -/

theorem massNormSq_rankScaledMass_le {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, MeasurableSpace (E i)] {μ : Measure (Vec 2)}
    {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (r : ι → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (Dj : ∀ i, JetL2 μ (K i) (E i)) :
    massNormSq ρ (rankScaledMass π r L) Dj ≤ massNormSq ρ π Dj := by
  unfold massNormSq
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
    (inv_rankScaledMass_le hπ r hL i) (factorialNormSq_nonneg ρ (Dj i))

theorem massNormSq_le_rankScaledMass {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, MeasurableSpace (E i)] {μ : Measure (Vec 2)}
    {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (r : ι → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (H : ℕ) (hrH : ∀ v, r v ≤ H) (Dj : ∀ i, JetL2 μ (K i) (E i)) :
    massNormSq ρ π Dj ≤ L ^ (2 * H) * massNormSq ρ (rankScaledMass π r L) Dj := by
  unfold massNormSq
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => (mul_le_mul_of_nonneg_right
    (inv_le_pow_mul_inv_rankScaledMass hπ r hL H (hrH i))
    (factorialNormSq_nonneg ρ (Dj i))).trans_eq (mul_assoc _ _ _)

theorem massGradNormSq_le_rankScaledMass {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, MeasurableSpace (E i)] {μ : Measure (Vec 2)}
    {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (r : ι → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (H : ℕ) (hrH : ∀ v, r v ≤ H) (Dj : ∀ i, JetL2 μ (K i + 1) (E i)) :
    massGradNormSq ρ π Dj ≤ L ^ (2 * H) * massGradNormSq ρ (rankScaledMass π r L) Dj := by
  unfold massGradNormSq
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => (mul_le_mul_of_nonneg_right
    (inv_le_pow_mul_inv_rankScaledMass hπ r hL H (hrH i))
    (Coarse.gradFactorialNormSq_nonneg ρ (Dj i))).trans_eq (mul_assoc _ _ _)

end AVRegularity.CycleComparison.Error
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.CycleComparison.Error

/-! The Schur matrix of the physical edge coefficient of a charted family is dominated by the
sampled forward envelope (with component energy and the factorial shift, the forward envelope gives
`x_v ≤ C d_v + C ∑_u b_{vu} x_u`). The coefficient seminorm is subadditive over finite sums of `C^K`
coefficients; the physical coefficient is the sum of its constituents, so its seminorm is at most
the sum of the constituent seminorms, which the envelope bounds (with the orders restricted to the
admissible ones, a subset of `[2, D]`). -/

/-! ### Subadditivity of the coefficient seminorm -/

section Subadditive

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative array of a finite sum of `C^j` coefficients is the sum of the arrays. -/
theorem coefficientDerivativeArray_finset_sum {κ : Type*} (s : Finset κ)
    (C : κ → Vec 2 → E →L[ℝ] F) (j : ℕ) (hC : ∀ c ∈ s, ContDiff ℝ (j : ℕ) (C c)) (x : Vec 2) :
    coefficientDerivativeArray (fun y => ∑ c ∈ s, C c y) j x =
      ∑ c ∈ s, coefficientDerivativeArray (C c) j x := by
  ext z w
  rw [coefficientDerivativeArray_apply,
    AVRegularity.Weighted.orderedCoefficientDerivative_finset_sum s C j hC w]
  simp

/-- **Subadditivity of the coefficient seminorm** over finite sums of `C^K` coefficients. -/
theorem coefficientSeminorm_finset_sum_le {κ : Type*} (s : Finset κ) (ρ : ℝ) (_hρ : 0 ≤ ρ)
    (K : ℕ) (t₀ t₁ : ℝ) (X : κ → ℝ → Vec 2 → E →L[ℝ] F)
    (hX : ∀ c ∈ s, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ K (X c t)) :
    coefficientSeminorm ρ K t₀ t₁ (fun t x => ∑ c ∈ s, X c t x) ≤
      ∑ c ∈ s, coefficientSeminorm ρ K t₀ t₁ (X c) := by
  have hpt : ∀ j : ℕ, j ≤ K → ∀ t ∈ Set.Icc t₀ t₁, ∀ x : Vec 2,
      (‖coefficientDerivativeArray (fun y => ∑ c ∈ s, X c t y) j x‖₊ : ℝ≥0∞) ≤
        ∑ c ∈ s, (‖coefficientDerivativeArray (X c t) j x‖₊ : ℝ≥0∞) := by
    intro j hj t ht x
    rw [coefficientDerivativeArray_finset_sum s (fun c => X c t) j
      (fun c hc => (hX c hc t ht).of_le (by exact_mod_cast hj)) x]
    exact (ENNReal.coe_le_coe.2 (nnnorm_sum_le _ _)).trans_eq
      (ENNReal.ofNNReal_finsetSum _ _)
  unfold coefficientSeminorm
  calc ∑ j ∈ Finset.range (K + 1), ENNReal.ofReal (ρ ^ j / (j.factorial : ℝ)) *
        ⨆ t ∈ Set.Icc t₀ t₁, ⨆ x : Vec 2,
          (‖coefficientDerivativeArray (fun y => ∑ c ∈ s, X c t y) j x‖₊ : ℝ≥0∞)
      ≤ ∑ j ∈ Finset.range (K + 1), ENNReal.ofReal (ρ ^ j / (j.factorial : ℝ)) *
          ∑ c ∈ s, ⨆ t ∈ Set.Icc t₀ t₁, ⨆ x : Vec 2,
            (‖coefficientDerivativeArray (X c t) j x‖₊ : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ zero_le
        have hjK : j ≤ K := by
          have := Finset.mem_range.mp hj
          omega
        refine iSup₂_le fun t ht => iSup_le fun x => ?_
        refine (hpt j hjK t ht x).trans (Finset.sum_le_sum fun c _ => ?_)
        exact le_iSup₂_of_le t ht
          (le_iSup (fun x => (‖coefficientDerivativeArray (X c t) j x‖₊ : ℝ≥0∞)) x)
    _ = ∑ c ∈ s, ∑ j ∈ Finset.range (K + 1), ENNReal.ofReal (ρ ^ j / (j.factorial : ℝ)) *
          ⨆ t ∈ Set.Icc t₀ t₁, ⨆ x : Vec 2,
            (‖coefficientDerivativeArray (X c t) j x‖₊ : ℝ≥0∞) := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm

end Subadditive

/-! ### The sampled envelope dominates the Schur matrix of the edge coefficient -/

section Sampled

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- `a b ≠ ⊤` and `b ≠ 0` give `a ≠ ⊤`. -/
theorem ennreal_ne_top_of_mul_left {a b : ℝ≥0∞} (hab : a * b ≠ ⊤) (hb : b ≠ 0) : a ≠ ⊤ :=
  fun ha => hab (ENNReal.mul_eq_top.2 (Or.inr ⟨ha, hb⟩))

/-- `a b ≠ ⊤` and `a ≠ 0` give `b ≠ ⊤`. -/
theorem ennreal_ne_top_of_mul_right {a b : ℝ≥0∞} (hab : a * b ≠ ⊤) (ha : a ≠ 0) : b ≠ ⊤ :=
  fun hb => hab (ENNReal.mul_eq_top.2 (Or.inl ⟨ha, hb⟩))

/-- The real order-`n` budget of the edge `u → v`: the constituent seminorms summed before the
normalization `(K_v+n-2)!/(K_v! ν ρ^{n-2})`. -/
def sampledOrderTerm (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (actual : ∀ p, Ctx p)
    (K : ι → ℕ) (ρ t₀ t₁ : ℝ) (v u : ι) (n : ℕ) : ℝ :=
  (∑ γ : F.Γ v u,
      (coefficientSeminorm ρ (K v) t₀ t₁ (constituentPhysical F ν e E actual v u γ n)).toReal) /
    (ν * ρ ^ (n - 2)) * (((K v + n - 2).factorial : ℝ) / ((K v).factorial : ℝ))

end Sampled

/-- **The sampled envelope bounds the Schur matrix of the edge coefficient.** -/
theorem sampled_edgeCoefficient_schur {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ)
    (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (actual : ∀ p, Ctx p) (t₀ t₁ ν e E ρ C : ℝ)
    (hν : 0 < ν) (hρ : 0 < ρ) (hC : 0 ≤ C) (b : ι → ι → ℝ) (hb : ∀ v u, 0 ≤ b v u)
    (hfwd : IsSampledEnvelope F π K actual t₀ t₁ ν e E ρ C b) (v u : ι) :
    (∀ d : admissibleOrders K D v u,
        coefficientSeminorm ρ (K v) t₀ t₁ (edgeCoefficient F ν e E actual K v u d) ≠ ⊤) ∧
      schurMatrix ν ρ π K D t₀ t₁ (edgeCoefficient F ν e E actual K) v u ≤ C * b v u := by
  have hsqpos : ENNReal.ofReal (Real.sqrt (π u / π v)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 (div_pos (hπ u) (hπ v)))).ne'
  have hden : ∀ n : ℕ, 0 < ν * ρ ^ (n - 2) := fun n => mul_pos hν (pow_pos hρ _)
  have hfact : ∀ n : ℕ, 0 < ((K v + n - 2).factorial : ℝ) / ((K v).factorial : ℝ) := fun n =>
    div_pos (Nat.cast_pos.2 (Nat.factorial_pos _)) (Nat.cast_pos.2 (Nat.factorial_pos _))
  have hall := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hfwd.2 v u)
  have hsum := ennreal_ne_top_of_mul_right hall hsqpos
  -- every constituent seminorm of every order of `[2, D]` is finite
  have hfin_c : ∀ (γ : F.Γ v u) (n : ℕ), n ∈ Finset.Icc 2 D →
      coefficientSeminorm ρ (K v) t₀ t₁ (constituentPhysical F ν e E actual v u γ n) ≠ ⊤ := by
    intro γ n hn
    have h3 := ENNReal.sum_ne_top.1 hsum γ (Finset.mem_univ γ)
    have h4 := ENNReal.sum_ne_top.1 h3 n hn
    exact ennreal_ne_top_of_mul_left
      (ennreal_ne_top_of_mul_left h4 (ENNReal.ofReal_pos.2 (hfact n)).ne')
      (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
  have htermfin : ∀ (γ : F.Γ v u) (n : ℕ), n ∈ Finset.Icc 2 D →
      coefficientSeminorm ρ (K v) t₀ t₁ (constituentPhysical F ν e E actual v u γ n) *
          (ENNReal.ofReal (ν * ρ ^ (n - 2)))⁻¹ *
          ENNReal.ofReal (((K v + n - 2).factorial : ℝ) / ((K v).factorial : ℝ)) ≠ ⊤ :=
    fun γ n hn => ENNReal.mul_ne_top (ENNReal.mul_ne_top (hfin_c γ n hn)
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (hden n)).ne')) ENNReal.ofReal_ne_top
  -- the seminorm of the physical coefficient against the constituents
  have hedge : ∀ d : admissibleOrders K D v u,
      coefficientSeminorm ρ (K v) t₀ t₁ (edgeCoefficient F ν e E actual K v u d) ≤
        ∑ γ : F.Γ v u,
          coefficientSeminorm ρ (K v) t₀ t₁ (constituentPhysical F ν e E actual v u γ d.1) :=
    fun d => coefficientSeminorm_finset_sum_le Finset.univ ρ hρ.le (K v) t₀ t₁
      (fun γ => constituentPhysical F ν e E actual v u γ d.1)
      (fun γ _ s hs => hfwd.1 v u γ d.1 s hs)
  refine ⟨fun d => ?_, ?_⟩
  · have hd1 : d.1 ∈ Finset.Icc 2 D := (Finset.mem_filter.1 d.2).1
    exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun γ _ => hfin_c γ d.1 hd1) (hedge d)
  -- the real budget
  have hterm : ∀ d : admissibleOrders K D v u,
      (coefficientSeminorm ρ (K v) t₀ t₁ (edgeCoefficient F ν e E actual K v u d)).toReal /
          (ν * ρ ^ (d.1 - 2)) * (((K v + d.1 - 2).factorial : ℝ) / ((K v).factorial : ℝ)) ≤
        sampledOrderTerm F ν e E actual K ρ t₀ t₁ v u d.1 := by
    intro d
    have hd1 : d.1 ∈ Finset.Icc 2 D := (Finset.mem_filter.1 d.2).1
    have hfinS : ∑ γ : F.Γ v u, coefficientSeminorm ρ (K v) t₀ t₁
        (constituentPhysical F ν e E actual v u γ d.1) ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun γ _ => hfin_c γ d.1 hd1
    have hreal : (coefficientSeminorm ρ (K v) t₀ t₁
          (edgeCoefficient F ν e E actual K v u d)).toReal ≤
        ∑ γ : F.Γ v u, (coefficientSeminorm ρ (K v) t₀ t₁
          (constituentPhysical F ν e E actual v u γ d.1)).toReal :=
      (ENNReal.toReal_mono hfinS (hedge d)).trans_eq
        (ENNReal.toReal_sum fun γ _ => hfin_c γ d.1 hd1)
    unfold sampledOrderTerm
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hreal (hden d.1).le)
      (hfact d.1).le
  have hG : ∀ n : ℕ, 0 ≤ sampledOrderTerm F ν e E actual K ρ t₀ t₁ v u n := fun n => by
    unfold sampledOrderTerm
    exact mul_nonneg (div_nonneg (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
      (hden n).le) (hfact n).le
  have hsub : ∑ d : admissibleOrders K D v u, sampledOrderTerm F ν e E actual K ρ t₀ t₁ v u d.1 ≤
      ∑ n ∈ Finset.Icc 2 D, sampledOrderTerm F ν e E actual K ρ t₀ t₁ v u n :=
    (Finset.sum_coe_sort (s := admissibleOrders K D v u)
      (f := fun n => sampledOrderTerm F ν e E actual K ρ t₀ t₁ v u n)).trans_le
      (Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => (Finset.mem_filter.1 hn).1)
        fun n _ _ => hG n)
  have hconv : (ENNReal.ofReal (Real.sqrt (π u / π v)) *
      ∑ γ : F.Γ v u, ∑ n ∈ Finset.Icc 2 D,
        coefficientSeminorm ρ (K v) t₀ t₁ (constituentPhysical F ν e E actual v u γ n) *
          (ENNReal.ofReal (ν * ρ ^ (n - 2)))⁻¹ *
          ENNReal.ofReal (((K v + n - 2).factorial : ℝ) / ((K v).factorial : ℝ))).toReal =
      Real.sqrt (π u / π v) *
        ∑ n ∈ Finset.Icc 2 D, sampledOrderTerm F ν e E actual K ρ t₀ t₁ v u n := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      ENNReal.toReal_sum fun γ _ => ENNReal.sum_ne_top.2 fun n hn => htermfin γ n hn]
    congr 1
    refine (Finset.sum_congr rfl fun γ _ =>
      ENNReal.toReal_sum fun n hn => htermfin γ n hn).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold sampledOrderTerm
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (hden n).le, ENNReal.toReal_ofReal (hfact n).le, ← div_eq_mul_inv]
  calc schurMatrix ν ρ π K D t₀ t₁ (edgeCoefficient F ν e E actual K) v u
      = Real.sqrt (π u / π v) * ∑ d : admissibleOrders K D v u,
          (coefficientSeminorm ρ (K v) t₀ t₁ (edgeCoefficient F ν e E actual K v u d)).toReal /
            (ν * ρ ^ (d.1 - 2)) *
            (((K v + d.1 - 2).factorial : ℝ) / ((K v).factorial : ℝ)) := rfl
    _ ≤ Real.sqrt (π u / π v) * ∑ d : admissibleOrders K D v u,
          sampledOrderTerm F ν e E actual K ρ t₀ t₁ v u d.1 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun d _ => hterm d) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (π u / π v) *
          ∑ n ∈ Finset.Icc 2 D, sampledOrderTerm F ν e E actual K ρ t₀ t₁ v u n :=
        mul_le_mul_of_nonneg_left hsub (Real.sqrt_nonneg _)
    _ = (ENNReal.ofReal (Real.sqrt (π u / π v)) *
          ∑ γ : F.Γ v u, ∑ n ∈ Finset.Icc 2 D,
            coefficientSeminorm ρ (K v) t₀ t₁ (constituentPhysical F ν e E actual v u γ n) *
              (ENNReal.ofReal (ν * ρ ^ (n - 2)))⁻¹ *
              ENNReal.ofReal (((K v + n - 2).factorial : ℝ) / ((K v).factorial : ℝ))).toReal :=
        hconv.symm
    _ ≤ (ENNReal.ofReal (C * b v u)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hfwd.2 v u)
    _ = C * b v u := ENNReal.toReal_ofReal (mul_nonneg hC (hb v u))

end AVRegularity.CycleComparison.Error
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Error

/-! Joint measurability of the actual edge coefficient on the observation window
(`coupled_energy_torus`, premise `hA_meas`). On the window only pieces whose weight is
continuous in time and whose material map is a renewal chart `ocChart l` carry weight (the observed pulses of `cycle_comparison` have `C¹` weights summing to one
there, so every other piece has weight zero on the window). The renewal chart is the smooth
stream flow, so the argument of `CycleJointProofs.physicalCoefficient_joint_measurable` applies with the natural
Jacobian of the renewal flow. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The same with the weight measurable only on the window. -/
theorem weighted_dimFlux_window_measurable (F : ChartedFamily ι h D P Ctx)
    (ν e E tA tZ : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tA tZ)) E n)
    (hmeas : F.IsTimeMeasurable) (p : P)
    (hw : Measurable (fun t : Set.Icc tA tZ => F.weight p t)) (c : Ctx p) (v u : ι)
    (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) :
    Measurable (fun z : Set.Icc tA tZ × (Vec 2 × Vec 2) =>
      F.weight p z.1 • F.dimFlux ν e E p c v u γ d I z.1 z.2.1 z.2.2) := by
  have hc (t : Set.Icc tA tZ) : Continuous (fun yz : Vec 2 × Vec 2 =>
      F.weight p t • F.dimFlux ν e E p c v u γ d I t yz.1 yz.2) := by
    simpa only [ChartedFamily.dimFlux, ChartedFamily.slowFlux, smul_smul] using
      CycleJointProofs.weighted_dimFlux_spatial_continuous F ν e E tA tZ n hs p c v u γ d I t
  have hm (yz : Vec 2 × Vec 2) : Measurable (fun t : Set.Icc tA tZ =>
      F.weight p t • F.dimFlux ν e E p c v u γ d I t yz.1 yz.2) := by
    change Measurable (fun t : Set.Icc tA tZ => F.weight p t •
      ((ν * e ^ (d - 2)) • F.flux p c v u γ d I t (E⁻¹ • yz.1) yz.2))
    exact hw.smul
      (((hmeas p c v u γ d I (E⁻¹ • yz.1) yz.2).comp measurable_subtype_coe).const_smul
        (ν * e ^ (d - 2)))
  exact (measurable_uncurry_of_continuous_of_measurable hc hm).comp measurable_swap

/-- The inverse of a material map that is a renewal chart is the inverse renewal chart. -/
theorem material_symm_eq_ocChartInv (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (X : Vec 2 ≃ₜ Vec 2) (l : ℤ) (t : ℝ)
    (hX : ⇑X = ocChart α q Λ m φ hφ l t) (x : Vec 2) :
    X.symm x = ocChartInv α q Λ m φ hφ l t x := by
  apply X.injective
  rw [Homeomorph.apply_symm_apply, hX, Charts.ocChart_ocChartInv]

/-- A weighted transported array of a piece whose material map is a renewal chart is jointly
measurable on the window. -/
theorem weighted_piece_array_window_measurable (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (F : ChartedFamily ι h D P Ctx) (ν e E tA tZ : ℝ)
    (n : ι → ℕ) (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tA tZ)) E n)
    (hmeas : F.IsTimeMeasurable) (p : P) (l : ℤ)
    (hmat : ∀ t, ⇑((F.piece p).material t) = ocChart α q Λ m φ hφ l t)
    (hw : Measurable (fun t : Set.Icc tA tZ => F.weight p t)) (c : Ctx p) (v u : ι)
    (γ : F.Γ v u) (r : ℕ) (A : DerivativeWord2 r) (a : Fin 2) :
    Measurable (fun z : Set.Icc tA tZ × Vec 2 => F.weight p z.1 *
      transportedCoeff (chartInvJacobian ⇑((F.piece p).material z.1).symm)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c v u γ d I z.1
          (((F.piece p).material z.1).symm z.2)
          (e⁻¹ • ((F.piece p).material z.1).symm z.2)) r A z.2 a) := by
  have hsymm : ∀ t x, ((F.piece p).material t).symm x = ocChartInv α q Λ m φ hφ l t x :=
    fun t x => material_symm_eq_ocChartInv α q Λ m φ hφ _ l t (hmat t) x
  have hJ : ∀ t, chartInvJacobian ⇑((F.piece p).material t).symm =
      CycleJointProofs.naturalPreparationJacobian hφ ((l : ℝ) * ocTauPP α q Λ m) t := by
    intro t
    funext x
    rw [CycleJointProofs.chartInvJacobian_homeomorph_symm ((F.piece p).material t)
      (((F.piece p).material_smooth t).differentiable (by simp))
      (((F.piece p).material_symm_smooth t).differentiable (by simp)), hmat t, hsymm t x]
    rfl
  let B := fun d (I : DerivativeWord2 (d - 1)) (z : Set.Icc tA tZ × Vec 2) =>
    F.weight p z.1 • F.dimFlux ν e E p c v u γ d I z.1
      (ocChartInv α q Λ m φ hφ l z.1 z.2) (e⁻¹ • ocChartInv α q Λ m φ hφ l z.1 z.2)
  have hy : Continuous (fun z : Set.Icc tA tZ × Vec 2 => ocChartInv α q Λ m φ hφ l z.1 z.2) :=
    (Charts.contDiff_ocChartInv_joint hφ α q Λ m l).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hB : ∀ d I i, Measurable (fun z => B d I z i) := by
    intro d I i
    exact (measurable_pi_apply i).comp
      ((weighted_dimFlux_window_measurable F ν e E tA tZ n hs hmeas p hw c v u γ d I).comp
        (measurable_fst.prodMk (hy.measurable.prodMk (hy.const_smul (e⁻¹)).measurable)))
  have hm := CycleJointProofs.transportedCoeff_joint_measurable tA tZ
    (CycleJointProofs.naturalPreparationJacobian hφ ((l : ℝ) * ocTauPP α q Λ m))
    (CycleJointProofs.naturalPreparationJacobian_entry_smooth hφ _)
    (F.identity v u γ).maxOrder B hB r A a
  convert hm using 1
  funext z
  dsimp only [B]
  rw [CycleJointProofs.transportedCoeff_smul_native, hJ z.1, hsymm z.1 z.2]
  simp only [Pi.smul_apply, smul_eq_mul]

variable [∀ i, FiniteDimensional ℝ (h i)]

/-- **Window measurability of the physical coefficient.** Every piece either has zero weight on
the window or has a continuous weight and a renewal chart. -/
theorem physicalCoefficient_window_measurable (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (F : ChartedFamily ι h D P Ctx) (ν e E tA tZ : ℝ)
    (n : ι → ℕ) (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tA tZ)) E n)
    (hmeas : F.IsTimeMeasurable)
    (hwin : ∀ p, (∀ t ∈ Set.Icc tA tZ, F.weight p t = 0) ∨
      (Continuous (F.weight p) ∧
        ∃ l : ℤ, ∀ t, ⇑((F.piece p).material t) = ocChart α q Λ m φ hφ l t))
    (actual : ∀ p, Ctx p) (v u : ι) (d : ℕ) :
    Measurable (fun z : Set.Icc tA tZ × Vec 2 =>
      physicalCoefficient F ν e E actual v u d z.1 z.2) := by
  unfold physicalCoefficient
  refine Finset.measurable_sum _ (fun γ _ => ?_)
  let b := fun p (z : Set.Icc tA tZ × Vec 2) k (A : DerivativeWord2 (d - 1)) =>
    transportedCoeff (chartInvJacobian ⇑((F.piece p).material z.1).symm)
      (F.identity v u γ).maxOrder
      (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I z.1
        (((F.piece p).material z.1).symm z.2)
        (e⁻¹ • ((F.piece p).material z.1).symm z.2)) (d - 1) A z.2 k
  change Measurable (fun z : Set.Icc tA tZ × Vec 2 => ∑ᶠ p,
    F.weight p z.1 • (CycleJointProofs.nativeArrayAssembly (d - 1) (F.identity v u γ).map
      (b p z)))
  apply CycleJointProofs.measurable_piece_finsum_onWindow F tA tZ
  · intro p
    rcases hwin p with hz | ⟨hcont, l, hmat⟩
    · have he : (fun z : Set.Icc tA tZ × Vec 2 => F.weight p z.1 •
          CycleJointProofs.nativeArrayAssembly (d - 1) (F.identity v u γ).map (b p z)) =
          fun _ => 0 := by
        funext z
        rw [hz z.1 z.1.property]
        exact zero_smul ℝ (CycleJointProofs.nativeArrayAssembly (d - 1) (F.identity v u γ).map
          (b p z))
      rw [he]
      exact measurable_const
    · have hw : Measurable (fun t : Set.Icc tA tZ => F.weight p t) :=
        hcont.measurable.comp measurable_subtype_coe
      have hm := CycleJointProofs.nativeArrayAssembly_measurable (d - 1)
        (F.identity v u γ).map (fun z k A => F.weight p z.1 * b p z k A)
        (fun k A => weighted_piece_array_window_measurable α q Λ m φ hφ F ν e E tA tZ n hs
          hmeas p l hmat hw (actual p) v u γ (d - 1) A k)
      convert hm using 1
      funext z
      exact ((CycleJointProofs.nativeArrayAssembly (d - 1) (F.identity v u γ).map).map_smul
        (F.weight p z.1) (b p z)).symm
  · intro p z hout
    rw [F.weight_zero p z.1 hout]
    exact zero_smul ℝ (CycleJointProofs.nativeArrayAssembly (d - 1) (F.identity v u γ).map
      (b p z))

end AVRegularity.CycleComparison.Error
end

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.CycleComparison.Error

/-! Two facts of the observation window used by the error clause of `cycle_comparison`.

* The observed pulses carry the whole weight of the window (their weights sum to one
  there), so every other piece of the family has weight zero on the window.
* The actual drift `𝐛_m = ∇^⊥Φ_m` is smooth, incompressible, periodic, bounded and jointly
  measurable (the drift premises of `coupled_energy_torus`). -/

/-- **Weight zero off the covered window.** If the weights of the pieces `pp k`, `k ∈ kset`
(injective), sum to one on a covered window, every other piece has weight zero there. -/
theorem weight_eq_zero_of_not_mem {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h D P Ctx) (kset : Finset ℤ) (pp : ℤ → P)
    (hinj : Set.InjOn pp (↑kset : Set ℤ)) (W : Set ℝ)
    (hcov : W ⊆ ⋃ p, (F.piece p).output)
    (hsum : ∀ t ∈ W, ∑ k ∈ kset, F.weight (pp k) t = 1)
    (p : P) (hp : ∀ k ∈ kset, pp k ≠ p) : ∀ t ∈ W, F.weight p t = 0 := by
  classical
  intro t ht
  have hp' : p ∉ kset.image pp := by
    intro hm
    obtain ⟨k, hk, hkp⟩ := Finset.mem_image.1 hm
    exact hp k hk hkp
  obtain ⟨p₀, hp₀⟩ := Set.mem_iUnion.1 (hcov ht)
  have h1 : ∑ᶠ p', F.weight p' t = 1 := F.weight_sum t ⟨p₀, hp₀⟩
  set S := kset.image pp with hS
  have hSsum : ∑ p' ∈ S, F.weight p' t = 1 := by
    rw [hS, Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
    exact hsum t ht
  set T := (F.locally_finite t t).toFinset ∪ insert p S with hT
  have hsupp : (Function.support fun p' => F.weight p' t) ⊆ ↑T := by
    intro p' hp'
    have hout : t ∈ (F.piece p').output := by
      by_contra hno
      exact hp' (F.weight_zero p' t hno)
    rw [hT, Finset.coe_union]
    left
    rw [Set.Finite.coe_toFinset]
    exact ⟨t, hout, le_rfl, le_rfl⟩
  have h2 : ∑ᶠ p', F.weight p' t = ∑ p' ∈ T, F.weight p' t :=
    finsum_eq_sum_of_support_subset _ hsupp
  have h3 : ∑ p' ∈ insert p S, F.weight p' t ≤ ∑ p' ∈ T, F.weight p' t :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
      (fun p' _ _ => F.weight_nonneg p' t)
  rw [Finset.sum_insert hp', hSsum] at h3
  have h4 := F.weight_nonneg p t
  linarith

/-- The drift premises of the coupled energy estimate for the actual drift `𝐛_m`. -/
theorem actual_drift_fields (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) (Λ : ℕ) (h128 : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (t₀ t₁ : ℝ) :
    (∃ C : ℝ, ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ‖streamVel (Φ m) t x‖ ≤ C) ∧
    (Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => streamVel (Φ m) p.1 p.2) ∧
    (∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (⊤ : ℕ∞) (streamVel (Φ m) t)) ∧
    (∀ t ∈ Set.Icc t₀ t₁, ∀ x,
      ∑ k : Fin 2, fderiv ℝ (streamVel (Φ m) t) x (basisVec k) k = 0) ∧
    (∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (streamVel (Φ m) t)) := by
  have hadm : IsAdmissibleStream (Φ m) :=
    AVRegularity.Velocity.streamSeq_admissible hζ h128 hΦ m
  have hsl : ∀ r : ℝ, ContDiff ℝ (⊤ : ℕ∞) (Φ m r) := fun r =>
    hadm.1.comp (contDiff_const.prodMk contDiff_id)
  have hvs : ∀ r : ℝ, ContDiff ℝ (⊤ : ℕ∞) (streamVel (Φ m) r) := fun r =>
    AVRegularity.Applications.streamVel_slice_smooth α q ζ hζ Λ h128 Φ hΦ m r
  refine ⟨⟨AVRegularity.Applications.velBound α q Λ, fun t _ x =>
      AVRegularity.Applications.streamVel_norm_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ h128 Φ hΦ
        m t x⟩,
    hadm.vel_continuous.measurable.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd),
    fun t _ => hvs t, fun t _ x => ?_,
    fun t _ => AVRegularity.Velocity.streamSeq_velocity_spatial_periodic hζ h128 hΦ m t⟩
  have h := AVRegularity.Applications.streamVel_classical_div hsl t x
  unfold AVRegularity.Applications.pd at h
  rw [AVRegularity.Velocity.Port.MaterialSpatial.fderiv_component_apply (hvs t) x 0 0,
    AVRegularity.Velocity.Port.MaterialSpatial.fderiv_component_apply (hvs t) x 1 1] at h
  rw [Fin.sum_univ_two]
  exact h

end AVRegularity.CycleComparison.Error
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Error

/-! Restriction and difference of torus weak solutions of the coupled system
(the solution class `IsCoupledWeakSolutionTorus`):
* a solution on `[t₀, t₂]` is a solution on every `[t₀, t₁]`, `t₁ ≤ t₂`;
* it is a solution on `[t₁, t₂]` started from its own value `u(t₁)`: the integrated identity at
  `t` minus the identity at `t₁` is the identity from `t₁` to `t`;
* the difference of two solutions on the same window, with the same drift and coefficients, is
  a solution with the differences of the data. -/

/-- The integrated identity from `a` to `t`, minus the one from `a` to `b ≤ t`, is the
integrated identity from `b` to `t` started from the value at `b`. -/
theorem coupledWeakIdentity_restrict_right {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (μ : Measure (Vec 2)) (ν a b t : ℝ) (hab : a ≤ b) (hbt : b ≤ t)
    (v : ℝ → Vec 2 → Vec 2) (u₁ u₂ f φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H) (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (g : ℝ → Vec 2 → H)
    (h₁ : CoupledWeakIdentity μ ν a b v u₁ f φ dφ du flux F g)
    (h₂ : CoupledWeakIdentity μ ν a t v u₂ f φ dφ du flux F g) :
    CoupledWeakIdentity μ ν b t v u₂ u₁ φ dφ du flux F g := by
  change Integrable (fun x => inner ℝ (u₁ x) (φ x)) μ ∧
    Integrable (fun x => inner ℝ (f x) (φ x)) μ ∧
    (∀ s ∈ Set.Ioc a b, Integrable (CycleWords.weakEquationRhs ν v φ dφ du flux F g s) μ) ∧
    IntegrableOn (fun s => ∫ x, CycleWords.weakEquationRhs ν v φ dφ du flux F g s x ∂μ)
      (Set.Ioc a b) ∧
    ((∫ x, inner ℝ (u₁ x) (φ x) ∂μ) - (∫ x, inner ℝ (f x) (φ x) ∂μ) =
      ∫ s in Set.Ioc a b, ∫ x, CycleWords.weakEquationRhs ν v φ dφ du flux F g s x ∂μ) at h₁
  change Integrable (fun x => inner ℝ (u₂ x) (φ x)) μ ∧
    Integrable (fun x => inner ℝ (f x) (φ x)) μ ∧
    (∀ s ∈ Set.Ioc a t, Integrable (CycleWords.weakEquationRhs ν v φ dφ du flux F g s) μ) ∧
    IntegrableOn (fun s => ∫ x, CycleWords.weakEquationRhs ν v φ dφ du flux F g s x ∂μ)
      (Set.Ioc a t) ∧
    ((∫ x, inner ℝ (u₂ x) (φ x) ∂μ) - (∫ x, inner ℝ (f x) (φ x) ∂μ) =
      ∫ s in Set.Ioc a t, ∫ x, CycleWords.weakEquationRhs ν v φ dφ du flux F g s x ∂μ) at h₂
  obtain ⟨hu₁, _, _, ht₁, he₁⟩ := h₁
  obtain ⟨hu₂, _, hs₂, ht₂, he₂⟩ := h₂
  change Integrable (fun x => inner ℝ (u₂ x) (φ x)) μ ∧
    Integrable (fun x => inner ℝ (u₁ x) (φ x)) μ ∧
    (∀ s ∈ Set.Ioc b t, Integrable (CycleWords.weakEquationRhs ν v φ dφ du flux F g s) μ) ∧
    IntegrableOn (fun s => ∫ x, CycleWords.weakEquationRhs ν v φ dφ du flux F g s x ∂μ)
      (Set.Ioc b t) ∧
    ((∫ x, inner ℝ (u₂ x) (φ x) ∂μ) - (∫ x, inner ℝ (u₁ x) (φ x) ∂μ) =
      ∫ s in Set.Ioc b t, ∫ x, CycleWords.weakEquationRhs ν v φ dφ du flux F g s x ∂μ)
  have hsub : Set.Ioc b t ⊆ Set.Ioc a t := Set.Ioc_subset_Ioc_left hab
  refine ⟨hu₂, hu₁, fun s hs => hs₂ s (hsub hs), ht₂.mono_set hsub, ?_⟩
  have hsplit :
      (∫ s in Set.Ioc a t, ∫ x, CycleWords.weakEquationRhs ν v φ dφ du flux F g s x ∂μ) =
        (∫ s in Set.Ioc a b, ∫ x, CycleWords.weakEquationRhs ν v φ dφ du flux F g s x ∂μ) +
          ∫ s in Set.Ioc b t, ∫ x, CycleWords.weakEquationRhs ν v φ dφ du flux F g s x ∂μ := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc hab hbt]
    exact setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc ht₁
      (ht₂.mono_set hsub)
  linarith

section Flux
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

/-- The coupling flux of a difference of jets is the difference of the coupling fluxes. -/
theorem flux_sum_sub_of_jets {D : ℕ} {K : ι → ℕ} (i : ι)
    (A : ∀ (i' : ι) (d : admissibleOrders K D i i'),
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (J J₁ J₂ : ∀ (i' : ι) (d : admissibleOrders K D i i'), DerivativeWord2 (d.1 - 1) → h i')
    (hJ : ∀ i' d word, J i' d word = J₁ i' d word - J₂ i' d word) :
    ∑ i' : ι, ∑ d : admissibleOrders K D i i', A i' d (WithLp.toLp 2 (J i' d)) =
      (∑ i' : ι, ∑ d : admissibleOrders K D i i', A i' d (WithLp.toLp 2 (J₁ i' d))) -
        ∑ i' : ι, ∑ d : admissibleOrders K D i i', A i' d (WithLp.toLp 2 (J₂ i' d)) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hfun : J i' d = J₁ i' d - J₂ i' d := funext (hJ i' d)
  rw [hfun, WithLp.toLp_sub, map_sub]

end Flux

section Torus
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {ν : ℝ} {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
  {A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h i))}

/-- A solution on `[t₀, t₂]` is a solution on `[t₀, t₁]` for `t₁ ≤ t₂`. -/
theorem isCoupledWeakSolutionTorus_restrict_left {t₀ t₁ t₂ : ℝ} (h₁₂ : t₁ ≤ t₂)
    {f : ∀ i, TorusHk (K i) (h i)}
    {F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g : ∀ i, ℝ → TorusHk (K i) (h i)} {u : ∀ i, ℝ → TorusHk (K i) (h i)}
    {w : ∀ i, ℝ → TorusHk (K i + 1) (h i)}
    (hsol : IsCoupledWeakSolutionTorus ν t₀ t₂ v D K A f F g u w) :
    IsCoupledWeakSolutionTorus ν t₀ t₁ v D K A f F g u w := by
  have hsub : Set.Icc t₀ t₁ ⊆ Set.Icc t₀ t₂ := Set.Icc_subset_Icc le_rfl h₁₂
  refine ⟨fun i => (hsol.1 i).mono hsub,
    fun i => (hsol.2.1 i).mono_measure (Measure.restrict_mono hsub le_rfl),
    fun i => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.1 i), hsol.2.2.2.1,
    fun i t ht φ => hsol.2.2.2.2 i t (hsub ht) φ⟩

/-- A solution on `[t₀, t₂]` is a solution on `[t₁, t₂]` started from its value at `t₁`. -/
theorem isCoupledWeakSolutionTorus_restrict_right {t₀ t₁ t₂ : ℝ} (h₀₁ : t₀ ≤ t₁)
    (h₁₂ : t₁ ≤ t₂) {f : ∀ i, TorusHk (K i) (h i)}
    {F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g : ∀ i, ℝ → TorusHk (K i) (h i)} {u : ∀ i, ℝ → TorusHk (K i) (h i)}
    {w : ∀ i, ℝ → TorusHk (K i + 1) (h i)}
    (hsol : IsCoupledWeakSolutionTorus ν t₀ t₂ v D K A f F g u w) :
    IsCoupledWeakSolutionTorus ν t₁ t₂ v D K A (fun i => u i t₁) F g u w := by
  have hsub : Set.Icc t₁ t₂ ⊆ Set.Icc t₀ t₂ := Set.Icc_subset_Icc h₀₁ le_rfl
  refine ⟨fun i => (hsol.1 i).mono hsub,
    fun i => (hsol.2.1 i).mono_measure (Measure.restrict_mono hsub le_rfl),
    fun i => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.1 i), fun _ => rfl, ?_⟩
  intro i t ht φ
  exact coupledWeakIdentity_restrict_right _ ν t₀ t₁ t h₀₁ ht.1 v _ _ _ _ _ _ _ _ _
    (hsol.2.2.2.2 i t₁ ⟨h₀₁, h₁₂⟩ φ) (hsol.2.2.2.2 i t (hsub ht) φ)

/-- The difference of two solutions on the same window is a solution with the differences of
the data. -/
theorem isCoupledWeakSolutionTorus_sub {t₀ t₁ : ℝ}
    {f f' : ∀ i, TorusHk (K i) (h i)}
    {F F' : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g g' : ∀ i, ℝ → TorusHk (K i) (h i)} {u u' : ∀ i, ℝ → TorusHk (K i) (h i)}
    {w w' : ∀ i, ℝ → TorusHk (K i + 1) (h i)}
    (hsol : IsCoupledWeakSolutionTorus ν t₀ t₁ v D K A f F g u w)
    (hsol' : IsCoupledWeakSolutionTorus ν t₀ t₁ v D K A f' F' g' u' w') :
    IsCoupledWeakSolutionTorus ν t₀ t₁ v D K A (fun i => f i - f' i)
      (fun i s => F i s - F' i s) (fun i s => g i s - g' i s) (fun i s => u i s - u' i s)
      (fun i s => w i s - w' i s) := by
  refine ⟨fun i => CoupledEnergy.Variational.timeContinuousOn_pointwise_sub (u i) (u' i) _
      (hsol.1 i) (hsol'.1 i),
    fun i => CoupledEnergy.Variational.timeMemLp_pointwise_sub _ 2 (w i) (w' i)
      (hsol.2.1 i) (hsol'.2.1 i), ?_, ?_, ?_⟩
  · intro i
    filter_upwards [hsol.2.2.1 i, hsol'.2.2.1 i] with s hs hs'
    show truncateTorusHk (Nat.le_succ (K i)) (w i s - w' i s) = u i s - u' i s
    rw [(truncateTorusHk (E := h i) (Nat.le_succ (K i))).map_sub, hs, hs']
  · intro i
    show u i t₀ - u' i t₀ = f i - f' i
    rw [hsol.2.2.2.1 i, hsol'.2.2.2.1 i]
  · intro i t ht φ
    have hd := CycleWords.coupledWeakIdentity_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (hsol.2.2.2.2 i t ht φ) (hsol'.2.2.2.2 i t ht φ)
    refine CycleJointProofs.coupledWeakIdentity_integrands_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ ?_ ?_ ?_ hd
    · filter_upwards [Coarse.jet_sub_ae (u i t) (u' i t)] with x hx
      simp only [Pi.sub_apply, hx]
    · filter_upwards [Coarse.jet_sub_ae (f i) (f' i)] with x hx
      simp only [Pi.sub_apply, hx]
    · intro s _
      refine CycleJointProofs.weakIdentityRhs_congr_ae _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact Filter.EventuallyEq.rfl
      · exact Filter.EventuallyEq.rfl
      · intro _
        exact Filter.EventuallyEq.rfl
      · intro k
        filter_upwards [Coarse.jet_sub_ae (w i s) (w' i s)] with x hx
        simp only [Pi.sub_apply, hx]
      · have hall : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ i' : ι, ∀ a,
            (w i' s - w' i' s).toFunction.jet a x =
              (w i' s).toFunction.jet a x - (w' i' s).toFunction.jet a x :=
          ae_all_iff.mpr (fun i' => Coarse.jet_sub_ae (w i' s) (w' i' s))
        filter_upwards [hall] with x hx
        simp only [Pi.sub_apply]
        symm
        apply flux_sum_sub_of_jets i (fun i' d => A i i' d s x)
        intro i' d word
        exact hx i' _
      · filter_upwards [Coarse.jet_sub_ae (F i s) (F' i s)] with x hx
        simp only [Pi.sub_apply, hx]
      · filter_upwards [Coarse.jet_sub_ae (g i s) (g' i s)] with x hx
        simp only [Pi.sub_apply, hx]

end Torus

end AVRegularity.CycleComparison.Error
end
