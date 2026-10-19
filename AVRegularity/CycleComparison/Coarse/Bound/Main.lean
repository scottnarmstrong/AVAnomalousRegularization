-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Coarse.Bound.FcNorm
import AVRegularity.CycleComparison.Coarse.Energy.Zero
public import AVRegularity.CycleComparison.Coarse.Energy.Word
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! **The time-integrated mass norm of the retained flux.** At almost every time of the window the
pointwise bound holds (the responses agree with their gradient fields almost everywhere); squaring,
the mass-weighted Schur test for the edge part and Cauchy–Schwarz over the cells bound the mass norm
by the gradient energies of the cells; integrating in time gives the bound by their time integrals. -/

section
/-- Cauchy–Schwarz over the cells, with masses. -/
theorem mass_cs_le {ι κ : Type*} [Fintype ι] (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (S : Finset κ)
    (g : κ → ι → ℝ) :
    ∑ v, (π v)⁻¹ * (∑ i ∈ S, Real.sqrt (g i v)) ^ 2 ≤
      (S.card : ℝ) * ∑ i ∈ S, ∑ v, (π v)⁻¹ * Real.sqrt (g i v) ^ 2 := by
  have hπi : ∀ v, 0 ≤ (π v)⁻¹ := fun v => inv_nonneg.2 (hπ v).le
  calc ∑ v, (π v)⁻¹ * (∑ i ∈ S, Real.sqrt (g i v)) ^ 2 ≤
        ∑ v, (π v)⁻¹ * ((S.card : ℝ) * ∑ i ∈ S, Real.sqrt (g i v) ^ 2) :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
          (sq_sum_le_card_mul_sum_sq) (hπi v)
    _ = _ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

/-- The Schur constant of the retained edge part. -/
def fcS (ρ t₀ t₁ B : ℝ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k p D H : ℕ) (Cstar Θ : ℝ) : ℝ :=
  cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p * covRatio t₀ t₁ ρ B Jm ^ (p + 1) *
    edgeS (k + (6 * p + D)) D H p B Cstar Θ

/-- The mass-weighted gradient energy density of one cell. -/
def cellGrad (ρ : ℝ) (π : ι → ℝ) {k J H L : ℕ}
    (Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)) (ij : ℕ × ℕ)
    (s : ℝ) : ℝ :=
  ∑ v, (π v)⁻¹ * gradFactorialNormSq ρ (Uw ij.1 ij.2 v s).val

section
variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

/-- **The mass norm of the retained flux at almost every time.** -/
theorem fc_mass_point_le (hC : 0 ≤ Cstar) (hΘ : 0 ≤ Θ) {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁)
    (hUw : ∀ ij ∈ cellBox J H, ∀ w,
      truncateTorusHk (Nat.le_succ _) (Uw ij.1 ij.2 w s) = U ij.1 ij.2 w s) :
    massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ π
        (fun v => (Fc v s).val) ≤
      4 * (fcC1 ρ a B₀ t₀ t₁ B Jm k p D AD ^ 2 *
          ((Finset.range J ×ˢ Finset.range (H + 1)).card : ℝ) *
            ∑ ij ∈ Finset.range J ×ˢ Finset.range (H + 1), cellGrad ρ π Uw ij s +
        fcS ρ t₀ t₁ B Jm k p D H Cstar Θ ^ 2 *
          ((Finset.range (J + 1) ×ˢ Finset.range H).card : ℝ) *
            ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H, cellGrad ρ π Uw ij s +
        fcC3 ρ a B₀ t₀ t₁ B Jm k p D AD ^ 2 *
          ((({J} : Finset ℕ) ×ˢ Finset.range (H + 1)).card : ℝ) *
            ∑ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1), cellGrad ρ π Uw ij s +
        fcC5 ρ t₀ t₁ B Jm k p D ^ 2 *
          ((Finset.range (J + 1) ×ˢ Finset.range (H + 1)).card : ℝ) *
            ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1), cellGrad ρ π Uw ij s) := by
  have hπ := P.mass_pos
  have hρ := P.rho_pos
  have hKc : k + (6 * p + D) ≤ N := Nat.le_of_succ_le (fcKc_le P)
  have hω := covRatio_nonneg t₀ t₁ ρ B Jm
  have hq : 0 ≤ cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p *
      covRatio t₀ t₁ ρ B Jm ^ (p + 1) :=
    mul_nonneg (cqpBig_nonneg (by positivity) p) (pow_nonneg hω _)
  have hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * fcC2 ρ t₀ t₁ B Jm k p D H CE v u ≤
      fcS ρ t₀ t₁ B Jm k p D H Cstar Θ := fun v => by
    have e : ∑ u, Real.sqrt (π u / π v) * fcC2 ρ t₀ t₁ B Jm k p D H CE v u =
        (cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p * covRatio t₀ t₁ ρ B Jm ^ (p + 1)) *
          ∑ u, Real.sqrt (π u / π v) * cellCgE ρ (k + (6 * p + D)) D H p t₀ t₁ CE v u := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by unfold fcC2; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (edge_row_le P hKc hC hΘ v) hq
  have hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * fcC2 ρ t₀ t₁ B Jm k p D H CE v u ≤
      fcS ρ t₀ t₁ B Jm k p D H Cstar Θ := fun u => by
    have e : ∑ v, Real.sqrt (π u / π v) * fcC2 ρ t₀ t₁ B Jm k p D H CE v u =
        (cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p * covRatio t₀ t₁ ρ B Jm ^ (p + 1)) *
          ∑ v, Real.sqrt (π u / π v) * cellCgE ρ (k + (6 * p + D)) D H p t₀ t₁ CE v u := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by unfold fcC2; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (edge_col_le P hKc hC hΘ u) hq
  have hc : ∀ v u, 0 ≤ fcC2 ρ t₀ t₁ B Jm k p D H CE v u := fun v u =>
    mul_nonneg hq (cellCgE_nonneg hρ _ v u)
  have hm := mass_four_le π hπ (fun v u => fcC2 ρ t₀ t₁ B Jm k p D H CE v u) hc hrow hcol
    (fun v => factorialNormSq ρ (Fc v s).val)
    (fun v => ∑ ij ∈ Finset.range J ×ˢ Finset.range (H + 1),
      Real.sqrt (gradFactorialNormSq ρ (Uw ij.1 ij.2 v s).val))
    (fun v => ∑ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1),
      Real.sqrt (gradFactorialNormSq ρ (Uw ij.1 ij.2 v s).val))
    (fun v => ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1),
      Real.sqrt (gradFactorialNormSq ρ (Uw ij.1 ij.2 v s).val))
    (fun u => ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H,
      Real.sqrt (gradFactorialNormSq ρ (Uw ij.1 ij.2 u s).val))
    (fun v => factorialNormSq_nonneg ρ _) (fun v => fc_point_le P hR hWit hs hUw v)
  have hcs : ∀ (S : Finset (ℕ × ℕ)), ∑ v, (π v)⁻¹ * (∑ ij ∈ S,
      Real.sqrt (gradFactorialNormSq ρ (Uw ij.1 ij.2 v s).val)) ^ 2 ≤
      (S.card : ℝ) * ∑ ij ∈ S, cellGrad ρ π Uw ij s := fun S => by
    refine (mass_cs_le π hπ S (fun ij v => gradFactorialNormSq ρ (Uw ij.1 ij.2 v s).val)).trans
      (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun ij _ => ?_
    unfold cellGrad
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Real.sq_sqrt (gradFactorialNormSq_nonneg ρ _)]
  have e0 : massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ π
      (fun v => (Fc v s).val) = ∑ v, (π v)⁻¹ * factorialNormSq ρ (Fc v s).val := rfl
  rw [e0]
  refine hm.trans ?_
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  refine mul_le_mul_of_nonneg_left ?_ h4
  have h1 := hcs (Finset.range J ×ˢ Finset.range (H + 1))
  have h2 := hcs (Finset.range (J + 1) ×ˢ Finset.range H)
  have h3 := hcs (({J} : Finset ℕ) ×ˢ Finset.range (H + 1))
  have h5 := hcs (Finset.range (J + 1) ×ˢ Finset.range (H + 1))
  have p1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (fcC1 ρ a B₀ t₀ t₁ B Jm k p D AD))
  have p2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (fcS ρ t₀ t₁ B Jm k p D H Cstar Θ))
  have p3 := mul_le_mul_of_nonneg_left h3 (sq_nonneg (fcC3 ρ a B₀ t₀ t₁ B Jm k p D AD))
  have p5 := mul_le_mul_of_nonneg_left h5 (sq_nonneg (fcC5 ρ t₀ t₁ B Jm k p D))
  simp only [mul_assoc] at p1 p2 p3 p5 ⊢
  linarith

end
end

/-! **The time-integrated mass norm of the retained flux**, bounded by the time integrals of the
gradient energies of the cells, and those by the word energies. -/

section
/-- The integral of a four-part combination of finite sums. -/
theorem integral_four {κ : Type*} {μ : Measure ℝ} (A1 A2 A3 A5 : ℝ)
    (S1 S2 S3 S5 : Finset κ) (F : κ → ℝ → ℝ) (h1 : ∀ i ∈ S1, Integrable (F i) μ)
    (h2 : ∀ i ∈ S2, Integrable (F i) μ) (h3 : ∀ i ∈ S3, Integrable (F i) μ)
    (h5 : ∀ i ∈ S5, Integrable (F i) μ) :
    Integrable (fun s => 4 * (A1 * ∑ i ∈ S1, F i s + A2 * ∑ i ∈ S2, F i s +
      A3 * ∑ i ∈ S3, F i s + A5 * ∑ i ∈ S5, F i s)) μ ∧
    ∫ s, 4 * (A1 * ∑ i ∈ S1, F i s + A2 * ∑ i ∈ S2, F i s +
      A3 * ∑ i ∈ S3, F i s + A5 * ∑ i ∈ S5, F i s) ∂μ =
      4 * (A1 * ∑ i ∈ S1, ∫ s, F i s ∂μ + A2 * ∑ i ∈ S2, ∫ s, F i s ∂μ +
        A3 * ∑ i ∈ S3, ∫ s, F i s ∂μ + A5 * ∑ i ∈ S5, ∫ s, F i s ∂μ) := by
  have i1 := (integrable_finsetSum S1 h1).const_mul A1
  have i2 := (integrable_finsetSum S2 h2).const_mul A2
  have i3 := (integrable_finsetSum S3 h3).const_mul A3
  have i5 := (integrable_finsetSum S5 h5).const_mul A5
  refine ⟨(((i1.add i2).add i3).add i5).const_mul 4, ?_⟩
  have e1 : ∫ s, (A1 * ∑ i ∈ S1, F i s + A2 * ∑ i ∈ S2, F i s + A3 * ∑ i ∈ S3, F i s) +
      A5 * ∑ i ∈ S5, F i s ∂μ = ∫ s, A1 * ∑ i ∈ S1, F i s + A2 * ∑ i ∈ S2, F i s +
        A3 * ∑ i ∈ S3, F i s ∂μ + ∫ s, A5 * ∑ i ∈ S5, F i s ∂μ :=
    integral_add (f := fun s => A1 * ∑ i ∈ S1, F i s + A2 * ∑ i ∈ S2, F i s +
      A3 * ∑ i ∈ S3, F i s) (g := fun s => A5 * ∑ i ∈ S5, F i s) ((i1.add i2).add i3) i5
  have e2 : ∫ s, (A1 * ∑ i ∈ S1, F i s + A2 * ∑ i ∈ S2, F i s) + A3 * ∑ i ∈ S3, F i s ∂μ =
      ∫ s, A1 * ∑ i ∈ S1, F i s + A2 * ∑ i ∈ S2, F i s ∂μ + ∫ s, A3 * ∑ i ∈ S3, F i s ∂μ :=
    integral_add (f := fun s => A1 * ∑ i ∈ S1, F i s + A2 * ∑ i ∈ S2, F i s)
      (g := fun s => A3 * ∑ i ∈ S3, F i s) (i1.add i2) i3
  have e3 : ∫ s, A1 * ∑ i ∈ S1, F i s + A2 * ∑ i ∈ S2, F i s ∂μ =
      ∫ s, A1 * ∑ i ∈ S1, F i s ∂μ + ∫ s, A2 * ∑ i ∈ S2, F i s ∂μ :=
    integral_add (f := fun s => A1 * ∑ i ∈ S1, F i s) (g := fun s => A2 * ∑ i ∈ S2, F i s) i1 i2
  rw [integral_const_mul, e1, e2, e3, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_finsetSum S1 h1, integral_finsetSum S2 h2,
    integral_finsetSum S3 h3, integral_finsetSum S5 h5]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem cellGrad_nonneg (ρ : ℝ) {π : ι → ℝ} [Fintype ι] (hπ : ∀ v, 0 < π v) {k J H L : ℕ}
    (Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v))
    (ij : ℕ × ℕ) (s : ℝ) : 0 ≤ cellGrad ρ π Uw ij s :=
  Finset.sum_nonneg fun v _ =>
    mul_nonneg (inv_nonneg.2 (hπ v).le) (gradFactorialNormSq_nonneg ρ _)

section
variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

/-- **The time-integrated mass norm of the retained flux.** -/
theorem fc_mass_lintegral_le (hC : 0 ≤ Cstar) (hΘ : 0 ≤ Θ) {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc) :
    ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (massNormSq
        (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ π
        (fun v => (Fc v s).val)) ≤
      ENNReal.ofReal (4 * (fcC1 ρ a B₀ t₀ t₁ B Jm k p D AD ^ 2 *
          ((Finset.range J ×ˢ Finset.range (H + 1)).card : ℝ) *
            ∑ ij ∈ Finset.range J ×ˢ Finset.range (H + 1),
              (∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s) +
        fcS ρ t₀ t₁ B Jm k p D H Cstar Θ ^ 2 *
          ((Finset.range (J + 1) ×ˢ Finset.range H).card : ℝ) *
            ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H,
              (∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s) +
        fcC3 ρ a B₀ t₀ t₁ B Jm k p D AD ^ 2 *
          ((({J} : Finset ℕ) ×ˢ Finset.range (H + 1)).card : ℝ) *
            ∑ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1),
              (∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s) +
        fcC5 ρ t₀ t₁ B Jm k p D ^ 2 *
          ((Finset.range (J + 1) ×ˢ Finset.range (H + 1)).card : ℝ) *
            ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1),
              (∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s))) := by
  have hS1 : ∀ ij ∈ Finset.range J ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hS2 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H, ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hS3 : ∀ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hij; omega
  have hS5 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hw : ∀ ij ∈ cellBox J H, (∀ v, MemLp (Uw ij.1 ij.2 v) 2
      (volume.restrict (Set.Icc t₀ t₁))) ∧ ∀ v, ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)),
        truncateTorusHk (Nat.le_succ _) (Uw ij.1 ij.2 v s) = U ij.1 ij.2 v s := by
    intro ij hij
    obtain ⟨hi, hj⟩ := mem_cellBox hij
    obtain ⟨f₀, -, hs, -⟩ := hR ij.1 hi ij.2 hj
    exact ⟨hs.2.1, hs.2.2.1⟩
  have hae : ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)), ∀ ij ∈ cellBox J H, ∀ w,
      truncateTorusHk (Nat.le_succ _) (Uw ij.1 ij.2 w s) = U ij.1 ij.2 w s := by
    rw [Filter.eventually_all_finset]
    intro ij hij
    rw [ae_all_iff]
    exact (hw ij hij).2
  have hint : ∀ ij ∈ cellBox J H, Integrable (cellGrad ρ π Uw ij)
      (volume.restrict (Set.Icc t₀ t₁)) := fun ij hij =>
    integrable_finsetSum _ fun v _ =>
      (integrable_gradFactorialNormSq_torus ((hw ij hij).1 v)).const_mul _
  obtain ⟨hΨi, hΨ⟩ := integral_four (μ := volume.restrict (Set.Icc t₀ t₁))
    (fcC1 ρ a B₀ t₀ t₁ B Jm k p D AD ^ 2 *
      ((Finset.range J ×ˢ Finset.range (H + 1)).card : ℝ))
    (fcS ρ t₀ t₁ B Jm k p D H Cstar Θ ^ 2 * ((Finset.range (J + 1) ×ˢ Finset.range H).card : ℝ))
    (fcC3 ρ a B₀ t₀ t₁ B Jm k p D AD ^ 2 *
      ((({J} : Finset ℕ) ×ˢ Finset.range (H + 1)).card : ℝ))
    (fcC5 ρ t₀ t₁ B Jm k p D ^ 2 *
      ((Finset.range (J + 1) ×ˢ Finset.range (H + 1)).card : ℝ))
    _ _ _ _ (fun ij s => cellGrad ρ π Uw ij s)
    (fun ij hij => hint ij (mem_cellBox_of hS1 hij)) (fun ij hij => hint ij (mem_cellBox_of hS2 hij))
    (fun ij hij => hint ij (mem_cellBox_of hS3 hij)) (fun ij hij => hint ij (mem_cellBox_of hS5 hij))
  have hg0 := cellGrad_nonneg ρ P.mass_pos Uw
  have hΨ0 : ∀ s, 0 ≤ 4 * (fcC1 ρ a B₀ t₀ t₁ B Jm k p D AD ^ 2 *
        ((Finset.range J ×ˢ Finset.range (H + 1)).card : ℝ) *
          ∑ ij ∈ Finset.range J ×ˢ Finset.range (H + 1), cellGrad ρ π Uw ij s +
      fcS ρ t₀ t₁ B Jm k p D H Cstar Θ ^ 2 *
        ((Finset.range (J + 1) ×ˢ Finset.range H).card : ℝ) *
          ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H, cellGrad ρ π Uw ij s +
      fcC3 ρ a B₀ t₀ t₁ B Jm k p D AD ^ 2 *
        ((({J} : Finset ℕ) ×ˢ Finset.range (H + 1)).card : ℝ) *
          ∑ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1), cellGrad ρ π Uw ij s +
      fcC5 ρ t₀ t₁ B Jm k p D ^ 2 *
        ((Finset.range (J + 1) ×ˢ Finset.range (H + 1)).card : ℝ) *
          ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1), cellGrad ρ π Uw ij s) :=
    fun s => by
      have hsum : ∀ S : Finset (ℕ × ℕ), 0 ≤ ∑ ij ∈ S, cellGrad ρ π Uw ij s :=
        fun S => Finset.sum_nonneg fun ij _ => hg0 ij s
      refine mul_nonneg (by norm_num) (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) <;>
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (hsum _)
  calc ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (massNormSq
        (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ π
        (fun v => (Fc v s).val)) ≤
      ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (4 * (fcC1 ρ a B₀ t₀ t₁ B Jm k p D AD ^ 2 *
          ((Finset.range J ×ˢ Finset.range (H + 1)).card : ℝ) *
            ∑ ij ∈ Finset.range J ×ˢ Finset.range (H + 1), cellGrad ρ π Uw ij s +
        fcS ρ t₀ t₁ B Jm k p D H Cstar Θ ^ 2 *
          ((Finset.range (J + 1) ×ˢ Finset.range H).card : ℝ) *
            ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H, cellGrad ρ π Uw ij s +
        fcC3 ρ a B₀ t₀ t₁ B Jm k p D AD ^ 2 *
          ((({J} : Finset ℕ) ×ˢ Finset.range (H + 1)).card : ℝ) *
            ∑ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1), cellGrad ρ π Uw ij s +
        fcC5 ρ t₀ t₁ B Jm k p D ^ 2 *
          ((Finset.range (J + 1) ×ˢ Finset.range (H + 1)).card : ℝ) *
            ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1), cellGrad ρ π Uw ij s)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with s h1 h2
        exact ENNReal.ofReal_le_ofReal (fc_mass_point_le P hC hΘ hR hWit h2 h1)
    _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hΨi (Filter.Eventually.of_forall hΨ0), hΨ]

end
end

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! The word energies of the cells at the letter sizes of the defect bound (whose constant
dominates the word constant), and the resulting bound of the time-integrated gradient energy of
each cell. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

section
variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem letter0_nonneg :
    0 ≤ a * B₀ * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
      + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
          (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal := by
  have ha := P.a_nonneg
  have hB0 : 0 ≤ B₀ := zero_le_one.trans P.B₀_ge
  have hB := P.B_pos
  have hσ : 0 ≤ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal := ENNReal.toReal_nonneg
  exact add_nonneg (div_nonneg (mul_nonneg (mul_nonneg ha hB0) hσ) hB.le) ENNReal.toReal_nonneg

/-- **The cell energies at the letter sizes of the defect bound.** -/
theorem cell_energy_le (hC : 0 ≤ Cstar) (hΘ : 0 ≤ Θ) {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {C : ℝ} (hCw : wordConst D H p J k ≤ C) {q₀ q₁ : ℝ}
    (hq₀ : q₀ = C * (a * B₀ * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
      + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
          (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal))
    (hq₁ : q₁ = C * (∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r)) {i j : ℕ} (hi : i ≤ J)
    (hj : j ≤ H) :
    AVRegularity.strongEnergy ρ B π t₀ t₁ (U i j) (Uw i j) ≤
      ENNReal.ofReal (4 * (Nat.choose (i + j) i : ℝ) * (4 * q₀) ^ i * (4 * q₁) ^ j *
        Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val))) := by
  have hs0 := letter0_nonneg P
  have hs1 : 0 ≤ ∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r :=
    Finset.sum_nonneg fun r _ => pow_nonneg (mul_nonneg hC hΘ) r
  have hw := word_energy P hC hΘ hR rfl rfl hi hj
  refine hw.trans (ENNReal.ofReal_le_ofReal ?_)
  have hF := Real.sqrt_nonneg (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val))
  have hw0 := wordConst_nonneg D H p J k
  have a0 : 0 ≤ 4 * (wordConst D H p J k * (a * B₀ *
      (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
      + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
          (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal)) := by positivity
  have a1 : 0 ≤ 4 * (wordConst D H p J k * ∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r) := by
    positivity
  have l0 : 4 * (wordConst D H p J k * (a * B₀ *
      (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
      + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
          (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal)) ≤ 4 * q₀ := by
    rw [hq₀]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCw hs0) (by norm_num)
  have l1 : 4 * (wordConst D H p J k * ∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r) ≤ 4 * q₁ := by
    rw [hq₁]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCw hs1) (by norm_num)
  have hc : (0 : ℝ) ≤ 4 * (Nat.choose (i + j) i : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ a0 l0 i) hc) (pow_le_pow_left₀ a1 l1 j) (pow_nonneg a1 j)
    (mul_nonneg hc (pow_nonneg (a0.trans l0) i))) hF

/-- **The time-integrated gradient energy of a cell.** -/
theorem cell_grad_le (hC : 0 ≤ Cstar) (hΘ : 0 ≤ Θ) {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {C : ℝ} (hCw : wordConst D H p J k ≤ C) {q₀ q₁ : ℝ}
    (hq₀ : q₀ = C * (a * B₀ * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
      + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
          (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal))
    (hq₁ : q₁ = C * (∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r)) {ij : ℕ × ℕ}
    (hij : ij ∈ cellBox J H) :
    B * ∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s ≤
      (4 * Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val))) ^ 2 *
        ((Nat.choose (ij.1 + ij.2) ij.1 : ℝ) * (4 * q₀) ^ ij.1 * (4 * q₁) ^ ij.2) ^ 2 := by
  obtain ⟨hi, hj⟩ := mem_cellBox hij
  have hE := cell_energy_le P hC hΘ hR hCw hq₀ hq₁ hi hj
  obtain ⟨f₀, -, hsol, -⟩ := hR ij.1 hi ij.2 hj
  have hg := grad_le_strongEnergy_sq (ρ := ρ) P.B_pos.le P.mass_pos (U ij.1 ij.2) (Uw ij.1 ij.2)
    hsol.2.1
  have hF := Real.sqrt_nonneg (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val))
  have hs0 := letter0_nonneg P
  have hs1 : 0 ≤ ∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r :=
    Finset.sum_nonneg fun r _ => pow_nonneg (mul_nonneg hC hΘ) r
  have hC0 : 0 ≤ C := (wordConst_nonneg D H p J k).trans hCw
  have hq0 : 0 ≤ q₀ := by rw [hq₀]; exact mul_nonneg hC0 hs0
  have hq1 : 0 ≤ q₁ := by rw [hq₁]; exact mul_nonneg hC0 hs1
  set X := 4 * (Nat.choose (ij.1 + ij.2) ij.1 : ℝ) * (4 * q₀) ^ ij.1 * (4 * q₁) ^ ij.2 *
    Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val)) with hX
  have hX0 : 0 ≤ X := by positivity
  have h2 : AVRegularity.strongEnergy ρ B π t₀ t₁ (U ij.1 ij.2) (Uw ij.1 ij.2) ^ (2 : ℝ) ≤
      ENNReal.ofReal X ^ (2 : ℝ) := ENNReal.rpow_le_rpow hE (by norm_num)
  have h3 : ENNReal.ofReal X ^ (2 : ℝ) = ENNReal.ofReal (X ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hX0 (by norm_num), Real.rpow_two]
  have h4 := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg X)).1 (hg.trans (h2.trans h3.le))
  calc B * ∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s ≤ X ^ 2 := h4
    _ = _ := by rw [hX]; ring

end
end

/-! **The defect bounds**: the energy of the retained field is at
most `C Σ F₀`, and the normalized `L²H` norm of the retained flux is at most
`C F₀ [{ω^{p+1}(q₀ + q₁) + k₀ ω^p} Σ + q₀ ∑_h binom(J+h,J)(4q₀)^J(4q₁)^h]`, with an explicit
constant depending only on `D, H, p, J, k`. -/

section
/-- The four letter constants of the retained flux, summed. -/
def boundK (D H p k : ℕ) : ℝ :=
  cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p * 28 * gfbD (k + (6 * p + D)) D p +
    cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p * gfbE (k + (6 * p + D)) D H p +
    28 * gfbD (k + (6 * p + D)) D p +
    ((p.factorial : ℝ)⁻¹) * (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) ^ p * 4

/-- **The constant of the defect bounds.** -/
def boundC (D H p J k : ℕ) : ℝ :=
  max (max 1 (wordConst D H p J k))
    (max (8 * Real.sqrt (((J + 1) * (H + 1) : ℕ) : ℝ) * boundK D H p k)
      (4 * covPolyConst (4 * ((k + 2 * (D + 8 * p + 4) : ℕ) : ℝ) ^ 2) p *
        Real.sqrt (((J + 1) * (H + 1) : ℕ) : ℝ)))

theorem one_le_boundC (D H p J k : ℕ) : 1 ≤ boundC D H p J k :=
  le_max_of_le_left (le_max_left _ _)

theorem boundC_nonneg (D H p J k : ℕ) : 0 ≤ boundC D H p J k :=
  zero_le_one.trans (one_le_boundC D H p J k)

theorem sum_sq_le_sq_sum {κ : Type*} (S : Finset κ) (x : κ → ℝ) (hx : ∀ i ∈ S, 0 ≤ x i) :
    ∑ i ∈ S, x i ^ 2 ≤ (∑ i ∈ S, x i) ^ 2 := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hx hi) (hx i hi)

theorem card_le_box {J H : ℕ} {S : Finset (ℕ × ℕ)} (hS : ∀ ij ∈ S, ij.1 ≤ J ∧ ij.2 ≤ H) :
    (S.card : ℝ) ≤ (((J + 1) * (H + 1) : ℕ) : ℝ) := by
  have h1 : S ⊆ cellBox J H := fun ij hij => mem_cellBox_of hS hij
  have h2 : (cellBox J H).card = (J + 1) * (H + 1) := by
    simp [cellBox, Finset.card_product]
  exact_mod_cast h2 ▸ Finset.card_le_card h1

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

section
variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem cellCgD_div_le :
    cellCgD ρ a B₀ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal (k + (6 * p + D)) D p
      t₀ t₁ AD / B ≤ 28 * gfbD (k + (6 * p + D)) D p *
        (a * B₀ * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
          + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
              (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal) := by
  have hσ : 0 ≤ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal := ENNReal.toReal_nonneg
  have hKc : k + (6 * p + D) ≤ N := Nat.le_of_succ_le (fcKc_le P)
  have h1 := letterD_le P hσ hKc
  have h0 : 0 ≤ cellCgD ρ a B₀ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal
      (k + (6 * p + D)) D p t₀ t₁ AD / B := div_nonneg (cellCgD_nonneg P hσ _) P.B_pos.le
  have h48 : 1 ≤ Real.sqrt 48 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  calc _ ≤ Real.sqrt 48 * (cellCgD ρ a B₀ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal
        (k + (6 * p + D)) D p t₀ t₁ AD / B) := le_mul_of_one_le_left h0 h48
    _ = Real.sqrt 48 * cellCgD ρ a B₀ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal
        (k + (6 * p + D)) D p t₀ t₁ AD / B := (mul_div_assoc _ _ _).symm
    _ ≤ _ := h1

/-- **The defect bounds.** -/
theorem coarse_defect_bound_main (hC : 0 ≤ Cstar) (hΘ : 0 ≤ Θ) {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    {q₀ q₁ : ℝ}
    (hq₀ : q₀ = boundC D H p J k * (a * B₀ *
      (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
      + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
          (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal))
    (hq₁ : q₁ = boundC D H p J k * (∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r))
    {Sig ω k₀ : ℝ}
    (hSig : Sig = ∑ i ∈ Finset.range (J + 1), ∑ j ∈ Finset.range (H + 1),
      (Nat.choose (i + j) i : ℝ) * (4 * q₀) ^ i * (4 * q₁) ^ j)
    (hω : ω = (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / ρ ^ 2)
    (hk₀ : k₀ = (matrixSupNorm (fun t => Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁).toReal /
      B) :
    AVRegularity.strongEnergyUpTo ρ B π t₀ t₁ k W
        ≤ ENNReal.ofReal (boundC D H p J k * Sig *
          Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val))) ∧
      ENNReal.ofReal (Real.sqrt B)⁻¹ * (∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal
          (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ π
            (fun v => (Fc v s).val))) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (boundC D H p J k *
          Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val)) *
          ((ω ^ (p + 1) * (q₀ + q₁) + k₀ * ω ^ p) * Sig
            + q₀ * ∑ j ∈ Finset.range (H + 1),
              (Nat.choose (J + j) J : ℝ) * (4 * q₀) ^ J * (4 * q₁) ^ j)) := by
  set C := boundC D H p J k with hCdef
  set F₀ := Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val)) with hF₀
  have hB := P.B_pos
  have hC1 : 1 ≤ C := one_le_boundC D H p J k
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  have hCw : wordConst D H p J k ≤ C := le_max_of_le_left (le_max_right _ _)
  have hCF : 8 * Real.sqrt (((J + 1) * (H + 1) : ℕ) : ℝ) * boundK D H p k ≤ C :=
    le_max_of_le_right (le_max_left _ _)
  have hCW : 4 * covPolyConst (4 * ((k + 2 * (D + 8 * p + 4) : ℕ) : ℝ) ^ 2) p *
      Real.sqrt (((J + 1) * (H + 1) : ℕ) : ℝ) ≤ C := le_max_of_le_right (le_max_right _ _)
  have hF : 0 ≤ F₀ := Real.sqrt_nonneg _
  have hs0 := letter0_nonneg P
  have hs1 : 0 ≤ ∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r :=
    Finset.sum_nonneg fun r _ => pow_nonneg (mul_nonneg hC hΘ) r
  have hq0 : 0 ≤ q₀ := by rw [hq₀]; exact mul_nonneg hC0 hs0
  have hq1 : 0 ≤ q₁ := by rw [hq₁]; exact mul_nonneg hC0 hs1
  -- the cell weights
  set e : ℕ × ℕ → ℝ := fun ij => (Nat.choose (ij.1 + ij.2) ij.1 : ℝ) * (4 * q₀) ^ ij.1 *
    (4 * q₁) ^ ij.2 with he
  have he0 : ∀ ij, 0 ≤ e ij := fun ij => by simp only [he]; positivity
  have hSigBox : ∑ ij ∈ cellBox J H, e ij = Sig := by
    rw [hSig, cellBox, Finset.sum_product]
  have hsub : ∀ {S : Finset (ℕ × ℕ)}, (∀ ij ∈ S, ij.1 ≤ J ∧ ij.2 ≤ H) →
      ∑ ij ∈ S, e ij ≤ Sig := fun hS => by
    rw [← hSigBox]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun ij hij => mem_cellBox_of hS hij)
      (fun ij _ _ => he0 ij)
  refine ⟨?_, ?_⟩
  · -- the retained field
    have hEw := retainedW_energy_le P hR hWit
    have hcells : ∑ ij ∈ cellBox J H,
        AVRegularity.strongEnergy ρ B π t₀ t₁ (U ij.1 ij.2) (Uw ij.1 ij.2) ≤
        ∑ ij ∈ cellBox J H, ENNReal.ofReal (4 * F₀ * e ij) :=
      Finset.sum_le_sum fun ij hij => by
        obtain ⟨hi, hj⟩ := mem_cellBox hij
        refine (cell_energy_le P hC hΘ hR hCw hq₀ hq₁ hi hj).trans (le_of_eq ?_)
        congr 1; simp only [he]; ring
    rw [← ENNReal.ofReal_sum_of_nonneg fun ij _ => mul_nonneg (by positivity) (he0 ij),
      ← Finset.mul_sum, hSigBox] at hcells
    have hL : covPolyConst (4 * ((k + 2 * L : ℕ) : ℝ) ^ 2) p =
        covPolyConst (4 * ((k + 2 * (D + 8 * p + 4) : ℕ) : ℝ) ^ 2) p := by rw [P.L_eq]
    rw [hL] at hEw
    refine hEw.trans ((mul_le_mul_right hcells _).trans ?_)
    rw [← ENNReal.ofReal_mul (mul_nonneg (covPolyConst_nonneg' (by positivity) p)
      (Real.sqrt_nonneg _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hSig0 : 0 ≤ Sig := hSigBox ▸ Finset.sum_nonneg fun ij _ => he0 ij
    calc covPolyConst (4 * ((k + 2 * (D + 8 * p + 4) : ℕ) : ℝ) ^ 2) p *
          Real.sqrt (((J + 1) * (H + 1) : ℕ) : ℝ) * (4 * F₀ * Sig) =
        (4 * covPolyConst (4 * ((k + 2 * (D + 8 * p + 4) : ℕ) : ℝ) ^ 2) p *
          Real.sqrt (((J + 1) * (H + 1) : ℕ) : ℝ)) * (Sig * F₀) := by ring
      _ ≤ C * (Sig * F₀) := mul_le_mul_of_nonneg_right hCW (mul_nonneg hSig0 hF)
      _ = C * Sig * F₀ := by ring
  · -- the retained flux
    have hlin := fc_mass_lintegral_le P hC hΘ hR hWit
    have hS1 : ∀ ij ∈ Finset.range J ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
      intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
    have hS2 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H, ij.1 ≤ J ∧ ij.2 ≤ H := by
      intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
    have hS3 : ∀ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
      intro ij hij
      simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hij; omega
    have hS5 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
      intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
    have hY : ∀ {S : Finset (ℕ × ℕ)}, (∀ ij ∈ S, ij.1 ≤ J ∧ ij.2 ≤ H) →
        B * ∑ ij ∈ S, (∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s) ≤
          (4 * F₀) ^ 2 * (∑ ij ∈ S, e ij) ^ 2 := fun {S} hS => by
      rw [Finset.mul_sum]
      calc ∑ ij ∈ S, B * (∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s) ≤
            ∑ ij ∈ S, (4 * F₀) ^ 2 * e ij ^ 2 := Finset.sum_le_sum fun ij hij =>
              (cell_grad_le P hC hΘ hR hCw hq₀ hq₁ (mem_cellBox_of hS hij)).trans_eq
                (by simp only [he]; rfl)
        _ = (4 * F₀) ^ 2 * ∑ ij ∈ S, e ij ^ 2 := (Finset.mul_sum _ _ _).symm
        _ ≤ (4 * F₀) ^ 2 * (∑ ij ∈ S, e ij) ^ 2 :=
            mul_le_mul_of_nonneg_left (sum_sq_le_sq_sum S e fun ij _ => he0 ij) (sq_nonneg _)
    have hcr : covRatio t₀ t₁ ρ B Jm = ω := by rw [hω]; rfl
    have hω0 : 0 ≤ ω := hcr ▸ covRatio_nonneg t₀ t₁ ρ B Jm
    have hσJ : 0 ≤ jDev t₀ t₁ B Jm := ENNReal.toReal_nonneg
    have hk0 : 0 ≤ k₀ := by rw [hk₀]; exact div_nonneg ENNReal.toReal_nonneg hB.le
    have hσ : 0 ≤ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal := ENNReal.toReal_nonneg
    have hκ : 0 ≤ cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p := cqpBig_nonneg (by positivity) p
    have hgD := gfbD_nonneg (k + (6 * p + D)) D p
    have hgE := gfbE_nonneg (k + (6 * p + D)) D H p
    have hc1 : 0 ≤ fcC1 ρ a B₀ t₀ t₁ B Jm k p D AD :=
      mul_nonneg (mul_nonneg hκ (pow_nonneg (covRatio_nonneg t₀ t₁ ρ B Jm) _))
        (cellCgD_nonneg P hσ _)
    have hc2 : 0 ≤ fcS ρ t₀ t₁ B Jm k p D H Cstar Θ := by
      unfold fcS edgeS
      exact mul_nonneg (mul_nonneg hκ (pow_nonneg (covRatio_nonneg t₀ t₁ ρ B Jm) _))
        (mul_nonneg (mul_nonneg hgE hB.le) hs1)
    have hc3 : 0 ≤ fcC3 ρ a B₀ t₀ t₁ B Jm k p D AD := cellCgD_nonneg P hσ _
    have hc5 : 0 ≤ fcC5 ρ t₀ t₁ B Jm k p D := by
      unfold fcC5 taylorC
      exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (pow_nonneg (mul_nonneg (by positivity) (covRatio_nonneg t₀ t₁ ρ B Jm)) p))
        (by positivity)
    have hb1 : fcC1 ρ a B₀ t₀ t₁ B Jm k p D AD / B ≤
        (cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p * 28 * gfbD (k + (6 * p + D)) D p) *
          ω ^ (p + 1) * (a * B₀ * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
            + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
                (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal) := by
      have e1 : fcC1 ρ a B₀ t₀ t₁ B Jm k p D AD / B =
          cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p * ω ^ (p + 1) *
            (cellCgD ρ a B₀ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal
              (k + (6 * p + D)) D p t₀ t₁ AD / B) := by
        unfold fcC1; rw [hcr]; ring
      rw [e1]
      calc _ ≤ cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p * ω ^ (p + 1) *
            (28 * gfbD (k + (6 * p + D)) D p *
              (a * B₀ * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
                + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
                    (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal)) :=
            mul_le_mul_of_nonneg_left (cellCgD_div_le P) (mul_nonneg hκ (pow_nonneg hω0 _))
        _ = _ := by ring
    have hb2 : fcS ρ t₀ t₁ B Jm k p D H Cstar Θ / B ≤
        (cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p * gfbE (k + (6 * p + D)) D H p) *
          ω ^ (p + 1) * (∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r) := by
      refine le_of_eq ?_
      unfold fcS edgeS
      rw [hcr]
      field_simp
    have hb3 : fcC3 ρ a B₀ t₀ t₁ B Jm k p D AD / B ≤
        (28 * gfbD (k + (6 * p + D)) D p) *
          (a * B₀ * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
            + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
                (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal) := cellCgD_div_le P
    have hb5 : fcC5 ρ t₀ t₁ B Jm k p D / B ≤
        (((p.factorial : ℝ)⁻¹) * (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) ^ p * 4) * k₀ *
          ω ^ p := by
      refine le_of_eq ?_
      unfold fcC5 taylorC
      rw [hcr, hk₀, mul_pow]
      unfold jDev
      field_simp
    have hTJ : ∑ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1), e ij =
        ∑ j ∈ Finset.range (H + 1), (Nat.choose (J + j) J : ℝ) * (4 * q₀) ^ J * (4 * q₁) ^ j := by
      rw [Finset.sum_product, Finset.sum_singleton]
    have hΨ0 : 0 ≤ 4 * (fcC1 ρ a B₀ t₀ t₁ B Jm k p D AD ^ 2 *
          ((Finset.range J ×ˢ Finset.range (H + 1)).card : ℝ) *
            ∑ ij ∈ Finset.range J ×ˢ Finset.range (H + 1),
              (∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s) +
        fcS ρ t₀ t₁ B Jm k p D H Cstar Θ ^ 2 *
          ((Finset.range (J + 1) ×ˢ Finset.range H).card : ℝ) *
            ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H,
              (∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s) +
        fcC3 ρ a B₀ t₀ t₁ B Jm k p D AD ^ 2 *
          ((({J} : Finset ℕ) ×ˢ Finset.range (H + 1)).card : ℝ) *
            ∑ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1),
              (∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s) +
        fcC5 ρ t₀ t₁ B Jm k p D ^ 2 *
          ((Finset.range (J + 1) ×ˢ Finset.range (H + 1)).card : ℝ) *
            ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1),
              (∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s)) := by
      have hI : ∀ ij, 0 ≤ ∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s := fun ij =>
        setIntegral_nonneg measurableSet_Icc fun s _ => cellGrad_nonneg ρ P.mass_pos Uw ij s
      have hsum : ∀ S : Finset (ℕ × ℕ), 0 ≤ ∑ ij ∈ S, (∫ s in Set.Icc t₀ t₁, cellGrad ρ π Uw ij s) :=
        fun S => Finset.sum_nonneg fun ij _ => hI ij
      refine mul_nonneg (by norm_num) (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) <;>
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (hsum _)
    have hsq := final_sqrt_le hB hF (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (card_le_box hS1) (card_le_box hS2) (card_le_box hS3) (card_le_box hS5)
      hc1 hc2 hc3 hc5 (Finset.sum_nonneg fun ij _ => he0 ij)
      (Finset.sum_nonneg fun ij _ => he0 ij) (Finset.sum_nonneg fun ij _ => he0 ij)
      (Finset.sum_nonneg fun ij _ => he0 ij) (hY hS1) (hY hS2) (hY hS3) (hY hS5)
    have hcmp := final_compare_le (Nb := (((J + 1) * (H + 1) : ℕ) : ℝ)) hB hF hC1
      (mul_nonneg (mul_nonneg hκ (by norm_num)) hgD) (mul_nonneg hκ hgE)
      (mul_nonneg (by norm_num) hgD) (by positivity) (pow_nonneg hω0 _) (pow_nonneg hω0 _) hs0 hs1
      hk0 (Finset.sum_nonneg fun ij _ => he0 ij) (Finset.sum_nonneg fun ij _ => he0 ij)
      (Finset.sum_nonneg fun ij _ => he0 ij) (Finset.sum_nonneg fun ij _ => he0 ij)
      hb1 hb2 hb3 hb5 (hsub hS1) (hsub hS2) (le_of_eq hTJ) (le_of_eq hSigBox) hq₀ hq₁ hCF
      hc1 hc2 hc3 hc5
    refine (mul_le_mul_right (ENNReal.rpow_le_rpow hlin (by norm_num)) _).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg hΨ0 (by norm_num), ← Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_mul_eq_div, ← Real.sqrt_div' _ hB.le]
    exact hsq.trans hcmp

end
end

end AVRegularity.CycleComparison.Coarse
end
