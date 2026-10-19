-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.ActualMeans.Transfer
public import AVRegularity.Statements.Intermediate.CycleOutput.PulseMeanField
import AVRegularity.CycleComparison.Lift.MixedJetEnergyBound
public import AVRegularity.CycleComparison.ActualMeans.KernelRegular
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.ActualMeans

/-! The transfer bound for the Eulerian diagonal letter `adLetter`: identical-history metric
stability and the Piola deformation cost `C B g_m`, and the higher diagonal means cost
`C ε_c^{n-2}`, hence `α_R ≤ C(g_m + d_sw + ∑_{n=3}^{N'+1} ε_c^{n-2})`.

The glued scalar kernel splits into the letters of order two and the letters of higher order.
* The higher orders are bounded by the weighted kernel bound, without the order `n = 2`.
* The order two is compared with the reference flux: on the lift window of a pulse the
  chart-frame letter `c⁻¹ ε_c² ρ² L_{2,2} + 𝖩` is small (the premise `θ`), and the Piola deformation
  `DΦ 𝖩 DΦᵀ - 𝖩` of the constant matrix `𝖩` is small with the deviation `g` of the chart Jacobian
  from the identity. The partition sums to one, so `𝖩 = ∑_k ϖ_k 𝖩`. -/

section
/-! ### The chain-rule coefficient of first order -/

/-- `∂_α (g ∘ Φ) = ∑_β ∂_αΦ_β (∂_β g) ∘ Φ` for words of length one. -/
theorem chainCoeff_one_one (Φ : Vec 2 → Vec 2) (α β : DerivativeWord2 1) (y : Vec 2) :
    chainCoeff Φ 1 α 1 β y = jacMatrix Φ y (β 0) (α 0) := by
  have h1 : chainCoeff Φ 0 (fun i => α i.castSucc) 1 β = fun _ => 0 := by
    rw [chainCoeff_zero]
    funext _
    simp
  have h0 : chainCoeff Φ 0 (fun i => α i.castSucc) 0 (fun i => β i.castSucc) y = 1 := by
    rw [chainCoeff_zero]
    simp
  have hz : fderiv ℝ (fun _ : Vec 2 => (0 : ℝ)) y = 0 := (hasFDerivAt_const (0 : ℝ) y).fderiv
  show fderiv ℝ (chainCoeff Φ 0 (fun i => α i.castSucc) 1 β) y (basisVec (α (Fin.last 0))) +
      chainCoeff Φ 0 (fun i => α i.castSucc) 0 (fun i => β i.castSucc) y *
        jacMatrix Φ y (β (Fin.last 0)) (α (Fin.last 0)) = jacMatrix Φ y (β 0) (α 0)
  rw [h1, hz, h0, one_mul]
  exact zero_add _

/-- The scalar entry `g • id` is no larger than `g`. -/
theorem norm_iteratedFDeriv_smul_id_le (j : ℕ) {g : Vec 2 → ℝ}
    (hg : ContDiff ℝ (j : WithTop ℕ∞) g) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun x => g x • ContinuousLinearMap.id ℝ ℝ) x‖ ≤
      ‖iteratedFDeriv ℝ j g x‖ := by
  have hn : ‖ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      (ContinuousLinearMap.id ℝ ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun s => ?_
    show ‖s • ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 * ‖s‖
    rw [norm_smul, one_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
  have hle := (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
    (ContinuousLinearMap.id ℝ ℝ)).norm_iteratedFDeriv_comp_left (f := g) (x := x)
      hg.contDiffAt (n := j) le_rfl
  exact hle.trans ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans (one_mul _).le)

/-- The amplitudes of the higher orders factor out of the sum over the orders. -/
theorem sum_hi_eq (w A₃ : ℝ) (f : ℕ → ℝ) (S : Finset ℕ) :
    ∑ n ∈ S, (if n = 2 then 0 else w * A₃) * f n =
      w * (A₃ * ∑ n ∈ S, if n = 2 then 0 else f n) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n = 2
  · rw [ite_eq_left hn, ite_eq_left hn]
    ring
  · rw [ite_eq_right hn, ite_eq_right hn]
    ring

/-- Sums over word arrays of scaled entries. -/
theorem scaled_array_sum_le {m : ℕ} (a : DerivativeWord2 m → Fin 2 → ℝ) (r B : ℝ)
    (h : ∀ β k', r * a β k' ≤ B) :
    r * ∑ β : DerivativeWord2 m, ∑ k' : Fin 2, a β k' ≤ 2 ^ m * 2 * B := by
  rw [Finset.mul_sum]
  calc ∑ β : DerivativeWord2 m, r * ∑ k' : Fin 2, a β k'
      ≤ ∑ _β : DerivativeWord2 m, 2 * B := Finset.sum_le_sum fun β _ => by
        rw [Finset.mul_sum]
        calc ∑ k' : Fin 2, r * a β k' ≤ ∑ _k' : Fin 2, B :=
              Finset.sum_le_sum fun k' _ => h β k'
          _ = 2 * B := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              norm_num
    _ = 2 ^ m * 2 * B := by
        rw [Finset.sum_const, ChartTransport.card_derivativeWord2, nsmul_eq_mul]
        push_cast
        ring

/-! ### Splitting the letters of order two from the higher orders -/

section Split

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The letters of the orders `n ≠ 2`. -/
def hiPart (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G) (n d : ℕ)
    (α : DerivativeWord2 (d - 1)) (l : Fin 2) (X : Vec 2) : G :=
  if n = 2 then 0 else W n d α l X

/-- The letters of the order `n = 2`. -/
def twoPart (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G) (n d : ℕ)
    (α : DerivativeWord2 (d - 1)) (l : Fin 2) (X : Vec 2) : G :=
  if n = 2 then W n d α l X else 0

omit [NormedSpace ℝ G] in
theorem hiPart_two (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G) (d : ℕ)
    (α : DerivativeWord2 (d - 1)) (l : Fin 2) (X : Vec 2) : hiPart W 2 d α l X = 0 := by
  rw [hiPart, ite_eq_left rfl]

omit [NormedSpace ℝ G] in
theorem hiPart_of_ne (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G) {n : ℕ}
    (hn : n ≠ 2) (d : ℕ) (α : DerivativeWord2 (d - 1)) (l : Fin 2) (X : Vec 2) :
    hiPart W n d α l X = W n d α l X := by
  rw [hiPart, ite_eq_right hn]

omit [NormedSpace ℝ G] in
theorem twoPart_two (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G) (d : ℕ)
    (α : DerivativeWord2 (d - 1)) (l : Fin 2) (X : Vec 2) :
    twoPart W 2 d α l X = W 2 d α l X := by
  rw [twoPart, ite_eq_left rfl]

omit [NormedSpace ℝ G] in
theorem twoPart_of_ne (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G) {n : ℕ}
    (hn : n ≠ 2) (d : ℕ) (α : DerivativeWord2 (d - 1)) (l : Fin 2) (X : Vec 2) :
    twoPart W n d α l X = 0 := by
  rw [twoPart, ite_eq_right hn]

omit [NormedSpace ℝ G] in
theorem hiPart_fun_two (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G) (d : ℕ)
    (α : DerivativeWord2 (d - 1)) (l : Fin 2) : hiPart W 2 d α l = fun _ => 0 :=
  funext fun X => hiPart_two W d α l X

omit [NormedSpace ℝ G] in
theorem hiPart_fun_of_ne (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G) {n : ℕ}
    (hn : n ≠ 2) (d : ℕ) (α : DerivativeWord2 (d - 1)) (l : Fin 2) :
    hiPart W n d α l = W n d α l :=
  funext fun X => hiPart_of_ne W hn d α l X

theorem contDiff_hiPart (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G) (n d : ℕ)
    (α : DerivativeWord2 (d - 1)) (l : Fin 2) {m : ℕ∞} (h : ContDiff ℝ m (W n d α l)) :
    ContDiff ℝ m (hiPart W n d α l) := by
  by_cases hn : n = 2
  · subst hn
    rw [hiPart_fun_two]
    exact contDiff_const
  · rw [hiPart_fun_of_ne W hn]
    exact h

/-- The kernel of vanishing letters vanishes. -/
theorem pulseKernel_eq_zero (c ρ εc : ℝ) (M : ℕ) (chart label : Vec 2 → Vec 2)
    {W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G}
    (hW : ∀ n d α l X, W n d α l X = 0) (m' : ℕ) (β : DerivativeWord2 m') (k' : Fin 2) :
    pulseKernel c ρ εc M chart label W m' β k' = fun _ => 0 := by
  funext x
  simp only [pulseKernel, hW, smul_zero, Finset.sum_const_zero]

/-- The kernel is the sum of the kernels of the higher orders and of the order two. -/
theorem pulseKernel_split (c ρ εc : ℝ) (M : ℕ) (chart label : Vec 2 → Vec 2)
    (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G) (m' : ℕ)
    (β : DerivativeWord2 m') (k' : Fin 2) (x : Vec 2) :
    pulseKernel c ρ εc M chart label W m' β k' x =
      pulseKernel c ρ εc M chart label (hiPart W) m' β k' x +
        pulseKernel c ρ εc M chart label (twoPart W) m' β k' x := by
  simp only [pulseKernel]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n = 2
  · subst hn
    simp only [hiPart_two, twoPart_two, smul_zero, Finset.sum_const_zero, zero_add]
  · simp only [hiPart_of_ne W hn, twoPart_of_ne W hn, smul_zero, Finset.sum_const_zero, add_zero]

/-- The kernel of the order two, tested at order two. -/
theorem pulseKernel_twoPart_one (c ρ εc : ℝ) {M : ℕ} (hM : 2 ≤ M) (chart label : Vec 2 → Vec 2)
    (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G) (β : DerivativeWord2 1)
    (k' : Fin 2) (x : Vec 2) :
    pulseKernel c ρ εc M chart label (twoPart W) 1 β k' x =
      (c⁻¹ * εc ^ 2) • ∑ l : Fin 2, jacMatrix chart (label x) k' l •
        (ρ ^ 2 • ∑ α : DerivativeWord2 1,
          jacMatrix chart (label x) (β 0) (α 0) • W 2 2 α l (ρ⁻¹ • label x)) := by
  have h2 : (2 : ℕ) ∈ Finset.Icc 2 M := Finset.mem_Icc.2 ⟨le_rfl, hM⟩
  have hsum := Finset.sum_eq_single_of_mem
    (f := fun n => (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix chart (label x) k' l •
      ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
        chainCoeff chart (d - 1) α 1 β (label x) • twoPart W n d α l (ρ⁻¹ • label x)) 2 h2
    (fun n _ hn => by
      simp only [twoPart_of_ne W hn, smul_zero, Finset.sum_const_zero])
  refine hsum.trans ?_
  show (c⁻¹ * εc ^ 2) • ∑ l : Fin 2, jacMatrix chart (label x) k' l •
      ∑ d ∈ Finset.Icc 2 2, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
        chainCoeff chart (d - 1) α 1 β (label x) • twoPart W 2 d α l (ρ⁻¹ • label x) = _
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [Finset.Icc_self, Finset.sum_singleton]
  show ρ ^ 2 • ∑ α : DerivativeWord2 1,
      chainCoeff chart 1 α 1 β (label x) • twoPart W 2 2 α l (ρ⁻¹ • label x) = _
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [chainCoeff_one_one, twoPart_two]

/-- The kernel of the order two vanishes when tested at higher orders. -/
theorem pulseKernel_twoPart_of_ge (c ρ εc : ℝ) (M : ℕ) (chart label : Vec 2 → Vec 2)
    (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G) {m' : ℕ} (hm' : 2 ≤ m')
    (β : DerivativeWord2 m') (k' : Fin 2) (x : Vec 2) :
    pulseKernel c ρ εc M chart label (twoPart W) m' β k' x = 0 := by
  unfold pulseKernel
  refine Finset.sum_eq_zero fun n _ => ?_
  by_cases hn : n = 2
  · subst hn
    have hz : ∀ l : Fin 2, (∑ d ∈ Finset.Icc 2 2, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
        chainCoeff chart (d - 1) α m' β (label x) • twoPart W 2 d α l (ρ⁻¹ • label x)) = 0 := by
      intro l
      refine Finset.sum_eq_zero fun d hd => ?_
      have hd2 : d = 2 := by
        have := Finset.mem_Icc.1 hd
        omega
      subst hd2
      have h0 : ∀ α : DerivativeWord2 (2 - 1), chainCoeff chart (2 - 1) α m' β (label x) = 0 :=
        fun α => congrFun (chainCoeff_eq_zero_of_lt chart (2 - 1) α m' β (by omega)) (label x)
      simp only [h0, zero_smul, Finset.sum_const_zero, smul_zero]
    simp only [hz, smul_zero, Finset.sum_const_zero]
  · simp only [twoPart_of_ne W hn, smul_zero, Finset.sum_const_zero]

end Split

/-! ### The order two of one pulse against a constant matrix -/

/-- **The order-two kernel against the reference flux.** With `Dv = b₂ L + 𝖩` small in the slow
variable and the chart Jacobian `g`-close to the identity, the Eulerian order-two kernel plus `𝖩`
is small: `b₂ DΦ L DΦᵀ + 𝖩 = DΦ (b₂ L + 𝖩) DΦᵀ - (DΦ 𝖩 DΦᵀ - 𝖩)`. -/
theorem twoKernel_scaledJet (Kt : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ Rχ lam b₂ θ g CJ : ℝ) (chart label : Vec 2 → Vec 2)
      (L : DerivativeWord2 1 → Fin 2 → Vec 2 → ℝ) (J : Matrix (Fin 2) (Fin 2) ℝ)
      (β : DerivativeWord2 1) (k' : Fin 2),
      0 < ρ → 0 < Rχ → lam = ρ / Rχ → 0 ≤ θ → 0 ≤ g → 0 ≤ CJ →
      ContDiff ℝ (⊤ : ℕ∞) chart → ContDiff ℝ (⊤ : ℕ∞) label →
      ChartTransport.JetBound chart (Kt + 1) D Rχ → ChartTransport.JetBound label Kt D Rχ →
      (∀ a b : Fin 2, ScaledJet Kt Rχ
        (fun y => jacMatrix chart y a b - (if a = b then 1 else 0)) g) →
      (∀ a b, |J a b| ≤ CJ) →
      (∀ α l, ContDiff ℝ (Kt : ℕ∞) (L α l)) →
      (∀ α l, ∀ i, i ≤ Kt → ∀ X,
        ‖iteratedFDeriv ℝ i (fun X' => b₂ * L α l X' + J l (α 0)) X‖ ≤ θ * lam ^ i) →
      ScaledJet Kt Rχ (fun x => b₂ * (∑ l : Fin 2, ∑ α : DerivativeWord2 1,
          jacMatrix chart (label x) k' l * jacMatrix chart (label x) (β 0) (α 0) *
            L α l (ρ⁻¹ • label x)) + J k' (β 0))
        (C * (θ + CJ * g)) := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  refine ⟨(Kt.factorial : ℝ) * D ^ Kt * ((Kt : ℝ) + 1) *
    (((Finset.univ : Finset (Fin 2)).card : ℝ) *
      (((Finset.univ : Finset (DerivativeWord2 1)).card : ℝ) *
        ((2 ^ Kt * ((Kt : ℝ) + 1) * D) ^ 2 + 2 ^ Kt * ((Kt : ℝ) + 1) * D + 1))),
    by positivity, ?_⟩
  intro ρ Rχ lam b₂ θ g CJ chart label L J β k' hρ hR hlam hθ hg hCJ hchart hlabel hJc hJl hdev
    hJ hL hLb
  have hJac : ∀ a b : Fin 2, ScaledJet Kt Rχ (fun y => jacMatrix chart y a b) D := fun a b =>
    ⟨contDiff_natCast_of_top (contDiff_jacMatrix hchart a b) Kt, fun y q hq =>
      jacMatrix_scaled_bound hR hchart hJc a b y q (by omega)⟩
  -- the deviation letters in the slow variable
  have hDv : ∀ (α : DerivativeWord2 1) (l : Fin 2), ScaledJet Kt Rχ
      (fun y => b₂ * L α l (ρ⁻¹ • y) + J l (α 0)) (θ * lam ^ 0) := fun α l =>
    scaledJet_letter (W := fun X => b₂ * L α l X + J l (α 0))
      ((contDiff_const.mul (hL α l)).add contDiff_const) hρ hR hlam 0
      (fun i hi X => by
        rw [zero_add]
        exact hLb α l i hi X)
  -- one term of the sum over `(l, α)`
  have hterm : ∀ (l : Fin 2) (α : DerivativeWord2 1), ScaledJet Kt Rχ
      (fun y => jacMatrix chart y k' l * (jacMatrix chart y (β 0) (α 0) *
          (b₂ * L α l (ρ⁻¹ • y) + J l (α 0))) +
        (-J l (α 0)) * ((jacMatrix chart y k' l - (if k' = l then 1 else 0)) *
          jacMatrix chart y (β 0) (α 0)) +
        (-((if k' = l then 1 else 0) * J l (α 0))) *
          (jacMatrix chart y (β 0) (α 0) - (if β 0 = α 0 then 1 else 0)))
      (2 ^ Kt * ((Kt : ℝ) + 1) * D * (2 ^ Kt * ((Kt : ℝ) + 1) * D * (θ * lam ^ 0)) +
        CJ * (2 ^ Kt * ((Kt : ℝ) + 1) * g * D) + CJ * g) := by
    intro l α
    have h0 := scaledJet_smul hR (hJac k' l) (scaledJet_smul hR (hJac (β 0) (α 0)) (hDv α l))
    have h1 := scaledJet_const_smul (-J l (α 0))
      (scaledJet_smul hR (hdev k' l) (hJac (β 0) (α 0)))
    have h2 := scaledJet_const_smul (-((if k' = l then (1 : ℝ) else 0) * J l (α 0)))
      (hdev (β 0) (α 0))
    have hb1 : |(-J l (α 0))| * (2 ^ Kt * ((Kt : ℝ) + 1) * g * D) ≤
        CJ * (2 ^ Kt * ((Kt : ℝ) + 1) * g * D) := by
      rw [abs_neg]
      exact mul_le_mul_of_nonneg_right (hJ l (α 0)) (by positivity)
    have hb2 : |(-((if k' = l then (1 : ℝ) else 0) * J l (α 0)))| * g ≤ CJ * g := by
      rw [abs_neg, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ hg
      calc |(if k' = l then (1 : ℝ) else 0)| * |J l (α 0)| ≤ 1 * CJ :=
            mul_le_mul (abs_ite_one_zero_le_one _) (hJ l (α 0)) (abs_nonneg _) zero_le_one
        _ = CJ := one_mul _
    exact scaledJet_add hR.le (scaledJet_add hR.le h0 (scaledJet_mono h1 hb1))
      (scaledJet_mono h2 hb2)
  have hsum := scaledJet_sum_card (Finset.univ : Finset (Fin 2)) hR.le
    (fun l _ => scaledJet_sum_card (Finset.univ : Finset (DerivativeWord2 1)) hR.le
      (fun α _ => hterm l α))
  have hcomp := scaledJet_comp hD hR hsum (contDiff_natCast_of_top hlabel Kt) hJl
  -- the pointwise identity
  have hfun : (fun x => b₂ * (∑ l : Fin 2, ∑ α : DerivativeWord2 1,
        jacMatrix chart (label x) k' l * jacMatrix chart (label x) (β 0) (α 0) *
          L α l (ρ⁻¹ • label x)) + J k' (β 0)) =
      fun x => ∑ l : Fin 2, ∑ α : DerivativeWord2 1,
        (jacMatrix chart (label x) k' l * (jacMatrix chart (label x) (β 0) (α 0) *
            (b₂ * L α l (ρ⁻¹ • label x) + J l (α 0))) +
          (-J l (α 0)) * ((jacMatrix chart (label x) k' l - (if k' = l then 1 else 0)) *
            jacMatrix chart (label x) (β 0) (α 0)) +
          (-((if k' = l then 1 else 0) * J l (α 0))) *
            (jacMatrix chart (label x) (β 0) (α 0) - (if β 0 = α 0 then 1 else 0))) := by
    funext x
    have hα : ∀ l : Fin 2, ∑ α : DerivativeWord2 1,
        (if k' = l then (1 : ℝ) else 0) * (if β 0 = α 0 then 1 else 0) * J l (α 0) =
          (if k' = l then (1 : ℝ) else 0) * J l (β 0) := by
      intro l
      rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2))
        (fun α : DerivativeWord2 1 =>
          (if k' = l then (1 : ℝ) else 0) * (if β 0 = α 0 then 1 else 0) * J l (α 0))
        (fun a : Fin 2 => (if k' = l then (1 : ℝ) else 0) * (if β 0 = a then 1 else 0) * J l a)
        (fun α => rfl), Finset.sum_eq_single (β 0)]
      · rw [ite_eq_left rfl, mul_one]
      · intro b _ hb
        rw [ite_eq_right (Ne.symm hb), mul_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hδ : ∑ l : Fin 2, ∑ α : DerivativeWord2 1,
        (if k' = l then (1 : ℝ) else 0) * (if β 0 = α 0 then 1 else 0) * J l (α 0) =
          J k' (β 0) := by
      rw [Finset.sum_congr rfl fun l _ => hα l, Finset.sum_eq_single k']
      · rw [ite_eq_left rfl, one_mul]
      · intro b _ hb
        rw [ite_eq_right (Ne.symm hb), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    calc b₂ * (∑ l : Fin 2, ∑ α : DerivativeWord2 1,
          jacMatrix chart (label x) k' l * jacMatrix chart (label x) (β 0) (α 0) *
            L α l (ρ⁻¹ • label x)) + J k' (β 0)
        = b₂ * (∑ l : Fin 2, ∑ α : DerivativeWord2 1,
            jacMatrix chart (label x) k' l * jacMatrix chart (label x) (β 0) (α 0) *
              L α l (ρ⁻¹ • label x)) +
          ∑ l : Fin 2, ∑ α : DerivativeWord2 1,
            (if k' = l then (1 : ℝ) else 0) * (if β 0 = α 0 then 1 else 0) * J l (α 0) := by
          rw [hδ]
      _ = _ := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun α _ => ?_
          ring
  rw [hfun]
  refine scaledJet_mono hcomp ?_
  have hX : 0 ≤ (2 ^ Kt * ((Kt : ℝ) + 1) * D) ^ 2 := by positivity
  have hY : 0 ≤ 2 ^ Kt * ((Kt : ℝ) + 1) * D + 1 := by positivity
  have hZ : 0 ≤ CJ * g := mul_nonneg hCJ hg
  have hbT : 2 ^ Kt * ((Kt : ℝ) + 1) * D * (2 ^ Kt * ((Kt : ℝ) + 1) * D * (θ * lam ^ 0)) +
      CJ * (2 ^ Kt * ((Kt : ℝ) + 1) * g * D) + CJ * g ≤
      ((2 ^ Kt * ((Kt : ℝ) + 1) * D) ^ 2 + 2 ^ Kt * ((Kt : ℝ) + 1) * D + 1) * (θ + CJ * g) := by
    rw [pow_zero, mul_one]
    nlinarith [mul_nonneg hX hZ, mul_nonneg hY hθ]
  have hK₃ : 0 ≤ (Kt.factorial : ℝ) * D ^ Kt * ((Kt : ℝ) + 1) := by positivity
  calc (Kt.factorial : ℝ) * D ^ Kt * ((Kt : ℝ) + 1) *
        (((Finset.univ : Finset (Fin 2)).card : ℝ) *
          (((Finset.univ : Finset (DerivativeWord2 1)).card : ℝ) *
            (2 ^ Kt * ((Kt : ℝ) + 1) * D * (2 ^ Kt * ((Kt : ℝ) + 1) * D * (θ * lam ^ 0)) +
              CJ * (2 ^ Kt * ((Kt : ℝ) + 1) * g * D) + CJ * g)))
      ≤ (Kt.factorial : ℝ) * D ^ Kt * ((Kt : ℝ) + 1) *
        (((Finset.univ : Finset (Fin 2)).card : ℝ) *
          (((Finset.univ : Finset (DerivativeWord2 1)).card : ℝ) *
            (((2 ^ Kt * ((Kt : ℝ) + 1) * D) ^ 2 + 2 ^ Kt * ((Kt : ℝ) + 1) * D + 1) *
              (θ + CJ * g)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbT (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) hK₃
    _ = _ := by ring

/-! ### Per-pulse bounds -/

/-- The higher orders of one pulse: the weighted kernel bound without the order two. -/
theorem hiKernel_scaledJet (M Kt : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c ρ εc Rχ lam A₃ : ℝ) (ϖ : ℝ → ℝ) (s₀ s₁ t : ℝ)
      (chart label : Vec 2 → Vec 2)
      (L : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ),
      0 < c → 0 < ρ → 0 ≤ εc → 0 < Rχ → lam = ρ / Rχ → 0 ≤ A₃ → 0 ≤ ϖ t →
      (ϖ t ≠ 0 → c⁻¹ * t ∈ Set.Icc s₀ s₁) →
      ContDiff ℝ (⊤ : ℕ∞) chart → ContDiff ℝ (⊤ : ℕ∞) label →
      (c⁻¹ * t ∈ Set.Icc s₀ s₁ → ChartTransport.JetBound chart (Kt + M) D Rχ ∧
        ChartTransport.JetBound label (Kt + M) D Rχ) →
      (∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2),
        ∀ s ∈ Set.Icc s₀ s₁, ContDiff ℝ (Kt : ℕ∞) (L n d α l s)) →
      (∀ n, 3 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2),
        ∀ i, i ≤ Kt → ∀ s ∈ Set.Icc s₀ s₁, ∀ X,
          ‖iteratedFDeriv ℝ i (L n d α l s) X‖ ≤ A₃ * lam ^ (n - d + i)) →
      ∀ d', 2 ≤ d' → d' ≤ M → ∀ (β : DerivativeWord2 (d' - 1)) (k' : Fin 2),
        ScaledJet Kt Rχ
          (pulseKernel c ρ εc M chart label
            (hiPart fun n d α l => windowLetter ϖ c s₀ s₁ (L n d α l) t) (d' - 1) β k')
          (ϖ t * (C * (A₃ * ∑ n ∈ Finset.Icc d' M,
            if n = 2 then 0 else c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d')))) := by
  obtain ⟨C, hC, hs⟩ := pulseKernel_scaledJet_weighted M Kt D hD
  refine ⟨C, hC, ?_⟩
  intro c ρ εc Rχ lam A₃ ϖ s₀ s₁ t chart label L hc hρ hε hR hlam hA hϖ hsupp hchart hlabel hJ
    hLC hLb d' hd' hd'M β k'
  have hlam0 : 0 < lam := by
    rw [hlam]
    exact div_pos hρ hR
  by_cases hwin : c⁻¹ * t ∈ Set.Icc s₀ s₁
  · obtain ⟨hJc, hJl⟩ := hJ hwin
    have hAn : ∀ n : ℕ, 0 ≤ (if n = 2 then 0 else ϖ t * A₃) := fun n => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg hϖ hA
    have hWC : ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ContDiff ℝ (Kt : ℕ∞)
          (hiPart (fun n d α l => windowLetter ϖ c s₀ s₁ (L n d α l) t) n d α l) :=
      fun n hn hnM d hd hdn α l => contDiff_hiPart _ n d α l
        (contDiff_windowLetter ϖ c s₀ s₁ (L n d α l) t (Kt : ℕ∞)
          (fun s hs => hLC n hn hnM d hd hdn α l s hs))
    have hWJ : ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ i, i ≤ Kt → ∀ X,
          ‖iteratedFDeriv ℝ i
            (hiPart (fun n d α l => windowLetter ϖ c s₀ s₁ (L n d α l) t) n d α l) X‖ ≤
            (if n = 2 then 0 else ϖ t * A₃) * lam ^ (n - d + i) := by
      intro n hn hnM d hd hdn α l i hi X
      by_cases h2 : n = 2
      · subst h2
        have e : ‖iteratedFDeriv ℝ i
            (hiPart (fun n d α l => windowLetter ϖ c s₀ s₁ (L n d α l) t) 2 d α l) X‖ = 0 := by
          rw [hiPart_fun_two, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
        refine e.le.trans (le_of_eq ?_)
        rw [ite_eq_left rfl, zero_mul]
      · rw [hiPart_fun_of_ne _ h2, ite_eq_right h2]
        have h1 := norm_iteratedFDeriv_windowLetter_le ϖ c s₀ s₁ (L n d α l) t i X
          (A₃ * lam ^ (n - d + i)) (mul_nonneg hA (pow_nonneg hlam0.le _))
          (fun s hs => hLb n (by omega) hnM d hd hdn α l i hi s hs X)
        rw [abs_of_nonneg hϖ] at h1
        calc _ ≤ ϖ t * (A₃ * lam ^ (n - d + i)) := h1
          _ = ϖ t * A₃ * lam ^ (n - d + i) := by ring
    have h := hs c ρ εc Rχ lam (fun n => if n = 2 then 0 else ϖ t * A₃) chart label
      (hiPart fun n d α l => windowLetter ϖ c s₀ s₁ (L n d α l) t) hc hρ hε hR hlam hAn hchart
      hlabel hJc hJl hWC hWJ d' hd' hd'M β k'
    refine scaledJet_mono h (le_of_eq ?_)
    rw [sum_hi_eq]
    ring
  · have hϖ0 : ϖ t = 0 := by
      by_contra hne
      exact hwin (hsupp hne)
    have hz : pulseKernel c ρ εc M chart label
        (hiPart fun n d α l => windowLetter ϖ c s₀ s₁ (L n d α l) t) (d' - 1) β k' =
          fun _ => 0 :=
      pulseKernel_eq_zero c ρ εc M chart label (fun n d α l X => by
        by_cases h2 : n = 2
        · subst h2
          exact hiPart_two _ d α l X
        · rw [hiPart_of_ne _ h2, windowLetter_of_notMem _ hwin]) (d' - 1) β k'
    rw [hz, hϖ0, zero_mul]
    exact scaledJet_of_eq_zero contDiff_const rfl Rχ

/-- The order two of one pulse, with its share `ϖ(t) 𝖩` of the reference flux. -/
theorem twoPulse_scaledJet (Kt : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M : ℕ} (c ρ εc Rχ lam θ g CJ : ℝ) (ϖ : ℝ → ℝ) (s₀ s₁ t : ℝ)
      (chart label : Vec 2 → Vec 2)
      (L : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ)
      (J : Matrix (Fin 2) (Fin 2) ℝ),
      2 ≤ M → 0 < ρ → 0 < Rχ → lam = ρ / Rχ → 0 ≤ θ → 0 ≤ g → 0 ≤ CJ → 0 ≤ ϖ t →
      (ϖ t ≠ 0 → c⁻¹ * t ∈ Set.Icc s₀ s₁) →
      ContDiff ℝ (⊤ : ℕ∞) chart → ContDiff ℝ (⊤ : ℕ∞) label →
      (c⁻¹ * t ∈ Set.Icc s₀ s₁ → ChartTransport.JetBound chart (Kt + 1) D Rχ ∧
        ChartTransport.JetBound label Kt D Rχ ∧
        ∀ a b : Fin 2, ScaledJet Kt Rχ
          (fun y => jacMatrix chart y a b - (if a = b then 1 else 0)) g) →
      (∀ a b, |J a b| ≤ CJ) →
      (∀ (α : DerivativeWord2 1) (l : Fin 2), ∀ s ∈ Set.Icc s₀ s₁,
        ContDiff ℝ (Kt : ℕ∞) (L 2 2 α l s)) →
      (c⁻¹ * t ∈ Set.Icc s₀ s₁ → ∀ (α : DerivativeWord2 1) (l : Fin 2), ∀ i, i ≤ Kt → ∀ X,
        ‖iteratedFDeriv ℝ i
          (fun X' => c⁻¹ * εc ^ 2 * ρ ^ 2 * L 2 2 α l (c⁻¹ * t) X' + J l (α 0)) X‖ ≤
            θ * lam ^ i) →
      ∀ (β : DerivativeWord2 1) (k' : Fin 2),
        ScaledJet Kt Rχ
          (fun x => pulseKernel c ρ εc M chart label
            (twoPart fun n d α l => windowLetter ϖ c s₀ s₁ (L n d α l) t) 1 β k' x +
              ϖ t * J k' (β 0))
          (ϖ t * (C * (θ + CJ * g))) := by
  obtain ⟨C, hC, htwo⟩ := twoKernel_scaledJet Kt D hD
  refine ⟨C, hC, ?_⟩
  intro M c ρ εc Rχ lam θ g CJ ϖ s₀ s₁ t chart label L J hM hρ hR hlam hθ hg hCJ hϖ hsupp hchart
    hlabel hJ hJb hLC hLb β k'
  by_cases hwin : c⁻¹ * t ∈ Set.Icc s₀ s₁
  · obtain ⟨hJc, hJl, hdev⟩ := hJ hwin
    have h := htwo ρ Rχ lam (c⁻¹ * εc ^ 2 * ρ ^ 2) θ g CJ chart label
      (fun α l => L 2 2 α l (c⁻¹ * t)) J β k' hρ hR hlam hθ hg hCJ hchart hlabel hJc hJl hdev hJb
      (fun α l => hLC α l _ hwin) (fun α l i hi X => hLb hwin α l i hi X)
    have hfun : (fun x => pulseKernel c ρ εc M chart label
          (twoPart fun n d α l => windowLetter ϖ c s₀ s₁ (L n d α l) t) 1 β k' x +
            ϖ t * J k' (β 0)) =
        fun x => ϖ t • (c⁻¹ * εc ^ 2 * ρ ^ 2 * (∑ l : Fin 2, ∑ α : DerivativeWord2 1,
          jacMatrix chart (label x) k' l * jacMatrix chart (label x) (β 0) (α 0) *
            L 2 2 α l (c⁻¹ * t) (ρ⁻¹ • label x)) + J k' (β 0)) := by
      funext x
      rw [pulseKernel_twoPart_one c ρ εc hM chart label _ β k' x]
      simp only [windowLetter_of_mem _ hwin, smul_eq_mul, Finset.mul_sum, mul_add]
      congr 1
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun α _ => ?_
      ring
    rw [hfun]
    refine scaledJet_mono (scaledJet_const_smul (ϖ t) h) (le_of_eq ?_)
    rw [abs_of_nonneg hϖ]
  · have hϖ0 : ϖ t = 0 := by
      by_contra hne
      exact hwin (hsupp hne)
    have hz : (fun x => pulseKernel c ρ εc M chart label
          (twoPart fun n d α l => windowLetter ϖ c s₀ s₁ (L n d α l) t) 1 β k' x +
            ϖ t * J k' (β 0)) = fun _ => (0 : ℝ) := by
      funext x
      rw [pulseKernel_eq_zero c ρ εc M chart label (fun n d α l X => by
        by_cases h2 : n = 2
        · subst h2
          rw [twoPart_two, windowLetter_of_notMem _ hwin]
        · exact twoPart_of_ne _ h2 d α l X) 1 β k', hϖ0, zero_mul, add_zero]
    rw [hz, hϖ0, zero_mul]
    exact scaledJet_of_eq_zero contDiff_const rfl Rχ

/-! ### The entries and the letter -/

/-- **The entries of the diagonal letter**: the glued scalar kernel plus the reference flux. -/
theorem adEntry_scaledJet (N D Kt : ℕ) (Cχ : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc lam Rχ : ℝ)
      (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
      (Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ)
      (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A₃ θ g CJ : ℝ) (t : ℝ),
      2 ≤ N + D → 0 < c → 0 < ρ → 0 ≤ εc → 0 < Rχ → lam = ρ / Rχ → 0 ≤ A₃ → 0 ≤ θ → 0 ≤ g →
      0 ≤ CJ →
      (∀ k ∈ kset, 0 ≤ ϖ k t) → ∑ k ∈ kset, ϖ k t = 1 →
      (∀ k ∈ kset, ϖ k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k)) →
      (∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (chart k t)) →
      (∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (label k t)) →
      (∀ k ∈ kset, c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) → ∀ p, 1 ≤ p → p ≤ Kt + N + D → ∀ y,
        ‖iteratedFDeriv ℝ p (chart k t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1) ∧
        ‖iteratedFDeriv ℝ p (label k t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1)) →
      (∀ k ∈ kset, c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) → ∀ a b : Fin 2,
        ScaledJet Kt Rχ (fun y => jacMatrix (chart k t) y a b - (if a = b then 1 else 0)) g) →
      (∀ a b, |Jm t a b| ≤ CJ) →
      (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
          ContDiff ℝ (Kt : ℕ∞) (Lsc k n d α l s)) →
      (∀ k ∈ kset, ∀ n, 3 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ i, i ≤ Kt →
          ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
            ‖iteratedFDeriv ℝ i (Lsc k n d α l s) X‖ ≤ A₃ * lam ^ (n - d + i)) →
      (∀ k ∈ kset, ∀ (α : DerivativeWord2 1) (l : Fin 2), ∀ i, i ≤ Kt →
        ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
          ‖iteratedFDeriv ℝ i
            (fun X' => c⁻¹ * εc ^ 2 * ρ ^ 2 * Lsc k 2 2 α l s X' + Jm (c * s) l (α 0)) X‖ ≤
              θ * lam ^ i) →
      ∀ d', 2 ≤ d' → d' ≤ N + D → ∀ (β : DerivativeWord2 (d' - 1)) (k' : Fin 2),
        ScaledJet Kt Rχ
          (fun x => gluedKernel kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lsc (d' - 1) β k' t x +
            jmEntry Jm t (d' - 1) β k')
          (C * (A₃ * (∑ n ∈ Finset.Icc d' (N + D),
              if n = 2 then 0 else c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d')) +
            if d' = 2 then θ + CJ * g else 0)) := by
  obtain ⟨C₀, hC₀, hhi⟩ := hiKernel_scaledJet (N + D) Kt
    (1 + ∑ p ∈ Finset.range (Kt + (N + D) + 1), |Cχ p|)
    (ChartTransport.one_le_jetConst Cχ (Kt + (N + D)))
  obtain ⟨C₂, hC₂, htwo⟩ := twoPulse_scaledJet Kt
    (1 + ∑ p ∈ Finset.range (Kt + (N + D) + 1), |Cχ p|)
    (ChartTransport.one_le_jetConst Cχ (Kt + (N + D)))
  refine ⟨C₀ + C₂, add_nonneg hC₀ hC₂, ?_⟩
  intro kset ϖ c ρ εc lam Rχ chart label s₀ s₁ Lsc Jm A₃ θ g CJ t hM hc hρ hεc hRχ hlam hA hθ hg
    hCJ hϖ0 hsum1 hsupp hchart hlabel hjets hdev hJb hLC hL3 hL2 d' hd' hd'M β k'
  have hJBc : ∀ k ∈ kset, c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) →
      ChartTransport.JetBound (chart k t) (Kt + (N + D))
        (1 + ∑ p ∈ Finset.range (Kt + (N + D) + 1), |Cχ p|) Rχ := fun k hk hwin =>
    ChartTransport.jetBound_of_Cχ hRχ fun p hp1 hpN y => (hjets k hk hwin p hp1 (by omega) y).1
  have hJBl : ∀ k ∈ kset, c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) →
      ChartTransport.JetBound (label k t) (Kt + (N + D))
        (1 + ∑ p ∈ Finset.range (Kt + (N + D) + 1), |Cχ p|) Rχ := fun k hk hwin =>
    ChartTransport.jetBound_of_Cχ hRχ fun p hp1 hpN y => (hjets k hk hwin p hp1 (by omega) y).2
  have hS0 : 0 ≤ ∑ n ∈ Finset.Icc d' (N + D),
      (if n = 2 then 0 else c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d')) :=
    Finset.sum_nonneg fun n _ => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (mul_nonneg (inv_nonneg.2 hc.le) (pow_nonneg (mul_nonneg hεc hρ.le) _))
          (pow_nonneg (inv_nonneg.2 hRχ.le) _)
  -- the higher orders of every pulse
  have hHi : ∀ k ∈ kset, ScaledJet Kt Rχ
      (pulseKernel c ρ εc (N + D) (chart k t) (label k t)
        (hiPart fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k) (Lsc k n d α l) t)
        (d' - 1) β k')
      (ϖ k t * (C₀ * (A₃ * ∑ n ∈ Finset.Icc d' (N + D),
        if n = 2 then 0 else c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d')))) := fun k hk =>
    hhi c ρ εc Rχ lam A₃ (ϖ k) (s₀ k) (s₁ k) t (chart k t) (label k t) (Lsc k) hc hρ hεc hRχ hlam
      hA (hϖ0 k hk) (hsupp k hk) (hchart k hk) (hlabel k hk)
      (fun hwin => ⟨hJBc k hk hwin, hJBl k hk hwin⟩) (hLC k hk) (hL3 k hk) d' hd' hd'M β k'
  -- the order two of every pulse
  have hTwo : ∀ k ∈ kset, ScaledJet Kt Rχ
      (fun x => pulseKernel c ρ εc (N + D) (chart k t) (label k t)
        (twoPart fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k) (Lsc k n d α l) t)
        (d' - 1) β k' x + ϖ k t * jmEntry Jm t (d' - 1) β k')
      (ϖ k t * (if d' = 2 then C₂ * (θ + CJ * g) else 0)) := by
    intro k hk
    by_cases h2 : d' = 2
    · subst h2
      have hj : jmEntry Jm t (2 - 1) β k' = Jm t k' (β 0) := jmEntry_one Jm t β k'
      rw [hj, ite_eq_left rfl]
      exact htwo (M := N + D) c ρ εc Rχ lam θ g CJ (ϖ k) (s₀ k) (s₁ k) t (chart k t) (label k t)
        (Lsc k) (Jm t) hM hρ hRχ hlam hθ hg hCJ (hϖ0 k hk) (hsupp k hk) (hchart k hk)
        (hlabel k hk)
        (fun hwin => ⟨fun p hp1 hp y => hJBc k hk hwin p hp1 (by omega) y,
          fun p hp1 hp y => hJBl k hk hwin p hp1 (by omega) y, hdev k hk hwin⟩)
        hJb (fun α l s hs => hLC k hk 2 le_rfl hM 2 le_rfl le_rfl α l s hs)
        (fun hwin α l i hi X => by
          have h := hL2 k hk α l i hi (c⁻¹ * t) hwin X
          rwa [mul_inv_cancel_left₀ hc.ne'] at h) β k'
    · have hz : (fun x => pulseKernel c ρ εc (N + D) (chart k t) (label k t)
          (twoPart fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k) (Lsc k n d α l) t)
          (d' - 1) β k' x + ϖ k t * jmEntry Jm t (d' - 1) β k') = fun _ => (0 : ℝ) := by
        funext x
        rw [pulseKernel_twoPart_of_ge c ρ εc (N + D) (chart k t) (label k t) _ (by omega) β k' x,
          jmEntry_of_ne Jm t (by omega) β k', mul_zero, add_zero]
      rw [hz, ite_eq_right h2, mul_zero]
      exact scaledJet_of_eq_zero contDiff_const rfl Rχ
  -- the sum over the pulses
  have hE : (fun x => gluedKernel kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lsc (d' - 1) β k' t x +
        jmEntry Jm t (d' - 1) β k') =
      fun x => ∑ k ∈ kset,
        (pulseKernel c ρ εc (N + D) (chart k t) (label k t)
            (hiPart fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k) (Lsc k n d α l) t)
            (d' - 1) β k' x +
          (pulseKernel c ρ εc (N + D) (chart k t) (label k t)
            (twoPart fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k) (Lsc k n d α l) t)
            (d' - 1) β k' x + ϖ k t * jmEntry Jm t (d' - 1) β k')) := by
    funext x
    calc gluedKernel kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lsc (d' - 1) β k' t x +
          jmEntry Jm t (d' - 1) β k'
        = (∑ k ∈ kset, pulseKernel c ρ εc (N + D) (chart k t) (label k t)
            (fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k) (Lsc k n d α l) t)
            (d' - 1) β k' x) + ∑ k ∈ kset, ϖ k t * jmEntry Jm t (d' - 1) β k' := by
          rw [← Finset.sum_mul, hsum1, one_mul]
          rfl
      _ = _ := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [pulseKernel_split, add_assoc]
  have hsumJ := scaledJet_sum kset hRχ.le
    (fun k hk => scaledJet_add hRχ.le (hHi k hk) (hTwo k hk))
  rw [hE]
  refine scaledJet_mono hsumJ ?_
  have hsumb : ∑ k ∈ kset, (ϖ k t * (C₀ * (A₃ * ∑ n ∈ Finset.Icc d' (N + D),
        if n = 2 then 0 else c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d'))) +
        ϖ k t * (if d' = 2 then C₂ * (θ + CJ * g) else 0)) =
      C₀ * (A₃ * ∑ n ∈ Finset.Icc d' (N + D),
        if n = 2 then 0 else c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d')) +
        (if d' = 2 then C₂ * (θ + CJ * g) else 0) := by
    simp only [← mul_add, ← Finset.sum_mul, hsum1, one_mul]
  rw [hsumb]
  have hX : 0 ≤ A₃ * ∑ n ∈ Finset.Icc d' (N + D),
      (if n = 2 then 0 else c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d')) := mul_nonneg hA hS0
  have hY : 0 ≤ θ + CJ * g := add_nonneg hθ (mul_nonneg hCJ hg)
  by_cases h2 : d' = 2
  · rw [ite_eq_left h2, ite_eq_left h2]
    nlinarith [mul_nonneg hC₀ hY, mul_nonneg hC₂ hX]
  · rw [ite_eq_right h2, ite_eq_right h2]
    nlinarith [mul_nonneg hC₂ hX]

/-- **Transfer bound for the diagonal letter**, scale-weighted at the chart scale. -/
theorem adLetter_transfer (N D Kt : ℕ) (Cχ : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc lam Rχ : ℝ)
      (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
      (Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ)
      (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A₃ θ g CJ : ℝ) (t : ℝ),
      2 ≤ N + D → 0 < c → 0 < ρ → 0 ≤ εc → 0 < Rχ → lam = ρ / Rχ → 0 ≤ A₃ → 0 ≤ θ → 0 ≤ g →
      0 ≤ CJ →
      (∀ k ∈ kset, 0 ≤ ϖ k t) → ∑ k ∈ kset, ϖ k t = 1 →
      (∀ k ∈ kset, ϖ k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k)) →
      (∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (chart k t)) →
      (∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (label k t)) →
      (∀ k ∈ kset, c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) → ∀ p, 1 ≤ p → p ≤ Kt + N + D → ∀ y,
        ‖iteratedFDeriv ℝ p (chart k t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1) ∧
        ‖iteratedFDeriv ℝ p (label k t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1)) →
      (∀ k ∈ kset, c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) → ∀ a b : Fin 2,
        ScaledJet Kt Rχ (fun y => jacMatrix (chart k t) y a b - (if a = b then 1 else 0)) g) →
      (∀ a b, |Jm t a b| ≤ CJ) →
      (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
          ContDiff ℝ (Kt : ℕ∞) (Lsc k n d α l s)) →
      (∀ k ∈ kset, ∀ n, 3 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ i, i ≤ Kt →
          ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
            ‖iteratedFDeriv ℝ i (Lsc k n d α l s) X‖ ≤ A₃ * lam ^ (n - d + i)) →
      (∀ k ∈ kset, ∀ (α : DerivativeWord2 1) (l : Fin 2), ∀ i, i ≤ Kt →
        ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
          ‖iteratedFDeriv ℝ i
            (fun X' => c⁻¹ * εc ^ 2 * ρ ^ 2 * Lsc k 2 2 α l s X' + Jm (c * s) l (α 0)) X‖ ≤
              θ * lam ^ i) →
      ∀ (d : Finset.Icc 2 (N + D)) (j : ℕ), j ≤ Kt → ∀ x,
        Rχ ^ j * ‖coefficientDerivativeArray
            (adLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lsc Jm d t) j x‖ ≤
          C * (A₃ * (∑ n ∈ Finset.Icc d.1 (N + D),
              if n = 2 then 0 else c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d.1)) +
            if d.1 = 2 then θ + CJ * g else 0) := by
  obtain ⟨C₁, hC₁, hent⟩ := adEntry_scaledJet N D Kt Cχ
  refine ⟨2 ^ Kt * (2 ^ (N + D) * 2) * C₁, by positivity, ?_⟩
  intro kset ϖ c ρ εc lam Rχ chart label s₀ s₁ Lsc Jm A₃ θ g CJ t hM hc hρ hεc hRχ hlam hA hθ hg
    hCJ hϖ0 hsum1 hsupp hchart hlabel hjets hdev hJb hLC hL3 hL2 d j hj x
  have hd2 := Finset.mem_Icc.1 d.2
  have hE := fun (β : DerivativeWord2 (d.1 - 1)) (k' : Fin 2) =>
    hent kset ϖ c ρ εc lam Rχ chart label s₀ s₁ Lsc Jm A₃ θ g CJ t hM hc hρ hεc hRχ hlam hA hθ hg
      hCJ hϖ0 hsum1 hsupp hchart hlabel hjets hdev hJb hLC hL3 hL2 d.1 hd2.1 hd2.2 β k'
  have hjK : ((j : ℕ) : WithTop ℕ∞) ≤ ((Kt : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hj
  have hK : ∀ (β : DerivativeWord2 (d.1 - 1)) (k' : Fin 2), ContDiff ℝ (j : WithTop ℕ∞)
      (fun x => (gluedKernel kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lsc (d.1 - 1) β k' t x +
        jmEntry Jm t (d.1 - 1) β k') • ContinuousLinearMap.id ℝ ℝ) := fun β k' =>
    (((hE β k').contDiff).of_le hjK).smul contDiff_const
  have h1 := norm_coefficientDerivativeArray_neg_arrayOp_le
    (K := fun x β k' => (gluedKernel kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lsc (d.1 - 1) β k'
      t x + jmEntry Jm t (d.1 - 1) β k') • ContinuousLinearMap.id ℝ ℝ) j hK x
  have hterm : ∀ (β : DerivativeWord2 (d.1 - 1)) (k' : Fin 2),
      Rχ ^ j * ‖iteratedFDeriv ℝ j (fun x =>
        (gluedKernel kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lsc (d.1 - 1) β k' t x +
          jmEntry Jm t (d.1 - 1) β k') • ContinuousLinearMap.id ℝ ℝ) x‖ ≤
        C₁ * (A₃ * (∑ n ∈ Finset.Icc d.1 (N + D),
            if n = 2 then 0 else c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d.1)) +
          if d.1 = 2 then θ + CJ * g else 0) := fun β k' =>
    (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_smul_id_le j ((hE β k').contDiff.of_le hjK) x)
      (pow_nonneg hRχ.le j)).trans ((hE β k').bound x j hj)
  have hB0 : 0 ≤ C₁ * (A₃ * (∑ n ∈ Finset.Icc d.1 (N + D),
      if n = 2 then 0 else c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d.1)) +
      if d.1 = 2 then θ + CJ * g else 0) := by
    refine mul_nonneg hC₁ (add_nonneg (mul_nonneg hA (Finset.sum_nonneg fun n _ => ?_)) ?_)
    · split_ifs
      · exact le_rfl
      · exact mul_nonneg (mul_nonneg (inv_nonneg.2 hc.le) (pow_nonneg (mul_nonneg hεc hρ.le) _))
          (pow_nonneg (inv_nonneg.2 hRχ.le) _)
    · split_ifs
      · exact add_nonneg hθ (mul_nonneg hCJ hg)
      · exact le_rfl
  have h2j : (2 : ℝ) ^ j ≤ 2 ^ Kt := pow_le_pow_right₀ (by norm_num) hj
  have h2d : (2 : ℝ) ^ (d.1 - 1) ≤ 2 ^ (N + D) := pow_le_pow_right₀ (by norm_num) (by omega)
  refine (mul_le_mul_of_nonneg_left h1 (pow_nonneg hRχ.le j)).trans ?_
  rw [mul_left_comm]
  refine (mul_le_mul_of_nonneg_left (scaled_array_sum_le _ _ _ hterm) (by positivity)).trans ?_
  calc (2 : ℝ) ^ j * (2 ^ (d.1 - 1) * 2 * (C₁ * (A₃ * (∑ n ∈ Finset.Icc d.1 (N + D),
          if n = 2 then 0 else c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d.1)) +
          if d.1 = 2 then θ + CJ * g else 0)))
      = 2 ^ j * (2 ^ (d.1 - 1) * 2) * (C₁ * (A₃ * (∑ n ∈ Finset.Icc d.1 (N + D),
          if n = 2 then 0 else c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d.1)) +
          if d.1 = 2 then θ + CJ * g else 0)) := by ring
    _ ≤ 2 ^ Kt * (2 ^ (N + D) * 2) * (C₁ * (A₃ * (∑ n ∈ Finset.Icc d.1 (N + D),
          if n = 2 then 0 else c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d.1)) +
          if d.1 = 2 then θ + CJ * g else 0)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h2j
          (mul_le_mul_of_nonneg_right h2d (by norm_num)) (by positivity) (by positivity)) hB0
    _ = _ := by ring
end

/-! One pulse of the actual means:
the local Eulerian mean `ℓ^{-2} ∑_n ε_c^n L_n^{(r)} a_ρ` of a pulse is the label-frame divergence
of the dimensional chart flux `chartFlux`, whose letters are the chart-frame mean letters read at
`y/ρ` and restored by `ρ^d` (`∂_X = ρ ∂_y`: `d - 1` factors from the tested word, one from the
outer divergence). -/

section
section Generic

/-- The lambda form of `HasFDerivAt.const_smul`. -/
theorem hasFDerivAt_fun_const_smul {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f f' x) (c : ℝ) : HasFDerivAt (fun y => c • f y) (c • f') x :=
  hf.const_smul c

/-- Moving the flux direction sum outside the degree, order and word sums. -/
theorem sum_flux_reorder {A : Type*} [AddCommGroup A] [Module ℝ A] (c ρ εc : ℝ) (M : ℕ)
    (F : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → A) :
    c⁻¹ • ∑ n ∈ Finset.Icc 2 M, εc ^ n • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
        ∑ α : DerivativeWord2 (d - 1), ∑ l : Fin 2, F n d α l =
      ∑ l : Fin 2, ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
        ∑ α : DerivativeWord2 (d - 1), F n d α l := by
  have hd (n d : ℕ) : ρ ^ d • ∑ α : DerivativeWord2 (d - 1), ∑ l : Fin 2, F n d α l =
      ∑ l : Fin 2, ρ ^ d • ∑ α : DerivativeWord2 (d - 1), F n d α l := by
    rw [Finset.sum_comm, Finset.smul_sum]
  have hn (n : ℕ) : c⁻¹ • εc ^ n • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
        ∑ α : DerivativeWord2 (d - 1), ∑ l : Fin 2, F n d α l =
      ∑ l : Fin 2, (c⁻¹ * εc ^ n) • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
        ∑ α : DerivativeWord2 (d - 1), F n d α l := by
    rw [smul_smul, Finset.sum_congr rfl (fun d _ => hd n d), Finset.sum_comm, Finset.smul_sum]
  rw [Finset.smul_sum, Finset.sum_congr rfl (fun n _ => hn n), Finset.sum_comm]

end Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- One word term of the chart flux: the chart-frame letter of order `d` and word `α`, read at
`y/ρ`, applied to the label-frame word derivative of `g`. -/
def chartFluxTerm (ρ : ℝ) (b : MeanCoeff ι h) (g : Vec 2 → ∀ i, h i) (s : ℝ) (d : ℕ)
    (α : DerivativeWord2 (d - 1)) (l : Fin 2) (y : Vec 2) (v : ι) : h v :=
  ∑ u : ι, b d α s (ρ⁻¹ • y) l v u (orderedDerivative α g y u)

/-- The dimensional chart-frame flux of one pulse and one grade, in label coordinates. -/
def chartFlux (c ρ εc : ℝ) (M : ℕ) (Lb : ℕ → MeanCoeff ι h) (g : Vec 2 → ∀ i, h i)
    (s : ℝ) (y : Vec 2) (l : Fin 2) (v : ι) : h v :=
  ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) •
    ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1), ∑ u : ι,
      Lb n d α s (ρ⁻¹ • y) l v u (orderedDerivative α g y u)

theorem chartFlux_eq_sum_chartFluxTerm (c ρ εc : ℝ) (M : ℕ) (Lb : ℕ → MeanCoeff ι h)
    (g : Vec 2 → ∀ i, h i) (s : ℝ) (y : Vec 2) (l : Fin 2) (v : ι) :
    chartFlux c ρ εc M Lb g s y l v =
      ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
        ∑ α : DerivativeWord2 (d - 1), chartFluxTerm ρ (Lb n) g s d α l y v := rfl

/-- A word term of the chart flux is differentiable in `y` when its letter is `C¹`. -/
theorem differentiable_chartFluxTerm (ρ : ℝ) (b : MeanCoeff ι h) (g : Vec 2 → ∀ i, h i)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (s : ℝ) (d : ℕ) (α : DerivativeWord2 (d - 1)) (l : Fin 2)
    (v : ι) (hb : ∀ u, ContDiff ℝ 1 (fun X => b d α s X l v u)) :
    Differentiable ℝ (fun y => chartFluxTerm ρ b g s d α l y v) := by
  have hterm : ∀ u ∈ (Finset.univ : Finset ι), Differentiable ℝ
      (fun y : Vec 2 => b d α s (ρ⁻¹ • y) l v u (orderedDerivative α g y u)) := by
    intro u _
    have hL : Differentiable ℝ (fun y : Vec 2 => b d α s (ρ⁻¹ • y) l v u) :=
      ((hb u).comp (contDiff_const_smul ρ⁻¹)).differentiable (by simp)
    have hw : Differentiable ℝ (fun y : Vec 2 => orderedDerivative α g y u) :=
      (contDiff_pi.mp (contDiff_top_orderedDerivative α hg) u).differentiable (by simp)
    exact hL.clm_apply hw
  show Differentiable ℝ
    (fun y : Vec 2 => ∑ u : ι, b d α s (ρ⁻¹ • y) l v u (orderedDerivative α g y u))
  exact Differentiable.fun_sum hterm

/-- The derivative of `chartFlux` in `y`, term by term. -/
theorem hasFDerivAt_chartFlux (c ρ εc : ℝ) (M : ℕ) (Lb : ℕ → MeanCoeff ι h)
    (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (s : ℝ)
    (hLb : ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1))
      (k₀ : Fin 2) (v u : ι), ContDiff ℝ 1 (fun X => Lb n d α s X k₀ v u))
    (l : Fin 2) (v : ι) (y₀ : Vec 2) :
    HasFDerivAt (fun y => chartFlux c ρ εc M Lb g s y l v)
      (∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
        ∑ α : DerivativeWord2 (d - 1),
          fderiv ℝ (fun y => chartFluxTerm ρ (Lb n) g s d α l y v) y₀) y₀ := by
  have hterm : ∀ n ∈ Finset.Icc 2 M, ∀ d ∈ Finset.Icc 2 n, ∀ α : DerivativeWord2 (d - 1),
      HasFDerivAt (fun y => chartFluxTerm ρ (Lb n) g s d α l y v)
        (fderiv ℝ (fun y => chartFluxTerm ρ (Lb n) g s d α l y v) y₀) y₀ := by
    intro n hn d hd α
    have hn' := Finset.mem_Icc.mp hn
    have hd' := Finset.mem_Icc.mp hd
    exact (differentiable_chartFluxTerm ρ (Lb n) g hg s d α l v
      (fun u => hLb n hn'.1 hn'.2 d hd'.1 hd'.2 α l v u) y₀).hasFDerivAt
  have hdsum : ∀ n ∈ Finset.Icc 2 M, ∀ d ∈ Finset.Icc 2 n,
      HasFDerivAt
        (fun y => ρ ^ d • ∑ α : DerivativeWord2 (d - 1), chartFluxTerm ρ (Lb n) g s d α l y v)
        (ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
          fderiv ℝ (fun y => chartFluxTerm ρ (Lb n) g s d α l y v) y₀) y₀ :=
    fun n hn d hd =>
      hasFDerivAt_fun_const_smul (HasFDerivAt.fun_sum fun α _ => hterm n hn d hd α) (ρ ^ d)
  have hnsum : ∀ n ∈ Finset.Icc 2 M,
      HasFDerivAt
        (fun y => (c⁻¹ * εc ^ n) • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
          ∑ α : DerivativeWord2 (d - 1), chartFluxTerm ρ (Lb n) g s d α l y v)
        ((c⁻¹ * εc ^ n) • ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
          fderiv ℝ (fun y => chartFluxTerm ρ (Lb n) g s d α l y v) y₀) y₀ :=
    fun n hn =>
      hasFDerivAt_fun_const_smul (HasFDerivAt.fun_sum fun d hd => hdsum n hn d hd)
        (c⁻¹ * εc ^ n)
  simp only [chartFlux_eq_sum_chartFluxTerm]
  exact HasFDerivAt.fun_sum hnsum

/-- `chartFlux` is differentiable in `y` when the letters are `C¹` in the slow variable. -/
theorem differentiable_chartFlux (c ρ εc : ℝ) (M : ℕ) (Lb : ℕ → MeanCoeff ι h)
    (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (s : ℝ)
    (hLb : ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1))
      (k₀ : Fin 2) (v u : ι), ContDiff ℝ 1 (fun X => Lb n d α s X k₀ v u))
    (l : Fin 2) (v : ι) : Differentiable ℝ (fun y => chartFlux c ρ εc M Lb g s y l v) :=
  fun y₀ => (hasFDerivAt_chartFlux c ρ εc M Lb g hg s hLb l v y₀).differentiableAt

/-- A directional derivative of `chartFlux`, term by term. -/
theorem fderiv_chartFlux_apply (c ρ εc : ℝ) (M : ℕ) (Lb : ℕ → MeanCoeff ι h)
    (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (s : ℝ)
    (hLb : ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1))
      (k₀ : Fin 2) (v u : ι), ContDiff ℝ 1 (fun X => Lb n d α s X k₀ v u))
    (l : Fin 2) (v : ι) (y₀ e : Vec 2) :
    fderiv ℝ (fun y => chartFlux c ρ εc M Lb g s y l v) y₀ e =
      ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
        ∑ α : DerivativeWord2 (d - 1),
          fderiv ℝ (fun y => chartFluxTerm ρ (Lb n) g s d α l y v) y₀ e := by
  rw [(hasFDerivAt_chartFlux c ρ εc M Lb g hg s hLb l v y₀).fderiv]
  simp only [sum_apply, smul_apply]

/-- The chart-frame flux of the dilated field `g(ρ ·)` is the dilated label-frame word term. -/
theorem dilated_flux_eq (ρ : ℝ) (hρ : ρ ≠ 0) (b : MeanCoeff ι h) (g : Vec 2 → ∀ i, h i)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (s : ℝ) (d : ℕ) (α : DerivativeWord2 (d - 1)) (l : Fin 2) :
    (fun (X' : Vec 2) (v' : ι) => ∑ u : ι,
      b d α s X' l v' u (orderedDerivative α (fun X'' => g (ρ • X'')) X' u)) =
    fun Z => ρ ^ (d - 1) • chartFluxTerm ρ b g s d α l (ρ • Z) := by
  funext X' v'
  have he := congrFun
    (AVRegularity.CycleComparison.Lift.orderedDerivative_dilation α ρ g hg) X'
  rw [he]
  show ∑ u : ι, b d α s X' l v' u ((ρ ^ (d - 1) • orderedDerivative α g (ρ • X')) u) =
    ρ ^ (d - 1) • ∑ u : ι, b d α s (ρ⁻¹ • ρ • X') l v' u (orderedDerivative α g (ρ • X') u)
  rw [inv_smul_smul₀ hρ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Pi.smul_apply, map_smul]

/-- The outer divergence of the chart-frame flux of the dilated field, read at `y₀/ρ`, is `ρ^d`
times the label-frame derivative of the word term. -/
theorem fderiv_dilated_flux (ρ : ℝ) (hρ : ρ ≠ 0) (b : MeanCoeff ι h) (g : Vec 2 → ∀ i, h i)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (s : ℝ) (d : ℕ) (hd : 1 ≤ d) (α : DerivativeWord2 (d - 1))
    (l : Fin 2) (hb : ∀ v u, ContDiff ℝ 1 (fun X => b d α s X l v u)) (y₀ : Vec 2) (v : ι) :
    fderiv ℝ (fun (X' : Vec 2) (v' : ι) => ∑ u : ι,
        b d α s X' l v' u (orderedDerivative α (fun X'' => g (ρ • X'')) X' u))
      (ρ⁻¹ • y₀) (basisVec l) v =
      ρ ^ d • fderiv ℝ (fun y => chartFluxTerm ρ b g s d α l y v) y₀ (basisVec l) := by
  rw [dilated_flux_eq ρ hρ b g hg s d α l]
  have he := AVRegularity.CycleComparison.Lift.fderiv_dilation_smul
    (chartFluxTerm ρ b g s d α l) ρ (ρ ^ (d - 1)) (ρ⁻¹ • y₀) (basisVec l)
  have hpow : ρ ^ (d - 1) * ρ = ρ ^ d := by rw [← pow_succ, Nat.sub_add_cancel hd]
  rw [smul_inv_smul₀ hρ, hpow] at he
  have hdiff : DifferentiableAt ℝ (chartFluxTerm ρ b g s d α l) y₀ :=
    differentiableAt_pi.mpr
      (fun v' => differentiable_chartFluxTerm ρ b g hg s d α l v' (hb v') y₀)
  have hcomp : fderiv ℝ (chartFluxTerm ρ b g s d α l) y₀ (basisVec l) v =
      fderiv ℝ (fun y => chartFluxTerm ρ b g s d α l y v) y₀ (basisVec l) :=
    (congrArg (fun L : Vec 2 →L[ℝ] h v => L (basisVec l)) (fderiv_apply hdiff v)).symm
  rw [he, Pi.smul_apply, hcomp]

/-- The divergence-form mean action on the dilated field `g(ρ ·)`, read at `y₀/ρ`, in terms of
the label-frame word terms. -/
theorem meanApply_dilated_eq (ρ : ℝ) (hρ : ρ ≠ 0) (n : ℕ) (b : MeanCoeff ι h)
    (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (s : ℝ)
    (hb : ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
      ContDiff ℝ 1 (fun X => b d α s X k₀ v u))
    (y₀ : Vec 2) (v : ι) :
    meanApply n b (fun _ X' => g (ρ • X')) s (ρ⁻¹ • y₀) v =
      ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1), ∑ l : Fin 2,
        fderiv ℝ (fun y => chartFluxTerm ρ b g s d α l y v) y₀ (basisVec l) := by
  show (∑ d ∈ Finset.Icc 2 n, ∑ α : DerivativeWord2 (d - 1), ∑ l : Fin 2,
      fderiv ℝ (fun (X' : Vec 2) (v' : ι) => ∑ u : ι,
          b d α s X' l v' u (orderedDerivative α (fun X'' => g (ρ • X'')) X' u))
        (ρ⁻¹ • y₀) (basisVec l) v) = _
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' := Finset.mem_Icc.mp hd
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact fderiv_dilated_flux ρ hρ b g hg s d (by have h2 := hd'.1; omega) α l
    (fun v' u => hb d hd'.1 hd'.2 α l v' u) y₀ v

variable {D : ℕ}

/-- The lift mean of the pulse input at the lift time `c⁻¹ t` is the divergence-form mean action
on the time-frozen dilated field. -/
theorem pulse_liftMean_eq_meanApply (c ρ : ℝ) (hc : c ≠ 0) (r n : ℕ)
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (chart : ℝ → Vec 2 → Vec 2)
    (b : MeanCoeff ι h) (s₀ s₁ : ℝ)
    (hpres : ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ s ∈ Set.Icc s₀ s₁, ∀ X,
      liftMean Q Cc (fun _ => a₀) r n s X = meanApply n b (fun _ => a₀) s X)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) (a t))
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (chart t)) (ht : c⁻¹ * t ∈ Set.Icc s₀ s₁) (X : Vec 2) :
    liftMean Q Cc (fun s' X' => a (c * s') (chart (c * s') (ρ • X'))) r n (c⁻¹ * t) X =
      meanApply n b (fun _ X' => a t (chart t (ρ • X'))) (c⁻¹ * t) X := by
  have hdate : c * (c⁻¹ * t) = t := mul_inv_cancel_left₀ hc t
  have he := AVRegularity.CycleComparison.Lift.liftMean_congr_time_input Q Cc
    (fun s' X' => a (c * s') (chart (c * s') (ρ • X')))
    (fun _ X' => a t (chart t (ρ • X'))) r n (c⁻¹ * t) (by funext X'; simp only [hdate])
  rw [he]
  exact hpres (fun X' => a t (chart t (ρ • X')))
    ((ha.comp hchart).comp (contDiff_const_smul ρ)) (c⁻¹ * t) ht X

/-- One pulse: the Eulerian mean field is the label-frame divergence of the chart flux. -/
theorem pulseMeanField_eq_div_chartFlux (c ρ εc : ℝ) (hc : c ≠ 0) (hρ : ρ ≠ 0)
    (N r : ℕ) (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℝ → Vec 2 → Vec 2) (Lb : ℕ → MeanCoeff ι h) (s₀ s₁ : ℝ)
    (hpres : ∀ n, 2 ≤ n → n ≤ N + D → ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
      ∀ s ∈ Set.Icc s₀ s₁, ∀ X,
        liftMean Q Cc (fun _ => a₀) r n s X = meanApply n (Lb n) (fun _ => a₀) s X)
    (hLb : ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1))
      (k₀ : Fin 2) (v u : ι), ∀ s ∈ Set.Icc s₀ s₁, ContDiff ℝ 1 (fun X => Lb n d α s X k₀ v u))
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) (a t))
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (chart t)) (ht : c⁻¹ * t ∈ Set.Icc s₀ s₁) (x : Vec 2) (v : ι) :
    pulseMeanField c ρ εc N r Q Cc chart label a t x v =
      ∑ l : Fin 2, fderiv ℝ
        (fun y => chartFlux c ρ εc (N + D) Lb (fun y' => a t (chart t y')) (c⁻¹ * t) y l v)
        (label t x) (basisVec l) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y' => a t (chart t y')) := ha.comp hchart
  have hLb' : ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
        ContDiff ℝ 1 (fun X => Lb n d α (c⁻¹ * t) X k₀ v u) :=
    fun n hn hnM d hd hdn α k₀ v u => hLb n hn hnM d hd hdn α k₀ v u (c⁻¹ * t) ht
  have hL : pulseMeanField c ρ εc N r Q Cc chart label a t x v =
      c⁻¹ • ∑ n ∈ Finset.Icc 2 (N + D), εc ^ n •
        liftMean Q Cc (fun s' X' => a (c * s') (chart (c * s') (ρ • X'))) r n (c⁻¹ * t)
          (ρ⁻¹ • label t x) v := by
    simp only [pulseMeanField, Pi.smul_apply, Finset.sum_apply]
  have hmean : ∀ n ∈ Finset.Icc 2 (N + D),
      εc ^ n • liftMean Q Cc (fun s' X' => a (c * s') (chart (c * s') (ρ • X'))) r n
          (c⁻¹ * t) (ρ⁻¹ • label t x) v =
        εc ^ n • ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1), ∑ l : Fin 2,
          fderiv ℝ (fun y => chartFluxTerm ρ (Lb n) (fun y' => a t (chart t y')) (c⁻¹ * t)
            d α l y v) (label t x) (basisVec l) := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    rw [pulse_liftMean_eq_meanApply c ρ hc r n Q Cc chart (Lb n) s₀ s₁
      (hpres n hn'.1 hn'.2) a t ha hchart ht (ρ⁻¹ • label t x)]
    rw [meanApply_dilated_eq ρ hρ n (Lb n) (fun y' => a t (chart t y')) hg (c⁻¹ * t)
      (hLb' n hn'.1 hn'.2) (label t x) v]
  have hR : ∀ l ∈ (Finset.univ : Finset (Fin 2)),
      (∑ n ∈ Finset.Icc 2 (N + D), (c⁻¹ * εc ^ n) • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
        ∑ α : DerivativeWord2 (d - 1),
          fderiv ℝ (fun y => chartFluxTerm ρ (Lb n) (fun y' => a t (chart t y')) (c⁻¹ * t)
            d α l y v) (label t x) (basisVec l)) =
      fderiv ℝ
        (fun y => chartFlux c ρ εc (N + D) Lb (fun y' => a t (chart t y')) (c⁻¹ * t) y l v)
        (label t x) (basisVec l) :=
    fun l _ => (fderiv_chartFlux_apply c ρ εc (N + D) Lb (fun y' => a t (chart t y')) hg
      (c⁻¹ * t) hLb' l v (label t x) (basisVec l)).symm
  rw [hL, Finset.sum_congr rfl hmean,
    sum_flux_reorder c ρ εc (N + D) (fun n d α l =>
      fderiv ℝ (fun y => chartFluxTerm ρ (Lb n) (fun y' => a t (chart t y')) (c⁻¹ * t)
        d α l y v) (label t x) (basisVec l))]
  exact Finset.sum_congr rfl hR
end

end AVRegularity.CycleComparison.ActualMeans
end
