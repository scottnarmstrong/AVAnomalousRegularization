-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.FrontierFlux.Jets
import Mathlib.Algebra.Order.Chebyshev

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The readout energy, jets: the level-weighted quadratic forms**.

`rweQ ω D = ∑_a ω_{|a|} ‖D a‖²` for a weight `ω` on the levels. The four norms of the readout
energy are `rweQ` for one weight each (`factorialNormSq`, `factorialNormSqUpTo`,
`gradFactorialNormSq`, `gradFactorialNormSqUpTo`); the lemmas are the monotonicity in the weight,
the truncation to a lower order, Cauchy--Schwarz for a finite weighted sum of jets and the change
of the length. -/

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  {μ : Measure (Vec 2)} {K : ℕ}

/-- The quadratic form of a level weight on a jet. -/
def rweQ (ω : ℕ → ℝ) (D : JetL2 μ K E) : ℝ :=
  ∑ a : JetIndex2 K, ω a.1.val * ‖D a‖ ^ 2

/-- Weight of the factorial norm up to the order `m`. -/
def rweWUp (ρ : ℝ) (m : ℕ) (j : ℕ) : ℝ := if j ≤ m then factorialWeight ρ j else 0

/-- Weight of the gradient factorial norm up to the order `m`. -/
def rweWGr (ρ : ℝ) (m : ℕ) (j : ℕ) : ℝ :=
  if 1 ≤ j ∧ j ≤ m + 1 then factorialWeight ρ (j - 1) else 0

/-- Weight of the full gradient factorial norm. -/
def rweWGrFull (ρ : ℝ) (j : ℕ) : ℝ := if 1 ≤ j then factorialWeight ρ (j - 1) else 0

theorem rweQ_eq_levels (ω : ℕ → ℝ) (D : JetL2 μ K E) :
    rweQ ω D = ∑ j : Fin (K + 1), ω j.val * derivativeNormSq D j := by
  unfold rweQ derivativeNormSq
  simp_rw [Finset.mul_sum]
  exact (Fintype.sum_sigma (fun a : JetIndex2 K => ω a.1.val * ‖D a‖ ^ 2))

theorem rweQ_factorialNormSq (ρ : ℝ) (D : JetL2 μ K E) :
    factorialNormSq ρ D = rweQ (factorialWeight ρ) D := by
  rw [rweQ_eq_levels]; rfl

theorem rweQ_factorialNormSqUpTo (ρ : ℝ) (m : ℕ) (D : JetL2 μ K E) :
    factorialNormSqUpTo ρ m D = rweQ (rweWUp ρ m) D := by
  rw [rweQ_eq_levels]
  unfold factorialNormSqUpTo rweWUp
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem rweQ_gradFactorialNormSqUpTo (ρ : ℝ) (m : ℕ) (D : JetL2 μ K E) :
    gradFactorialNormSqUpTo ρ m D = rweQ (rweWGr ρ m) D := by
  rw [rweQ_eq_levels]
  unfold gradFactorialNormSqUpTo rweWGr
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem rweQ_gradFactorialNormSq (ρ : ℝ) (D : JetL2 μ (K + 1) E) :
    gradFactorialNormSq ρ D = rweQ (rweWGrFull ρ) D := by
  rw [rweQ_eq_levels, Fin.sum_univ_succ]
  unfold gradFactorialNormSq rweWGrFull
  simp only [Fin.val_zero, Fin.val_succ]
  simp only [show ¬ (1 ≤ 0) from by omega, ite_false, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [show 1 ≤ (j : ℕ) + 1 from by omega, ite_true, Nat.add_sub_cancel]
  rfl

theorem rweQ_mono_weight {ω ω' : ℕ → ℝ} (h : ∀ j, ω j ≤ ω' j) (D : JetL2 μ K E) :
    rweQ ω D ≤ rweQ ω' D :=
  Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_right (h _) (sq_nonneg _)

theorem rweQ_nonneg {ω : ℕ → ℝ} (h : ∀ j, 0 ≤ ω j) (D : JetL2 μ K E) : 0 ≤ rweQ ω D :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (h _) (sq_nonneg _)

theorem rweQ_smul_weight (c : ℝ) (ω : ℕ → ℝ) (D : JetL2 μ K E) :
    rweQ (fun j => c * ω j) D = c * rweQ ω D := by
  unfold rweQ; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring

variable [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
/-- Truncation to a lower order does not increase a nonnegative level form. -/
theorem rweQ_truncate_le {ω : ℕ → ℝ} (hω : ∀ j, 0 ≤ ω j) {L : ℕ} (hKL : K ≤ L)
    (D : JetL2 μ L E) : rweQ ω (truncateJet hKL D) ≤ rweQ ω D := by
  unfold rweQ
  exact sum_comp_le_sum_nonneg (truncateJetIndex hKL) (truncateJetIndex_injective hKL)
    (fun b : JetIndex2 L => ω b.1.val * ‖D b‖ ^ 2) (fun b => mul_nonneg (hω _) (sq_nonneg _))

omit [BorelSpace E] [CompleteSpace E] in
/-- Cauchy--Schwarz for a finite weighted sum of jets. -/
theorem rweQ_sum_le {ω : ℕ → ℝ} (hω : ∀ j, 0 ≤ ω j) {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (D : ι → JetL2 μ K E) :
    rweQ ω (∑ c ∈ s, r c • D c) ≤ (s.card : ℝ) * ∑ c ∈ s, r c ^ 2 * rweQ ω (D c) := by
  classical
  have hpt : ∀ a : JetIndex2 K, ‖(∑ c ∈ s, r c • D c) a‖ ^ 2 ≤
      (s.card : ℝ) * ∑ c ∈ s, r c ^ 2 * ‖D c a‖ ^ 2 := by
    intro a
    have h1 : ‖(∑ c ∈ s, r c • D c) a‖ ≤ ∑ c ∈ s, |r c| * ‖D c a‖ := by
      have hap : (∑ c ∈ s, r c • D c) a = ∑ c ∈ s, r c • D c a := by simp
      rw [hap]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
    calc ‖(∑ c ∈ s, r c • D c) a‖ ^ 2 ≤ (∑ c ∈ s, |r c| * ‖D c a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (s.card : ℝ) * ∑ c ∈ s, (|r c| * ‖D c a‖) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = _ := by
          congr 1
          exact Finset.sum_congr rfl fun c _ => by rw [mul_pow, sq_abs]
  unfold rweQ
  calc ∑ a : JetIndex2 K, ω a.1.val * ‖(∑ c ∈ s, r c • D c) a‖ ^ 2
      ≤ ∑ a : JetIndex2 K, ω a.1.val * ((s.card : ℝ) * ∑ c ∈ s, r c ^ 2 * ‖D c a‖ ^ 2) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpt a) (hω _)
    _ = ∑ a : JetIndex2 K, ∑ c ∈ s, (s.card : ℝ) * (r c ^ 2 * (ω a.1.val * ‖D c a‖ ^ 2)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = ∑ c ∈ s, ∑ a : JetIndex2 K, (s.card : ℝ) * (r c ^ 2 * (ω a.1.val * ‖D c a‖ ^ 2)) :=
        Finset.sum_comm
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]

/-- The change of the length for the weights up to the order `m`. -/
theorem rweWUp_scale_le (ρ s : ℝ) (hs : 0 ≤ s) (m j : ℕ) :
    rweWUp (s * ρ) m j ≤ radiusChangeFactor s m ^ 2 * rweWUp ρ m j := by
  unfold rweWUp
  split_ifs with h
  · unfold factorialWeight radiusChangeFactor
    rw [mul_pow, mul_div_assoc, ← pow_mul, mul_comm m 2]
    have h1 : s ^ (2 * j) ≤ max 1 s ^ (2 * m) :=
      (pow_le_pow_left₀ hs (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (by omega))
    have h2 : 0 ≤ ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2 := by
      rw [← factorialWeight]; exact factorialWeight_nonneg ρ j
    calc s ^ (2 * j) * (ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2)
        ≤ max 1 s ^ (2 * m) * (ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = _ := rfl
  · simp

/-- The change of the length for the gradient weights up to the order `m`. -/
theorem rweWGr_scale_le (ρ s : ℝ) (hs : 0 ≤ s) (m j : ℕ) :
    rweWGr (s * ρ) m j ≤ radiusChangeFactor s m ^ 2 * rweWGr ρ m j := by
  unfold rweWGr
  split_ifs with h
  · unfold factorialWeight radiusChangeFactor
    rw [mul_pow, mul_div_assoc, ← pow_mul, mul_comm m 2]
    have h1 : s ^ (2 * (j - 1)) ≤ max 1 s ^ (2 * m) :=
      (pow_le_pow_left₀ hs (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (by omega))
    have h2 : 0 ≤ ρ ^ (2 * (j - 1)) / ((j - 1).factorial : ℝ) ^ 2 := by
      rw [← factorialWeight]; exact factorialWeight_nonneg ρ _
    calc s ^ (2 * (j - 1)) * (ρ ^ (2 * (j - 1)) / ((j - 1).factorial : ℝ) ^ 2)
        ≤ max 1 s ^ (2 * m) * (ρ ^ (2 * (j - 1)) / ((j - 1).factorial : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = _ := rfl
  · simp

theorem rweWUp_nonneg (ρ : ℝ) (m j : ℕ) : 0 ≤ rweWUp ρ m j := by
  unfold rweWUp; split_ifs
  · exact factorialWeight_nonneg _ _
  · exact le_rfl

theorem rweWGr_nonneg (ρ : ℝ) (m j : ℕ) : 0 ≤ rweWGr ρ m j := by
  unfold rweWGr; split_ifs
  · exact factorialWeight_nonneg _ _
  · exact le_rfl

theorem rweWUp_le_full (ρ : ℝ) (m j : ℕ) : rweWUp ρ m j ≤ factorialWeight ρ j := by
  unfold rweWUp; split_ifs
  · exact le_rfl
  · exact factorialWeight_nonneg _ _

theorem rweWGr_le_full (ρ : ℝ) (m j : ℕ) : rweWGr ρ m j ≤ rweWGrFull ρ j := by
  unfold rweWGr rweWGrFull; split_ifs with h1 h2
  · exact le_rfl
  · exact absurd h1.1 h2
  · exact factorialWeight_nonneg _ _
  · exact le_rfl

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- **Change of the length for the factorial norm up to the order `m`** (any jet order). -/
theorem rweQ_up_radius_le (ρ s : ℝ) (hs : 0 ≤ s) (m : ℕ) (D : JetL2 μ K E) :
    rweQ (rweWUp (s * ρ) m) D ≤ radiusChangeFactor s m ^ 2 * factorialNormSq ρ D := by
  rw [rweQ_factorialNormSq, ← rweQ_smul_weight]
  exact rweQ_mono_weight (fun j => (rweWUp_scale_le ρ s hs m j).trans
    (mul_le_mul_of_nonneg_left (rweWUp_le_full ρ m j) (sq_nonneg _))) D

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- **Change of the length for the gradient factorial norm up to the order `m`.** -/
theorem rweQ_gr_radius_le (ρ s : ℝ) (hs : 0 ≤ s) (m : ℕ) (D : JetL2 μ K E) :
    rweQ (rweWGr (s * ρ) m) D ≤ radiusChangeFactor s m ^ 2 * rweQ (rweWGrFull ρ) D := by
  rw [← rweQ_smul_weight]
  exact rweQ_mono_weight (fun j => (rweWGr_scale_le ρ s hs m j).trans
    (mul_le_mul_of_nonneg_left (rweWGr_le_full ρ m j) (sq_nonneg _))) D

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end

section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The strong energy from per-parent pointwise bounds** (abstract algebra of
the transfer: the supremum and the dissipative integral per parent, the count of the parents,
the square root). -/

/-- **The strong energy of a family with per-parent pointwise bounds** -/
theorem rwe_energy_abstract {V : Type} [Fintype V] (π : V → ℝ) (hπ : ∀ v, 0 ≤ π v)
    (S G : V → ℝ → ℝ) (Mt Gm : ℝ → ℝ) (I : Set ℝ) (hI : I.Nonempty)
    (B Z : ℝ) (hZ : 0 ≤ Z) (n : ℕ) (hcV : Fintype.card V ≤ n)
    (hS : ∀ v, ∀ t ∈ I, (π v)⁻¹ * S v t ≤ n * Mt t)
    (hG : ∀ v, ∀ᵐ τ ∂(volume.restrict I), (π v)⁻¹ * G v τ ≤ n * Gm τ)
    (hM : ∀ t ∈ I, ENNReal.ofReal (Mt t) +
      ENNReal.ofReal (B / 2) * ∫⁻ τ in I, ENNReal.ofReal (Gm τ) ≤ ENNReal.ofReal Z) :
    (∑ v, ENNReal.ofReal (π v)⁻¹ * ((⨆ t ∈ I, ENNReal.ofReal (S v t)) +
      ENNReal.ofReal B * ∫⁻ τ in I, ENNReal.ofReal (G v τ))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (2 * n * n * Z)) := by
  have hB2 : ENNReal.ofReal B = 2 * ENNReal.ofReal (B / 2) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  have hsup := PartB.partB_iSup_add_le hI (fun t => ENNReal.ofReal (Mt t)) _ (ENNReal.ofReal Z) hM
  have hper : ∀ v, ENNReal.ofReal (π v)⁻¹ * ((⨆ t ∈ I, ENNReal.ofReal (S v t)) +
      ENNReal.ofReal B * ∫⁻ τ in I, ENNReal.ofReal (G v τ)) ≤
      (n : ℝ≥0∞) * (2 * ENNReal.ofReal Z) := by
    intro v
    have hp : 0 ≤ (π v)⁻¹ := inv_nonneg.2 (hπ v)
    have e1 : ENNReal.ofReal (π v)⁻¹ * (⨆ t ∈ I, ENNReal.ofReal (S v t)) ≤
        (n : ℝ≥0∞) * ⨆ t ∈ I, ENNReal.ofReal (Mt t) := by
      simp only [ENNReal.mul_iSup]
      refine iSup₂_le fun t ht => ?_
      rw [← ENNReal.ofReal_mul hp]
      calc _ ≤ ENNReal.ofReal (n * Mt t) := ENNReal.ofReal_le_ofReal (hS v t ht)
        _ = (n : ℝ≥0∞) * ENNReal.ofReal (Mt t) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        _ ≤ _ := le_iSup₂ (f := fun t (_ : t ∈ I) => (n : ℝ≥0∞) * ENNReal.ofReal (Mt t)) t ht
    have e2 : ENNReal.ofReal (π v)⁻¹ * ∫⁻ τ in I, ENNReal.ofReal (G v τ) ≤
        (n : ℝ≥0∞) * ∫⁻ τ in I, ENNReal.ofReal (Gm τ) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _
        (ENNReal.natCast_ne_top n)]
      refine lintegral_mono_ae ?_
      filter_upwards [hG v] with τ hτ
      rw [← ENNReal.ofReal_mul hp]
      calc _ ≤ ENNReal.ofReal (n * Gm τ) := ENNReal.ofReal_le_ofReal hτ
        _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    calc ENNReal.ofReal (π v)⁻¹ * ((⨆ t ∈ I, ENNReal.ofReal (S v t)) +
          ENNReal.ofReal B * ∫⁻ τ in I, ENNReal.ofReal (G v τ))
        = ENNReal.ofReal (π v)⁻¹ * (⨆ t ∈ I, ENNReal.ofReal (S v t)) + ENNReal.ofReal B *
          (ENNReal.ofReal (π v)⁻¹ * ∫⁻ τ in I, ENNReal.ofReal (G v τ)) := by
          rw [mul_add, mul_left_comm]
      _ ≤ (n : ℝ≥0∞) * (⨆ t ∈ I, ENNReal.ofReal (Mt t)) + ENNReal.ofReal B *
          ((n : ℝ≥0∞) * ∫⁻ τ in I, ENNReal.ofReal (Gm τ)) := add_le_add e1 (mul_le_mul' le_rfl e2)
      _ = (n : ℝ≥0∞) * ((⨆ t ∈ I, ENNReal.ofReal (Mt t)) +
          ENNReal.ofReal B * ∫⁻ τ in I, ENNReal.ofReal (Gm τ)) := by
          rw [mul_add, mul_left_comm (ENNReal.ofReal B)]
      _ ≤ (n : ℝ≥0∞) * (2 * ENNReal.ofReal Z) := by
          refine mul_le_mul' le_rfl ?_
          calc (⨆ t ∈ I, ENNReal.ofReal (Mt t)) + ENNReal.ofReal B * ∫⁻ τ in I, ENNReal.ofReal (Gm τ)
              ≤ 2 * (⨆ t ∈ I, ENNReal.ofReal (Mt t)) +
                2 * (ENNReal.ofReal (B / 2) * ∫⁻ τ in I, ENNReal.ofReal (Gm τ)) := by
                rw [hB2, mul_assoc]
                exact add_le_add (le_mul_of_one_le_left bot_le (by norm_num)) le_rfl
            _ = 2 * ((⨆ t ∈ I, ENNReal.ofReal (Mt t)) +
                ENNReal.ofReal (B / 2) * ∫⁻ τ in I, ENNReal.ofReal (Gm τ)) := by rw [mul_add]
            _ ≤ 2 * ENNReal.ofReal Z := mul_le_mul' le_rfl hsup
  refine PartB.partB_sqrt_step _ _ n hcV Z hZ ?_
  calc _ ≤ ∑ _v : V, (n : ℝ≥0∞) * (2 * ENNReal.ofReal Z) := Finset.sum_le_sum fun v _ => hper v
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The energy of the readout `W = cdW` in the window norm** (statement only).

The hypotheses `hEn`, `hX` of the physical lift at a weak passage `M < i ≤ M + J_w`: the readout
`W = cdW` of the high family `Uhi (i-1)` at the order `K' = k + 1 + D_c`, measured at the LIFT
LENGTH `ρ = ε_{i-1}` (not at the plan's energy radius `plan.radius R · ε_{i-1}` of the high-reserve energy statement), with the
dissipation weight `κ_M` and the masses `π_v = weakMass`, in `strongEnergyUpTo`, for every order
`ord` with `ord + 1 ≤ k + 1 + D_c`:
```
strongEnergyUpTo ε_{i-1} κ_M π [t_i, a + T₀] ord W ≤ C_en(ρ_plan, R, m, ord) · Φ.
```
The families are those of the high-reserve energy statement (the clauses `hpass`, `hvr`, `hval`); the constant is the named
function `weakReadoutWindowConst`: the change-of-length factor `(max 1 (ρ_plan)⁻¹)^ord`
(`radiusChangeFactor`) times `√(2 n² C_A)`, where `n = weakReadoutCountConst A` is the count of the
menu and `C_A = weakCoarseHighConst ρ_plan R m` is the constant of the high-reserve energy statement.

The degenerate cases are included: `R_w = 0` gives one child per parent (`n` is the count of the
menu, an upper bound); `Φ = 0` gives `0`; at `ord = 0` the factor is `1` and the radius does not
enter. -/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Residual

/-- **`C_en`** of the readout energy bound: a named function of the normalized radius `ρ = plan.radius R`, the
request, the order `m` and the order `ord` of the window norm. -/
def weakReadoutWindowConst {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (ρ : ℝ)
    (R : WeakPassageRequest A) (m ord : ℕ) : ℝ :=
  radiusChangeFactor ρ⁻¹ ord *
    Real.sqrt (2 * (weakReadoutCountConst A : ℝ) * weakReadoutCountConst A *
      weakCoarseHighConst ρ R m)

variable {plan : WeakPassagePlan}

/-- **The energy of the readout in the window norm.** -/
def WeakReadoutWindowEnergyStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (Dc m k ord : ℕ) (_hm : m ≤ weakEntryMmax R) (hk : k + 1 + Dc ≤ R.Kw + m)
    (_hord : ord + 1 ≤ k + 1 + Dc)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (_hstart : r.a < r.tq (c.M + A.Jw + 1))
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j),
    (∀ j, c.M < j → j ≤ c.M + A.Jw →
      WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi j) →
    -- the clauses exported by `WeakCoarseHighEnergyAt`: the top family and the truncations
    (∀ v : CompIn (c.stage (c.M + A.Jw)).comps,
      ∀ t ∈ Set.Icc (r.tq (c.M + A.Jw + 1)) (r.a + A.T₀),
      truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (c.M + A.Jw) v t) =
        r.Ur (c.M + A.Jw) v t) →
    (∀ j, c.M < j → j ≤ c.M + A.Jw → ∀ v : CompIn (c.stage (j - 1)).comps,
      ∀ t ∈ Set.Icc (r.tq j) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (j - 1) v t) =
          r.Ur (j - 1) v t) →
    ∀ (i : ℕ) (_hi : c.M < i) (_hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i),
    strongEnergyUpTo (c.D.eps (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (r.tq i) (r.a + A.T₀) ord
        (cdW c m (k + 1 + Dc) (fun w => hk.trans (weakReductionReserve_kw R m w)) i Uhi) ≤
      ENNReal.ofReal (weakReadoutWindowConst (plan.radius R) R m ord * h.Φ)

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The readout energy, per time: the readout `cdReadout` is a Cauchy--Schwarz over the children**.

`rweQ_readout_le`: for a nonnegative level weight `ω`, the form of the readout at a parent is at
most `n` times the sum over its children of the squared readout factor times the form of the
child. The transfer (`rweTransfer_parent` at one parent): with the mass comparison
`π_parent⁻¹ ρ² ≤ π_child⁻¹` of `WeakReadoutMassStatement` and the counts, the mass-weighted sum
over the parents of the form of
the readout is at most `n²` times the mass-weighted sum over the children (the algebra
at the level of the classes). -/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Residual

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem rwe_torus_val_sum {ι : Type*} (s : Finset ι) (f : ι → TorusHk K E) :
    (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val :=
  AddSubmonoidClass.coe_finsetSum f s

/-- The Cauchy--Schwarz bound of a finite selected weighted sum of classes. -/
theorem rwe_sum_ite_le {ω : ℕ → ℝ} (hω : ∀ j, 0 ≤ ω j) {ι : Type*} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (w : ι → ℝ) (X : ι → TorusHk K E) (n : ℕ)
    (hn : (Finset.univ.filter p).card ≤ n) :
    rweQ ω (∑ i, if p i then w i • X i else (0 : TorusHk K E)).val ≤
      (n : ℝ) * ∑ i, if p i then w i ^ 2 * rweQ ω (X i).val else 0 := by
  have h1 : (∑ i, if p i then w i • X i else (0 : TorusHk K E)) =
      ∑ i ∈ Finset.univ.filter p, w i • X i := by
    rw [Finset.sum_filter]
  have h2 : (∑ i, if p i then w i ^ 2 * rweQ ω (X i).val else 0) =
      ∑ i ∈ Finset.univ.filter p, w i ^ 2 * rweQ ω (X i).val := by
    rw [Finset.sum_filter]
  rw [h1, h2, rwe_torus_val_sum]
  have h3 : ∀ i ∈ Finset.univ.filter p, (w i • X i).val = w i • (X i).val := fun i _ => rfl
  rw [Finset.sum_congr rfl h3]
  refine (rweQ_sum_le hω _ w (fun i => (X i).val)).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn)
    (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (rweQ_nonneg hω _))

end Generic

section Weak

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

open scoped Classical in
/-- **The readout at a parent**: the form of `cdReadout` is at most `n` times the sum over the
children of the squared readout weight times the form of the child. -/
theorem rweQ_readout_le {ω : ℕ → ℝ} (hω : ∀ j, 0 ≤ ω j) (c : WeakPassageInstance plan R)
    (m K' : ℕ) (hK : ∀ w, K' ≤ weakReductionReserve R m w) (i : ℕ)
    (U : ∀ v' : CompIn (c.stage (i - 1)).comps,
      TorusHk (weakReductionReserve R m v'.1) (ScalarH v'.1.root))
    (v : CompIn (c.stage i).comps) (n : ℕ)
    (hn : (Finset.univ.filter
      fun v' : CompIn (c.stage (i - 1)).comps => compParent i v'.1 = v.1).card ≤ n) :
    rweQ ω (cdReadout c m K' hK i (fun _ => True) U v).val ≤
      (n : ℝ) * ∑ v' : CompIn (c.stage (i - 1)).comps,
        if compParent i v'.1 = v.1 then cdWeight c i v'.1 ^ 2 * rweQ ω (U v').val else 0 := by
  have key := rwe_sum_ite_le (E := ScalarH v.1.root) (K := K') hω
    (fun v' : CompIn (c.stage (i - 1)).comps => compParent i v'.1 = v.1 ∧ True)
    (fun v' => cdWeight c i v'.1) (fun v' => truncateTorusHk (hK v'.1) (U v')) n
    (by simpa only [and_true] using hn)
  have hdef : rweQ ω (cdReadout c m K' hK i (fun _ => True) U v).val =
      rweQ ω (∑ v' : CompIn (c.stage (i - 1)).comps,
        if compParent i v'.1 = v.1 ∧ True then
          cdWeight c i v'.1 • truncateTorusHk (hK v'.1) (U v') else (0 : TorusHk K' (ScalarH v.1.root))).val := by
    unfold cdReadout
    congr!
  rw [hdef]
  refine key.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  refine Finset.sum_le_sum fun v' _ => ?_
  by_cases h : compParent i v'.1 = v.1
  · simp only [h, and_self, ite_true]
    exact mul_le_mul_of_nonneg_left (rweQ_truncate_le hω (hK v'.1) (U v').val) (sq_nonneg _)
  · simp [h]

open scoped Classical in
/-- **The transfer to one parent, with the masses**: `π_v⁻¹ Q(readout_v) ≤ n ∑_{v'} π_{v'}⁻¹ Q(U_{v'})`. -/
theorem rweTransfer_parent (hMass : WeakReadoutMassStatement plan) {ω : ℕ → ℝ}
    (hω : ∀ j, 0 ≤ ω j)
    (c : WeakPassageInstance plan R) (m K' : ℕ) (hK : ∀ w, K' ≤ weakReductionReserve R m w)
    (i : ℕ) (U : ∀ v' : CompIn (c.stage (i - 1)).comps,
      TorusHk (weakReductionReserve R m v'.1) (ScalarH v'.1.root)) (n : ℕ)
    (hfib : ∀ v : Comp, (Finset.univ.filter
      fun v' : CompIn (c.stage (i - 1)).comps => compParent i v'.1 = v).card ≤ n)
    (v : CompIn (c.stage i).comps) :
    (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
      rweQ ω (cdReadout c m K' hK i (fun _ => True) U v).val ≤
    (n : ℝ) * ∑ v' : CompIn (c.stage (i - 1)).comps,
        (weakMass c.D A.Nw A.Jw A.η₀ v'.1)⁻¹ * rweQ ω (U v').val := by
  have hπ : ∀ v : Comp, 0 < weakMass c.D A.Nw A.Jw A.η₀ v := fun v => PartB.partB_mass_pos c v
  have h1 := rweQ_readout_le hω c m K' hK i U v n (hfib v.1)
  have hpv : 0 ≤ (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ := inv_nonneg.2 (hπ _).le
  calc (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ * rweQ ω (cdReadout c m K' hK i (fun _ => True) U v).val
      ≤ (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ * ((n : ℝ) * ∑ v' : CompIn (c.stage (i - 1)).comps,
          if compParent i v'.1 = v.1 then cdWeight c i v'.1 ^ 2 * rweQ ω (U v').val else 0) :=
        mul_le_mul_of_nonneg_left h1 hpv
    _ = (n : ℝ) * ∑ v' : CompIn (c.stage (i - 1)).comps,
          if compParent i v'.1 = v.1 then
            (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ * cdWeight c i v'.1 ^ 2 * rweQ ω (U v').val
          else 0 := by
        rw [mul_left_comm, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun v' _ => ?_
        split_ifs
        · ring
        · simp
    _ ≤ (n : ℝ) * ∑ v' : CompIn (c.stage (i - 1)).comps,
        (weakMass c.D A.Nw A.Jw A.η₀ v'.1)⁻¹ * rweQ ω (U v').val := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v' _ => ?_) (Nat.cast_nonneg _)
        by_cases h : compParent i v'.1 = v.1
        · simp only [h, ite_true]
          have hm := (hMass c i v'.1).1
          rw [h] at hm
          exact mul_le_mul_of_nonneg_right hm (rweQ_nonneg hω _)
        · simp only [h, ite_false]
          exact mul_nonneg (inv_nonneg.2 (hπ _).le) (rweQ_nonneg hω _)

end Weak

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The energy of the readout in the window norm, proved**.

`weakReadoutWindowEnergy : WeakReadoutWindowEnergyStatement plan` under `WeakPassageCommonOK plan`
and `WeakCoarsePlanOK plan`. The high-reserve energy bound at the plan radius for the given families
(`rwe_partA`), the per-parent Cauchy--Schwarz over the children with the masses
(`rwe_sup_bound`, `rwe_grad_bound`: truncation of the order, `Whi` truncating to `Uhi` almost
everywhere, change of the length by `radiusChangeFactor (plan.radius R)⁻¹ ord`), then the
supremum, the dissipative integral and the count (`rwe_energy_abstract`). -/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Residual

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The high-reserve energy for given families**: the bound of `weakCoarse_high_energy_at` for any families with
the clauses `hpass`, `hvr`, `hval`. -/
theorem rwe_partA (hcommon : WeakPassageCommonOK plan) (hok : WeakCoarsePlanOK plan)
    (m : ℕ) (hm : m ≤ weakEntryMmax R)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (hstart : r.a < r.tq (c.M + A.Jw + 1))
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j)
    (hpass : ∀ j, c.M < j → j ≤ c.M + A.Jw →
      WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi j)
    (hvr : ∀ v : CompIn (c.stage (c.M + A.Jw)).comps,
      ∀ t ∈ Set.Icc (r.tq (c.M + A.Jw + 1)) (r.a + A.T₀),
      truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (c.M + A.Jw) v t) =
        r.Ur (c.M + A.Jw) v t)
    (hval : ∀ j, c.M < j → j ≤ c.M + A.Jw → ∀ v : CompIn (c.stage (j - 1)).comps,
      ∀ t ∈ Set.Icc (r.tq j) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (j - 1) v t) =
          r.Ur (j - 1) v t)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (Φ : ℝ)
    (hΦ : ∀ t ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀),
      weightedNorm 1 (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1)
        (fun v => truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t)) ≤ Φ)
    (t : ℝ) (ht : t ∈ Set.Icc (r.tq i) (r.a + A.T₀)) :
    ENNReal.ofReal (massNormSq (plan.radius R * c.D.eps (i - 1))
        (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (Uhi (i - 1) v t).val)) +
      ENNReal.ofReal (c.D.κ c.M / 2) *
        ∫⁻ τ in Set.Icc (r.tq i) (r.a + A.T₀),
          ENNReal.ofReal (massGradNormSq (plan.radius R * c.D.eps (i - 1))
            (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
            (fun v => (Whi (i - 1) v τ).val)) ≤
      ENNReal.ofReal (weakCoarseHighConst (plan.radius R) R m * Φ ^ 2) := by
  classical
  obtain ⟨hfl, hfit⟩ := hok
  have henergy := weakCoarse_passage_energy hcommon hfl c (weakCoarseClock r hstart) m hm Uhi Whi
    i hi hit (hpass i hi hit) t ht
  have hq := weakCoarse_trace_bound hcommon m (hfit R m hm) c r hstart Uhi hvr hval i hi hit Φ hΦ
  refine henergy.trans ?_
  unfold weakCoarseHighConst
  rw [ENNReal.ofReal_mul (weakRawPassageConst_nonneg _ _)]
  calc _ ≤ ENNReal.ofReal (weakRawPassageConst (plan.radius R) R) *
          ENNReal.ofReal ((max 1 ((weakQuietCoefficientPlan weakCoarseQuietSeed).traceC
            (weakEntryLiftRequest R m))) ^ 2 * Φ ^ 2) :=
        mul_le_mul' le_rfl hq
    _ = _ := by
        rw [← ENNReal.ofReal_mul (weakRawPassageConst_nonneg _ _)]
        congr 1; ring

theorem rwe_scale_ennreal (F : ℝ) (hF : 0 ≤ F) (a : ℝ) (κ' : ℝ) (I : Set ℝ) (g : ℝ → ℝ) :
    ENNReal.ofReal (F * a) + ENNReal.ofReal κ' * ∫⁻ τ in I, ENNReal.ofReal (F * g τ) =
      ENNReal.ofReal F * (ENNReal.ofReal a + ENNReal.ofReal κ' * ∫⁻ τ in I, ENNReal.ofReal (g τ)) := by
  have h1 : ∫⁻ τ in I, ENNReal.ofReal (F * g τ) = ENNReal.ofReal F * ∫⁻ τ in I, ENNReal.ofReal (g τ) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun τ => ENNReal.ofReal_mul hF
  rw [h1, ENNReal.ofReal_mul hF, mul_add, mul_left_comm]

open scoped Classical in
/-- The supremum part, per parent and time. -/
theorem rwe_sup_bound (hMass : WeakReadoutMassStatement plan) (c : WeakPassageInstance plan R)
    (m K' : ℕ) (hK : ∀ w, K' ≤ weakReductionReserve R m w) (i ord n : ℕ)
    (hfib : ∀ v : Comp, (Finset.univ.filter
      fun v' : CompIn (c.stage (i - 1)).comps => compParent i v'.1 = v).card ≤ n)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j) (ρ₂ s : ℝ) (hs0 : 0 ≤ s)
    (hρ : c.D.eps (i - 1) = s * ρ₂) (v : CompIn (c.stage i).comps) (t : ℝ) :
    (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ * factorialNormSqUpTo (c.D.eps (i - 1)) ord
        (cdW c m K' hK i Uhi v t).val ≤
      (n : ℝ) * (radiusChangeFactor s ord ^ 2 * massNormSq ρ₂
        (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (Uhi (i - 1) v t).val)) := by
  have hπ : ∀ v : Comp, 0 < weakMass c.D A.Nw A.Jw A.η₀ v := fun v => PartB.partB_mass_pos c v
  have e : factorialNormSqUpTo (c.D.eps (i - 1)) ord (cdW c m K' hK i Uhi v t).val =
      rweQ (rweWUp (c.D.eps (i - 1)) ord)
        (cdReadout c m K' hK i (fun _ => True) (fun v' => Uhi (i - 1) v' t) v).val :=
    rweQ_factorialNormSqUpTo _ _ _
  rw [e]
  refine (rweTransfer_parent hMass (rweWUp_nonneg _ ord) c m K' hK i
    (fun v' => Uhi (i - 1) v' t) n hfib v).trans
    (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  unfold massNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v' _ => ?_
  have h1 := rweQ_up_radius_le ρ₂ s hs0 ord (Uhi (i - 1) v' t).val
  rw [← hρ] at h1
  calc (weakMass c.D A.Nw A.Jw A.η₀ v'.1)⁻¹ * rweQ (rweWUp (c.D.eps (i - 1)) ord)
        (Uhi (i - 1) v' t).val
      ≤ (weakMass c.D A.Nw A.Jw A.η₀ v'.1)⁻¹ *
          (radiusChangeFactor s ord ^ 2 * factorialNormSq ρ₂ (Uhi (i - 1) v' t).val) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (hπ _).le)
    _ = _ := by ring

open scoped Classical in
/-- The dissipative part, per parent and time. -/
theorem rwe_grad_bound (hMass : WeakReadoutMassStatement plan) (c : WeakPassageInstance plan R)
    (m K' : ℕ) (hK : ∀ w, K' ≤ weakReductionReserve R m w) (i ord n : ℕ)
    (hfib : ∀ v : Comp, (Finset.univ.filter
      fun v' : CompIn (c.stage (i - 1)).comps => compParent i v'.1 = v).card ≤ n)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j) (ρ₂ s : ℝ) (hs0 : 0 ≤ s)
    (hρ : c.D.eps (i - 1) = s * ρ₂) (v : CompIn (c.stage i).comps) (τ : ℝ)
    (hτ : ∀ v' : CompIn (c.stage (i - 1)).comps,
      truncateTorusHk (Nat.le_succ (weakReductionReserve R m v'.1)) (Whi (i - 1) v' τ) =
        Uhi (i - 1) v' τ) :
    (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ * gradFactorialNormSqUpTo (c.D.eps (i - 1)) ord
        (cdW c m K' hK i Uhi v τ).val ≤
      (n : ℝ) * (radiusChangeFactor s ord ^ 2 * massGradNormSq ρ₂
        (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (Whi (i - 1) v τ).val)) := by
  have hπ : ∀ v : Comp, 0 < weakMass c.D A.Nw A.Jw A.η₀ v := fun v => PartB.partB_mass_pos c v
  have e : gradFactorialNormSqUpTo (c.D.eps (i - 1)) ord (cdW c m K' hK i Uhi v τ).val =
      rweQ (rweWGr (c.D.eps (i - 1)) ord)
        (cdReadout c m K' hK i (fun _ => True) (fun v' => Uhi (i - 1) v' τ) v).val :=
    rweQ_gradFactorialNormSqUpTo _ _ _
  rw [e]
  refine (rweTransfer_parent hMass (rweWGr_nonneg _ ord) c m K' hK i
    (fun v' => Uhi (i - 1) v' τ) n hfib v).trans
    (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  unfold massGradNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v' _ => ?_
  have h1 := rweQ_gr_radius_le ρ₂ s hs0 ord (Whi (i - 1) v' τ).val
  rw [← hρ] at h1
  have h2 : rweQ (rweWGr (c.D.eps (i - 1)) ord) (Uhi (i - 1) v' τ).val ≤
      rweQ (rweWGr (c.D.eps (i - 1)) ord) (Whi (i - 1) v' τ).val := by
    rw [← hτ v']
    exact rweQ_truncate_le (rweWGr_nonneg _ ord) (Nat.le_succ _) (Whi (i - 1) v' τ).val
  rw [rweQ_gradFactorialNormSq]
  calc (weakMass c.D A.Nw A.Jw A.η₀ v'.1)⁻¹ * rweQ (rweWGr (c.D.eps (i - 1)) ord)
        (Uhi (i - 1) v' τ).val
      ≤ (weakMass c.D A.Nw A.Jw A.η₀ v'.1)⁻¹ *
          (radiusChangeFactor s ord ^ 2 * rweQ (rweWGrFull ρ₂) (Whi (i - 1) v' τ).val) :=
        mul_le_mul_of_nonneg_left (h2.trans h1) (inv_nonneg.2 (hπ _).le)
    _ = _ := by ring

open scoped Classical in
/-- **The energy of the readout in the window norm.** -/
theorem weakReadoutWindowEnergy (hcommon : WeakPassageCommonOK plan) (hok : WeakCoarsePlanOK plan) :
    WeakReadoutWindowEnergyStatement plan := by
  intro B A R Dc m k ord hm hk hord c r hstart Uhi Whi hpass hvr hval i hi hit h
  obtain ⟨hcV, hfib⟩ := weakReadoutCount_at plan R c i hi hit
  have hMass : WeakReadoutMassStatement plan := weakReadoutMass plan
  have hwin := weak_quiet_window c r i hi hit
  have hΦ0 : 0 ≤ h.Φ :=
    (by unfold weightedNorm; positivity : (0 : ℝ) ≤ _).trans
      (h.mass_bound (r.tq (i + 1)) ⟨le_rfl, hwin.2.2.1.le.trans hwin.2.1⟩)
  have hrad : 0 < plan.radius R := plan.radius_pos R
  have hs0 : 0 ≤ (plan.radius R)⁻¹ := inv_nonneg.2 hrad.le
  have hρ : c.D.eps (i - 1) = (plan.radius R)⁻¹ * (plan.radius R * c.D.eps (i - 1)) := by
    field_simp
  have hF0 : 0 ≤ radiusChangeFactor (plan.radius R)⁻¹ ord ^ 2 := sq_nonneg _
  have hπ : ∀ v : Comp, 0 < weakMass c.D A.Nw A.Jw A.η₀ v := fun v => PartB.partB_mass_pos c v
  have hI : (Set.Icc (r.tq i) (r.a + A.T₀)).Nonempty := ⟨r.tq i, le_rfl, hwin.2.1⟩
  have hae : ∀ᵐ τ ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))),
      ∀ v' : CompIn (c.stage (i - 1)).comps,
        truncateTorusHk (Nat.le_succ (weakReductionReserve R m v'.1)) (Whi (i - 1) v' τ) =
          Uhi (i - 1) v' τ :=
    ae_all_iff.2 fun v' => (hpass i hi hit).2.2.1 v'
  have hA := fun t ht => rwe_partA hcommon hok m hm c r hstart Uhi Whi hpass hvr hval i hi hit
    h.Φ h.mass_bound t ht
  unfold strongEnergyUpTo
  refine (rwe_energy_abstract (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
    (fun v => (hπ _).le)
    (fun v t => factorialNormSqUpTo (c.D.eps (i - 1)) ord
      (cdW c m (k + 1 + Dc) (fun w => hk.trans (weakReductionReserve_kw R m w)) i Uhi v t).val)
    (fun v t => gradFactorialNormSqUpTo (c.D.eps (i - 1)) ord
      (cdW c m (k + 1 + Dc) (fun w => hk.trans (weakReductionReserve_kw R m w)) i Uhi v t).val)
    (fun t => radiusChangeFactor (plan.radius R)⁻¹ ord ^ 2 * massNormSq
      (plan.radius R * c.D.eps (i - 1))
      (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (fun v => (Uhi (i - 1) v t).val))
    (fun τ => radiusChangeFactor (plan.radius R)⁻¹ ord ^ 2 * massGradNormSq
      (plan.radius R * c.D.eps (i - 1))
      (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (fun v => (Whi (i - 1) v τ).val))
    (Set.Icc (r.tq i) (r.a + A.T₀)) hI (c.D.κ c.M)
    (radiusChangeFactor (plan.radius R)⁻¹ ord ^ 2 *
      (weakCoarseHighConst (plan.radius R) R m * h.Φ ^ 2))
    (mul_nonneg hF0 (mul_nonneg (weakCoarseHighConst_nonneg _ R m) (sq_nonneg _)))
    (weakReadoutCountConst A) hcV ?_ ?_ ?_).trans ?_
  · intro v t _
    exact rwe_sup_bound hMass c m _ _ i ord _ hfib Uhi _ _ hs0 hρ v t
  · intro v
    filter_upwards [hae] with τ hτ
    exact rwe_grad_bound hMass c m _ _ i ord _ hfib Uhi Whi _ _ hs0 hρ v τ hτ
  · intro t ht
    refine (le_of_eq (rwe_scale_ennreal _ hF0 _ (c.D.κ c.M / 2) _ _)).trans ?_
    rw [ENNReal.ofReal_mul hF0]
    exact mul_le_mul' le_rfl (hA t ht)
  · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hrc := radiusChangeFactor_nonneg (plan.radius R)⁻¹ ord
    have e1 : 2 * (weakReadoutCountConst A : ℝ) * weakReadoutCountConst A *
        (radiusChangeFactor (plan.radius R)⁻¹ ord ^ 2 *
          (weakCoarseHighConst (plan.radius R) R m * h.Φ ^ 2)) =
        (radiusChangeFactor (plan.radius R)⁻¹ ord * h.Φ) ^ 2 *
          (2 * weakReadoutCountConst A * weakReadoutCountConst A *
            weakCoarseHighConst (plan.radius R) R m) := by ring
    rw [e1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hrc hΦ0)]
    unfold weakReadoutWindowConst
    ring

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end
end
