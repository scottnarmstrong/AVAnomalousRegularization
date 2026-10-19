-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime
public import AVRegularity.CycleComparison.Residual.LiftStatements
import AVRegularity.CycleComparison.Residual.TailJets
import AVRegularity.CycleComparison.Residual.Jets.Lift
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CoarseFluxDiff

/-! Differentiated coarse flux: the pointwise-in-time bound of the word derivative of the scalar
residual density. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The scalar residual (vector valued). -/
def remVec (ℓ ρ e εc : ℝ) (A N : ℕ) (Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (t : ℝ) (x : Vec 2) : ∀ i, h i :=
  ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem remVec_eval (ℓ ρ e εc t τ : ℝ) (hτt : (ℓ ^ 2)⁻¹ * t = τ)
    (Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) (A N : ℕ) (x : Vec 2) (v : ι) :
    remVec ℓ ρ e εc A N Vn t x v =
      (ρ⁻¹ * (e / ρ) ^ A) • ∑ n ∈ Finset.Icc 1 N, εc ^ n •
        cleanupSource (fun j => Vn n j τ) A (ρ⁻¹ • x) (e⁻¹ • x) v := by
  have : ∀ n, cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x v =
      (e / ρ) ^ A • cleanupSource (fun j => Vn n j τ) A (ρ⁻¹ • x) (e⁻¹ • x) v := by
    intro n
    simp only [cleanupRemainder, diagSample, hτt, Pi.smul_apply]
  simp only [remVec, Pi.smul_apply, Finset.sum_apply, this]
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [smul_smul]
  congr 1
  ring

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem contDiff_remVec {π : ι → ℝ} {I : Set ℝ} {A r N kres sZ : ℕ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e rs εc τ : ℝ} {s : ℝ≥0∞}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : DiffTime π I A r N kres sZ c Fc ℓ ρ e rs εc τ s (fun n j => Vn n j τ)) (t : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) {j : ℕ} (hj : j ≤ r) :
    ContDiff ℝ (j : ℕ∞) (fun x => remVec ℓ ρ e εc A N Vn t x) := by
  unfold remVec
  refine ContDiff.const_smul _ (ContDiff.sum fun n hn => ContDiff.const_smul _ ?_)
  have hd := hT.deg n hn
  have hA := hd.hA
  have hF : IsBoxSmooth (A + 2 + r) sZ (fun (_ _ : Vec 2) (_ : Fin 2) => (0 : ∀ i, h i)) :=
    isBoxSmooth_zero _ _
  have hbox := IsCleanupChain.isBoxSmooth hF hd.chain (A - 1) (by omega)
  have hW : IsBoxSmooth (A + 1 + r) sZ (cleanupSource (fun j' => Vn n j' τ) A) :=
    isBoxSmooth_cleanupSource (sX := A + 1 + r) (hV := by
      have : A + 1 + r + 1 = A + 2 + r := by omega
      rw [this]; exact hbox)
  have := contDiff_sample hW (j := j) (by omega) (by have := hd.hZ; omega) ρ e
  unfold cleanupRemainder
  refine ContDiff.const_smul _ ?_
  have e1 : diagSample (ℓ ^ 2)⁻¹ ρ e (fun τ' X z => cleanupSource (fun j' => Vn n j' τ') A X z) t =
      fun x => cleanupSource (fun j' => Vn n j' τ) A (ρ⁻¹ • x) (e⁻¹ • x) := by
    funext x; simp [diagSample, hτt]
  rw [e1]; exact this

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem contDiff_remSample {π : ι → ℝ} {I : Set ℝ} {A r N kres sZ : ℕ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e rs εc τ : ℝ} {s : ℝ≥0∞}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : DiffTime π I A r N kres sZ c Fc ℓ ρ e rs εc τ s (fun n j => Vn n j τ)) {j : ℕ}
    (hj : j ≤ r) {n : ℕ} (hn : n ∈ Finset.Icc 1 N) (v : ι) :
    ContDiff ℝ (j : ℕ∞) (fun x' => cleanupSource (fun j' => Vn n j' τ) A (ρ⁻¹ • x') (e⁻¹ • x') v) := by
  have hd := hT.deg n hn
  have hA := hd.hA
  have hF : IsBoxSmooth (A + 2 + r) sZ (fun (_ _ : Vec 2) (_ : Fin 2) => (0 : ∀ i, h i)) :=
    isBoxSmooth_zero _ _
  have hbox := IsCleanupChain.isBoxSmooth hF hd.chain (A - 1) (by omega)
  have hW : IsBoxSmooth (A + 1 + r) sZ (cleanupSource (fun j' => Vn n j' τ) A) :=
    isBoxSmooth_cleanupSource (sX := A + 1 + r) (hV := by
      have : A + 1 + r + 1 = A + 2 + r := by omega
      rw [this]; exact hbox)
  have hWv : IsBoxSmooth (A + 1 + r) sZ (fun X y => cleanupSource (fun j' => Vn n j' τ) A X y v) :=
    hW.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
  exact contDiff_sample hWv (j := j) (by omega) (by have := hd.hZ; omega) ρ e

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem remVec_word_coord {π : ι → ℝ} {I : Set ℝ} {A r N kres sZ : ℕ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e rs εc τ : ℝ} {s : ℝ≥0∞}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : DiffTime π I A r N kres sZ c Fc ℓ ρ e rs εc τ s (fun n j => Vn n j τ)) (t : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) (v : ι) (x : Vec 2) :
    (rs ^ j • orderedDerivative β (fun x' => remVec ℓ ρ e εc A N Vn t x') x) v =
      (ρ⁻¹ * (e / ρ) ^ A) • ∑ n ∈ Finset.Icc 1 N, εc ^ n • (rs ^ j • orderedDerivative β
        (fun x' => cleanupSource (fun j' => Vn n j' τ) A (ρ⁻¹ • x') (e⁻¹ • x') v) x) := by
  have hG := contDiff_remVec hT t hτt hj
  rw [Pi.smul_apply, orderedDerivative_apply β hG v x]
  have hfun : (fun x' => remVec ℓ ρ e εc A N Vn t x' v) = fun x' =>
      (ρ⁻¹ * (e / ρ) ^ A) • ∑ n ∈ Finset.Icc 1 N, εc ^ n •
        cleanupSource (fun j' => Vn n j' τ) A (ρ⁻¹ • x') (e⁻¹ • x') v :=
    funext fun x' => remVec_eval ℓ ρ e εc t τ hτt Vn A N x' v
  rw [hfun, orderedDerivative_sum_smul β (Finset.Icc 1 N) (ρ⁻¹ * (e / ρ) ^ A) (fun n => εc ^ n)
    (H := fun n x' => cleanupSource (fun j' => Vn n j' τ) A (ρ⁻¹ • x') (e⁻¹ • x') v)
    (fun n hn => contDiff_remSample hT hj hn v)]
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_comm (rs ^ j) (ρ⁻¹ * (e / ρ) ^ A), smul_comm (rs ^ j) (εc ^ n)]

omit [∀ i, CompleteSpace (h i)] in
/-- The pointwise-in-time bound of the word derivative of the scalar residual density. -/
theorem rem_time_bound {π : ι → ℝ} {I : Set ℝ} {A r N kres sZ : ℕ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e rs εc τ : ℝ} {s : ℝ≥0∞}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : DiffTime π I A r N kres sZ c Fc ℓ ρ e rs εc τ s (fun n j => Vn n j τ)) (t : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) (hℓτ : ℓ ^ 2 * τ = t) (θ : ℝ) (hs : s = ENNReal.ofReal θ)
    (hθ : 0 ≤ θ) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖(rs ^ j • orderedDerivative β (fun x' => remVec ℓ ρ e εc A N Vn t x') x) v‖ₑ ^ 2
      ≤ ENNReal.ofReal (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * εc ^ 2 * θ ^ 2 *
          ∑ n ∈ Finset.Icc 1 N, remWordConst n A r j) * fluxDensity ρ kres π Fc t := by
  classical
  have hcard : ((Finset.Icc 1 N).card : ℝ) = N := by simp
  have hpt : ∀ (v : ι) (x : Vec 2),
      ‖(rs ^ j • orderedDerivative β (fun x' => remVec ℓ ρ e εc A N Vn t x') x) v‖ₑ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (εc ^ n) ^ 2) *
        ‖rs ^ j • orderedDerivative β
          (fun x' => cleanupSource (fun j' => Vn n j' τ) A (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2 := by
    intro v x
    rw [remVec_word_coord hT t hτt hj β v x]
    have := enorm_sq_sum_smul_le (Finset.Icc 1 N) (ρ⁻¹ * (e / ρ) ^ A) (fun n => εc ^ n)
      (fun n => rs ^ j • orderedDerivative β
        (fun x' => cleanupSource (fun j' => Vn n j' τ) A (ρ⁻¹ • x') (e⁻¹ • x') v) x)
    rwa [hcard] at this
  have hmeas : ∀ (v : ι), ∀ n ∈ Finset.Icc 1 N, Measurable fun x : Vec 2 =>
      ‖rs ^ j • orderedDerivative β
        (fun x' => cleanupSource (fun j' => Vn n j' τ) A (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2 :=
    fun v n hn => (((continuous_const.smul (contDiff_orderedDerivative (p := 0) β
      (by simpa using contDiff_remSample hT hj hn v)).continuous)).enorm.measurable).pow_const 2
  have hint : ∀ v : ι, ∫⁻ x in AVenhance.unitCube,
      ‖(rs ^ j • orderedDerivative β (fun x' => remVec ℓ ρ e εc A N Vn t x') x) v‖ₑ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (εc ^ n) ^ 2) *
        ∫⁻ x in AVenhance.unitCube, ‖rs ^ j • orderedDerivative β
          (fun x' => cleanupSource (fun j' => Vn n j' τ) A (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2 := by
    intro v
    refine (lintegral_mono (hpt v)).trans (le_of_eq ?_)
    rw [lintegral_finsetSum _ fun n hn => (hmeas v n hn).const_mul _]
    exact Finset.sum_congr rfl fun n hn => lintegral_const_mul _ (hmeas v n hn)
  set G : ℝ≥0∞ := fluxDensity ρ kres π Fc t with hG
  have hdeg : ∀ n ∈ Finset.Icc 1 N, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
      ‖rs ^ j • orderedDerivative β
        (fun x' => cleanupSource (fun j' => Vn n j' τ) A (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2
      ≤ ENNReal.ofReal (remWordConst n A r j) * ENNReal.ofReal (θ ^ 2) * G := by
    intro n hn
    have := (hT.deg n hn).rem_word_bound hj β
    rw [hs, ← ENNReal.ofReal_pow hθ, hℓτ] at this
    exact this
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖(rs ^ j • orderedDerivative β (fun x' => remVec ℓ ρ e εc A N Vn t x') x) v‖ₑ ^ 2
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
          ENNReal.ofReal (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (εc ^ n) ^ 2) *
            ∫⁻ x in AVenhance.unitCube, ‖rs ^ j • orderedDerivative β
              (fun x' => cleanupSource (fun j' => Vn n j' τ) A (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2 :=
        Finset.sum_le_sum fun v _ => by gcongr; exact hint v
    _ = ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (εc ^ n) ^ 2) *
          ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ‖rs ^ j • orderedDerivative β
            (fun x' => cleanupSource (fun j' => Vn n j' τ) A (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun v _ => by ring_nf
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * εc ^ 2) *
          (ENNReal.ofReal (remWordConst n A r j) * ENNReal.ofReal (θ ^ 2) * G) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : n ≠ 0 := by have := (Finset.mem_Icc.1 hn).1; omega
        have h1 : εc ^ n ≤ εc := pow_le_of_le_one hT.ε_nonneg hT.ε_le hn1
        have h2 : (εc ^ n) ^ 2 ≤ εc ^ 2 := pow_le_pow_left₀ (pow_nonneg hT.ε_nonneg n) h1 2
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left h2 (by positivity))) (hdeg n hn)
    _ = _ := by
        have hnn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, remWordConst n A r j :=
          Finset.sum_nonneg fun n _ => remWordConst_nonneg n A r j
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun n _ =>
          mul_nonneg (by positivity) (remWordConst_nonneg n A r j), Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        have e3 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → ENNReal.ofReal a *
            (ENNReal.ofReal b * ENNReal.ofReal c * G) = ENNReal.ofReal (a * b * c) * G :=
          fun a b c ha hb hc => by
            rw [ENNReal.ofReal_mul (mul_nonneg ha hb), ENNReal.ofReal_mul ha]; ring
        rw [e3 _ _ _ (by positivity) (remWordConst_nonneg n A r j) (by positivity)]
        congr 2
        ring
end

/-! Differentiated coarse flux: the cell-time data of all degrees from the lift sequence, the
grading and the cleanup chains. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, CompleteSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
/-- The data of every degree at one cell time. -/
theorem diffTime_at (π : ι → ℝ) (hπ : ∀ v, 0 < π v) {t₀ t₁ : ℝ} {A r N kl Ll kres : ℕ}
    (hA : 1 ≤ A) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ)
    (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) {ℓ ρ e rs εc lam Θ Cg : ℝ}
    (hρ : 0 < ρ) (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ) (hM : ∃ M : ℕ, e⁻¹ = (M : ℝ))
    (hε0 : 0 ≤ εc) (hε1 : εc ≤ 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hΘ : 0 ≤ Θ)
    (hCg : 0 ≤ Cg) (hℓ2 : 0 < ℓ ^ 2) (hk : A + 2 + r + N + 1 ≤ kres + r)
    (hbox : ∀ n m α v u, ∀ t ∈ Set.Icc t₀ t₁,
      IsBoxSmooth (A + 2 + r) r (fun X z => Cc hh n m α t X z v u))
    (hcgt : ∀ n m, n < m → ∀ α, ∀ t ∈ Set.Icc t₀ t₁, ∀ X z v u, Cc hh n m α t X z v u = 0)
    (hz : ∀ n, 1 ≤ n → n ≤ N → ∀ α, ∀ t ∈ Set.Icc t₀ t₁, ∀ X z v u, Cc hh n 0 α t X z v u = 0)
    (hgr : ∀ n, 1 ≤ n → n ≤ N → ∀ m, 1 ≤ m → m ≤ n → ∀ j, j ≤ A + 2 + r →
      schurEnergyJet π (Set.Icc t₀ t₁) (kl + r) j (Cc hh n m) ≤
        ENNReal.ofReal (Cg * Θ ^ hh * lam ^ (n - m + j)))
    (hFc : ∀ t k, ContDiff ℝ ((kres + r + 1 : ℕ) : ℕ∞) (fun x => Fc t x k))
    (Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hVn : ∀ n, 1 ≤ n → n ≤ N → ∀ τ ∈ Set.Icc t₀ t₁,
      IsCleanupChain (A + 2 + r) (max (kl + r + 1) (Ll + r + 2)) A
        (liftApply n (Cc hh n) (coarseField Fc ℓ ρ) τ) (fun _ _ _ => 0) (fun j => Vn n j τ))
    (t : ℝ) (ht : t ∈ Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) :
    DiffTime π (Set.Icc t₀ t₁) A r N (kres + r) (max (kl + r + 1) (Ll + r + 2))
      (fun n => Cc hh n) Fc ℓ ρ e rs εc ((ℓ ^ 2)⁻¹ * t)
      (ENNReal.ofReal (2 ^ (A + 2 + r) * Cg * Θ ^ hh)) (fun n j => Vn n j ((ℓ ^ 2)⁻¹ * t)) := by
  have hτ : (ℓ ^ 2)⁻¹ * t ∈ Set.Icc t₀ t₁ := by
    constructor
    · rw [le_inv_mul_iff₀ hℓ2]; linarith [ht.1]
    · rw [inv_mul_le_iff₀ hℓ2]; linarith [ht.2]
  have hℓτ : ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ hℓ2.ne', one_mul]
  refine ⟨fun n hn => ?_, hε0, hε1, fun k => ?_, by omega⟩
  · have hn1 := (Finset.mem_Icc.1 hn).1
    have hnN := (Finset.mem_Icc.1 hn).2
    obtain ⟨hj0, hj⟩ := mjet_bounds π (Set.Icc t₀ t₁) (A := A) (r := r) (k := kl + r)
      (by omega) (Cc hh n) Cg Θ lam hCg hΘ hlam0 hlam1 hh n
      (fun m α v u t ht => hbox n m α v u t ht) (fun α t ht X z v u => hz n hn1 hnN α t ht X z v u)
      (fun m hm α t ht X z v u => hcgt n m hm α t ht X z v u)
      (fun m hm1 hmn j hj => hgr n hn1 hnN m hm1 hmn j hj)
    exact {
      mass_pos := hπ
      τ_mem := hτ
      ρ_pos := hρ
      rs_pos := hrs
      rs_le := hrse
      e_le := heρ
      e_inv := hM
      hA := hA
      hZ := by omega
      order := by omega
      box := fun m α v u => hbox n m α v u _ hτ
      mjet0 := hj0
      mjet := hj
      smooth := fun k => by
        have := hFc ((ℓ ^ 2) * ((ℓ ^ 2)⁻¹ * t)) k
        rw [hℓτ] at this ⊢
        exact hFc t k
      chain := hVn n hn1 hnN _ hτ }
  · rw [hℓτ]
    exact hFc t k
end

/-! Differentiated coarse flux: the residual norm of a word derivative from the cell-time data. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The constant of the differentiated coarse flux bound for the word length `j`. -/
def wordBoundConst (N A r j : ℕ) (C₀ : ℝ) : ℝ :=
  max (Real.sqrt (2 * ((j.factorial : ℝ)) ^ 2))
    (max (C₀ * Real.sqrt (2 * N * ∑ n ∈ Finset.Icc 1 N, fluxWordConst n A r j))
      (C₀ * Real.sqrt (N * ∑ n ∈ Finset.Icc 1 N, remWordConst n A r j)))

theorem wordBoundConst_nonneg (N A r j : ℕ) (C₀ : ℝ) : 0 ≤ wordBoundConst N A r j C₀ :=
  (Real.sqrt_nonneg _).trans (le_max_left _ _)

omit [∀ i, CompleteSpace (h i)] in
theorem core_bound (π : ι → ℝ) {t₀ t₁ ν B ρ e ℓ rs εc : ℝ} (hν : 0 < ν) (hB : 0 < B)
    (hρ : 0 < ρ) (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ) (hℓ : ℓ = e / Real.sqrt ν)
    (hε : εc = ℓ * Real.sqrt B / ρ) (hwin : t₀ ≤ t₁) {C₀ Θ : ℝ} (hC₀ : 0 ≤ C₀) (hΘ : 0 ≤ Θ)
    (hh : ℕ) {A N r kres sZ : ℕ} {I : Set ℝ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : ∀ t ∈ Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁),
      DiffTime π I A r N kres sZ c Fc ℓ ρ e rs εc ((ℓ ^ 2)⁻¹ * t)
        (ENNReal.ofReal (C₀ * Θ ^ hh)) (fun n j => Vn n j ((ℓ ^ 2)⁻¹ * t)))
    {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) {Z : ℝ}
    (hZ : Z = Real.sqrt (ℓ ^ 2 * (t₁ - t₀)) / ℓ * (e / ρ) ^ A) :
    residualNorm ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
        (fun t x k => rs ^ j • orderedDerivative β
          (fun x' => (if hh = 0 then Fc t x' k else 0) +
            ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x' k) x)
        (fun t x => rs ^ j • orderedDerivative β (fun x' => ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
          εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x') x)
      ≤ ENNReal.ofReal (wordBoundConst N A r j C₀ * ((if hh = 0 then Real.sqrt (B / ν) else 0)
            + Θ ^ hh * εc ^ 2 * (1 + Z)) * (Real.sqrt B)⁻¹) *
        classicalFluxL2H ρ π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) kres Fc := by
  classical
  have he : 0 < e := hrs.trans_le hrse
  have hsν := Real.sqrt_pos.2 hν
  have hsB := Real.sqrt_pos.2 hB
  have hℓpos : 0 < ℓ := by rw [hℓ]; exact div_pos he hsν
  have hΘh : 0 ≤ Θ ^ hh := pow_nonneg hΘ hh
  set θ : ℝ := C₀ * Θ ^ hh with hθdef
  have hθ : 0 ≤ θ := mul_nonneg hC₀ hΘh
  set cf : ℝ := ∑ n ∈ Finset.Icc 1 N, fluxWordConst n A r j with hcf
  set cr : ℝ := ∑ n ∈ Finset.Icc 1 N, remWordConst n A r j with hcr
  have hcf0 : 0 ≤ cf := Finset.sum_nonneg fun n _ => fluxWordConst_nonneg n A r j
  have hcr0 : 0 ≤ cr := Finset.sum_nonneg fun n _ => remWordConst_nonneg n A r j
  have hεpos : 0 < εc := by rw [hε]; positivity
  set X₁ : ℝ := (if hh = 0 then 2 * ((j.factorial : ℝ)) ^ 2 else 0) +
    2 * N * (e / ρ) ^ 2 * εc ^ 2 * θ ^ 2 * cf with hX₁
  set X₂ : ℝ := N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * εc ^ 2 * θ ^ 2 * cr with hX₂
  have hX₁0 : 0 ≤ X₁ := by
    rw [hX₁]
    exact add_nonneg (by split_ifs <;> positivity) (mul_nonneg (by positivity) hcf0)
  have hX₂0 : 0 ≤ X₂ := by rw [hX₂]; exact mul_nonneg (by positivity) hcr0
  set G : ℝ → ℝ≥0∞ := fun t => fluxDensity ρ kres π Fc t with hGdef
  have hR : ∀ t ∈ Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁), ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
      ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖(rs ^ j • orderedDerivative β (fun x' =>
        (if hh = 0 then Fc t x' k else 0) + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
          εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x' k) x) v‖ₑ ^ 2
      ≤ ENNReal.ofReal ((Real.sqrt X₁) ^ 2) * G t := by
    intro t ht
    rw [Real.sq_sqrt hX₁0]
    have hℓτ : ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * t) = t := by
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    exact flux_time_bound (hT t ht) hh t rfl hℓτ θ rfl hθ hj β hrs (hrse.trans heρ)
  have hq : ∀ t ∈ Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁), ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
      ∫⁻ x in AVenhance.unitCube, ‖(rs ^ j • orderedDerivative β (fun x' => ρ⁻¹ •
        ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x') x) v‖ₑ ^ 2
      ≤ ENNReal.ofReal ((Real.sqrt X₂) ^ 2) * G t := by
    intro t ht
    rw [Real.sq_sqrt hX₂0]
    have hℓτ : ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * t) = t := by
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    exact rem_time_bound (hT t ht) t rfl hℓτ θ rfl hθ hj β
  have hres := residualNorm_le_of_pointwise ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
    (fun t x k => rs ^ j • orderedDerivative β
      (fun x' => (if hh = 0 then Fc t x' k else 0) +
        ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x' k) x)
    (fun t x => rs ^ j • orderedDerivative β (fun x' => ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
      εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x') x) G
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) measurableSet_Icc hR hq
  have hvol : volume (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (ℓ ^ 2 * (t₁ - t₀))) := by
    rw [Real.volume_Icc, ENNReal.ofReal_rpow_of_nonneg (by nlinarith [sq_nonneg ℓ]) (by norm_num),
      ← Real.sqrt_eq_rpow]
    congr 2; ring
  rw [hvol] at hres
  have hGs : classicalFluxL2H ρ π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) kres Fc =
      (∫⁻ t in Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁), G t) ^ (1 / 2 : ℝ) := rfl
  rw [hGs]
  refine hres.trans ?_
  have hL : 0 ≤ ℓ ^ 2 * (t₁ - t₀) := mul_nonneg (by positivity) (by linarith)
  have hind : (if hh = 0 then (1 : ℝ) else 0) = 0 ∨ (if hh = 0 then (1 : ℝ) else 0) = 1 := by
    split_ifs <;> simp
  have hreal := final_real (ν := ν) (B := B) (ρ := ρ) (e := e) (ℓ := ℓ) (εc := εc)
    (L := ℓ ^ 2 * (t₁ - t₀)) (C₀ := C₀) (Θh := Θ ^ hh) (N := (N : ℝ)) (cf := cf) (cr := cr)
    (indr := if hh = 0 then 1 else 0) (c1 := 2 * ((j.factorial : ℝ)) ^ 2) (A := A) hν hB hρ he hℓ hε
    hC₀ hΘh (by positivity) hcf0 (by positivity) hind
  have hX₁' : X₁ = 2 * ((j.factorial : ℝ)) ^ 2 * (if hh = 0 then (1 : ℝ) else 0) +
      2 * N * (e / ρ) ^ 2 * εc ^ 2 * (C₀ * Θ ^ hh) ^ 2 * cf := by
    rw [hX₁, hθdef]; split_ifs <;> simp
  have hind' : (if hh = 0 then (1 : ℝ) else 0) * Real.sqrt (B / ν) =
      if hh = 0 then Real.sqrt (B / ν) else 0 := by split_ifs <;> simp
  calc ENNReal.ofReal (Real.sqrt ν)⁻¹ * ENNReal.ofReal (Real.sqrt X₁) *
        (∫⁻ t in Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁), G t) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (Real.sqrt X₂) * ENNReal.ofReal (Real.sqrt (ℓ ^ 2 * (t₁ - t₀))) *
          (∫⁻ t in Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁), G t) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal ((Real.sqrt ν)⁻¹ * Real.sqrt X₁ + Real.sqrt X₂ *
          Real.sqrt (ℓ ^ 2 * (t₁ - t₀))) *
        (∫⁻ t in Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁), G t) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        ring
    _ ≤ _ := by
        gcongr
        rw [hX₁', hX₂]
        refine hreal.trans (le_of_eq ?_)
        have hw : wordBoundConst N A r j C₀ = max (Real.sqrt (2 * ((j.factorial : ℝ)) ^ 2))
            (max (C₀ * Real.sqrt (2 * N * cf)) (C₀ * Real.sqrt (N * cr))) := rfl
        rw [hw, hZ, ← hind']
end

end AVRegularity.CoarseFluxDiff
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The differentiated lifted coarse-flux reconstruction from the lift grading and
structure statements. -/

universe u v

theorem cycle_residual_coarse_flux_differentiated_of_lift (Acl N D H kl Ll : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (hgrad : ∀ r, CycleLiftGradingStatement.{u, v} N (Acl + 2 + r) (kl + r) (Ll + r) D H CG Cw Cj)
    (hstruct : ∀ r, CycleLiftStructureStatement.{u, v} N (Acl + 2 + r) (kl + r) (Ll + r) D H CG Cw Cj) :
    CoarseFluxDiff.Statement.{u, v} Acl N D H kl Ll CG Cw Cj := by
  intro hA r
  obtain ⟨Cg, hCg0, hgr⟩ := hgrad r
  refine ⟨∑ j ∈ Finset.range (r + 1),
    CoarseFluxDiff.wordBoundConst N Acl r j (2 ^ (Acl + 2 + r) * Cg),
    Finset.sum_nonneg fun j _ => CoarseFluxDiff.wordBoundConst_nonneg N Acl r j _, ?_⟩
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ rs E ℓ dstar εc lam par V qs qf b Θ hrs hrse heρ kres s0
    hkres hs0 hset hM Cc hseq hh hhH Fc hFc hFcper Vn hVn Z hZ j hj β
  subst hs0
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨v₀⟩⟩
  · simp [residualNorm, Finset.univ_eq_empty]
  have he := hset.e_pos
  have hν := hset.ν_pos
  have hB := hset.B_pos
  have hρ := hset.ρ_pos
  have hsν := Real.sqrt_pos.2 hν
  have hsB := Real.sqrt_pos.2 hB
  have hℓ : 0 < ℓ := by rw [hset.ℓ_eq]; exact div_pos he hsν
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have he_eq : e = ℓ * Real.sqrt ν := by rw [hset.ℓ_eq]; field_simp
  have hℓe : ℓ = e / Real.sqrt ν := hset.ℓ_eq
  have hεc_eq : εc = ℓ * Real.sqrt B / ρ := by rw [hset.εc_eq, hset.dstar_eq]
  have hεc0 : 0 ≤ εc := by rw [hεc_eq]; positivity
  have hΘ : 0 ≤ Θ := le_trans (Finset.sum_nonneg fun u _ => hset.envelope.nonneg v₀ u)
    (hset.envelope.row_sum v₀)
  have hlam0 : 0 ≤ lam := by rw [hset.lam_eq]; exact div_nonneg hρ.le hset.E_pos.le
  have hgr' := hgr Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ hset Cc hseq
  have hst := (hstruct r Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ hset Cc hseq).1
  have hT : ∀ t ∈ Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁),
      CoarseFluxDiff.DiffTime π (Set.Icc t₀ t₁) Acl r N (kres + r)
        (max (kl + r + 1) (Ll + r + 2)) (fun n => Cc hh n) Fc ℓ ρ e rs εc ((ℓ ^ 2)⁻¹ * t)
        (ENNReal.ofReal ((2 ^ (Acl + 2 + r) * Cg) * Θ ^ hh)) (fun n j => Vn n j ((ℓ ^ 2)⁻¹ * t)) :=
    fun t ht => CoarseFluxDiff.diffTime_at π hset.mass_pos hA Cc hh Fc hρ hrs hrse heρ hM hεc0
      hset.εc_le hlam0 hset.lam_le hΘ hCg0 hℓ2 (by omega)
      (fun n m α v u t ht => ((hseq.2.2.2.2.2.1 hh hhH n m α v u t ht).1).mono
        (sX' := Acl + 2 + r) (sZ' := r) (by omega) (by omega))
      (fun n m hm α t ht X z v u => hseq.2.2.2.1 hh hhH n m hm α t X z v u)
      (fun n hn1 hnN α t ht X z v u => CoarseFluxDiff.coeff_zero_of_const (Cc hh n) n t X z
        (fun c0 => (hst c0 hh hhH t ht X z).1 n hn1 hnN) α v u)
      (fun n hn1 hnN m hm1 hmn j hj => (hgr' hh hhH n hn1 hnN m hm1 hmn j hj).1)
      hFc Vn hVn t ht
  have hcore := CoarseFluxDiff.core_bound π hν hB hρ hrs hrse heρ hℓe hεc_eq hset.window
    (C₀ := 2 ^ (Acl + 2 + r) * Cg) (Θ := Θ) (by positivity) hΘ hh hT hj β hZ
  refine hcore.trans ?_
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hw : CoarseFluxDiff.wordBoundConst N Acl r j (2 ^ (Acl + 2 + r) * Cg) ≤
      ∑ j' ∈ Finset.range (r + 1), CoarseFluxDiff.wordBoundConst N Acl r j' (2 ^ (Acl + 2 + r) * Cg) :=
    Finset.single_le_sum (f := fun j' => CoarseFluxDiff.wordBoundConst N Acl r j'
      (2 ^ (Acl + 2 + r) * Cg)) (fun j' _ => CoarseFluxDiff.wordBoundConst_nonneg N Acl r j' _)
      (Finset.mem_range.2 (by omega))
  have hX0 : 0 ≤ ((if hh = 0 then Real.sqrt (B / ν) else 0) + Θ ^ hh * εc ^ 2 * (1 + Z)) *
      (Real.sqrt B)⁻¹ := by
    refine mul_nonneg (add_nonneg (by split_ifs <;> positivity) (by positivity)) (by positivity)
  gcongr

end AVRegularity
end
