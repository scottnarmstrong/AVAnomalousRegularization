-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.SlowJet
import AVRegularity.CycleComparison.Residual.TailJets
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.BoundPointwise
import AVRegularity.CycleComparison.Residual.FastJets.Chain
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CoarseFluxDiff

/-! Differentiated coarse flux: the data of one lift degree at one cell time, and the bounds of the
word derivatives of the sampled cleanup flux and remainder of that degree. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The per-degree weight `J_{n,p} = liftJetConst · ∑_q coarseConst`. -/
def jetWeight (n p : ℕ) : ℝ := liftJetConst n p * ∑ q ∈ Finset.Icc 1 (p + n), coarseConst q

theorem jetWeight_nonneg (n p : ℕ) : 0 ≤ jetWeight n p :=
  mul_nonneg (liftJetConst_nonneg n p) (Finset.sum_nonneg fun q _ => coarseConst_nonneg q)

/-- The number of pairs of subwords: `∑_{a+b=j} 2^b`. -/
def wordCount (j : ℕ) : ℝ := ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, (2 : ℝ) ^ ab.2

theorem wordCount_nonneg (j : ℕ) : 0 ≤ wordCount j :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The constant of the word derivatives of the sampled cleanup flux of one degree. -/
def fluxWordConst (n A r j : ℕ) : ℝ :=
  (A : ℝ) ^ 2 * 4 ^ j * 4 * wordCount j * ∑ p ∈ Finset.range (A + r + 2), jetWeight n p

/-- The constant of the word derivatives of the sampled cleanup remainder of one degree. -/
def remWordConst (n A r j : ℕ) : ℝ :=
  4 ^ j * 4 * wordCount j * 2 * ∑ p ∈ Finset.range (A + r + 3), jetWeight n p

theorem fluxWordConst_nonneg (n A r j : ℕ) : 0 ≤ fluxWordConst n A r j :=
  mul_nonneg (mul_nonneg (by positivity) (wordCount_nonneg j))
    (Finset.sum_nonneg fun p _ => jetWeight_nonneg n p)

theorem remWordConst_nonneg (n A r j : ℕ) : 0 ≤ remWordConst n A r j :=
  mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (wordCount_nonneg j)) (by norm_num))
    (Finset.sum_nonneg fun p _ => jetWeight_nonneg n p)

theorem sum_words_const (j : ℕ) (T : ℝ≥0∞) :
    ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ _δ : DerivativeWord2 ab.2, T =
      ENNReal.ofReal (wordCount j) * T := by
  unfold wordCount
  rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [Finset.sum_const, card_derivativeWord2, nsmul_eq_mul, ENNReal.ofReal_pow (by norm_num)]
  simp

theorem enorm_sq_sum_pow_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : ℕ)
    {ϑ : ℝ} (hϑ0 : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1) (b : ℕ → E) :
    ‖∑ j ∈ Finset.range A, ϑ ^ j • b j‖ₑ ^ 2 ≤
      (A : ℝ≥0∞) * ∑ j ∈ Finset.range A, ‖b j‖ₑ ^ 2 := by
  have hϑ : ∀ j : ℕ, ‖ϑ ^ j‖ₑ ≤ 1 := by
    intro j
    rw [enorm_pow, Real.enorm_eq_ofReal hϑ0]
    exact pow_le_one₀ bot_le (ENNReal.ofReal_le_one.2 hϑ1)
  calc ‖∑ j ∈ Finset.range A, ϑ ^ j • b j‖ₑ ^ 2
      ≤ (∑ j ∈ Finset.range A, ‖b j‖ₑ) ^ 2 := by
        gcongr
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [enorm_smul]
        calc ‖ϑ ^ j‖ₑ * ‖b j‖ₑ ≤ 1 * ‖b j‖ₑ := by gcongr; exact hϑ j
          _ = _ := one_mul _
    _ ≤ _ := by
        simpa using ennreal_sq_sum_le_card_mul_sum_sq (Finset.range A) (fun j => ‖b j‖ₑ)

theorem flux_const_eq (A j P : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (Jp : ℕ → ℝ) (hJ : ∀ p, 0 ≤ Jp p)
    (s G : ℝ≥0∞) :
    (A : ℝ≥0∞) * ((A : ℝ≥0∞) * (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2))) *
        ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ _δ : DerivativeWord2 ab.2,
          ∑ p ∈ Finset.range P, (ENNReal.ofReal (ρ⁻¹ ^ 2 * Jp p) * s ^ 2 * G) =
      ENNReal.ofReal ((A : ℝ) ^ 2 * 4 ^ j * 4 * wordCount j * ∑ p ∈ Finset.range P, Jp p) *
        s ^ 2 * G := by
  rw [sum_words_const]
  have hρ2 : ρ ^ 2 * ρ⁻¹ ^ 2 = 1 := by field_simp
  have e1 : ∑ p ∈ Finset.range P, (ENNReal.ofReal (ρ⁻¹ ^ 2 * Jp p) * s ^ 2 * G) =
      ENNReal.ofReal (∑ p ∈ Finset.range P, ρ⁻¹ ^ 2 * Jp p) * (s ^ 2 * G) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun p _ => mul_nonneg (by positivity) (hJ p), Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e1]
  have e2 : ENNReal.ofReal ((A : ℝ) ^ 2 * 4 ^ j * 4 * wordCount j * ∑ p ∈ Finset.range P, Jp p) =
      (A : ℝ≥0∞) * ((A : ℝ≥0∞) * (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2))) *
        (ENNReal.ofReal (wordCount j) *
          ENNReal.ofReal (∑ p ∈ Finset.range P, ρ⁻¹ ^ 2 * Jp p)) := by
    have hJs : 0 ≤ ∑ p ∈ Finset.range P, Jp p := Finset.sum_nonneg fun p _ => hJ p
    have hJs' : 0 ≤ ∑ p ∈ Finset.range P, ρ⁻¹ ^ 2 * Jp p :=
      Finset.sum_nonneg fun p _ => mul_nonneg (by positivity) (hJ p)
    have hX : (A : ℝ) ^ 2 * 4 ^ j * 4 * wordCount j * ∑ p ∈ Finset.range P, Jp p =
        ((A : ℝ) * ((A : ℝ) * (4 ^ j * (4 * ρ ^ 2)))) *
          (wordCount j * ∑ p ∈ Finset.range P, ρ⁻¹ ^ 2 * Jp p) := by
      rw [← Finset.mul_sum]
      calc (A : ℝ) ^ 2 * 4 ^ j * 4 * wordCount j * ∑ p ∈ Finset.range P, Jp p
          = (A : ℝ) ^ 2 * 4 ^ j * 4 * wordCount j * ((ρ ^ 2 * ρ⁻¹ ^ 2) *
              ∑ p ∈ Finset.range P, Jp p) := by rw [hρ2, one_mul]
        _ = _ := by ring
    rw [hX, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (wordCount_nonneg j), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by norm_num)]
    simp
  rw [e2]
  ring

theorem isBoxSmooth_cleanupSource {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {sX sZ : ℕ}
    {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E} {j : ℕ} (hV : IsBoxSmooth (sX + 1) sZ (V (j - 1))) :
    IsBoxSmooth sX sZ (cleanupSource V j) := by
  have h1 : ∀ k : Fin 2, IsBoxSmooth sX sZ
      (AVRegularity.slowPartial k (fun X z => V (j - 1) X z k)) := fun k =>
    (hV.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k)).slowPartial k
  have := (IsBoxSmooth.sum Finset.univ fun k _ => h1 k).neg
  exact this

theorem rem_const_eq (j P : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (Jp : ℕ → ℝ) (hJ : ∀ p, 0 ≤ Jp p)
    (s G : ℝ≥0∞) :
    (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2)) *
        ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ _δ : DerivativeWord2 ab.2,
          (2 * ∑ p ∈ Finset.range P, (ENNReal.ofReal (ρ⁻¹ ^ 2 * Jp p) * s ^ 2 * G)) =
      ENNReal.ofReal (4 ^ j * 4 * wordCount j * 2 * ∑ p ∈ Finset.range P, Jp p) * s ^ 2 * G := by
  rw [sum_words_const]
  have hρ2 : ρ ^ 2 * ρ⁻¹ ^ 2 = 1 := by field_simp
  have e1 : ∑ p ∈ Finset.range P, (ENNReal.ofReal (ρ⁻¹ ^ 2 * Jp p) * s ^ 2 * G) =
      ENNReal.ofReal (∑ p ∈ Finset.range P, ρ⁻¹ ^ 2 * Jp p) * (s ^ 2 * G) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun p _ => mul_nonneg (by positivity) (hJ p), Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e1]
  have hX : (4 : ℝ) ^ j * 4 * wordCount j * 2 * ∑ p ∈ Finset.range P, Jp p =
      (4 ^ j * (4 * ρ ^ 2)) * (wordCount j * (2 * ∑ p ∈ Finset.range P, ρ⁻¹ ^ 2 * Jp p)) := by
    rw [← Finset.mul_sum]
    calc (4 : ℝ) ^ j * 4 * wordCount j * 2 * ∑ p ∈ Finset.range P, Jp p
        = (4 : ℝ) ^ j * 4 * wordCount j * 2 * ((ρ ^ 2 * ρ⁻¹ ^ 2) *
            ∑ p ∈ Finset.range P, Jp p) := by rw [hρ2, one_mul]
      _ = _ := by ring
  have hJs' : 0 ≤ ∑ p ∈ Finset.range P, ρ⁻¹ ^ 2 * Jp p :=
    Finset.sum_nonneg fun p _ => mul_nonneg (by positivity) (hJ p)
  have h4 : ENNReal.ofReal ((4 : ℝ) ^ j) = 4 ^ j := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  have h2 : ENNReal.ofReal (2 * ∑ p ∈ Finset.range P, ρ⁻¹ ^ 2 * Jp p) =
      2 * ENNReal.ofReal (∑ p ∈ Finset.range P, ρ⁻¹ ^ 2 * Jp p) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  have hall : ENNReal.ofReal (4 ^ j * 4 * wordCount j * 2 * ∑ p ∈ Finset.range P, Jp p) =
      (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2)) * (ENNReal.ofReal (wordCount j) *
        (2 * ENNReal.ofReal (∑ p ∈ Finset.range P, ρ⁻¹ ^ 2 * Jp p))) := by
    rw [hX, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (wordCount_nonneg j),
      ENNReal.ofReal_mul (by positivity), h2, h4]
  rw [hall]
  ring

/-- The data of one degree at one cell time. -/
structure DiffDegree (π : ι → ℝ) (I : Set ℝ) (A r n kres sZ : ℕ) (c : LiftCoeff ι h)
    (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (ℓ ρ e rs τ : ℝ) (s : ℝ≥0∞)
    (V : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) : Prop where
  mass_pos : ∀ v, 0 < π v
  τ_mem : τ ∈ I
  ρ_pos : 0 < ρ
  rs_pos : 0 < rs
  rs_le : rs ≤ e
  e_le : e ≤ ρ
  e_inv : ∃ M : ℕ, e⁻¹ = (M : ℝ)
  hA : 1 ≤ A
  hZ : r + 1 ≤ sZ
  order : A + 2 + r + n + 1 ≤ kres
  box : ∀ m α v u, IsBoxSmooth (A + 2 + r) r (fun X y => c m α τ X y v u)
  mjet0 : ∀ b, b ≤ r → ∀ δ : DerivativeWord2 b, ∀ i, MixedTail.schurMixedJet π I i δ (c 0) = 0
  mjet : ∀ b, b ≤ r → ∀ δ : DerivativeWord2 b, ∀ i, i ≤ A + 2 + r → ∀ m,
    MixedTail.schurMixedJet π I i δ (c m) ≤ s
  smooth : ∀ k, ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * τ) x k)
  chain : IsCleanupChain (A + 2 + r) sZ A (liftApply n c (coarseField Fc ℓ ρ) τ)
    (fun _ _ _ => 0) V

namespace DiffDegree

variable {π : ι → ℝ} {I : Set ℝ} {A r n kres sZ : ℕ} {c : LiftCoeff ι h}
  {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e rs τ : ℝ} {s : ℝ≥0∞}
  {V : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem slow_f (hd : DiffDegree π I A r n kres sZ c Fc ℓ ρ e rs τ s V) :
    IsSlowSmooth (A + 2 + r) (liftApply n c (coarseField Fc ℓ ρ) τ) := by
  have hF' : ∀ k, ContDiff ℝ (((A + 2 + r) + n + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * τ) x k) :=
    fun k => (hd.smooth k).of_le (by exact_mod_cast (by have := hd.order; omega))
  exact isSlowSmooth_liftApply n (A + 2 + r) c (coarseField Fc ℓ ρ) τ
    (fun m α v u => (hd.box m α v u).isSlowSmooth)
    (contDiff_coarseField τ hF')

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The chain projected on one component. -/
theorem chain_component (hd : DiffDegree π I A r n kres sZ c Fc ℓ ρ e rs τ s V) (v : ι) :
    IsCleanupChain (A + 2 + r) sZ A (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v)
      (fun _ _ _ => (0 : h v)) (fun j X y k => V j X y k v) :=
  IsCleanupChain.clm_comp (by omega) (by have := hd.hZ; omega) (IsSlowSmooth.zero) hd.chain
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)

omit [∀ i, CompleteSpace (h i)] in
/-- The mixed jets of one lift action of the coarse field, integrated over the slow cell. -/
theorem T_bound (hd : DiffDegree π I A r n kres sZ c Fc ℓ ρ e rs τ s V) {p : ℕ}
    (hp : p ≤ A + 2 + r) (hpk : p + n + 1 ≤ kres) {b : ℕ} (hb : b ≤ r) (δ : DerivativeWord2 b) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
        FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X
      ≤ ENNReal.ofReal (ρ⁻¹ ^ 2 * jetWeight n p) * s ^ 2 * fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) := by
  have key := slowCell_scalJetF_le π hd.mass_pos I n p kres δ hpk c hd.τ_mem
    (fun m α v u => (hd.box m α v u).mono hp hb) (fun i => hd.mjet0 b hb δ i) s
    (fun i hi m => hd.mjet b hb δ i (by omega) m) Fc ℓ ρ hd.ρ_pos hd.smooth
  refine le_trans ?_ key
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact sum_lintegral_le_lintegral_sum _ _

theorem vecJetF_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {b : ℕ}
    (δ : DerivativeWord2 b) (q : ℕ) (X : Vec 2) :
    FastJets.vecJetF (fun (_ _ : Vec 2) (_ : Fin 2) => (0 : F)) q δ X = 0 := by
  unfold FastJets.vecJetF
  refine Finset.sum_eq_zero fun β _ => ?_
  have h1 : ∀ y : Vec 2, (fun X' : Vec 2 => orderedDerivative δ (fun _ : Vec 2 => (0 : F)) y) =
      fun _ => 0 := fun y => by simp [orderedDerivative_const_zero]
  simp [orderedDerivative_const_zero]

omit [∀ i, CompleteSpace (h i)] in
/-- One member of the cleanup chain: its mixed jets are controlled by those of the source. -/
theorem flux_member (hd : DiffDegree π I A r n kres sZ c Fc ℓ ρ e rs τ s V) {j' : ℕ} (hj' : j' < A)
    {a b : ℕ} (ha : a ≤ r) (hb : b ≤ r) (δ : DerivativeWord2 b) (v : ι) :
    ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
        FastJets.vecJetF (fun X y k => V j' X y k v) (a + m) δ X
      ≤ ∑ p ∈ Finset.range (A + r + 2), ∫⁻ X in slowCell ρ,
        FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X := by
  have hch := hd.chain_component v
  have hF : IsBoxSmooth (A + 2 + r) sZ (fun (_ _ : Vec 2) (_ : Fin 2) => (0 : h v)) :=
    isBoxSmooth_zero _ _
  have hb1 : b + 1 ≤ sZ := by have := hd.hZ; omega
  calc ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
        FastJets.vecJetF (fun X y k => V j' X y k v) (a + m) δ X
      ≤ ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
          FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v)
            (m + (a + j')) δ X := by
        refine Finset.sum_le_sum fun m hm => lintegral_mono fun X => ?_
        have hm3 := Finset.mem_range.1 hm
        calc FastJets.vecJetF (fun X y k => V j' X y k v) (a + m) δ X
            ≤ (2 * antidivConst) ^ j' * FastJets.vecJetF (fun X y k => V 0 X y k v) (a + m + j') δ X :=
              FastJets.vecJetF_cleanupChain_le δ hb1 hF hch j' hj' (a + m) (by omega) X
          _ ≤ 1 * FastJets.vecJetF (fun X y k => V 0 X y k v) (a + m + j') δ X := by
              gcongr; exact pow_le_one₀ bot_le two_mul_antidivConst_le_one
          _ ≤ FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v)
                (m + (a + j')) δ X := by
              rw [one_mul]
              refine (FastJets.vecJetF_cleanupChain_zero_le δ hb1 hF hch (m := a + m + j')
                (by omega) X).trans ?_
              rw [vecJetF_zero, mul_zero, zero_add, show m + (a + j') = a + m + j' by omega]
              calc 2 * (antidivConst * FastJets.scalJetF
                    (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) (a + m + j') δ X)
                  ≤ 1 * (FastJets.scalJetF
                    (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) (a + m + j') δ X) := by
                    rw [← mul_assoc]; gcongr; exact two_mul_antidivConst_le_one
                _ = _ := one_mul _
    _ ≤ _ := sum_range_shift_le (fun p => ∫⁻ X in slowCell ρ,
          FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X)
          (by omega)

omit [∀ i, CompleteSpace (h i)] in
/-- One member of the chain, one component: the `L²` norm of the word derivative of its sample. -/
theorem flux_member_word (hd : DiffDegree π I A r n kres sZ c Fc ℓ ρ e rs τ s V) {j' : ℕ}
    (hj' : j' < A) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) (v : ι) {M : ℕ}
    (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k v) x‖ₑ ^ 2
      ≤ 4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
        ∑ δ : DerivativeWord2 ab.2, ∑ p ∈ Finset.range (A + r + 2), ∫⁻ X in slowCell ρ,
          FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X := by
  have hch := hd.chain_component v
  have hF : IsBoxSmooth (A + 2 + r) sZ (fun (_ _ : Vec 2) (_ : Fin 2) => (0 : h v)) :=
    isBoxSmooth_zero _ _
  have hbox := IsCleanupChain.isBoxSmooth hF hch j' hj'
  have hW : IsBoxSmooth (j + 2) j (fun X y k => V j' X y k v) :=
    hbox.mono (by omega) (by have := hd.hZ; omega)
  have hper : ∀ X, AVenhance.IsZ2Periodic (fun y k => V j' X y k v) :=
    IsCleanupChain.periodic (fun X n y => rfl) hch j' hj'
  refine (sampled_word_vec_le β hW hper hd.rs_pos hd.rs_le hd.e_le M hM).trans ?_
  gcongr with ab hab δ _
  have hab' := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  exact hd.flux_member hj' (by omega) (by omega) δ v

omit [∀ i, CompleteSpace (h i)] in
/-- Per component: the word derivative of the sampled cleanup flux of one degree. -/
theorem flux_word_component (hd : DiffDegree π I A r n kres sZ c Fc ℓ ρ e rs τ s V) {j : ℕ}
    (hj : j ≤ r) (β : DerivativeWord2 j) (v : ι) {M : ℕ} (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
          (rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2
      ≤ (A : ℝ≥0∞) * ((A : ℝ≥0∞) * (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2))) *
        ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ δ : DerivativeWord2 ab.2,
          ∑ p ∈ Finset.range (A + r + 2), ∫⁻ X in slowCell ρ,
            FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X := by
  have he : 0 ≤ e := (hd.rs_pos.trans_le hd.rs_le).le
  have hϑ0 : 0 ≤ e / ρ := div_nonneg he hd.ρ_pos.le
  have hϑ1 : e / ρ ≤ 1 := (div_le_one hd.ρ_pos).2 hd.e_le
  have hch := hd.chain_component v
  have hF : IsBoxSmooth (A + 2 + r) sZ (fun (_ _ : Vec 2) (_ : Fin 2) => (0 : h v)) :=
    isBoxSmooth_zero _ _
  have hbox := IsCleanupChain.isBoxSmooth hF hch
  have hmeas : ∀ j' ∈ Finset.range A, Measurable fun x : Vec 2 => ∑ k : Fin 2,
      ‖rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k v) x‖ₑ ^ 2 := by
    intro j' hj'
    refine Finset.measurable_sum _ fun k _ => ?_
    exact measurable_sampled_word β (W := fun X y => V j' X y k v)
      ((hbox j' (Finset.mem_range.1 hj')).clm_comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => h v) k))
      (by have := hd.hZ; omega) (by have := hd.hZ; omega) ρ e _
  have hpt : ∀ x : Vec 2, ∑ k : Fin 2,
      ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
        (rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2 ≤
      (A : ℝ≥0∞) * ∑ j' ∈ Finset.range A, ∑ k : Fin 2,
        ‖rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k v) x‖ₑ ^ 2 := by
    intro x
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    exact enorm_sq_sum_pow_smul_le A hϑ0 hϑ1 _
  calc ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
          (rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2
      ≤ ∫⁻ x in AVenhance.unitCube, (A : ℝ≥0∞) * ∑ j' ∈ Finset.range A, ∑ k : Fin 2,
        ‖rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k v) x‖ₑ ^ 2 :=
        lintegral_mono hpt
    _ = (A : ℝ≥0∞) * ∑ j' ∈ Finset.range A, ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k v) x‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum _ hmeas]
    _ ≤ (A : ℝ≥0∞) * ∑ _j' ∈ Finset.range A, 4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) *
        ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ δ : DerivativeWord2 ab.2,
          ∑ p ∈ Finset.range (A + r + 2), ∫⁻ X in slowCell ρ,
            FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X := by
        gcongr with j' hj'
        exact hd.flux_member_word (Finset.mem_range.1 hj') hj β v hM
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

omit [∀ i, CompleteSpace (h i)] in
/-- The word derivative of the sampled cleanup flux of one degree, with the mass weights. -/
theorem flux_word_bound (hd : DiffDegree π I A r n kres sZ c Fc ℓ ρ e rs τ s V) {j : ℕ}
    (hj : j ≤ r) (β : DerivativeWord2 j) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
          (rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2
      ≤ ENNReal.ofReal (fluxWordConst n A r j) * s ^ 2 * fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) := by
  obtain ⟨M, hM⟩ := hd.e_inv
  set G := fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) with hG
  set C : ℝ≥0∞ := (A : ℝ≥0∞) * ((A : ℝ≥0∞) * (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2))) with hC
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
          (rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (C * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
          ∑ δ : DerivativeWord2 ab.2, ∑ p ∈ Finset.range (A + r + 2), ∫⁻ X in slowCell ρ,
            FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X) :=
        Finset.sum_le_sum fun v _ => by
          gcongr
          exact hd.flux_word_component hj β v hM
    _ = C * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ δ : DerivativeWord2 ab.2,
          ∑ p ∈ Finset.range (A + r + 2), ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
            FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun v _ => by ring
    _ ≤ C * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ _δ : DerivativeWord2 ab.2,
          ∑ p ∈ Finset.range (A + r + 2),
            (ENNReal.ofReal (ρ⁻¹ ^ 2 * jetWeight n p) * s ^ 2 * G) := by
        gcongr with ab hab δ _ p hp
        have hab' := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
        have hp' := Finset.mem_range.1 hp
        exact hd.T_bound (by omega) (by have := hd.order; omega) (by omega) δ
    _ = _ := by
        rw [hC, flux_const_eq A j (A + r + 2) hd.ρ_pos (jetWeight n) (jetWeight_nonneg n) s G]
        rfl

omit [∀ i, CompleteSpace (h i)] in
/-- The mixed jets of the source of the chain are controlled by those of the initial source. -/
theorem rem_member (hd : DiffDegree π I A r n kres sZ c Fc ℓ ρ e rs τ s V)
    {a b : ℕ} (ha : a ≤ r) (hb : b ≤ r) (δ : DerivativeWord2 b) (v : ι) :
    ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
        FastJets.scalJetF (cleanupSource (fun j' X y k => V j' X y k v) A) (a + m) δ X
      ≤ 2 * ∑ p ∈ Finset.range (A + r + 3), ∫⁻ X in slowCell ρ,
        FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X := by
  have hch := hd.chain_component v
  have hF : IsBoxSmooth (A + 2 + r) sZ (fun (_ _ : Vec 2) (_ : Fin 2) => (0 : h v)) :=
    isBoxSmooth_zero _ _
  have hb1 : b + 1 ≤ sZ := by have := hd.hZ; omega
  have hA := hd.hA
  calc ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
        FastJets.scalJetF (cleanupSource (fun j' X y k => V j' X y k v) A) (a + m) δ X
      ≤ ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, 2 *
          FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v)
            (m + (a + A)) δ X := by
        refine Finset.sum_le_sum fun m hm => lintegral_mono fun X => ?_
        have hm3 := Finset.mem_range.1 hm
        calc FastJets.scalJetF (cleanupSource (fun j' X y k => V j' X y k v) A) (a + m) δ X
            ≤ 2 * ((2 * antidivConst) ^ (A - 1) *
                FastJets.vecJetF (fun X y k => V 0 X y k v) (a + m + A) δ X) :=
              FastJets.scalJetF_cleanupChain_remainder_le δ hb1 hA hF hch (m := a + m)
                (by omega) X
          _ ≤ 2 * (1 * FastJets.vecJetF (fun X y k => V 0 X y k v) (a + m + A) δ X) := by
              gcongr; exact pow_le_one₀ bot_le two_mul_antidivConst_le_one
          _ ≤ 2 * FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v)
                (m + (a + A)) δ X := by
              rw [one_mul]
              gcongr
              refine (FastJets.vecJetF_cleanupChain_zero_le δ hb1 hF hch (m := a + m + A)
                (by omega) X).trans ?_
              rw [vecJetF_zero, mul_zero, zero_add, show m + (a + A) = a + m + A by omega]
              calc 2 * (antidivConst * FastJets.scalJetF
                    (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) (a + m + A) δ X)
                  ≤ 1 * (FastJets.scalJetF
                    (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) (a + m + A) δ X) := by
                    rw [← mul_assoc]; gcongr; exact two_mul_antidivConst_le_one
                _ = _ := one_mul _
    _ = 2 * ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
          FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v)
            (m + (a + A)) δ X := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ =>
          lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num)
    _ ≤ _ := by
        gcongr
        exact sum_range_shift_le (fun p => ∫⁻ X in slowCell ρ,
          FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X)
          (by omega)

omit [∀ i, CompleteSpace (h i)] in
/-- Per component: the word derivative of the sampled cleanup source of one degree. -/
theorem rem_word_component (hd : DiffDegree π I A r n kres sZ c Fc ℓ ρ e rs τ s V) {j : ℕ}
    (hj : j ≤ r) (β : DerivativeWord2 j) (v : ι) {M : ℕ} (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube, ‖rs ^ j • orderedDerivative β (fun x' =>
        cleanupSource (fun j' X y k => V j' X y k v) A (ρ⁻¹ • x') (e⁻¹ • x')) x‖ₑ ^ 2
      ≤ 4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
        ∑ δ : DerivativeWord2 ab.2, (2 * ∑ p ∈ Finset.range (A + r + 3), ∫⁻ X in slowCell ρ,
          FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X) := by
  have hch := hd.chain_component v
  have hF : IsBoxSmooth (A + 2 + r) sZ (fun (_ _ : Vec 2) (_ : Fin 2) => (0 : h v)) :=
    isBoxSmooth_zero _ _
  have hA := hd.hA
  have hbox := IsCleanupChain.isBoxSmooth hF hch (A - 1) (by omega)
  have hW : IsBoxSmooth (j + 2) j (cleanupSource (fun j' X y k => V j' X y k v) A) :=
    (isBoxSmooth_cleanupSource (sX := A + 1 + r) (hV := by
      have : A + 1 + r + 1 = A + 2 + r := by omega
      rw [this]; exact hbox)).mono (by omega) (by have := hd.hZ; omega)
  have hper : ∀ X, AVenhance.IsZ2Periodic
      (cleanupSource (fun j' X y k => V j' X y k v) A X) :=
    fun X => cleanupSource_periodic (IsCleanupChain.periodic (fun X n y => rfl) hch (A - 1)
      (by omega)) X
  refine (FastJets.lintegral_rs_odL_diag_sq_le β hW hper hd.rs_pos hd.rs_le hd.e_le M hM).trans ?_
  gcongr with ab hab δ _
  have hab' := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  exact hd.rem_member (by omega) (by omega) δ v

omit [∀ i, CompleteSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)] in
theorem cleanupSource_comp (hd : DiffDegree π I A r n kres sZ c Fc ℓ ρ e rs τ s V) (v : ι) :
    cleanupSource (fun j' X y k => V j' X y k v) A =
      fun X y => cleanupSource V A X y v := by
  have hF : IsBoxSmooth (A + 2 + r) sZ (fun (_ _ : Vec 2) (_ : Fin 2) => (0 : ∀ i, h i)) :=
    isBoxSmooth_zero _ _
  have hbox := IsCleanupChain.isBoxSmooth hF hd.chain (A - 1) (by have := hd.hA; omega)
  exact cleanupSource_clm_comp (sX := A + 2 + r) (by omega) (V := V) (j := A)
    hbox.isSlowSmooth (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)

omit [∀ i, CompleteSpace (h i)] in
/-- The word derivative of the sampled cleanup source of one degree, with the mass weights. -/
theorem rem_word_bound (hd : DiffDegree π I A r n kres sZ c Fc ℓ ρ e rs τ s V) {j : ℕ}
    (hj : j ≤ r) (β : DerivativeWord2 j) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖rs ^ j • orderedDerivative β (fun x' => cleanupSource V A (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2
      ≤ ENNReal.ofReal (remWordConst n A r j) * s ^ 2 * fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) := by
  obtain ⟨M, hM⟩ := hd.e_inv
  set G := fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) with hG
  set C : ℝ≥0∞ := 4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) with hC
  have hcomp : ∀ v, (fun x' => cleanupSource V A (ρ⁻¹ • x') (e⁻¹ • x') v) =
      fun x' => cleanupSource (fun j' X y k => V j' X y k v) A (ρ⁻¹ • x') (e⁻¹ • x') := by
    intro v
    funext x'
    rw [hd.cleanupSource_comp v]
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖rs ^ j • orderedDerivative β (fun x' => cleanupSource V A (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (C * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
          ∑ δ : DerivativeWord2 ab.2, (2 * ∑ p ∈ Finset.range (A + r + 3), ∫⁻ X in slowCell ρ,
            FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X)) :=
        Finset.sum_le_sum fun v _ => by
          gcongr
          rw [hcomp v]
          exact hd.rem_word_component hj β v hM
    _ = C * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ δ : DerivativeWord2 ab.2,
          (2 * ∑ p ∈ Finset.range (A + r + 3), ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
            FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun v _ => ?_
        ring
    _ ≤ C * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ _δ : DerivativeWord2 ab.2,
          (2 * ∑ p ∈ Finset.range (A + r + 3),
            (ENNReal.ofReal (ρ⁻¹ ^ 2 * jetWeight n p) * s ^ 2 * G)) := by
        gcongr with ab hab δ _ p hp
        have hab' := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
        have hp' := Finset.mem_range.1 hp
        have hA := hd.hA
        exact hd.T_bound (by omega) (by have := hd.order; omega) (by omega) δ
    _ = _ := by
        rw [hC, rem_const_eq j (A + r + 3) hd.ρ_pos (jetWeight n) (jetWeight_nonneg n) s G]
        rfl

end DiffDegree
end

/-! Differentiated coarse flux: linearity of word derivatives for the sampled cleanup flux and
remainder, the coordinate evaluation, and the identity term. -/

section
section Word

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedDerivative_const_smul {j : ℕ} (β : DerivativeWord2 j) (c : ℝ) {g : Vec 2 → F}
    (hg : ContDiff ℝ (j : ℕ∞) g) :
    orderedDerivative β (fun x => c • g x) = fun x => c • orderedDerivative β g x := by
  have := orderedDerivative_clm_comp (c • ContinuousLinearMap.id ℝ F) β hg
  simpa using this

/-- Linearity of the word derivative on a combination `a + c ∑_n d_n ∑_i e_i H_{ni}`. -/
theorem orderedDerivative_combo {j : ℕ} (β : DerivativeWord2 j) (S T : Finset ℕ) (c : ℝ)
    (d e : ℕ → ℝ) {a : Vec 2 → F} {H : ℕ → ℕ → Vec 2 → F} (ha : ContDiff ℝ (j : ℕ∞) a)
    (hH : ∀ n ∈ S, ∀ i ∈ T, ContDiff ℝ (j : ℕ∞) (H n i)) :
    orderedDerivative β (fun x => a x + c • ∑ n ∈ S, d n • ∑ i ∈ T, e i • H n i x) =
      fun x => orderedDerivative β a x +
        c • ∑ n ∈ S, d n • ∑ i ∈ T, e i • orderedDerivative β (H n i) x := by
  have hi : ∀ n ∈ S, ContDiff ℝ (j : ℕ∞) (fun x => ∑ i ∈ T, e i • H n i x) := fun n hn =>
    ContDiff.sum fun i hi => (hH n hn i hi).const_smul (e i)
  have hn : ContDiff ℝ (j : ℕ∞) (fun x => ∑ n ∈ S, d n • ∑ i ∈ T, e i • H n i x) :=
    ContDiff.sum fun n hn' => (hi n hn').const_smul (d n)
  have e1 : ∀ n ∈ S, orderedDerivative β (fun x => d n • ∑ i ∈ T, e i • H n i x) =
      fun x => d n • ∑ i ∈ T, e i • orderedDerivative β (H n i) x := by
    intro n hn'
    rw [orderedDerivative_const_smul β (d n) (hi n hn')]
    funext x
    congr 1
    rw [MixedTail.orderedDerivative_sum T β (g := fun i x => e i • H n i x)
      (fun i hi' => (hH n hn' i hi').const_smul (e i))]
    refine Finset.sum_congr rfl fun i hi' => ?_
    rw [orderedDerivative_const_smul β (e i) (hH n hn' i hi')]
  have e2 : orderedDerivative β (fun x => ∑ n ∈ S, d n • ∑ i ∈ T, e i • H n i x) =
      fun x => ∑ n ∈ S, d n • ∑ i ∈ T, e i • orderedDerivative β (H n i) x := by
    rw [MixedTail.orderedDerivative_sum S β (g := fun n x => d n • ∑ i ∈ T, e i • H n i x)
      (fun n hn' => (hi n hn').const_smul (d n))]
    funext x
    exact Finset.sum_congr rfl fun n hn' => congrFun (e1 n hn') x
  rw [orderedDerivative_add β ha (hn.const_smul c), orderedDerivative_const_smul β c hn, e2]

/-- Linearity of the word derivative on `c ∑_n d_n H_n`. -/
theorem orderedDerivative_sum_smul {j : ℕ} (β : DerivativeWord2 j) (S : Finset ℕ) (c : ℝ)
    (d : ℕ → ℝ) {H : ℕ → Vec 2 → F} (hH : ∀ n ∈ S, ContDiff ℝ (j : ℕ∞) (H n)) :
    orderedDerivative β (fun x => c • ∑ n ∈ S, d n • H n x) =
      fun x => c • ∑ n ∈ S, d n • orderedDerivative β (H n) x := by
  have hn : ContDiff ℝ (j : ℕ∞) (fun x => ∑ n ∈ S, d n • H n x) :=
    ContDiff.sum fun n hn' => (hH n hn').const_smul (d n)
  rw [orderedDerivative_const_smul β c hn,
    MixedTail.orderedDerivative_sum S β (g := fun n x => d n • H n x)
      (fun n hn' => (hH n hn').const_smul (d n))]
  funext x
  congr 1
  exact Finset.sum_congr rfl fun n hn' => by
    rw [orderedDerivative_const_smul β (d n) (hH n hn')]

end Word

section Coord

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- Coordinates commute with word derivatives. -/
theorem orderedDerivative_apply {j : ℕ} (β : DerivativeWord2 j) {g : Vec 2 → ∀ i, h i}
    (hg : ContDiff ℝ (j : ℕ∞) g) (v : ι) (x : Vec 2) :
    orderedDerivative β g x v = orderedDerivative β (fun x' => g x' v) x :=
  (congrFun (orderedDerivative_clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) β hg) x).symm

end Coord

/-- A diagonal sample of a box smooth field is `C^j` as soon as `j` is below both orders. -/
theorem contDiff_sample {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {sX sZ j : ℕ}
    {W : Vec 2 → Vec 2 → E} (hW : IsBoxSmooth sX sZ W) (hX : j ≤ sX) (hZ : j ≤ sZ) (ρ e : ℝ) :
    ContDiff ℝ (j : ℕ∞) (fun x' : Vec 2 => W (ρ⁻¹ • x') (e⁻¹ • x')) :=
  (hW.contDiff_uncurry hX hZ).comp ((contDiff_const_smul _).prodMk (contDiff_const_smul _))

/-- The identity term: a word derivative of the coarse flux in terms of the factorial norm. -/
theorem lintegral_rs_word_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ρ rs : ℝ}
    (hrs : 0 < rs) (hρ : rs ≤ ρ) {j m : ℕ} (hjm : j ≤ m) (β : DerivativeWord2 j) (g : Vec 2 → F) :
    ∫⁻ x in AVenhance.unitCube, ‖rs ^ j • orderedDerivative β g x‖ₑ ^ 2 ≤
      ENNReal.ofReal (((j.factorial : ℝ)) ^ 2) * classicalFactorialSq ρ m g := by
  have hρ0 : 0 < ρ := hrs.trans_le hρ
  have hfac : (0 : ℝ) < ((j.factorial : ℝ)) ^ 2 := by positivity
  have hpt : ∀ x, ‖rs ^ j • orderedDerivative β g x‖ₑ ^ 2 =
      ENNReal.ofReal ((rs ^ j) ^ 2) * ‖orderedDerivative β g x‖ₑ ^ 2 := by
    intro x
    rw [enorm_smul, mul_pow, Real.enorm_eq_ofReal (by positivity), ← ENNReal.ofReal_pow (by positivity)]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hterm : ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
      ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative β g x‖ₑ ^ 2 ≤ classicalFactorialSq ρ m g := by
    unfold classicalFactorialSq
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => ENNReal.ofReal (ρ ^ (2 * j) /
      ((j.factorial : ℝ)) ^ 2) * ∑ w : DerivativeWord2 j,
        ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2) (fun _ _ => bot_le)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hjm)))
    gcongr
    exact Finset.single_le_sum (f := fun w : DerivativeWord2 j =>
      ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2) (fun _ _ => bot_le)
      (Finset.mem_univ β)
  have hc : (rs ^ j) ^ 2 ≤ ((j.factorial : ℝ)) ^ 2 * (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) := by
    have h1 : (rs ^ j) ^ 2 ≤ (ρ ^ j) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hrs.le hρ j) 2
    calc (rs ^ j) ^ 2 ≤ (ρ ^ j) ^ 2 := h1
      _ = ((j.factorial : ℝ)) ^ 2 * (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) := by
        rw [← pow_mul, mul_comm j 2]; field_simp
  calc ENNReal.ofReal ((rs ^ j) ^ 2) * ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative β g x‖ₑ ^ 2
      ≤ ENNReal.ofReal (((j.factorial : ℝ)) ^ 2 * (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2)) *
          ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative β g x‖ₑ ^ 2 := by
        gcongr
    _ = ENNReal.ofReal (((j.factorial : ℝ)) ^ 2) * (ENNReal.ofReal (ρ ^ (2 * j) /
          ((j.factorial : ℝ)) ^ 2) * ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative β g x‖ₑ ^ 2) := by
        rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ ≤ _ := by gcongr
end

/-! Differentiated coarse flux: the cell-time data of all degrees, and the pointwise-in-time
bounds of the word derivative of the flux residual density. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The degree data at one cell time for every degree `1 ≤ n ≤ N`. -/
structure DiffTime (π : ι → ℝ) (I : Set ℝ) (A r N kres sZ : ℕ) (c : ℕ → LiftCoeff ι h)
    (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (ℓ ρ e rs εc τ : ℝ) (s : ℝ≥0∞)
    (V : ℕ → ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) : Prop where
  deg : ∀ n ∈ Finset.Icc 1 N, DiffDegree π I A r n kres sZ (c n) Fc ℓ ρ e rs τ s (V n)
  ε_nonneg : 0 ≤ εc
  ε_le : εc ≤ 1
  smooth : ∀ k, ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * τ) x k)
  order : r ≤ kres

/-- The flux of the residual (vector valued). -/
def fluxVec (hh : ℕ) (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (ℓ ρ e εc : ℝ) (A N : ℕ)
    (Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) (k : Fin 2) :
    ∀ i, h i :=
  (if hh = 0 then Fc t x k else 0) + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
    εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x k

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem fluxVec_eval (hh : ℕ) (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (ℓ ρ e εc t τ : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) (Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) (A N : ℕ)
    (x : Vec 2) (k : Fin 2) (v : ι) :
    fluxVec hh Fc ℓ ρ e εc A N Vn t x k v =
      (if hh = 0 then Fc t x k v else 0) + (ρ⁻¹ * e) • ∑ n ∈ Finset.Icc 1 N, εc ^ n •
        ∑ j ∈ Finset.range A, (e / ρ) ^ j • Vn n j τ (ρ⁻¹ • x) (e⁻¹ • x) k v := by
  have : ∀ n, cleanupFlux (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x k v =
      e • ∑ j ∈ Finset.range A, (e / ρ) ^ j • Vn n j τ (ρ⁻¹ • x) (e⁻¹ • x) k v := by
    intro n
    simp only [cleanupFlux, diagSample, hτt, Pi.smul_apply, Finset.sum_apply]
  simp only [fluxVec, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, this]
  congr 1
  · split_ifs <;> simp
  · rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [smul_smul]
    congr 1
    ring

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem contDiff_fluxVec {π : ι → ℝ} {I : Set ℝ} {A r N kres sZ : ℕ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e rs εc τ : ℝ} {s : ℝ≥0∞}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : DiffTime π I A r N kres sZ c Fc ℓ ρ e rs εc τ s (fun n j => Vn n j τ)) (hh : ℕ) (t : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) (hℓτ : ℓ ^ 2 * τ = t) {j : ℕ} (hj : j ≤ r) (k : Fin 2) :
    ContDiff ℝ (j : ℕ∞) (fun x => fluxVec hh Fc ℓ ρ e εc A N Vn t x k) := by
  unfold fluxVec
  have hFc : ContDiff ℝ (j : ℕ∞) (fun x => Fc t x k) := by
    have := (hT.smooth k).of_le (show (j : WithTop ℕ∞) ≤ ((kres + 1 : ℕ) : ℕ∞) by
      exact_mod_cast (by have := hT.order; omega))
    rwa [hℓτ] at this
  refine (?_ : ContDiff ℝ (j : ℕ∞) (fun x => if hh = 0 then Fc t x k else 0)).add ?_
  · split_ifs
    · exact hFc
    · exact contDiff_const
  · refine ContDiff.const_smul _ (ContDiff.sum fun n hn => ContDiff.const_smul _ ?_)
    have hd := hT.deg n hn
    have hF : IsBoxSmooth (A + 2 + r) sZ (fun (_ _ : Vec 2) (_ : Fin 2) => (0 : ∀ i, h i)) :=
      isBoxSmooth_zero _ _
    have hbox := IsCleanupChain.isBoxSmooth hF hd.chain
    unfold cleanupFlux
    refine ContDiff.const_smul _ (ContDiff.sum fun j' hj' => ContDiff.const_smul _ ?_)
    have hb : IsBoxSmooth (A + 2 + r) sZ (fun X y => Vn n j' τ X y k) :=
      (hbox j' (Finset.mem_range.1 hj')).clm_comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ∀ i, h i) k)
    have := contDiff_sample hb (j := j) (by omega) (by have := hd.hZ; omega) ρ e
    have e : diagSample (ℓ ^ 2)⁻¹ ρ e (fun τ' X z => Vn n j' τ' X z k) t =
        fun x => Vn n j' τ (ρ⁻¹ • x) (e⁻¹ • x) k := by
      funext x; simp [diagSample, hτt]
    rw [e]; exact this

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
/-- The coordinate of the weighted word derivative of the flux residual. -/
theorem fluxVec_word_coord {π : ι → ℝ} {I : Set ℝ} {A r N kres sZ : ℕ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e rs εc τ : ℝ} {s : ℝ≥0∞}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : DiffTime π I A r N kres sZ c Fc ℓ ρ e rs εc τ s (fun n j => Vn n j τ)) (hh : ℕ) (t : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) (hℓτ : ℓ ^ 2 * τ = t) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j)
    (k : Fin 2) (v : ι) (x : Vec 2) :
    (rs ^ j • orderedDerivative β (fun x' => fluxVec hh Fc ℓ ρ e εc A N Vn t x' k) x) v =
      (if hh = 0 then rs ^ j • orderedDerivative β (fun x' => Fc t x' k v) x else 0) +
        (ρ⁻¹ * e) • ∑ n ∈ Finset.Icc 1 N, εc ^ n • ∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
          (rs ^ j • orderedDerivative β (fun x' => Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v) x) := by
  have hG := contDiff_fluxVec hT hh t hτt hℓτ hj k
  have hFc : ContDiff ℝ (j : ℕ∞) (fun x => Fc t x k v) := by
    have := (hT.smooth k).of_le (show (j : WithTop ℕ∞) ≤ ((kres + 1 : ℕ) : ℕ∞) by
      exact_mod_cast (by have := hT.order; omega))
    rw [hℓτ] at this
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).contDiff.comp this
  have ha : ContDiff ℝ (j : ℕ∞) (fun x => if hh = 0 then Fc t x k v else 0) := by
    split_ifs
    · exact hFc
    · exact contDiff_const
  have hH : ∀ n ∈ Finset.Icc 1 N, ∀ j' ∈ Finset.range A, ContDiff ℝ (j : ℕ∞)
      (fun x' => Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v) := by
    intro n hn j' hj'
    have hd := hT.deg n hn
    have hF : IsBoxSmooth (A + 2 + r) sZ (fun (_ _ : Vec 2) (_ : Fin 2) => (0 : ∀ i, h i)) :=
      isBoxSmooth_zero _ _
    have hbox := IsCleanupChain.isBoxSmooth hF hd.chain j' (Finset.mem_range.1 hj')
    have hb : IsBoxSmooth (A + 2 + r) sZ (fun X y => Vn n j' τ X y k v) :=
      hbox.clm_comp ((ContinuousLinearMap.proj (R := ℝ) (φ := h) v).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ∀ i, h i) k))
    exact contDiff_sample hb (j := j) (by omega) (by have := hd.hZ; omega) ρ e
  rw [Pi.smul_apply, orderedDerivative_apply β hG v x]
  have hfun : (fun x' => fluxVec hh Fc ℓ ρ e εc A N Vn t x' k v) = fun x' =>
      (if hh = 0 then Fc t x' k v else 0) + (ρ⁻¹ * e) • ∑ n ∈ Finset.Icc 1 N, εc ^ n •
        ∑ j' ∈ Finset.range A, (e / ρ) ^ j' • Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v :=
    funext fun x' => fluxVec_eval hh Fc ℓ ρ e εc t τ hτt Vn A N x' k v
  rw [hfun, orderedDerivative_combo β (Finset.Icc 1 N) (Finset.range A) (ρ⁻¹ * e)
    (fun n => εc ^ n) (fun j' => (e / ρ) ^ j') ha hH]
  simp only [smul_add, Finset.smul_sum]
  congr 1
  · split_ifs
    · rfl
    · simp [orderedDerivative_const_zero]
  · refine Finset.sum_congr rfl fun n _ => ?_
    simp only [smul_comm (rs ^ j)]
end

/-! Differentiated coarse flux: the pointwise-in-time bound of the word derivative of the flux
residual density by the flux density of the coarse flux. -/

section
theorem ite_enorm_sq {E : Type*} [NormedAddCommGroup E] (p : Prop) [Decidable p] (a : E) :
    ‖(if p then a else 0)‖ₑ ^ 2 = if p then ‖a‖ₑ ^ 2 else 0 := by
  split_ifs <;> simp

theorem lintegral_bound_split (P : Prop) [Decidable P] (S : Finset ℕ) (a : Vec 2 → ℝ≥0∞)
    (ha : Measurable a) (w : ℕ → ℝ≥0∞) (b : ℕ → Vec 2 → ℝ≥0∞) (hb : ∀ n ∈ S, Measurable (b n))
    (U : Vec 2 → ℝ≥0∞)
    (hU : ∀ x, U x ≤ 2 * (if P then a x else 0) + ∑ n ∈ S, w n * b n x) :
    ∫⁻ x in AVenhance.unitCube, U x ≤
      2 * (if P then ∫⁻ x in AVenhance.unitCube, a x else 0) +
        ∑ n ∈ S, w n * ∫⁻ x in AVenhance.unitCube, b n x := by
  have hm1 : Measurable fun x => 2 * (if P then a x else 0) := by
    by_cases hP : P
    · simp only [hP, ite_true]; exact ha.const_mul _
    · simp only [hP, ite_false]; exact measurable_const
  calc ∫⁻ x in AVenhance.unitCube, U x
      ≤ ∫⁻ x in AVenhance.unitCube, (2 * (if P then a x else 0) + ∑ n ∈ S, w n * b n x) :=
        lintegral_mono hU
    _ = (∫⁻ x in AVenhance.unitCube, 2 * (if P then a x else 0)) +
          ∫⁻ x in AVenhance.unitCube, ∑ n ∈ S, w n * b n x := lintegral_add_left hm1 _
    _ = _ := by
        congr 1
        · rw [lintegral_const_mul' _ _ (by simp)]
          congr 1
          by_cases hP : P <;> simp [hP]
        · rw [lintegral_finsetSum _ fun n hn => (hb n hn).const_mul _]
          exact Finset.sum_congr rfl fun n hn => lintegral_const_mul _ (hb n hn)

section Flux

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, CompleteSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem flux_pointwise {π : ι → ℝ} {I : Set ℝ} {A r N kres sZ : ℕ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e rs εc τ : ℝ} {s : ℝ≥0∞}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : DiffTime π I A r N kres sZ c Fc ℓ ρ e rs εc τ s (fun n j => Vn n j τ)) (hh : ℕ) (t : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) (hℓτ : ℓ ^ 2 * τ = t) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j)
    (v : ι) (x : Vec 2) :
    ∑ k : Fin 2, ‖(rs ^ j • orderedDerivative β
        (fun x' => fluxVec hh Fc ℓ ρ e εc A N Vn t x' k) x) v‖ₑ ^ 2 ≤
      2 * (if hh = 0 then ∑ k : Fin 2, ‖rs ^ j • orderedDerivative β (fun x' => Fc t x' k v) x‖ₑ ^ 2
        else 0) +
        ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * (εc ^ n) ^ 2) *
          ∑ k : Fin 2, ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
            (rs ^ j • orderedDerivative β (fun x' => Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2 := by
  classical
  have hcard : ((Finset.Icc 1 N).card : ℝ) = N := by simp
  calc ∑ k : Fin 2, ‖(rs ^ j • orderedDerivative β
        (fun x' => fluxVec hh Fc ℓ ρ e εc A N Vn t x' k) x) v‖ₑ ^ 2
      = ∑ k : Fin 2, ‖(if hh = 0 then rs ^ j • orderedDerivative β
            (fun x' => Fc t x' k v) x else 0) + (ρ⁻¹ * e) • ∑ n ∈ Finset.Icc 1 N, εc ^ n •
          ∑ j' ∈ Finset.range A, (e / ρ) ^ j' • (rs ^ j • orderedDerivative β
            (fun x' => Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [fluxVec_word_coord hT hh t hτt hℓτ hj β k v x]
    _ ≤ ∑ k : Fin 2, (2 * ‖(if hh = 0 then rs ^ j • orderedDerivative β
            (fun x' => Fc t x' k v) x else 0)‖ₑ ^ 2 +
          ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (2 * ((Finset.Icc 1 N).card : ℝ) *
            (ρ⁻¹ * e) ^ 2 * (εc ^ n) ^ 2) * ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
              (rs ^ j • orderedDerivative β
                (fun x' => Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2) :=
        Finset.sum_le_sum fun k _ => enorm_sq_add_sum_smul_le (Finset.Icc 1 N) _ (ρ⁻¹ * e)
          (fun n => εc ^ n) (fun n => ∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
            (rs ^ j • orderedDerivative β (fun x' => Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v) x))
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcard, Finset.sum_comm]
        congr 1
        · simp only [ite_enorm_sq]
          split_ifs <;> simp
        · refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem continuous_word_sample {A r N kres sZ : ℕ} {π : ι → ℝ} {I : Set ℝ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e rs εc τ : ℝ} {s : ℝ≥0∞}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : DiffTime π I A r N kres sZ c Fc ℓ ρ e rs εc τ s (fun n j => Vn n j τ)) {j : ℕ}
    (hj : j ≤ r) (β : DerivativeWord2 j) {n : ℕ} (hn : n ∈ Finset.Icc 1 N) {j' : ℕ} (hj' : j' < A)
    (k : Fin 2) (v : ι) :
    Continuous fun x => rs ^ j • orderedDerivative β
      (fun x' => Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v) x := by
  have hd := hT.deg n hn
  have hF : IsBoxSmooth (A + 2 + r) sZ (fun (_ _ : Vec 2) (_ : Fin 2) => (0 : ∀ i, h i)) :=
    isBoxSmooth_zero _ _
  have hbox := IsCleanupChain.isBoxSmooth hF hd.chain j' hj'
  have hb : IsBoxSmooth (A + 2 + r) sZ (fun X y => Vn n j' τ X y k v) :=
    hbox.clm_comp ((ContinuousLinearMap.proj (R := ℝ) (φ := h) v).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ∀ i, h i) k))
  have hH := contDiff_sample hb (j := j) (by omega) (by have := hd.hZ; omega) ρ e
  exact continuous_const.smul (contDiff_orderedDerivative (p := 0) β (by simpa using hH)).continuous

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem continuous_word_coarse {A r N kres sZ : ℕ} {π : ι → ℝ} {I : Set ℝ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e rs εc τ : ℝ} {s : ℝ≥0∞}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : DiffTime π I A r N kres sZ c Fc ℓ ρ e rs εc τ s (fun n j => Vn n j τ)) (t : ℝ)
    (hℓτ : ℓ ^ 2 * τ = t) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) (k : Fin 2) (v : ι) :
    Continuous fun x => rs ^ j • orderedDerivative β (fun x' => Fc t x' k v) x := by
  have := (hT.smooth k).of_le (show (j : WithTop ℕ∞) ≤ ((kres + 1 : ℕ) : ℕ∞) by
    exact_mod_cast (by have := hT.order; omega))
  rw [hℓτ] at this
  have hc : ContDiff ℝ (j : ℕ∞) (fun x => Fc t x k v) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).contDiff.comp this
  exact continuous_const.smul (contDiff_orderedDerivative (p := 0) β (by simpa using hc)).continuous

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
/-- Per component, integrated. -/
theorem flux_integrated {π : ι → ℝ} {I : Set ℝ} {A r N kres sZ : ℕ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e rs εc τ : ℝ} {s : ℝ≥0∞}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : DiffTime π I A r N kres sZ c Fc ℓ ρ e rs εc τ s (fun n j => Vn n j τ)) (hh : ℕ) (t : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) (hℓτ : ℓ ^ 2 * τ = t) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j)
    (hρ : rs ≤ ρ) (hrs : 0 < rs) (v : ι) :
    ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖(rs ^ j • orderedDerivative β
        (fun x' => fluxVec hh Fc ℓ ρ e εc A N Vn t x' k) x) v‖ₑ ^ 2 ≤
      2 * (if hh = 0 then ENNReal.ofReal (((j.factorial : ℝ)) ^ 2) * ∑ k : Fin 2,
          classicalFactorialSq ρ kres (fun x => Fc t x k v) else 0) +
        ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * (εc ^ n) ^ 2) *
          ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
            (rs ^ j • orderedDerivative β
              (fun x' => Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2 := by
  classical
  have hFc : ∀ k, Measurable fun x => ‖rs ^ j • orderedDerivative β (fun x' => Fc t x' k v) x‖ₑ ^ 2 :=
    fun k => ((continuous_word_coarse hT t hℓτ hj β k v).enorm.measurable).pow_const 2
  have hb : ∀ n ∈ Finset.Icc 1 N, Measurable fun x : Vec 2 => ∑ k : Fin 2,
      ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' • (rs ^ j • orderedDerivative β
        (fun x' => Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2 := by
    intro n hn
    refine Finset.measurable_sum _ fun k _ => ?_
    refine (Continuous.enorm ?_).measurable.pow_const 2
    exact continuous_finsetSum _ fun j' hj' =>
      continuous_const.smul (continuous_word_sample hT hj β hn (Finset.mem_range.1 hj') k v)
  refine (lintegral_bound_split (hh = 0) (Finset.Icc 1 N)
    (fun x => ∑ k : Fin 2, ‖rs ^ j • orderedDerivative β (fun x' => Fc t x' k v) x‖ₑ ^ 2)
    (Finset.measurable_sum _ fun k _ => hFc k)
    (fun n => ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * (εc ^ n) ^ 2))
    (fun n x => ∑ k : Fin 2, ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
      (rs ^ j • orderedDerivative β (fun x' => Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2) hb _
    (fun x => flux_pointwise hT hh t hτt hℓτ hj β v x)).trans ?_
  gcongr
  split_ifs
  · rw [lintegral_finsetSum _ fun k _ => hFc k, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => lintegral_rs_word_le hrs hρ (by have := hT.order; omega) β _
  · exact le_rfl

omit [∀ i, CompleteSpace (h i)] in
/-- The pointwise-in-time bound of the word derivative of the flux residual density. -/
theorem flux_time_bound {π : ι → ℝ} {I : Set ℝ} {A r N kres sZ : ℕ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e rs εc τ : ℝ} {s : ℝ≥0∞}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : DiffTime π I A r N kres sZ c Fc ℓ ρ e rs εc τ s (fun n j => Vn n j τ)) (hh : ℕ) (t : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) (hℓτ : ℓ ^ 2 * τ = t) (θ : ℝ) (hs : s = ENNReal.ofReal θ)
    (hθ : 0 ≤ θ) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) (hrs : 0 < rs) (hrsρ : rs ≤ ρ) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖(rs ^ j • orderedDerivative β (fun x' => fluxVec hh Fc ℓ ρ e εc A N Vn t x' k) x) v‖ₑ ^ 2
      ≤ ENNReal.ofReal ((if hh = 0 then 2 * ((j.factorial : ℝ)) ^ 2 else 0) +
          2 * N * (e / ρ) ^ 2 * εc ^ 2 * θ ^ 2 * ∑ n ∈ Finset.Icc 1 N, fluxWordConst n A r j) *
        fluxDensity ρ kres π Fc t := by
  classical
  set G : ℝ≥0∞ := fluxDensity ρ kres π Fc t with hG
  set ind : ℝ≥0∞ := if hh = 0 then 1 else 0 with hind
  have hite : ∀ X : ℝ≥0∞, (if hh = 0 then X else 0) = ind * X := fun X => by
    simp only [hind]; split_ifs <;> simp
  have hdeg : ∀ n ∈ Finset.Icc 1 N, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
      ∑ k : Fin 2, ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
        (rs ^ j • orderedDerivative β
          (fun x' => Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2
      ≤ ENNReal.ofReal (fluxWordConst n A r j) * ENNReal.ofReal (θ ^ 2) * G := by
    intro n hn
    have := (hT.deg n hn).flux_word_bound hj β
    rw [hs, ← ENNReal.ofReal_pow hθ, hℓτ] at this
    exact this
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖(rs ^ j • orderedDerivative β (fun x' => fluxVec hh Fc ℓ ρ e εc A N Vn t x' k) x) v‖ₑ ^ 2
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (2 * (ind * (ENNReal.ofReal (((j.factorial : ℝ)) ^ 2) *
          ∑ k : Fin 2, classicalFactorialSq ρ kres (fun x => Fc t x k v))) +
          ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * (εc ^ n) ^ 2) *
            ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
              (rs ^ j • orderedDerivative β
                (fun x' => Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2) := by
        refine Finset.sum_le_sum fun v _ => ?_
        gcongr
        exact (flux_integrated hT hh t hτt hℓτ hj β hrsρ hrs v).trans_eq (by rw [hite])
    _ = 2 * (ENNReal.ofReal (((j.factorial : ℝ)) ^ 2) * (ind * G)) + ∑ n ∈ Finset.Icc 1 N,
          ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * (εc ^ n) ^ 2) *
          ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
            ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' • (rs ^ j • orderedDerivative β
              (fun x' => Vn n j' τ (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2 := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · simp only [hG, fluxDensity, Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          ring_nf
        · simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun v _ => by ring
    _ ≤ 2 * (ENNReal.ofReal (((j.factorial : ℝ)) ^ 2) * (ind * G)) + ∑ n ∈ Finset.Icc 1 N,
          ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * εc ^ 2) *
          (ENNReal.ofReal (fluxWordConst n A r j) * ENNReal.ofReal (θ ^ 2) * G) := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun n hn => ?_)
        have hn1 : n ≠ 0 := by have := (Finset.mem_Icc.1 hn).1; omega
        have h1 : εc ^ n ≤ εc := pow_le_of_le_one hT.ε_nonneg hT.ε_le hn1
        have h2 : (εc ^ n) ^ 2 ≤ εc ^ 2 := pow_le_pow_left₀ (pow_nonneg hT.ε_nonneg n) h1 2
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left h2 (by positivity))) (hdeg n hn)
    _ = _ := by
        have hnn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, fluxWordConst n A r j :=
          Finset.sum_nonneg fun n _ => fluxWordConst_nonneg n A r j
        have hK : ENNReal.ofReal ((if hh = 0 then 2 * ((j.factorial : ℝ)) ^ 2 else 0) +
            2 * N * (e / ρ) ^ 2 * εc ^ 2 * θ ^ 2 * ∑ n ∈ Finset.Icc 1 N, fluxWordConst n A r j) =
            2 * (ENNReal.ofReal (((j.factorial : ℝ)) ^ 2) * ind) + ∑ n ∈ Finset.Icc 1 N,
              ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * εc ^ 2) *
                (ENNReal.ofReal (fluxWordConst n A r j) * ENNReal.ofReal (θ ^ 2)) := by
          rw [ENNReal.ofReal_add (by split_ifs <;> positivity) (by positivity)]
          congr 1
          · simp only [hind]; split_ifs
            · rw [ENNReal.ofReal_mul (by norm_num)]; simp
            · simp
          · rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun n _ =>
              mul_nonneg (by positivity) (fluxWordConst_nonneg n A r j)]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [← ENNReal.ofReal_mul (fluxWordConst_nonneg n A r j),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [div_eq_inv_mul]; ring
        rw [hK, add_mul, Finset.sum_mul]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun n _ => by ring

end Flux
end

end AVRegularity.CoarseFluxDiff
end
