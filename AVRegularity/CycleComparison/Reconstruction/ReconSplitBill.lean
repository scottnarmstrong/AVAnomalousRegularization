-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.ApproxJets
public import AVRegularity.CycleComparison.Reconstruction.PulseIdentity
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Jets of the classical defect field**.
The classical defect field `g₁(a) = -𝐛·∇a + div Ξ(a)`, `Ξ = ∑_{r ≤ H} F^{[r]} a`
(`classicalDefectField`, `classicalTotalFlux`), is a linear differential expression of order `D`
in the coarse field `a` with coefficients `𝐛`, `𝖩`, `A_d`, `C^{[r]}_{vu,d}`.

* `JetBoundedBy P f A`: `f` is of class `C^P` and its jets of order at most `P` are bounded by
  `A`. The predicate is stable under sums, products by scalar fields (Leibniz rule), continuous
  linear maps, applications of operator fields, coordinate derivatives and word derivatives.
* `classicalDefectField_jetBounded`: if the jets of order `≤ P + D` of `a(s)` are bounded by `A`,
  those of order `≤ P` of `𝐛(s)` and of order `≤ P + 1` of `A_d(s)`, `C^{[r]}(s)` by `Cco`, and
  `|𝖩(s)| ≤ Cco`, then the jets of order `≤ P` of `g₁(a)(s)` are bounded by `c Cco A`, with a
  constant `c = defectJetConst P D H` depending only on `P, D, H` and the fibers.
* `classicalDefectField_sub`: `g₁` is linear, `g₁(a) - g₁(a') = g₁(a - a')`.
* `exists_coeff_jetBounded`: periodic coefficients of finite smoothness have bounded jets. -/

/-! ### Fields with bounded jets -/

section Generic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `f` is of class `C^P` and its jets of order at most `P` are bounded by `A` everywhere. -/
def JetBoundedBy (P : ℕ) (f : Vec 2 → F) (A : ℝ) : Prop :=
  ContDiff ℝ (P : ℕ∞) f ∧ ∀ i ≤ P, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ A

theorem JetBoundedBy.nonneg {P : ℕ} {f : Vec 2 → F} {A : ℝ} (hf : JetBoundedBy P f A) :
    0 ≤ A :=
  (norm_nonneg _).trans (hf.2 0 (Nat.zero_le P) 0)

theorem JetBoundedBy.mono {P P' : ℕ} {f : Vec 2 → F} {A A' : ℝ} (hf : JetBoundedBy P f A)
    (hP : P' ≤ P) (hA : A ≤ A') : JetBoundedBy P' f A' :=
  ⟨hf.1.of_le (by exact_mod_cast hP), fun i hi x => (hf.2 i (hi.trans hP) x).trans hA⟩

theorem JetBoundedBy.add {P : ℕ} {f g : Vec 2 → F} {A B : ℝ} (hf : JetBoundedBy P f A)
    (hg : JetBoundedBy P g B) : JetBoundedBy P (fun x => f x + g x) (A + B) := by
  refine ⟨hf.1.add hg.1, fun i hi x => ?_⟩
  have hfi : ContDiff ℝ (i : ℕ∞) f := hf.1.of_le (by exact_mod_cast hi)
  have hgi : ContDiff ℝ (i : ℕ∞) g := hg.1.of_le (by exact_mod_cast hi)
  have e : iteratedFDeriv ℝ i (fun x => f x + g x) x =
      iteratedFDeriv ℝ i f x + iteratedFDeriv ℝ i g x :=
    iteratedFDeriv_add_apply hfi.contDiffAt hgi.contDiffAt
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (hf.2 i hi x) (hg.2 i hi x))

theorem JetBoundedBy.sub {P : ℕ} {f g : Vec 2 → F} {A B : ℝ} (hf : JetBoundedBy P f A)
    (hg : JetBoundedBy P g B) : JetBoundedBy P (fun x => f x - g x) (A + B) := by
  refine ⟨hf.1.sub hg.1, fun i hi x => ?_⟩
  have hfi : ContDiff ℝ (i : ℕ∞) f := hf.1.of_le (by exact_mod_cast hi)
  have hgi : ContDiff ℝ (i : ℕ∞) g := hg.1.of_le (by exact_mod_cast hi)
  have e : iteratedFDeriv ℝ i (fun x => f x - g x) x =
      iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i g x :=
    iteratedFDeriv_sub_apply hfi.contDiffAt hgi.contDiffAt
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add (hf.2 i hi x) (hg.2 i hi x))

theorem JetBoundedBy.neg {P : ℕ} {g : Vec 2 → F} {B : ℝ} (hg : JetBoundedBy P g B) :
    JetBoundedBy P (fun x => -g x) B := by
  refine ⟨hg.1.neg, fun i hi x => ?_⟩
  have e : iteratedFDeriv ℝ i (fun x => -g x) x = -iteratedFDeriv ℝ i g x :=
    iteratedFDeriv_neg_apply (f := g)
  rw [e, norm_neg]
  exact hg.2 i hi x

theorem JetBoundedBy.const_smul {P : ℕ} {g : Vec 2 → F} {B : ℝ} (r : ℝ)
    (hg : JetBoundedBy P g B) : JetBoundedBy P (fun x => r • g x) (|r| * B) := by
  refine ⟨hg.1.const_smul r, fun i hi x => ?_⟩
  have hgi : ContDiff ℝ (i : ℕ∞) g := hg.1.of_le (by exact_mod_cast hi)
  rw [iteratedFDeriv_const_smul_apply' hgi.contDiffAt, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hg.2 i hi x) (abs_nonneg r)

/-- **Leibniz rule** for a scalar field times a vector field. -/
theorem JetBoundedBy.smul {P : ℕ} {c : Vec 2 → ℝ} {g : Vec 2 → F} {A B : ℝ}
    (hc : JetBoundedBy P c A) (hg : JetBoundedBy P g B) :
    JetBoundedBy P (fun x => c x • g x) (2 ^ P * A * B) := by
  have hA : 0 ≤ A := hc.nonneg
  have hB : 0 ≤ B := hg.nonneg
  refine ⟨hc.1.smul hg.1, fun i hi x => ?_⟩
  refine (norm_iteratedFDeriv_smul_le hc.1 hg.1 x (by exact_mod_cast hi)).trans ?_
  have hsum : (∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * A * B) = 2 ^ i * A * B := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hn : (∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ)) = 2 ^ i := by
      exact_mod_cast Nat.sum_range_choose i
    rw [hn]
  calc _ ≤ ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * A * B :=
        Finset.sum_le_sum fun k hk => by
          have hki : k ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hc.2 k (hki.trans hi) x)
            (Nat.cast_nonneg _)) (hg.2 (i - k) ((Nat.sub_le i k).trans hi) x) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = 2 ^ i * A * B := hsum
    _ ≤ 2 ^ P * A * B := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hi) hA) hB

/-- **Leibniz rule** for an operator field applied to a vector field. -/
theorem JetBoundedBy.clm_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {P : ℕ}
    {L : Vec 2 → F →L[ℝ] G} {g : Vec 2 → F} {A B : ℝ} (hL : JetBoundedBy P L A)
    (hg : JetBoundedBy P g B) : JetBoundedBy P (fun x => L x (g x)) (2 ^ P * A * B) := by
  refine ⟨hL.1.clm_apply hg.1, fun i hi x => ?_⟩
  refine (norm_iteratedFDeriv_clm_apply_le_two_pow hL.1 hg.1 hi x
    (fun p hp => hL.2 p (hp.trans hi) x) (fun p hp => hg.2 p (hp.trans hi) x)).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) hi) hL.nonneg) hg.nonneg

/-- A fixed continuous linear map applied to a field. -/
theorem JetBoundedBy.clm_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : F →L[ℝ] G) {P : ℕ} {f : Vec 2 → F} {A : ℝ} (hf : JetBoundedBy P f A) :
    JetBoundedBy P (fun x => T (f x)) (‖T‖ * A) := by
  refine ⟨T.contDiff.comp hf.1, fun i hi x => ?_⟩
  have hfi : ContDiff ℝ (i : ℕ∞) f := hf.1.of_le (by exact_mod_cast hi)
  exact (T.norm_iteratedFDeriv_comp_left hfi.contDiffAt le_rfl).trans
    (mul_le_mul_of_nonneg_left (hf.2 i hi x) (norm_nonneg T))

/-- The jets of a word derivative of order `q` are jets of order `+ q` of the field. -/
theorem JetBoundedBy.word {P q : ℕ} (α : DerivativeWord2 q) {f : Vec 2 → F} {A : ℝ}
    (hf : JetBoundedBy (P + q) f A) : JetBoundedBy P (orderedDerivative α f) A := by
  refine ⟨AVRegularity.contDiff_orderedDerivative α hf.1, fun i hi x => ?_⟩
  have hfi : ContDiff ℝ ((i + q : ℕ) : ℕ∞) f :=
    hf.1.of_le (by exact_mod_cast (by omega : i + q ≤ P + q))
  exact (AVRegularity.norm_iteratedFDeriv_orderedDerivative_le α hfi x).trans
    (hf.2 (i + q) (by omega) x)

/-- A coordinate derivative. -/
theorem JetBoundedBy.fderiv_basis {P : ℕ} (l : Fin 2) {f : Vec 2 → F} {A : ℝ}
    (hf : JetBoundedBy (P + 1) f A) :
    JetBoundedBy P (fun x => fderiv ℝ f x (basisVec l)) A := by
  have e : (fun x => fderiv ℝ f x (basisVec l)) = orderedDerivative (fun _ : Fin 1 => l) f :=
    (orderedDerivative_one_eq_fderiv (fun _ : Fin 1 => l) f).symm
  rw [e]
  exact hf.word (fun _ : Fin 1 => l)

theorem JetBoundedBy.sum {κ : Type*} (s : Finset κ) {P : ℕ} {f : κ → Vec 2 → F}
    {A : κ → ℝ} (hf : ∀ k ∈ s, JetBoundedBy P (f k) (A k)) :
    JetBoundedBy P (fun x => ∑ k ∈ s, f k x) (∑ k ∈ s, A k) := by
  refine ⟨ContDiff.sum fun k hk => (hf k hk).1, fun i hi x => ?_⟩
  refine (AVRegularity.norm_iteratedFDeriv_sum_le' s (p := i)
    (fun k hk => (hf k hk).1.of_le (by exact_mod_cast hi)) x).trans ?_
  exact Finset.sum_le_sum fun k hk => (hf k hk).2 i hi x

theorem JetBoundedBy.sum_mul {κ : Type*} (s : Finset κ) {P : ℕ} {f : κ → Vec 2 → F}
    {k : κ → ℝ} {S : ℝ} (hf : ∀ i ∈ s, JetBoundedBy P (f i) (k i * S)) :
    JetBoundedBy P (fun x => ∑ i ∈ s, f i x) ((∑ i ∈ s, k i) * S) :=
  (JetBoundedBy.sum s hf).mono le_rfl (Finset.sum_mul s k S).symm.le

theorem JetBoundedBy.sum_const_mul {κ : Type*} (s : Finset κ) {P : ℕ} {f : κ → Vec 2 → F}
    {c S : ℝ} (hf : ∀ i ∈ s, JetBoundedBy P (f i) (c * S)) :
    JetBoundedBy P (fun x => ∑ i ∈ s, f i x) ((∑ _i ∈ s, c) * S) :=
  JetBoundedBy.sum_mul s (k := fun _ => c) hf

/-- The jets of a periodic field are periodic. -/
theorem iteratedFDeriv_isZ2Periodic {f : Vec 2 → F} (hp : AVenhance.IsZ2Periodic f) (i : ℕ) :
    AVenhance.IsZ2Periodic (iteratedFDeriv ℝ i f) := fun n x => by
  have e : (fun z => f (z + AVenhance.latticeShift n)) = f := funext fun z => hp n z
  exact (iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) i (AVenhance.latticeShift n) x).symm.trans
    (congrArg (fun g => iteratedFDeriv ℝ i g x) e)

/-- **A periodic field of class `C^P` has bounded jets.** -/
theorem JetBoundedBy.exists_of_periodic {P : ℕ} {f : Vec 2 → F} (hf : ContDiff ℝ (P : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) : ∃ A, JetBoundedBy P f A := by
  have hb : ∀ i : Fin (P + 1), ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ M := fun i =>
    exists_bound_periodic_field
      (hf.continuous_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_iff.1 i.isLt))
      (iteratedFDeriv_isZ2Periodic hp i)
  choose M hM using hb
  refine ⟨∑ i, |M i|, hf, fun i hi x => ?_⟩
  exact (hM ⟨i, Nat.lt_succ_of_le hi⟩ x).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)))

end Generic

/-! ### Components and `L²` vectors -/

section Components

theorem JetBoundedBy.component {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {P : ℕ}
    {f : Vec 2 → ∀ i, h i} {A : ℝ} (hf : JetBoundedBy P f A) (v : ι) :
    JetBoundedBy P (fun x => f x v) A :=
  ⟨contDiff_pi.1 hf.1 v, fun i hi x => (norm_iteratedFDeriv_component_le
    (hf.1.of_le (by exact_mod_cast hi) : ContDiff ℝ (i : ℕ∞) f) v x).trans (hf.2 i hi x)⟩

theorem JetBoundedBy.of_components {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {P : ℕ}
    {f : Vec 2 → ∀ i, h i} {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ v, JetBoundedBy P (fun x => f x v) A) : JetBoundedBy P f A := by
  have hc : ContDiff ℝ (P : ℕ∞) f := contDiff_pi.2 fun v => (hf v).1
  exact ⟨hc, fun i hi x => norm_iteratedFDeriv_le_of_apply_le
    (hc.of_le (by exact_mod_cast hi) : ContDiff ℝ (i : ℕ∞) f) x hA fun v => (hf v).2 i hi x⟩

theorem norm_piLp_proj_le {κ : Type*} [Fintype κ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (j : κ) : ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : κ => E) j‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun X => by
    rw [one_mul]
    exact PiLp.norm_apply_le X j

theorem JetBoundedBy.piLp_component {κ : Type*} [Fintype κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {P : ℕ} {f : Vec 2 → PiLp 2 (fun _ : κ => E)}
    {A : ℝ} (hf : JetBoundedBy P f A) (j : κ) : JetBoundedBy P (fun x => f x j) A :=
  (hf.clm_comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : κ => E) j)).mono le_rfl
    (mul_le_of_le_one_left hf.nonneg (norm_piLp_proj_le j))

theorem norm_applyCLM_le {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (c : E) :
    ‖ContinuousLinearMap.apply ℝ G c‖ ≤ ‖c‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c) fun T => by
    show ‖T c‖ ≤ ‖c‖ * ‖T‖
    rw [mul_comm]
    exact T.le_opNorm c

theorem norm_toLp_single_le {κ : Type*} [Fintype κ] [DecidableEq κ] (α : κ) :
    ‖(WithLp.toLp 2 (Pi.single α (1 : ℝ)) : PiLp 2 (fun _ : κ => ℝ))‖ ≤ 1 :=
  le_of_eq (by rw [PiLp.toLp_single, PiLp.norm_single, norm_one])

/-- The norm of the identification of a family of word jets with an `L²` vector. -/
def wordLpConst (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℕ) : ℝ :=
  ‖((PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivativeWord2 q => E)).symm :
    (DerivativeWord2 q → E) →L[ℝ] PiLp 2 (fun _ : DerivativeWord2 q => E))‖

theorem wordLpConst_nonneg (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℕ) :
    0 ≤ wordLpConst E q :=
  norm_nonneg _

theorem JetBoundedBy.toLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {q P : ℕ}
    {w : Vec 2 → DerivativeWord2 q → E} {A : ℝ} (hw : JetBoundedBy P w A) :
    JetBoundedBy P (fun x => (WithLp.toLp 2 (w x) : PiLp 2 (fun _ : DerivativeWord2 q => E)))
      (wordLpConst E q * A) :=
  hw.clm_comp ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivativeWord2 q => E)).symm :
    (DerivativeWord2 q → E) →L[ℝ] PiLp 2 (fun _ : DerivativeWord2 q => E))

theorem clm_toLp_sub_apply {κ : Type*} [Fintype κ] {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : PiLp 2 (fun _ : κ => E) →L[ℝ] PiLp 2 (fun _ : Fin 2 => G)) (f g : κ → E)
    (k : Fin 2) :
    (L (WithLp.toLp 2 fun α => f α - g α)) k =
      (L (WithLp.toLp 2 f)) k - (L (WithLp.toLp 2 g)) k := by
  have e : (WithLp.toLp 2 fun α => f α - g α : PiLp 2 (fun _ : κ => E)) =
      WithLp.toLp 2 f - WithLp.toLp 2 g := rfl
  rw [e, map_sub, PiLp.sub_apply]

end Components

/-! ### The classical flux and the classical defect field -/

section Defect

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The jet constant of the classical total flux. -/
def fluxJetConst (P D H : ℕ) : ℝ :=
  ((∑ _l : Fin 2, (1 : ℝ)) +
      ∑ d : Finset.Icc 2 D, ∑ _α : DerivativeWord2 (d.1 - 1), (2 : ℝ) ^ (P + 1)) +
    ∑ _r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D,
      (2 : ℝ) ^ (P + 1) * wordLpConst (h u) (d.1 - 1)

theorem fluxJetConst_nonneg (P D H : ℕ) : 0 ≤ fluxJetConst (h := h) P D H := by
  unfold fluxJetConst
  exact add_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => zero_le_one)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity))
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (by positivity) (wordLpConst_nonneg _ _))

/-- The jet constant of the classical defect field. -/
def defectJetConst (P D H : ℕ) : ℝ :=
  ∑ _j : Fin 2, (2 : ℝ) ^ P + ∑ _j : Fin 2, fluxJetConst (h := h) P D H

theorem defectJetConst_nonneg (P D H : ℕ) : 0 ≤ defectJetConst (h := h) P D H := by
  unfold defectJetConst
  exact add_nonneg (Finset.sum_nonneg fun _ _ => by positivity)
    (Finset.sum_nonneg fun _ _ => fluxJetConst_nonneg P D H)

/-- **Jets of the classical total flux.** If the jets of order `≤ P + D` of `a(s)` are bounded by
`A`, those of order `≤ P + 1` of the coefficients `A_d(s)`, `C^{[r]}(s)` by `Cco` and
`|𝖩(s)| ≤ Cco`, then the jets of order `≤ P + 1` of the components of the flux `Ξ(a)(s)` are
bounded by `fluxJetConst P D H * Cco * A`. -/
theorem classicalTotalFlux_jetBounded {D H P : ℕ} (hD : 2 ≤ D)
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {a : ℝ → Vec 2 → ∀ i, h i} {s Cco A : ℝ}
    (hCco : 0 ≤ Cco) (ha : JetBoundedBy (P + D) (a s) A)
    (hAD : ∀ d, JetBoundedBy (P + 1) (AD d s) Cco)
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, JetBoundedBy (P + 1) (CE r v u d s) Cco)
    (hJ : ∀ k l, |Jm s k l| ≤ Cco) (v : ι) (j : Fin 2) :
    JetBoundedBy (P + 1) (fun x => classicalTotalFlux D H AD CE Jm a s v x j)
      (fluxJetConst (h := h) P D H * (Cco * A)) := by
  have hA : 0 ≤ A := ha.nonneg
  -- the word jets and the first derivatives of the components
  have hw : ∀ (u : ι) (d : Finset.Icc 2 D) (α : DerivativeWord2 (d.1 - 1)),
      JetBoundedBy (P + 1) (orderedDerivative α (fun y => a s y u)) A := fun u d α => by
    have hd := Finset.mem_Icc.1 d.2
    exact ((ha.component u).mono (by omega : P + 1 + (d.1 - 1) ≤ P + D) le_rfl).word α
  have hd1 : ∀ l : Fin 2, JetBoundedBy (P + 1)
      (fun x => fderiv ℝ (fun y => a s y v) x (basisVec l)) A := fun l =>
    ((ha.component v).mono (by omega : P + 1 + 1 ≤ P + D) le_rfl).fderiv_basis l
  -- the scalar coefficients of grade `0`
  have hcoef : ∀ (d : Finset.Icc 2 D) (c : PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ)),
      ‖c‖ ≤ 1 → JetBoundedBy (P + 1) (fun x => AD d s x c j) Cco := fun d c hc =>
    (((hAD d).clm_comp (ContinuousLinearMap.apply ℝ (PiLp 2 (fun _ : Fin 2 => ℝ)) c)).piLp_component
      j).mono le_rfl (mul_le_of_le_one_left hCco ((norm_applyCLM_le c).trans hc))
  -- the three parts of the flux
  have h1 : JetBoundedBy (P + 1)
      (fun x => ∑ l : Fin 2, Jm s j l • fderiv ℝ (fun y => a s y v) x (basisVec l))
      ((∑ _l : Fin 2, (1 : ℝ)) * (Cco * A)) :=
    JetBoundedBy.sum_const_mul Finset.univ fun l _ =>
      ((hd1 l).const_smul (Jm s j l)).mono le_rfl
        (by rw [one_mul]; exact mul_le_mul_of_nonneg_right (hJ j l) hA)
  have h2 : JetBoundedBy (P + 1)
      (fun x => ∑ d : Finset.Icc 2 D, ∑ α : DerivativeWord2 (d.1 - 1),
        (AD d s x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) j) •
          orderedDerivative α (fun y => a s y v) x)
      ((∑ d : Finset.Icc 2 D, ∑ _α : DerivativeWord2 (d.1 - 1), (2 : ℝ) ^ (P + 1)) *
        (Cco * A)) :=
    JetBoundedBy.sum_mul Finset.univ fun d _ =>
      JetBoundedBy.sum_const_mul Finset.univ fun α _ =>
        ((hcoef d _ (norm_toLp_single_le α)).smul (hw v d α)).mono le_rfl
          (mul_assoc _ _ _).le
  have h3 : JetBoundedBy (P + 1)
      (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D,
        (CE r v u d s x (WithLp.toLp 2 fun α => orderedDerivative α (fun y => a s y u) x)) j)
      ((∑ _r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D,
        (2 : ℝ) ^ (P + 1) * wordLpConst (h u) (d.1 - 1)) * (Cco * A)) :=
    JetBoundedBy.sum_mul _ fun r hr => JetBoundedBy.sum_mul Finset.univ fun u _ =>
      JetBoundedBy.sum_mul Finset.univ fun d _ =>
        (((hCE r hr v u d).clm_apply (JetBoundedBy.toLp (JetBoundedBy.of_components hA
          (f := fun x (α : DerivativeWord2 (d.1 - 1)) => orderedDerivative α (fun y => a s y u) x)
          fun α => hw u d α))).piLp_component j).mono le_rfl (mul_mul_mul_comm _ _ _ _).le
  have he : (fun x => classicalTotalFlux D H AD CE Jm a s v x j) = fun x =>
      ((∑ l : Fin 2, Jm s j l • fderiv ℝ (fun y => a s y v) x (basisVec l)) +
        ∑ d : Finset.Icc 2 D, ∑ α : DerivativeWord2 (d.1 - 1),
          (AD d s x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) j) •
            orderedDerivative α (fun y => a s y v) x) +
      ∑ r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D,
        (CE r v u d s x (WithLp.toLp 2 fun α => orderedDerivative α (fun y => a s y u) x)) j :=
    funext fun x => classicalTotalFlux_eq
  rw [he]
  refine ((h1.add h2).add h3).mono le_rfl (le_of_eq ?_)
  unfold fluxJetConst
  ring

/-- **Jets of the classical defect field.** If the jets of order `≤ P + D` of `a(s)` are bounded
by `A`, those of order `≤ P` of `𝐛(s)` and of order `≤ P + 1` of `A_d(s)`, `C^{[r]}(s)` by `Cco`,
and `|𝖩(s)| ≤ Cco`, then the jets of order `≤ P` of the components of `g₁(a)(s)` are bounded by
`defectJetConst P D H * Cco * A`. -/
theorem classicalDefectField_jetBounded {D H P : ℕ} (hD : 2 ≤ D) {b : ℝ → Vec 2 → Vec 2}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {a : ℝ → Vec 2 → ∀ i, h i} {s Cco A : ℝ}
    (hCco : 0 ≤ Cco) (ha : JetBoundedBy (P + D) (a s) A) (hb : JetBoundedBy P (b s) Cco)
    (hAD : ∀ d, JetBoundedBy (P + 1) (AD d s) Cco)
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, JetBoundedBy (P + 1) (CE r v u d s) Cco)
    (hJ : ∀ k l, |Jm s k l| ≤ Cco) (v : ι) :
    JetBoundedBy P (fun x => classicalDefectField b D H AD CE Jm a s v x)
      (defectJetConst (h := h) P D H * (Cco * A)) := by
  have h1 : JetBoundedBy P
      (fun x => ∑ j : Fin 2, b s x j • fderiv ℝ (fun y => a s y v) x (basisVec j))
      ((∑ _j : Fin 2, (2 : ℝ) ^ P) * (Cco * A)) :=
    JetBoundedBy.sum_const_mul Finset.univ fun j _ =>
      ((hb.component j).smul (((ha.component v).mono (by omega : P + 1 ≤ P + D)
        le_rfl).fderiv_basis j)).mono le_rfl (mul_assoc _ _ _).le
  have h2 : JetBoundedBy P
      (fun x => ∑ j : Fin 2,
        fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm a s v y j) x (basisVec j))
      ((∑ _j : Fin 2, fluxJetConst (h := h) P D H) * (Cco * A)) :=
    JetBoundedBy.sum_const_mul Finset.univ fun j _ =>
      (classicalTotalFlux_jetBounded hD hCco ha hAD hCE hJ v j).fderiv_basis j
  show JetBoundedBy P (fun x =>
      -(∑ j : Fin 2, b s x j • fderiv ℝ (fun y => a s y v) x (basisVec j)) +
        ∑ j : Fin 2,
          fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm a s v y j) x (basisVec j))
    (defectJetConst (h := h) P D H * (Cco * A))
  refine (h1.neg.add h2).mono le_rfl (le_of_eq ?_)
  unfold defectJetConst
  ring

/-- **The classical defect field is linear** in the coarse field. -/
theorem classicalDefectField_sub {b : ℝ → Vec 2 → Vec 2} {D H : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {a a' : ℝ → Vec 2 → ∀ i, h i} {s : ℝ}
    (ha : ContDiff ℝ (D : ℕ∞) (a s)) (ha' : ContDiff ℝ (D : ℕ∞) (a' s)) (hD : 1 ≤ D)
    (hF : ∀ v j, Differentiable ℝ (fun y => classicalTotalFlux D H AD CE Jm a s v y j))
    (hF' : ∀ v j, Differentiable ℝ (fun y => classicalTotalFlux D H AD CE Jm a' s v y j))
    (v : ι) (x : Vec 2) :
    classicalDefectField b D H AD CE Jm a s v x - classicalDefectField b D H AD CE Jm a' s v x =
      classicalDefectField b D H AD CE Jm (fun t y => a t y - a' t y) s v x := by
  have hD0 : ((D : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hdiff : ∀ (w : ι) (y : Vec 2), DifferentiableAt ℝ (fun y => a s y w) y := fun w y =>
    ((contDiff_pi.1 ha w).differentiable hD0) y
  have hdiff' : ∀ (w : ι) (y : Vec 2), DifferentiableAt ℝ (fun y => a' s y w) y := fun w y =>
    ((contDiff_pi.1 ha' w).differentiable hD0) y
  have hpart : ∀ (w : ι) (l : Fin 2) (y : Vec 2),
      fderiv ℝ (fun y => a s y w - a' s y w) y (basisVec l) =
        fderiv ℝ (fun y => a s y w) y (basisVec l) -
          fderiv ℝ (fun y => a' s y w) y (basisVec l) := fun w l y =>
    (DFunLike.congr_fun (fderiv_fun_sub (hdiff w y) (hdiff' w y)) (basisVec l)).trans rfl
  have hcd : ∀ (w : ι) (q : ℕ), q ≤ D → ContDiff ℝ (q : ℕ∞) (fun y => a s y w) :=
    fun w q hq => (contDiff_pi.1 ha w).of_le (by exact_mod_cast hq)
  have hcd' : ∀ (w : ι) (q : ℕ), q ≤ D → ContDiff ℝ (q : ℕ∞) (fun y => a' s y w) :=
    fun w q hq => (contDiff_pi.1 ha' w).of_le (by exact_mod_cast hq)
  have hword : ∀ (w : ι) (d : Finset.Icc 2 D) (α : DerivativeWord2 (d.1 - 1)) (y : Vec 2),
      orderedDerivative α (fun y => a s y w - a' s y w) y =
        orderedDerivative α (fun y => a s y w) y - orderedDerivative α (fun y => a' s y w) y :=
    fun w d α y => by
      have hd : d.1 - 1 ≤ D := by have := Finset.mem_Icc.1 d.2; omega
      exact congrFun (AVRegularity.orderedDerivative_sub α (hcd w _ hd) (hcd' w _ hd)) y
  -- the flux of the difference is the difference of the fluxes
  have hflux : ∀ (u : ι) (k : Fin 2) (y : Vec 2),
      classicalTotalFlux D H AD CE Jm (fun t y => a t y - a' t y) s u y k =
        classicalTotalFlux D H AD CE Jm a s u y k - classicalTotalFlux D H AD CE Jm a' s u y k := by
    intro u k y
    simp only [classicalTotalFlux_eq, Pi.sub_apply, hpart, hword, smul_sub, clm_toLp_sub_apply,
      Finset.sum_sub_distrib]
    abel
  have hdiv : ∀ k : Fin 2,
      fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm (fun t y => a t y - a' t y) s v y k) x
          (basisVec k) =
        fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm a s v y k) x (basisVec k) -
          fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm a' s v y k) x (basisVec k) :=
    fun k => by
      have e : (fun y => classicalTotalFlux D H AD CE Jm (fun t y => a t y - a' t y) s v y k) =
          fun y => classicalTotalFlux D H AD CE Jm a s v y k -
            classicalTotalFlux D H AD CE Jm a' s v y k := funext fun y => hflux v k y
      rw [e]
      exact (DFunLike.congr_fun (fderiv_fun_sub (hF v k x) (hF' v k x)) (basisVec k)).trans rfl
  show (-(∑ j : Fin 2, b s x j • fderiv ℝ (fun y => a s y v) x (basisVec j)) +
        ∑ j : Fin 2,
          fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm a s v y j) x (basisVec j)) -
      (-(∑ j : Fin 2, b s x j • fderiv ℝ (fun y => a' s y v) x (basisVec j)) +
        ∑ j : Fin 2,
          fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm a' s v y j) x (basisVec j)) =
    -(∑ j : Fin 2, b s x j • fderiv ℝ (fun y => a s y v - a' s y v) x (basisVec j)) +
      ∑ j : Fin 2, fderiv ℝ
        (fun y => classicalTotalFlux D H AD CE Jm (fun t y => a t y - a' t y) s v y j) x
          (basisVec j)
  simp only [hpart, hdiv, smul_sub, Finset.sum_sub_distrib]
  abel

/-- **Periodic coefficients of finite smoothness have bounded jets**: one constant `Cco` bounds
the jets of order `≤ Pb` of `𝐛(s)`, those of order `≤ Pc` of `A_d(s)` and `C^{[r]}(s)`, and
`|𝖩(s)|`. -/
theorem exists_coeff_jetBounded {D H Pb Pc : ℕ} (b : ℝ → Vec 2 → Vec 2)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ)
    (hb : ContDiff ℝ (Pb : ℕ∞) (b s)) (hbp : AVenhance.IsZ2Periodic (b s))
    (hAD : ∀ d, ContDiff ℝ (Pc : ℕ∞) (AD d s)) (hADp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ (Pc : ℕ∞) (CE r v u d s))
    (hCEp : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, AVenhance.IsZ2Periodic (CE r v u d s)) :
    ∃ Cco : ℝ, 0 ≤ Cco ∧ JetBoundedBy Pb (b s) Cco ∧ (∀ d, JetBoundedBy Pc (AD d s) Cco) ∧
      (∀ r ∈ Finset.Icc 1 H, ∀ v u d, JetBoundedBy Pc (CE r v u d s) Cco) ∧
      ∀ k l, |Jm s k l| ≤ Cco := by
  obtain ⟨Ab, hAb⟩ := JetBoundedBy.exists_of_periodic hb hbp
  choose AA hAA using fun d => JetBoundedBy.exists_of_periodic (hAD d) (hADp d)
  have hC : ∀ r v u d, ∃ A : ℝ, r ∈ Finset.Icc 1 H → JetBoundedBy Pc (CE r v u d s) A := by
    intro r v u d
    by_cases hr : r ∈ Finset.Icc 1 H
    · obtain ⟨A, hA⟩ := JetBoundedBy.exists_of_periodic (hCE r hr v u d) (hCEp r hr v u d)
      exact ⟨A, fun _ => hA⟩
    · exact ⟨0, fun h' => absurd h' hr⟩
  choose AC hAC using hC
  obtain ⟨SA, hSA⟩ : ∃ S : ℝ, S = ∑ d, |AA d| := ⟨_, rfl⟩
  obtain ⟨SC, hSC⟩ : ∃ S : ℝ, S = ∑ r ∈ Finset.Icc 1 H, ∑ v, ∑ u, ∑ d, |AC r v u d| :=
    ⟨_, rfl⟩
  obtain ⟨SJ, hSJ⟩ : ∃ S : ℝ, S = ∑ k, ∑ l, |Jm s k l| := ⟨_, rfl⟩
  have hAb0 : 0 ≤ |Ab| := abs_nonneg _
  have hSA0 : 0 ≤ SA := by rw [hSA]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hSC0 : 0 ≤ SC := by
    rw [hSC]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hSJ0 : 0 ≤ SJ := by
    rw [hSJ]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨|Ab| + SA + SC + SJ, add_nonneg (add_nonneg (add_nonneg hAb0 hSA0) hSC0) hSJ0,
    ?_, ?_, ?_, ?_⟩
  · exact hAb.mono le_rfl ((le_abs_self Ab).trans (le_add_of_le_of_nonneg
      (le_add_of_le_of_nonneg (le_add_of_le_of_nonneg le_rfl hSA0) hSC0) hSJ0))
  · intro d
    have h1 : |AA d| ≤ SA := by
      rw [hSA]
      exact Finset.single_le_sum (f := fun d => |AA d|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ d)
    exact (hAA d).mono le_rfl ((le_abs_self _).trans (h1.trans (le_add_of_le_of_nonneg
      (le_add_of_le_of_nonneg (le_add_of_nonneg_left hAb0) hSC0) hSJ0)))
  · intro r hr v u d
    have h1 : |AC r v u d| ≤ SC := by
      rw [hSC]
      refine le_trans ?_ (Finset.single_le_sum (f := fun r => ∑ v, ∑ u, ∑ d, |AC r v u d|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => abs_nonneg _) hr)
      refine le_trans ?_ (Finset.single_le_sum (f := fun v => ∑ u, ∑ d, |AC r v u d|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ v))
      refine le_trans ?_ (Finset.single_le_sum (f := fun u => ∑ d, |AC r v u d|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ u))
      exact Finset.single_le_sum (f := fun d => |AC r v u d|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ d)
    exact (hAC r v u d hr).mono le_rfl ((le_abs_self _).trans (h1.trans
      (le_add_of_le_of_nonneg (le_add_of_nonneg_left (add_nonneg hAb0 hSA0)) hSJ0)))
  · intro k l
    have h1 : |Jm s k l| ≤ SJ := by
      rw [hSJ]
      refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∑ l, |Jm s k l|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k))
      exact Finset.single_le_sum (f := fun l => |Jm s k l|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ l)
    exact h1.trans (le_add_of_nonneg_left (add_nonneg (add_nonneg hAb0 hSA0) hSC0))

end Defect

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The time integral of the mass norm of a limit of split carrier families**.
If `Q_n = A_n + B_n + C_n` at every time, `Q_n → q`, `√mass(A_n) ≤ β` with `β` integrable,
`B_n → 0` and the `C_n` are measurable with `∫ √mass(C_n) ≤ P`, then
`∫ √mass(q) ≤ ∫ β + P` (`integral_sqrt_massNormSq_le_of_split`). -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, CompleteSpace (E i)]

/-- The square root of the mass-weighted norm is continuous in the carrier family. -/
theorem continuous_sqrt_massNormSq (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    Continuous (fun U : ∀ i, TorusHk (K i) (E i) =>
      Real.sqrt (massNormSq ρ π (fun i => (U i).val))) := by
  have e : (fun U : ∀ i, TorusHk (K i) (E i) => Real.sqrt (massNormSq ρ π (fun i => (U i).val)))
      = fun U => ‖massWeightedCarrierCLM (E := E) K ρ π U‖ :=
    funext fun U => (massWeightedCarrierCLM_norm K ρ π hπ U).symm
  rw [e]
  exact (massWeightedCarrierCLM (E := E) K ρ π).continuous.norm

/-- **The mass-weighted norm of a family of a.e. strongly measurable carrier trajectories is a.e.
strongly measurable.** -/
theorem aestronglyMeasurable_massNormSq (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) {μ : Measure ℝ}
    (q : ℝ → ∀ i, TorusHk (K i) (E i))
    (hq : ∀ i, AEStronglyMeasurable (fun s => q s i) μ) :
    AEStronglyMeasurable (fun s => massNormSq ρ π (fun i => (q s i).val)) μ := by
  unfold massNormSq
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  have hc : Continuous (fun U : TorusHk (K i) (E i) => factorialNormSq ρ U.val) := by
    have e : (fun U : TorusHk (K i) (E i) => factorialNormSq ρ U.val) =
        fun U => ‖factorialWeightedJetCLM ρ (K i) U.val‖ ^ 2 := funext fun U => by
      rw [factorialWeightedJetCLM_apply, factorialWeightedJet_normSq]
    rw [e]
    exact (((factorialWeightedJetCLM ρ (K i)).continuous.comp
      continuous_subtype_val).norm).pow 2
  exact (hc.comp_aestronglyMeasurable (hq i)).const_mul _

/-- **The integral of the mass norm of a limit of split carrier families.** -/
theorem integral_sqrt_massNormSq_le_of_split {I : Set ℝ} (hI : MeasurableSet I) (K : ι → ℕ)
    (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Q A Bf Cf : ℕ → ℝ → ∀ i, TorusHk (K i) (E i)) (q : ℝ → ∀ i, TorusHk (K i) (E i))
    (hdec : ∀ n, ∀ s ∈ I, ∀ i, Q n s i = A n s i + Bf n s i + Cf n s i)
    (hlim : ∀ s ∈ I, ∀ i, Tendsto (fun n => Q n s i) atTop (𝓝 (q s i)))
    (hqm : ∀ i, AEStronglyMeasurable (fun s => q s i) (volume.restrict I))
    {β : ℝ → ℝ} (hβ0 : ∀ s, 0 ≤ β s) (hβ : IntegrableOn β I)
    (hA : ∀ n, ∀ s ∈ I, Real.sqrt (massNormSq ρ π (fun i => (A n s i).val)) ≤ β s)
    (hB : ∀ s ∈ I, ∀ i, Tendsto (fun n => Bf n s i) atTop (𝓝 0))
    (hCm : ∀ n i, AEStronglyMeasurable (fun s => Cf n s i) (volume.restrict I)) {P : ℝ}
    (hP : 0 ≤ P)
    (hC : ∀ n, ∫⁻ s in I, ENNReal.ofReal (Real.sqrt (massNormSq ρ π (fun i => (Cf n s i).val)))
      ≤ ENNReal.ofReal P) :
    ∫ s in I, Real.sqrt (massNormSq ρ π (fun i => (q s i).val)) ≤ (∫ s in I, β s) + P := by
  have hc := continuous_sqrt_massNormSq (E := E) K ρ π hπ
  refine integral_le_of_limit_split hI (fun s => Real.sqrt_nonneg _)
    ((aestronglyMeasurable_massNormSq K ρ π q hqm).aemeasurable.sqrt.aestronglyMeasurable)
    (fun n s => Real.sqrt (massNormSq ρ π (fun i => (Q n s i).val)))
    (fun n s => Real.sqrt (massNormSq ρ π (fun i => (Bf n s i).val)))
    (fun n s => Real.sqrt (massNormSq ρ π (fun i => (Cf n s i).val))) hβ0 hβ
    (fun s hs => (hc.tendsto _).comp (tendsto_pi_nhds.2 (hlim s hs)))
    (fun n s hs => ?_) (fun s hs => ?_)
    (fun n => (aestronglyMeasurable_massNormSq K ρ π (Cf n) (hCm n)).aemeasurable.sqrt) hP hC
  · have e : (fun i => (Q n s i).val) = fun i => ((fun i => A n s i + Bf n s i) i + Cf n s i).val :=
      funext fun i => by rw [hdec n s hs i]
    rw [e]
    have h1 := sqrt_massNormSq_add_le K ρ π hπ (fun i => A n s i + Bf n s i) (Cf n s)
    have h2 := sqrt_massNormSq_add_le K ρ π hπ (A n s) (Bf n s)
    have h3 : Real.sqrt (massNormSq ρ π (fun i => (A n s i + Bf n s i).val)) +
        Real.sqrt (massNormSq ρ π (fun i => (Cf n s i).val)) ≤
        β s + Real.sqrt (massNormSq ρ π (fun i => (Bf n s i).val)) +
          Real.sqrt (massNormSq ρ π (fun i => (Cf n s i).val)) :=
      add_le_add (h2.trans (add_le_add (hA n s hs) le_rfl)) le_rfl
    exact h1.trans h3
  · have h0 : Real.sqrt (massNormSq ρ π (fun i => ((0 : ∀ i, TorusHk (K i) (E i)) i).val)) = 0 := by
      have := massWeightedCarrierCLM_norm (E := E) K ρ π hπ (0 : ∀ i, TorusHk (K i) (E i))
      rw [← this, ContinuousLinearMap.map_zero, norm_zero]
    rw [← h0]
    exact (hc.tendsto _).comp (tendsto_pi_nhds.2 (hB s hs))

end AVRegularity.CycleComparison.Reconstruction
end
