-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.ActualMeans.Kernel
public import AVRegularity.Statements.Intermediate.CycleOutput.ClassicalGradeFlux
public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation
import AVRegularity.Weighted.PlaneH1Readouts
import AVRegularity.Weighted.MetricWordCoefficientArrayBound
import AVRegularity.CycleComparison.ActualMeans.KernelRegular
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.ActualMeans

/-! The Eulerian letters of the actual means and their flux identity.

The edge letters `ceLetter` and the diagonal letters `adLetter` are the word-array operators of
the glued kernels. Their classical grade flux is minus the glued Piola transport of the
dimensional chart-frame fluxes: the chain rule for ordered words turns `∂^α (a ∘ Φ)` into the
derivatives `∂^β a`, and the kernels collect the coefficients. The diagonal letter absorbs
`-𝖩`. -/

section
/-! ### Sums over output orders and words -/

section DSum

variable {A : Type*} [AddCommMonoid A]

/-- The sum over the output orders `d' ∈ S` and the words `β` of length `d' - 1`. -/
def dsum (S : Finset ℕ) (F : (d' : ℕ) → DerivativeWord2 (d' - 1) → A) : A :=
  ∑ d' ∈ S, ∑ β : DerivativeWord2 (d' - 1), F d' β

theorem smul_dsum [Module ℝ A] (c : ℝ) (S : Finset ℕ)
    (F : (d' : ℕ) → DerivativeWord2 (d' - 1) → A) :
    c • dsum S F = dsum S (fun d' β => c • F d' β) := by
  simp only [dsum, Finset.smul_sum]

theorem sum_dsum_comm {κ : Type*} (T : Finset κ) (S : Finset ℕ)
    (F : κ → (d' : ℕ) → DerivativeWord2 (d' - 1) → A) :
    ∑ i ∈ T, dsum S (F i) = dsum S (fun d' β => ∑ i ∈ T, F i d' β) := by
  simp only [dsum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d' _ => Finset.sum_comm

theorem map_dsum {A' : Type*} [AddCommMonoid A'] {Fn : Type*} [FunLike Fn A A']
    [AddMonoidHomClass Fn A A'] (φ : Fn) (S : Finset ℕ)
    (F : (d' : ℕ) → DerivativeWord2 (d' - 1) → A) :
    φ (dsum S F) = dsum S (fun d' β => φ (F d' β)) := by
  simp only [dsum, map_sum]

theorem dsum_congr {S : Finset ℕ} {F F' : (d' : ℕ) → DerivativeWord2 (d' - 1) → A}
    (h : ∀ d' ∈ S, ∀ β, F d' β = F' d' β) : dsum S F = dsum S F' :=
  Finset.sum_congr rfl fun d' hd' => Finset.sum_congr rfl fun β _ => h d' hd' β

end DSum

/-! ### The chain rule, indexed by orders -/

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem chainCoeff_zero_right_eq_zero (Φ : Vec 2 → Vec 2) {m : ℕ} (hm : 1 ≤ m)
    (α : DerivativeWord2 m) (β : DerivativeWord2 0) : chainCoeff Φ m α 0 β = 0 := by
  cases m with
  | zero => omega
  | succ m => exact chainCoeff_succ_zero_eq_zero Φ m α β

/-- The chain rule for a word of length `d - 1`, `2 ≤ d ≤ M`, as a sum over the orders
`d' ∈ [2, M]`. -/
theorem orderedDerivative_comp_chart_dsum {Φ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {g : Vec 2 → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (M d : ℕ) (hd : 2 ≤ d) (hdM : d ≤ M)
    (α : DerivativeWord2 (d - 1)) (y : Vec 2) :
    orderedDerivative α (fun y' => g (Φ y')) y =
      dsum (Finset.Icc 2 M) (fun d' β =>
        chainCoeff Φ (d - 1) α (d' - 1) β y • orderedDerivative β g (Φ y)) := by
  have h := congrFun (orderedDerivative_comp_chart hΦ hg (M - 1) (d - 1) (by omega) α) y
  have hM : M - 1 + 1 = M := by omega
  rw [h, hM, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < M)]
  have h0 : ∑ β : DerivativeWord2 0,
      chainCoeff Φ (d - 1) α 0 β y • orderedDerivative β g (Φ y) = 0 := by
    refine Finset.sum_eq_zero fun β _ => ?_
    rw [chainCoeff_zero_right_eq_zero Φ (by omega) α β, Pi.zero_apply, zero_smul]
  rw [h0, zero_add]
  symm
  unfold dsum
  refine Finset.sum_nbij' (fun d' => d' - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_
  · intro d' hd'
    have := Finset.mem_Icc.1 hd'
    exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
  · intro k hk
    have := Finset.mem_Ico.1 hk
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · intro d' hd'
    have := Finset.mem_Icc.1 hd'
    show d' - 1 + 1 = d'
    omega
  · intro k _
    rfl
  · intro d' _
    rfl

end Chain

/-! ### The pairing of a pulse kernel with the derivatives of a field -/

section Pairing

variable {G E E' : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- The pulse kernel is homogeneous in its letters. -/
theorem pulseKernel_smul (ω : ℝ) (c ρ εc : ℝ) (M : ℕ) (chart label : Vec 2 → Vec 2)
    (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G)
    (m' : ℕ) (β : DerivativeWord2 m') (k' : Fin 2) (x : Vec 2) :
    pulseKernel c ρ εc M chart label (fun n d α l X => ω • W n d α l X) m' β k' x =
      ω • pulseKernel c ρ εc M chart label W m' β k' x :=
  (clm_pulseKernel (ω • ContinuousLinearMap.id ℝ G) c ρ εc M chart label W m' β k' x).symm

/-- **Pairing.** The kernel coefficients, paired with the derivatives `∂^β g` through a bilinear
action `B`, give the Piola-transported chart-frame flux of `g ∘ Φ`. -/
theorem pulseKernel_pairing (B : G →L[ℝ] E →L[ℝ] E') (c ρ εc : ℝ) (M : ℕ)
    {chart label : Vec 2 → Vec 2} (hchart : ContDiff ℝ (⊤ : ℕ∞) chart)
    (hinv : ∀ x, chart (label x) = x)
    (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G)
    {g : Vec 2 → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (k' : Fin 2) (x : Vec 2) :
    dsum (Finset.Icc 2 M) (fun d' β =>
        B (pulseKernel c ρ εc M chart label W (d' - 1) β k' x) (orderedDerivative β g x)) =
      ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix chart (label x) k' l •
        ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
          B (W n d α l (ρ⁻¹ • label x))
            (orderedDerivative α (fun y => g (chart y)) (label x)) := by
  have hchain : ∀ n ∈ Finset.Icc 2 M, ∀ d ∈ Finset.Icc 2 n, ∀ α : DerivativeWord2 (d - 1),
      orderedDerivative α (fun y => g (chart y)) (label x) =
        dsum (Finset.Icc 2 M) (fun d' β =>
          chainCoeff chart (d - 1) α (d' - 1) β (label x) • orderedDerivative β g x) := by
    intro n hn d hd α
    have hn' := Finset.mem_Icc.1 hn
    have hd' := Finset.mem_Icc.1 hd
    have h := orderedDerivative_comp_chart_dsum hchart hg M d hd'.1 (by omega) α (label x)
    rw [hinv x] at h
    exact h
  symm
  calc ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix chart (label x) k' l •
        ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
          B (W n d α l (ρ⁻¹ • label x))
            (orderedDerivative α (fun y => g (chart y)) (label x))
      = ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix chart (label x) k' l •
        ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
          dsum (Finset.Icc 2 M) (fun d' β =>
            chainCoeff chart (d - 1) α (d' - 1) β (label x) •
              B (W n d α l (ρ⁻¹ • label x)) (orderedDerivative β g x)) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun d hd => ?_
        congr 1
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hchain n hn d hd α, map_dsum]
        exact dsum_congr fun d' _ β => map_smul _ _ _
    _ = dsum (Finset.Icc 2 M) (fun d' β =>
        ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix chart (label x) k' l •
          ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
            chainCoeff chart (d - 1) α (d' - 1) β (label x) •
              B (W n d α l (ρ⁻¹ • label x)) (orderedDerivative β g x)) := by
        simp only [sum_dsum_comm, smul_dsum]
    _ = dsum (Finset.Icc 2 M) (fun d' β =>
        B (pulseKernel c ρ εc M chart label W (d' - 1) β k' x) (orderedDerivative β g x)) := by
        refine dsum_congr fun d' _ β => ?_
        simp only [pulseKernel, map_sum, map_smul, _root_.sum_apply, smul_apply]

/-- The pairing for a windowed letter: where the partition function is supported in the
window, the cutoff is the weight `ϖ(t)`. -/
theorem pulseKernel_window_pairing (B : G →L[ℝ] E →L[ℝ] E') (c ρ εc : ℝ) (M : ℕ)
    {chart label : Vec 2 → Vec 2} (hchart : ContDiff ℝ (⊤ : ℕ∞) chart)
    (hinv : ∀ x, chart (label x) = x) (ϖ : ℝ → ℝ) (s₀ s₁ : ℝ)
    (L : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → G) {t : ℝ}
    (hsupp : ϖ t ≠ 0 → c⁻¹ * t ∈ Set.Icc s₀ s₁)
    {g : Vec 2 → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (k' : Fin 2) (x : Vec 2) :
    dsum (Finset.Icc 2 M) (fun d' β =>
        B (pulseKernel c ρ εc M chart label
          (fun n d α l => windowLetter ϖ c s₀ s₁ (L n d α l) t) (d' - 1) β k' x)
          (orderedDerivative β g x)) =
      ϖ t • ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2,
        jacMatrix chart (label x) k' l • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
          ∑ α : DerivativeWord2 (d - 1), B (L n d α l (c⁻¹ * t) (ρ⁻¹ • label x))
            (orderedDerivative α (fun y => g (chart y)) (label x)) := by
  have hW : (fun (n d : ℕ) (α : DerivativeWord2 (d - 1)) (l : Fin 2) =>
      windowLetter ϖ c s₀ s₁ (L n d α l) t) =
      fun n d α l X => ϖ t • L n d α l (c⁻¹ * t) X := by
    funext n d α l X
    exact windowLetter_eq_smul _ hsupp X
  have h := pulseKernel_pairing B c ρ εc M hchart hinv
    (fun n d α l X => L n d α l (c⁻¹ * t) X) hg k' x
  rw [hW, ← h, smul_dsum]
  refine dsum_congr fun d' _ β => ?_
  rw [pulseKernel_smul, map_smul, smul_apply]

end Pairing

/-! ### The letters -/

section Letters

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The chart-frame letters of the entry `(v, u)` and the grade `r`, as kernel letters. -/
def entryLetter (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h) (r : ℕ) (v u : ι) :
    ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → (h u →L[ℝ] h v) :=
  fun k n d α l s X => Lb k r n d α s X l v u

/-- The Eulerian edge letter: minus the word-array operator of the glued kernel. -/
def ceLetter (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) (M : ℕ)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ) (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
    (r : ℕ) (v u : ι) (d : Finset.Icc 2 M) (t : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h v) :=
  -arrayOp (fun β k' => gluedKernel kset ϖ c ρ εc M chart label s₀ s₁
    (entryLetter Lb r v u) (d.1 - 1) β k' t x)

/-- The reference-flux entry of the diagonal letter: `𝖩_{k', β₀}` on words of length one. -/
def jmEntry (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (m : ℕ) (β : DerivativeWord2 m)
    (k' : Fin 2) : ℝ :=
  if hm : m = 1 then Jm t k' (β ⟨0, by omega⟩) else 0

/-- The Eulerian diagonal letter: minus the glued scalar kernel, minus the reference flux. -/
def adLetter (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) (M : ℕ)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
    (Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ)
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (d : Finset.Icc 2 M) (t : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ) :=
  -arrayOp (fun β k' =>
    (gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc (d.1 - 1) β k' t x +
      jmEntry Jm t (d.1 - 1) β k') • ContinuousLinearMap.id ℝ ℝ)

theorem ceLetter_apply (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) (M : ℕ)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ) (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
    (r : ℕ) (v u : ι) (d : Finset.Icc 2 M) (t : ℝ) (x : Vec 2)
    (w : PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) (k' : Fin 2) :
    ceLetter kset ϖ c ρ εc M chart label s₀ s₁ Lb r v u d t x w k' =
      -∑ β : DerivativeWord2 (d.1 - 1), gluedKernel kset ϖ c ρ εc M chart label s₀ s₁
        (entryLetter Lb r v u) (d.1 - 1) β k' t x (w β) := by
  rw [ceLetter, neg_apply, PiLp.neg_apply, arrayOp_apply]

theorem adLetter_single (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) (M : ℕ)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
    (Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ)
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (d : Finset.Icc 2 M) (t : ℝ) (x : Vec 2)
    (α : DerivativeWord2 (d.1 - 1)) (k' : Fin 2) :
    adLetter kset ϖ c ρ εc M chart label s₀ s₁ Lsc Jm d t x
        (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k' =
      -(gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc (d.1 - 1) α k' t x +
        jmEntry Jm t (d.1 - 1) α k') := by
  have hs : ∀ β : DerivativeWord2 (d.1 - 1),
      (WithLp.toLp 2 (Pi.single α (1 : ℝ)) : PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ)) β =
        if β = α then 1 else 0 := fun β => Pi.single_apply α 1 β
  rw [adLetter, neg_apply, PiLp.neg_apply, arrayOp_apply, Finset.sum_eq_single α]
  · rw [smul_apply, ContinuousLinearMap.id_apply, hs, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro β _ hβ
    rw [smul_apply, ContinuousLinearMap.id_apply, hs, ite_eq_right hβ, smul_zero]
  · intro hα
    exact absurd (Finset.mem_univ α) hα

end Letters
end

/-! The flux identity of the Eulerian letters: the classical grade flux of `(adLetter, ceLetter)`
is minus the glued Piola transport of the dimensional chart-frame fluxes.
-/

section
section Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sum_coe_dsum {A : Type*} [AddCommMonoid A] (S : Finset ℕ)
    (F : (d' : ℕ) → DerivativeWord2 (d' - 1) → A) :
    ∑ d : S, ∑ β : DerivativeWord2 (d.1 - 1), F d.1 β = dsum S F :=
  Finset.sum_coe_sort S (fun d' => ∑ β : DerivativeWord2 (d' - 1), F d' β)

theorem orderedDerivative_word_one (β : DerivativeWord2 1) (g : Vec 2 → E) (x : Vec 2) :
    orderedDerivative β g x = fderiv ℝ g x (basisVec (β 0)) := by
  have h := congrFun (orderedDerivative_succ β g) x
  rw [h, orderedDerivative_zero]
  rfl

theorem jmEntry_one (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (β : DerivativeWord2 1)
    (k' : Fin 2) : jmEntry Jm t 1 β k' = Jm t k' (β 0) := by
  unfold jmEntry
  rw [dite_eq_left rfl]
  rfl

theorem jmEntry_of_ne (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) {m : ℕ} (hm : m ≠ 1)
    (β : DerivativeWord2 m) (k' : Fin 2) : jmEntry Jm t m β k' = 0 := by
  unfold jmEntry
  exact dite_eq_right hm

/-- The reference-flux entries pair with the first derivatives. -/
theorem dsum_jmEntry (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) {M : ℕ} (hM : 2 ≤ M)
    (k' : Fin 2) (g : Vec 2 → E) (x : Vec 2) :
    dsum (Finset.Icc 2 M) (fun d' β => jmEntry Jm t (d' - 1) β k' • orderedDerivative β g x) =
      ∑ l : Fin 2, Jm t k' l • fderiv ℝ g x (basisVec l) := by
  unfold dsum
  rw [Finset.sum_eq_single 2]
  · show ∑ β : DerivativeWord2 1, jmEntry Jm t 1 β k' • orderedDerivative β g x = _
    refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2)) _ _ fun β => ?_
    rw [orderedDerivative_word_one, jmEntry_one]
    rfl
  · intro d' hd' hne
    refine Finset.sum_eq_zero fun β _ => ?_
    have hd1 : d' - 1 ≠ 1 := by
      have := Finset.mem_Icc.1 hd'
      omega
    show jmEntry Jm t (d' - 1) β k' • orderedDerivative β g x = 0
    rw [jmEntry_of_ne Jm t hd1, zero_smul]
  · intro h2
    exact absurd (Finset.mem_Icc.2 ⟨le_rfl, hM⟩) h2

end Aux

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- Moving the component sum inside the glued chart-frame flux. -/
theorem sum_component_flux (kset : Finset ℤ) (w : ℤ → ℝ) (cn : ℕ → ℝ) (M : ℕ)
    (J : ℤ → Fin 2 → ℝ) (ρ : ℝ) {v : ι}
    (T : ι → ℤ → (n : ℕ) → Fin 2 → (d : ℕ) → DerivativeWord2 (d - 1) → h v) :
    ∑ u : ι, ∑ k ∈ kset, w k • ∑ n ∈ Finset.Icc 2 M, cn n • ∑ l : Fin 2, J k l •
        ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1), T u k n l d α =
      ∑ k ∈ kset, w k • ∑ n ∈ Finset.Icc 2 M, cn n • ∑ l : Fin 2, J k l •
        ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1), ∑ u : ι, T u k n l d α := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  exact Finset.sum_comm

/-- **Flux identity, positive grades.** -/
theorem classicalGradeFlux_edge (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) (M : ℕ)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ) (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
    (AD : ∀ d : Finset.Icc 2 M, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {r : ℕ} (hr : r ≠ 0) (a : ℝ → Vec 2 → ∀ i, h i)
    (t : ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) (a t))
    (hchart : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (chart k t))
    (hinv : ∀ k ∈ kset, ∀ x, chart k t (label k t x) = x)
    (hsupp : ∀ k ∈ kset, ϖ k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k))
    (x : Vec 2) (v : ι) (k' : Fin 2) :
    classicalGradeFlux M r AD (ceLetter kset ϖ c ρ εc M chart label s₀ s₁ Lb) Jm a v t x k' =
      -∑ k ∈ kset, ϖ k t • ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2,
        jacMatrix (chart k t) (label k t x) k' l • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
          ∑ α : DerivativeWord2 (d - 1), ∑ u : ι,
            Lb k r n d α (c⁻¹ * t) (ρ⁻¹ • label k t x) l v u
              (orderedDerivative α (fun y => a t (chart k t y)) (label k t x) u) := by
  have hau : ∀ u : ι, ContDiff ℝ (⊤ : ℕ∞) (fun y => a t y u) := fun u => contDiff_pi.1 ha u
  have hu : ∀ u : ι,
      ∑ d : Finset.Icc 2 M, (ceLetter kset ϖ c ρ εc M chart label s₀ s₁ Lb r v u d t x
        (WithLp.toLp 2 fun α => orderedDerivative α (fun y => a t y u) x)) k' =
      -∑ k ∈ kset, ϖ k t • ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2,
        jacMatrix (chart k t) (label k t x) k' l • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
          ∑ α : DerivativeWord2 (d - 1),
            Lb k r n d α (c⁻¹ * t) (ρ⁻¹ • label k t x) l v u
              (orderedDerivative α (fun y => a t (chart k t y) u) (label k t x)) := by
    intro u
    have h1 : ∑ d : Finset.Icc 2 M, (ceLetter kset ϖ c ρ εc M chart label s₀ s₁ Lb r v u d t x
          (WithLp.toLp 2 fun α => orderedDerivative α (fun y => a t y u) x)) k' =
        -dsum (Finset.Icc 2 M) (fun d' β => ∑ k ∈ kset,
          (pulseKernel c ρ εc M (chart k t) (label k t)
            (fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k)
              (entryLetter Lb r v u k n d α l) t) (d' - 1) β k' x)
            (orderedDerivative β (fun y => a t y u) x)) := by
      refine Eq.trans ?_ (congrArg Neg.neg (sum_coe_dsum (Finset.Icc 2 M) (fun d' β =>
        ∑ k ∈ kset, (pulseKernel c ρ εc M (chart k t) (label k t)
          (fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k)
            (entryLetter Lb r v u k n d α l) t) (d' - 1) β k' x)
          (orderedDerivative β (fun y => a t y u) x))))
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [ceLetter_apply]
      congr 1
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [gluedKernel, _root_.sum_apply]
    rw [h1, ← sum_dsum_comm]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    exact pulseKernel_window_pairing (ContinuousLinearMap.id ℝ (h u →L[ℝ] h v)) c ρ εc M
      (hchart k hk) (hinv k hk) (ϖ k) (s₀ k) (s₁ k) (entryLetter Lb r v u k) (hsupp k hk)
      (hau u) k' x
  have hflux : classicalGradeFlux M r AD (ceLetter kset ϖ c ρ εc M chart label s₀ s₁ Lb) Jm a
      v t x k' = ∑ u : ι, ∑ d : Finset.Icc 2 M,
        (ceLetter kset ϖ c ρ εc M chart label s₀ s₁ Lb r v u d t x
          (WithLp.toLp 2 fun α => orderedDerivative α (fun y => a t y u) x)) k' := by
    unfold classicalGradeFlux
    exact ite_eq_right hr
  rw [hflux, Finset.sum_congr rfl fun u _ => hu u, Finset.sum_neg_distrib]
  congr 1
  rw [sum_component_flux kset (fun k => ϖ k t) (fun n => c⁻¹ * εc ^ n) M
    (fun k l => jacMatrix (chart k t) (label k t x) k' l) ρ
    (fun u k n l d α => Lb k r n d α (c⁻¹ * t) (ρ⁻¹ • label k t x) l v u
      (orderedDerivative α (fun y => a t (chart k t y) u) (label k t x)))]
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun u _ => ?_
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y => a t (chart k t y)) := ha.comp (hchart k hk)
  rw [ChartTransport.orderedDerivative_apply α (hg.of_le (by exact_mod_cast le_top)) u
    (label k t x)]

/-- **Flux identity, grade zero.** The diagonal letter carries the scalar letters `Lsc` of the
diagonal chart-frame means and absorbs the reference flux. -/
theorem classicalGradeFlux_diag (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) {M : ℕ}
    (hM : 2 ≤ M) (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
    (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
    (Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ)
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 M), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) (a t))
    (hchart : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (chart k t))
    (hinv : ∀ k ∈ kset, ∀ x, chart k t (label k t x) = x)
    (hsupp : ∀ k ∈ kset, ϖ k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k))
    (hsc : ∀ k ∈ kset, c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) → ∀ n ∈ Finset.Icc 2 M,
      ∀ d ∈ Finset.Icc 2 n, ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2) (X : Vec 2),
        (∀ (v : ι) (ξ : h v), Lb k 0 n d α (c⁻¹ * t) X l v v ξ = Lsc k n d α l (c⁻¹ * t) X • ξ) ∧
        (∀ v u : ι, v ≠ u → Lb k 0 n d α (c⁻¹ * t) X l v u = 0))
    (x : Vec 2) (v : ι) (k' : Fin 2) :
    classicalGradeFlux M 0 (adLetter kset ϖ c ρ εc M chart label s₀ s₁ Lsc Jm) CE Jm a v t x k' =
      -∑ k ∈ kset, ϖ k t • ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2,
        jacMatrix (chart k t) (label k t x) k' l • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
          ∑ α : DerivativeWord2 (d - 1), ∑ u : ι,
            Lb k 0 n d α (c⁻¹ * t) (ρ⁻¹ • label k t x) l v u
              (orderedDerivative α (fun y => a t (chart k t y)) (label k t x) u) := by
  have hav : ContDiff ℝ (⊤ : ℕ∞) (fun y => a t y v) := contDiff_pi.1 ha v
  have hflux : classicalGradeFlux M 0 (adLetter kset ϖ c ρ εc M chart label s₀ s₁ Lsc Jm) CE Jm
      a v t x k' =
      (∑ l : Fin 2, Jm t k' l • fderiv ℝ (fun y => a t y v) x (basisVec l)) +
        ∑ d : Finset.Icc 2 M, ∑ α : DerivativeWord2 (d.1 - 1),
          (adLetter kset ϖ c ρ εc M chart label s₀ s₁ Lsc Jm d t x
            (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k') •
            orderedDerivative α (fun y => a t y v) x := by
    unfold classicalGradeFlux
    exact ite_eq_left rfl
  -- the letter sum splits into the kernel part and the reference-flux part
  have hsum : ∑ d : Finset.Icc 2 M, ∑ α : DerivativeWord2 (d.1 - 1),
      (adLetter kset ϖ c ρ εc M chart label s₀ s₁ Lsc Jm d t x
        (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k') • orderedDerivative α (fun y => a t y v) x =
      -dsum (Finset.Icc 2 M) (fun d' β =>
          gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc (d' - 1) β k' t x •
            orderedDerivative β (fun y => a t y v) x) -
        dsum (Finset.Icc 2 M) (fun d' β =>
          jmEntry Jm t (d' - 1) β k' • orderedDerivative β (fun y => a t y v) x) := by
    rw [← sum_coe_dsum, ← sum_coe_dsum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [adLetter_single, neg_add, add_smul, neg_smul, neg_smul, sub_eq_add_neg]
  -- the kernel part, pulse by pulse
  have hker : dsum (Finset.Icc 2 M) (fun d' β =>
      gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc (d' - 1) β k' t x •
        orderedDerivative β (fun y => a t y v) x) =
      ∑ k ∈ kset, ϖ k t • ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2,
        jacMatrix (chart k t) (label k t x) k' l • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
          ∑ α : DerivativeWord2 (d - 1), Lsc k n d α l (c⁻¹ * t) (ρ⁻¹ • label k t x) •
            orderedDerivative α (fun y => a t (chart k t y) v) (label k t x) := by
    have h1 : dsum (Finset.Icc 2 M) (fun d' β =>
        gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc (d' - 1) β k' t x •
          orderedDerivative β (fun y => a t y v) x) =
        ∑ k ∈ kset, dsum (Finset.Icc 2 M) (fun d' β =>
          pulseKernel c ρ εc M (chart k t) (label k t)
            (fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k) (Lsc k n d α l) t)
            (d' - 1) β k' x • orderedDerivative β (fun y => a t y v) x) := by
      rw [sum_dsum_comm]
      refine dsum_congr fun d' _ β => ?_
      rw [gluedKernel, Finset.sum_smul]
    rw [h1]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact pulseKernel_window_pairing (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h v →L[ℝ] h v)
      c ρ εc M (hchart k hk) (hinv k hk) (ϖ k) (s₀ k) (s₁ k) (Lsc k) (hsupp k hk) hav k' x
  rw [hflux, hsum, dsum_jmEntry Jm t hM k' (fun y => a t y v) x, hker]
  rw [add_sub_cancel]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hϖ : ϖ k t = 0
  · rw [hϖ, zero_smul, zero_smul]
  · have hwin := hsupp k hk hϖ
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    obtain ⟨hdiag, hoff⟩ := hsc k hk hwin n hn d hd α l (ρ⁻¹ • label k t x)
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y => a t (chart k t y)) := ha.comp (hchart k hk)
    rw [Finset.sum_eq_single v]
    · rw [hdiag, ChartTransport.orderedDerivative_apply α (hg.of_le (by exact_mod_cast le_top)) v
        (label k t x)]
    · intro u _ hu
      rw [hoff v u (Ne.symm hu), zero_apply]
    · intro hv
      exact absurd (Finset.mem_univ v) hv
end

/-! Regularity of a word-array operator `x ↦ -arrayOp (K x)` from the regularity of its entries:
smoothness, periodicity, measurability, and the operator norm of its derivative arrays (the norm
used by `coefficientSeminorm`). -/

section
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {m : ℕ}

theorem norm_arrayEntryL_le (m : ℕ) (β : DerivativeWord2 m) (k' : Fin 2) :
    ‖arrayEntryL (F := F) (G := G) m β k'‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => by
    rw [one_mul]
    exact norm_arrayEntryL_apply_le m β k' L

theorem contDiff_arrayEntry {n : WithTop ℕ∞} {f : Vec 2 → (F →L[ℝ] G)} (hf : ContDiff ℝ n f)
    (β : DerivativeWord2 m) (k' : Fin 2) :
    ContDiff ℝ n (fun x => arrayEntryL (F := F) (G := G) m β k' (f x)) :=
  (arrayEntryL (F := F) (G := G) m β k').contDiff.comp hf

theorem contDiff_neg_arrayOp {n : WithTop ℕ∞}
    {K : Vec 2 → DerivativeWord2 m → Fin 2 → (F →L[ℝ] G)}
    (hK : ∀ β k', ContDiff ℝ n (fun x => K x β k')) :
    ContDiff ℝ n (fun x => -arrayOp (K x)) :=
  (ContDiff.sum fun β _ => ContDiff.sum fun k' _ => contDiff_arrayEntry (hK β k') β k').neg

theorem isZ2Periodic_neg_arrayOp {K : Vec 2 → DerivativeWord2 m → Fin 2 → (F →L[ℝ] G)}
    (hK : ∀ β k', AVenhance.IsZ2Periodic (fun x => K x β k')) :
    AVenhance.IsZ2Periodic (fun x => -arrayOp (K x)) := by
  intro n x
  have hx : K (x + AVenhance.latticeShift n) = K x := by
    funext β k'
    exact hK β k' n x
  show -arrayOp (K (x + AVenhance.latticeShift n)) = -arrayOp (K x)
  rw [hx]

theorem measurable_arrayEntry {T : Type*} [MeasurableSpace T] [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ G] {f : T → (F →L[ℝ] G)} (hf : Measurable f)
    (β : DerivativeWord2 m) (k' : Fin 2) :
    Measurable (fun q => arrayEntryL (F := F) (G := G) m β k' (f q)) :=
  (arrayEntryL (F := F) (G := G) m β k').continuous.measurable.comp hf

theorem measurable_neg_arrayOp {T : Type*} [MeasurableSpace T] [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ G] {K : T → DerivativeWord2 m → Fin 2 → (F →L[ℝ] G)}
    (hK : ∀ β k', Measurable (fun q => K q β k')) :
    Measurable (fun q => -arrayOp (K q)) := by
  have h2 : Measurable (fun q => ∑ β : DerivativeWord2 m, ∑ k' : Fin 2,
      arrayEntryL (F := F) (G := G) m β k' (K q β k')) :=
    Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _ fun k' _ =>
      measurable_arrayEntry (hK β k') β k'
  exact h2.neg

/-- The jets of one placed entry are bounded by the jets of the entry. -/
theorem norm_iteratedFDeriv_arrayEntry_le (j : ℕ) {f : Vec 2 → (F →L[ℝ] G)}
    (hf : ContDiff ℝ (j : WithTop ℕ∞) f) (β : DerivativeWord2 m) (k' : Fin 2) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun x => arrayEntryL (F := F) (G := G) m β k' (f x)) x‖ ≤
      ‖iteratedFDeriv ℝ j f x‖ := by
  have hn := norm_arrayEntryL_le (F := F) (G := G) m β k'
  have hle := (arrayEntryL (F := F) (G := G) m β k').norm_iteratedFDeriv_comp_left (f := f)
    (x := x) hf.contDiffAt (n := j) le_rfl
  exact hle.trans ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans (one_mul _).le)

/-- The jets of a word-array operator are bounded by the jets of its entries. -/
theorem norm_iteratedFDeriv_neg_arrayOp_le (j : ℕ)
    {K : Vec 2 → DerivativeWord2 m → Fin 2 → (F →L[ℝ] G)}
    (hK : ∀ β k', ContDiff ℝ (j : WithTop ℕ∞) (fun x => K x β k')) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun x => -arrayOp (K x)) x‖ ≤
      ∑ β : DerivativeWord2 m, ∑ k' : Fin 2, ‖iteratedFDeriv ℝ j (fun x => K x β k') x‖ := by
  have hbk : ∀ (β : DerivativeWord2 m) (k' : Fin 2), ContDiff ℝ (j : WithTop ℕ∞)
      (fun x => arrayEntryL (F := F) (G := G) m β k' (K x β k')) := fun β k' =>
    contDiff_arrayEntry (hK β k') β k'
  have hb : ∀ β : DerivativeWord2 m, ContDiff ℝ (j : WithTop ℕ∞)
      (fun x => ∑ k' : Fin 2, arrayEntryL (F := F) (G := G) m β k' (K x β k')) := fun β =>
    ContDiff.sum fun k' _ => hbk β k'
  have e : (fun x => -arrayOp (K x)) = -(fun x => ∑ β : DerivativeWord2 m, ∑ k' : Fin 2,
      arrayEntryL (F := F) (G := G) m β k' (K x β k')) := rfl
  rw [e, iteratedFDeriv_neg_apply, norm_neg, iteratedFDeriv_fun_sum_apply
    (f := fun β x => ∑ k' : Fin 2, arrayEntryL (F := F) (G := G) m β k' (K x β k'))
    (fun β _ => (hb β).contDiffAt)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [iteratedFDeriv_fun_sum_apply
    (f := fun k' x => arrayEntryL (F := F) (G := G) m β k' (K x β k'))
    (fun k' _ => (hbk β k').contDiffAt)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' _ => ?_)
  exact norm_iteratedFDeriv_arrayEntry_le j (hK β k') β k' x

/-- The derivative array of an operator-valued coefficient is bounded by its jet. -/
theorem norm_coefficientDerivativeArray_le {E' F' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F'] (C : Vec 2 → E' →L[ℝ] F')
    (j : ℕ) (hC : ContDiff ℝ (j : WithTop ℕ∞) C) (x : Vec 2) :
    ‖coefficientDerivativeArray C j x‖ ≤ 2 ^ j * ‖iteratedFDeriv ℝ j C x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  calc ‖coefficientDerivativeArray C j x z‖
      ≤ ∑ w : DerivativeWord2 j, ‖coefficientDerivativeArray C j x z w‖ :=
        Weighted.finitePiLp_norm_le_sum _
    _ ≤ ∑ _w : DerivativeWord2 j, ‖iteratedFDeriv ℝ j C x‖ * ‖z‖ := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [coefficientDerivativeArray_apply]
        exact (ContinuousLinearMap.le_opNorm _ z).trans (mul_le_mul_of_nonneg_right
          (Weighted.orderedCoefficientDerivative_norm_le C j hC w x) (norm_nonneg z))
    _ = 2 ^ j * ‖iteratedFDeriv ℝ j C x‖ * ‖z‖ := by
        rw [Finset.sum_const, ChartTransport.card_derivativeWord2, nsmul_eq_mul]
        push_cast
        ring

/-- The derivative arrays of a word-array operator are bounded by the jets of its entries. -/
theorem norm_coefficientDerivativeArray_neg_arrayOp_le (j : ℕ)
    {K : Vec 2 → DerivativeWord2 m → Fin 2 → (F →L[ℝ] G)}
    (hK : ∀ β k', ContDiff ℝ (j : WithTop ℕ∞) (fun x => K x β k')) (x : Vec 2) :
    ‖coefficientDerivativeArray (fun x => -arrayOp (K x)) j x‖ ≤
      2 ^ j * ∑ β : DerivativeWord2 m, ∑ k' : Fin 2,
        ‖iteratedFDeriv ℝ j (fun x => K x β k') x‖ :=
  (norm_coefficientDerivativeArray_le _ j (contDiff_neg_arrayOp hK) x).trans
    (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_neg_arrayOp_le j hK x) (by positivity))
end

/-! Regularity of the glued kernels and of the Eulerian letters `ceLetter`, `adLetter`:
smoothness in the position, joint measurability in time and position, and `ℤ²`-periodicity
(the fields `AD_meas`, `AD_smooth`, `AD_per`, `CE_meas`, `CE_smooth`, `CE_per` of
`IsCoarseSetting`), and the jets of a glued kernel in terms of the jets of its pulse kernels. -/

section
/-- The inverse of a lattice-equivariant chart is lattice equivariant. -/
theorem label_latticeShift {chart label : Vec 2 → Vec 2}
    (hlc : ∀ y, label (chart y) = y) (hcl : ∀ x, chart (label x) = x)
    (hchart : ∀ (p : Fin 2 → ℤ) (y : Vec 2),
      chart (y + AVenhance.latticeShift p) = chart y + AVenhance.latticeShift p)
    (p : Fin 2 → ℤ) (x : Vec 2) :
    label (x + AVenhance.latticeShift p) = label x + AVenhance.latticeShift p := by
  have h := hchart p (label x)
  rw [hcl x] at h
  rw [← h, hlc]

section Generic

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem contDiff_gluedKernel (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) (M Kt : ℕ)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
    (L : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → G) (t : ℝ)
    (hchart : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (chart k t))
    (hlabel : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (label k t))
    (hL : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
        ContDiff ℝ (Kt : ℕ∞) (L k n d α l s))
    (m' : ℕ) (β : DerivativeWord2 m') (k' : Fin 2) :
    ContDiff ℝ (Kt : ℕ∞)
      (fun x => gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ L m' β k' t x) := by
  unfold gluedKernel
  refine ContDiff.sum fun k hk => ?_
  exact contDiff_pulseKernel c ρ εc M Kt (hchart k hk) (hlabel k hk)
    (fun n hn hnM d hd hdn α l => contDiff_windowLetter (ϖ k) c (s₀ k) (s₁ k) (L k n d α l) t
      (Kt : ℕ∞) (hL k hk n hn hnM d hd hdn α l)) m' β k'

theorem isZ2Periodic_gluedKernel (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) (M : ℕ)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
    (L : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → G) (t : ℝ)
    (hchart : ∀ k ∈ kset, ∀ (p : Fin 2 → ℤ) (y : Vec 2),
      chart k t (y + AVenhance.latticeShift p) = chart k t y + AVenhance.latticeShift p)
    (hlabel : ∀ k ∈ kset, ∀ (p : Fin 2 → ℤ) (x : Vec 2),
      label k t (x + AVenhance.latticeShift p) = label k t x + AVenhance.latticeShift p)
    (hL : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
        ∀ (p : Fin 2 → ℤ) (X : Vec 2),
          L k n d α l s (X + ρ⁻¹ • AVenhance.latticeShift p) = L k n d α l s X)
    (m' : ℕ) (β : DerivativeWord2 m') (k' : Fin 2) :
    AVenhance.IsZ2Periodic
      (fun x => gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ L m' β k' t x) := by
  intro p x
  show gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ L m' β k' t (x + AVenhance.latticeShift p) =
    gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ L m' β k' t x
  unfold gluedKernel
  refine Finset.sum_congr rfl fun k hk => ?_
  exact isZ2Periodic_pulseKernel c ρ εc M (hchart k hk) (hlabel k hk)
    (fun n hn hnM d hd hdn α l p X => windowLetter_periodic (ϖ k) c (s₀ k) (s₁ k)
      (L k n d α l) t (ρ⁻¹ • AVenhance.latticeShift p) X
      (fun s hs => hL k hk n hn hnM d hd hdn α l s hs p X)) m' β k' p x

/-- The jets of a glued kernel are bounded by the sum of the jets of its pulse kernels. -/
theorem norm_iteratedFDeriv_gluedKernel_le (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ)
    (M : ℕ) (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
    (L : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → G) (t : ℝ) (j : ℕ)
    (m' : ℕ) (β : DerivativeWord2 m') (k' : Fin 2) (x : Vec 2) (b : ℤ → ℝ)
    (hsm : ∀ k ∈ kset, ContDiff ℝ (j : WithTop ℕ∞)
      (pulseKernel c ρ εc M (chart k t) (label k t)
        (fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k) (L k n d α l) t) m' β k'))
    (hb : ∀ k ∈ kset, ‖iteratedFDeriv ℝ j (pulseKernel c ρ εc M (chart k t) (label k t)
      (fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k) (L k n d α l) t) m' β k') x‖ ≤ b k) :
    ‖iteratedFDeriv ℝ j
      (fun x => gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ L m' β k' t x) x‖ ≤
        ∑ k ∈ kset, b k := by
  have e : (fun x => gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ L m' β k' t x) =
      fun x => ∑ k ∈ kset, pulseKernel c ρ εc M (chart k t) (label k t)
        (fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k) (L k n d α l) t) m' β k' x := rfl
  rw [e, iteratedFDeriv_fun_sum_apply (f := fun k => pulseKernel c ρ εc M (chart k t)
    (label k t) (fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k) (L k n d α l) t) m' β k')
    (fun k hk => (hsm k hk).contDiffAt)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum hb)

end Generic

/-! ### The letters -/

section Letters

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem measurable_jmEntry (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hJm : ∀ i j, Measurable fun t => Jm t i j) (m : ℕ) (β : DerivativeWord2 m) (k' : Fin 2) :
    Measurable (fun t => jmEntry Jm t m β k') := by
  by_cases hm : m = 1
  · subst hm
    simp only [jmEntry_one]
    exact hJm k' (β 0)
  · simp only [jmEntry_of_ne Jm _ hm]
    exact measurable_const

/-- The scalar entries of the diagonal letter, as operators on `ℝ`. -/
theorem contDiff_adEntry {n : WithTop ℕ∞} {f : Vec 2 → ℝ} (hf : ContDiff ℝ n f) (a : ℝ) :
    ContDiff ℝ n (fun x => (f x + a) • ContinuousLinearMap.id ℝ ℝ) :=
  (hf.add contDiff_const).smul contDiff_const

theorem measurable_adEntry {T : Type*} [MeasurableSpace T] {f g : T → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun q => (f q + g q) • ContinuousLinearMap.id ℝ ℝ) :=
  (continuous_id.smul continuous_const :
    Continuous fun s : ℝ => s • ContinuousLinearMap.id ℝ ℝ).measurable.comp (hf.add hg)

end Letters
end

/-! Regularity of the Eulerian letters `adLetter` and `ceLetter`: `C^{Kt}` in the position,
jointly measurable in time and position, and `ℤ²`-periodic (the fields `AD_smooth`, `AD_meas`,
`AD_per`, `CE_smooth`, `CE_meas`, `CE_per` of `IsCoarseSetting`). -/

section
/-- Restriction of a jointly measurable function to a time window. -/
theorem measurable_window {G : Type*} [MeasurableSpace G] (T₀ T₁ : ℝ) {f : ℝ × Vec 2 → G}
    (hf : Measurable f) : Measurable (fun q : Set.Icc T₀ T₁ × Vec 2 => f ((q.1 : ℝ), q.2)) :=
  hf.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

/-- A measurable function of time, on a time window times the plane. -/
theorem measurable_window_time {G : Type*} [MeasurableSpace G] (T₀ T₁ : ℝ) {g : ℝ → G}
    (hg : Measurable g) : Measurable (fun q : Set.Icc T₀ T₁ × Vec 2 => g (q.1 : ℝ)) :=
  hg.comp (measurable_subtype_coe.comp measurable_fst)

/-! ### The diagonal letters -/

section Diagonal

variable (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) (M : ℕ)
  (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
  (Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ)
  (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)

theorem contDiff_adLetter (Kt : ℕ) (d : Finset.Icc 2 M) (t : ℝ)
    (hchart : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (chart k t))
    (hlabel : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (label k t))
    (hscC : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d', 2 ≤ d' → d' ≤ n →
      ∀ (α : DerivativeWord2 (d' - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
        ContDiff ℝ (Kt : ℕ∞) (Lsc k n d' α l s)) :
    ContDiff ℝ (Kt : ℕ∞) (adLetter kset ϖ c ρ εc M chart label s₀ s₁ Lsc Jm d t) := by
  have hK : ∀ (β : DerivativeWord2 (d.1 - 1)) (k' : Fin 2), ContDiff ℝ (Kt : ℕ∞)
      (fun x => (gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc (d.1 - 1) β k' t x +
        jmEntry Jm t (d.1 - 1) β k') • ContinuousLinearMap.id ℝ ℝ) := fun β k' =>
    contDiff_adEntry (contDiff_gluedKernel kset ϖ c ρ εc M Kt chart label s₀ s₁ Lsc t hchart
      hlabel hscC (d.1 - 1) β k') (jmEntry Jm t (d.1 - 1) β k')
  exact contDiff_neg_arrayOp hK

theorem measurable_adLetter (T₀ T₁ : ℝ) (d : Finset.Icc 2 M)
    (hJm : ∀ i j, Measurable fun t => Jm t i j) (hϖ : ∀ k ∈ kset, Measurable (ϖ k))
    (hchart : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => chart k q.1 q.2))
    (hlabel : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => label k q.1 q.2))
    (hscM : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d', 2 ≤ d' → d' ≤ n →
      ∀ (α : DerivativeWord2 (d' - 1)) (l : Fin 2) (X : Vec 2),
        Measurable (fun s : Set.Icc (s₀ k) (s₁ k) => Lsc k n d' α l s X))
    (hscC : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d', 2 ≤ d' → d' ≤ n →
      ∀ (α : DerivativeWord2 (d' - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
        Continuous (Lsc k n d' α l s)) :
    Measurable fun q : Set.Icc T₀ T₁ × Vec 2 =>
      adLetter kset ϖ c ρ εc M chart label s₀ s₁ Lsc Jm d q.1 q.2 := by
  have hK : ∀ (β : DerivativeWord2 (d.1 - 1)) (k' : Fin 2),
      Measurable (fun q : Set.Icc T₀ T₁ × Vec 2 =>
        (gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc (d.1 - 1) β k' (q.1 : ℝ) q.2 +
          jmEntry Jm (q.1 : ℝ) (d.1 - 1) β k') • ContinuousLinearMap.id ℝ ℝ) := by
    intro β k'
    have h1 : Measurable (fun q : Set.Icc T₀ T₁ × Vec 2 =>
        gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc (d.1 - 1) β k' (q.1 : ℝ) q.2) :=
      measurable_window T₀ T₁ (measurable_gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc hϖ
        hchart hlabel hscM hscC (d.1 - 1) β k')
    have h2 : Measurable (fun q : Set.Icc T₀ T₁ × Vec 2 =>
        jmEntry Jm (q.1 : ℝ) (d.1 - 1) β k') :=
      measurable_window_time T₀ T₁ (measurable_jmEntry Jm hJm (d.1 - 1) β k')
    exact measurable_adEntry h1 h2
  exact measurable_neg_arrayOp hK

theorem isZ2Periodic_adLetter (d : Finset.Icc 2 M) (t : ℝ)
    (hchart : ∀ k ∈ kset, ∀ (p : Fin 2 → ℤ) (y : Vec 2),
      chart k t (y + AVenhance.latticeShift p) = chart k t y + AVenhance.latticeShift p)
    (hlabel : ∀ k ∈ kset, ∀ (p : Fin 2 → ℤ) (x : Vec 2),
      label k t (x + AVenhance.latticeShift p) = label k t x + AVenhance.latticeShift p)
    (hscP : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d', 2 ≤ d' → d' ≤ n →
      ∀ (α : DerivativeWord2 (d' - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
        ∀ (p : Fin 2 → ℤ) (X : Vec 2),
          Lsc k n d' α l s (X + ρ⁻¹ • AVenhance.latticeShift p) = Lsc k n d' α l s X) :
    AVenhance.IsZ2Periodic (adLetter kset ϖ c ρ εc M chart label s₀ s₁ Lsc Jm d t) := by
  have hK : ∀ (β : DerivativeWord2 (d.1 - 1)) (k' : Fin 2), AVenhance.IsZ2Periodic
      (fun x => (gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc (d.1 - 1) β k' t x +
        jmEntry Jm t (d.1 - 1) β k') • ContinuousLinearMap.id ℝ ℝ) := by
    intro β k' p x
    have hper : gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc (d.1 - 1) β k' t
        (x + AVenhance.latticeShift p) =
        gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc (d.1 - 1) β k' t x :=
      isZ2Periodic_gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc t hchart hlabel hscP
        (d.1 - 1) β k' p x
    show (gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ Lsc (d.1 - 1) β k' t
        (x + AVenhance.latticeShift p) + jmEntry Jm t (d.1 - 1) β k') •
          ContinuousLinearMap.id ℝ ℝ = _
    rw [hper]
  exact isZ2Periodic_neg_arrayOp hK

end Diagonal

/-! ### The edge letters -/

section Edge

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) (M : ℕ)
  (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ) (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)

theorem contDiff_ceLetter (Kt : ℕ) (r : ℕ) (v u : ι) (d : Finset.Icc 2 M) (t : ℝ)
    (hchart : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (chart k t))
    (hlabel : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (label k t))
    (hLbC : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d', 2 ≤ d' → d' ≤ n →
      ∀ (α : DerivativeWord2 (d' - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
        ContDiff ℝ (Kt : ℕ∞) (fun X => Lb k r n d' α s X l v u)) :
    ContDiff ℝ (Kt : ℕ∞) (ceLetter kset ϖ c ρ εc M chart label s₀ s₁ Lb r v u d t) := by
  have hK : ∀ (β : DerivativeWord2 (d.1 - 1)) (k' : Fin 2), ContDiff ℝ (Kt : ℕ∞)
      (fun x => gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ (entryLetter Lb r v u)
        (d.1 - 1) β k' t x) := fun β k' =>
    contDiff_gluedKernel kset ϖ c ρ εc M Kt chart label s₀ s₁ (entryLetter Lb r v u) t hchart
      hlabel (fun k hk n hn hnM d' hd hdn α l s hs => hLbC k hk n hn hnM d' hd hdn α l s hs)
      (d.1 - 1) β k'
  exact contDiff_neg_arrayOp hK

theorem measurable_ceLetter [∀ i, FiniteDimensional ℝ (h i)] (T₀ T₁ : ℝ) (r : ℕ) (v u : ι)
    (d : Finset.Icc 2 M) (hϖ : ∀ k ∈ kset, Measurable (ϖ k))
    (hchart : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => chart k q.1 q.2))
    (hlabel : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => label k q.1 q.2))
    (hLbM : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d', 2 ≤ d' → d' ≤ n →
      ∀ (α : DerivativeWord2 (d' - 1)) (l : Fin 2) (X : Vec 2),
        Measurable (fun s : Set.Icc (s₀ k) (s₁ k) => Lb k r n d' α s X l v u))
    (hLbC : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d', 2 ≤ d' → d' ≤ n →
      ∀ (α : DerivativeWord2 (d' - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
        Continuous (fun X => Lb k r n d' α s X l v u)) :
    Measurable fun q : Set.Icc T₀ T₁ × Vec 2 =>
      ceLetter kset ϖ c ρ εc M chart label s₀ s₁ Lb r v u d q.1 q.2 := by
  have hK : ∀ (β : DerivativeWord2 (d.1 - 1)) (k' : Fin 2),
      Measurable (fun q : Set.Icc T₀ T₁ × Vec 2 =>
        gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ (entryLetter Lb r v u) (d.1 - 1) β k'
          (q.1 : ℝ) q.2) := fun β k' =>
    measurable_window T₀ T₁ (measurable_gluedKernel kset ϖ c ρ εc M chart label s₀ s₁
      (entryLetter Lb r v u) hϖ hchart hlabel
      (fun k hk n hn hnM d' hd hdn α l X => hLbM k hk n hn hnM d' hd hdn α l X)
      (fun k hk n hn hnM d' hd hdn α l s hs => hLbC k hk n hn hnM d' hd hdn α l s hs)
      (d.1 - 1) β k')
  exact measurable_neg_arrayOp hK

theorem isZ2Periodic_ceLetter (r : ℕ) (v u : ι) (d : Finset.Icc 2 M) (t : ℝ)
    (hchart : ∀ k ∈ kset, ∀ (p : Fin 2 → ℤ) (y : Vec 2),
      chart k t (y + AVenhance.latticeShift p) = chart k t y + AVenhance.latticeShift p)
    (hlabel : ∀ k ∈ kset, ∀ (p : Fin 2 → ℤ) (x : Vec 2),
      label k t (x + AVenhance.latticeShift p) = label k t x + AVenhance.latticeShift p)
    (hLbP : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d', 2 ≤ d' → d' ≤ n →
      ∀ (α : DerivativeWord2 (d' - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
        ∀ (p : Fin 2 → ℤ) (X : Vec 2),
          Lb k r n d' α s (X + ρ⁻¹ • AVenhance.latticeShift p) l v u = Lb k r n d' α s X l v u) :
    AVenhance.IsZ2Periodic (ceLetter kset ϖ c ρ εc M chart label s₀ s₁ Lb r v u d t) := by
  have hK : ∀ (β : DerivativeWord2 (d.1 - 1)) (k' : Fin 2), AVenhance.IsZ2Periodic
      (fun x => gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ (entryLetter Lb r v u)
        (d.1 - 1) β k' t x) := fun β k' =>
    isZ2Periodic_gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ (entryLetter Lb r v u) t hchart
      hlabel (fun k hk n hn hnM d' hd hdn α l s hs p X =>
        hLbP k hk n hn hnM d' hd hdn α l s hs p X) (d.1 - 1) β k'
  exact isZ2Periodic_neg_arrayOp hK

end Edge
end

/-! The entrywise transfer bound for the Eulerian edge letters: an entrywise envelope `M λ^{n-d+i}` of the
chart-frame letters gives
`‖∇^j CE_{vu,d'}‖ ≤ C M (∑_k |ϖ_k|) ∑_{n ≥ d'} c⁻¹ (ε_c ρ)^n Rχ^{-(n+j-d')}`. -/

/-- Outside the lift window of the pulse, the pulse kernel of the windowed letters vanishes. -/
theorem pulseKernel_of_notMem {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c ρ εc : ℝ) (M : ℕ) (chart label : Vec 2 → Vec 2) (ϖ : ℝ → ℝ) (s₀ s₁ : ℝ)
    (L : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → G) {t : ℝ}
    (ht : c⁻¹ * t ∉ Set.Icc s₀ s₁) (m' : ℕ) (β : DerivativeWord2 m') (k' : Fin 2) :
    pulseKernel c ρ εc M chart label
      (fun n d α l => windowLetter ϖ c s₀ s₁ (L n d α l) t) m' β k' = fun _ => 0 := by
  funext x
  simp only [pulseKernel, windowLetter_of_notMem _ ht, smul_zero, Finset.sum_const_zero]

/-- **Transfer bound for the edge letters.** -/
theorem ceLetter_transfer (N D Kt : ℕ) (Cχ : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, NormedSpace ℝ (h i)] (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc lam Rχ : ℝ)
      (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ) (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
      (r : ℕ) (v u : ι) (Mb : ℝ) (t : ℝ),
      0 < c → 0 < ρ → 0 ≤ εc → 0 < Rχ → lam = ρ / Rχ → 0 ≤ Mb →
      (∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (chart k t)) →
      (∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (label k t)) →
      (∀ k ∈ kset, c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) → ∀ p, 1 ≤ p → p ≤ Kt + N + D → ∀ y,
        ‖iteratedFDeriv ℝ p (chart k t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1) ∧
        ‖iteratedFDeriv ℝ p (label k t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1)) →
      (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
          ContDiff ℝ (Kt : ℕ∞) (fun X => Lb k r n d α s X k₀ v u)) →
      (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2), ∀ i, i ≤ Kt →
          ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
            ‖iteratedFDeriv ℝ i (fun X' => Lb k r n d α s X' k₀ v u) X‖ ≤
              Mb * lam ^ (n - d + i)) →
      ∀ (d : Finset.Icc 2 (N + D)) (j : ℕ), j ≤ Kt → ∀ x,
        ‖coefficientDerivativeArray
            (ceLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lb r v u d t) j x‖ ≤
          C * Mb * (∑ k ∈ kset, |ϖ k t|) *
            ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1) := by
  obtain ⟨C₀, hC₀, hbound⟩ := pulseKernel_jet_bound (N + D) Kt
    (1 + ∑ p ∈ Finset.range (Kt + (N + D) + 1), |Cχ p|)
    (ChartTransport.one_le_jetConst Cχ (Kt + (N + D)))
  refine ⟨2 ^ Kt * (2 ^ (N + D) * 2) * C₀, by positivity, ?_⟩
  intro ι h _ _ kset ϖ c ρ εc lam Rχ chart label s₀ s₁ Lb r v u Mb t hc hρ hεc hRχ hlam hMb
    hchart hlabel hjets hLbC hLjet d j hj x
  have hlam0 : 0 < lam := by
    rw [hlam]
    exact div_pos hρ hRχ
  have hd2 := Finset.mem_Icc.1 d.2
  -- the chart jets, in the normalized form
  have hJBc : ∀ k ∈ kset, c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) →
      ChartTransport.JetBound (chart k t) (Kt + (N + D))
        (1 + ∑ p ∈ Finset.range (Kt + (N + D) + 1), |Cχ p|) Rχ := fun k hk hwin =>
    ChartTransport.jetBound_of_Cχ hRχ fun p hp1 hpN y => (hjets k hk hwin p hp1 (by omega) y).1
  have hJBl : ∀ k ∈ kset, c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) →
      ChartTransport.JetBound (label k t) (Kt + (N + D))
        (1 + ∑ p ∈ Finset.range (Kt + (N + D) + 1), |Cχ p|) Rχ := fun k hk hwin =>
    ChartTransport.jetBound_of_Cχ hRχ fun p hp1 hpN y => (hjets k hk hwin p hp1 (by omega) y).2
  -- the windowed letters of one pulse
  have hWC : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d', 2 ≤ d' → d' ≤ n →
      ∀ (α : DerivativeWord2 (d' - 1)) (l : Fin 2), ContDiff ℝ (Kt : ℕ∞)
        (windowLetter (ϖ k) c (s₀ k) (s₁ k) (entryLetter Lb r v u k n d' α l) t) :=
    fun k hk n hn hnM d' hd hdn α l =>
      contDiff_windowLetter (ϖ k) c (s₀ k) (s₁ k) (entryLetter Lb r v u k n d' α l) t (Kt : ℕ∞)
        (fun s hs => hLbC k hk n hn hnM d' hd hdn α l s hs)
  have hWJ : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d', 2 ≤ d' → d' ≤ n →
      ∀ (α : DerivativeWord2 (d' - 1)) (l : Fin 2), ∀ i, i ≤ Kt → ∀ X,
        ‖iteratedFDeriv ℝ i
          (windowLetter (ϖ k) c (s₀ k) (s₁ k) (entryLetter Lb r v u k n d' α l) t) X‖ ≤
            |ϖ k t| * Mb * lam ^ (n - d' + i) := by
    intro k hk n hn hnM d' hd hdn α l i hi X
    have h1 := norm_iteratedFDeriv_windowLetter_le (ϖ k) c (s₀ k) (s₁ k)
      (entryLetter Lb r v u k n d' α l) t i X (Mb * lam ^ (n - d' + i))
      (mul_nonneg hMb (pow_nonneg hlam0.le _))
      (fun s hs => hLjet k hk n hn hnM d' hd hdn α l i hi s hs X)
    calc _ ≤ |ϖ k t| * (Mb * lam ^ (n - d' + i)) := h1
      _ = |ϖ k t| * Mb * lam ^ (n - d' + i) := by ring
  have hpk : ∀ k ∈ kset, ∀ (β : DerivativeWord2 (d.1 - 1)) (k' : Fin 2), ContDiff ℝ (Kt : ℕ∞)
      (pulseKernel c ρ εc (N + D) (chart k t) (label k t)
        (fun n d' α l => windowLetter (ϖ k) c (s₀ k) (s₁ k)
          (entryLetter Lb r v u k n d' α l) t) (d.1 - 1) β k') := fun k hk β k' =>
    contDiff_pulseKernel c ρ εc (N + D) Kt (hchart k hk) (hlabel k hk)
      (fun n hn hnM d' hd hdn α l => hWC k hk n hn hnM d' hd hdn α l) (d.1 - 1) β k'
  have hjK : ((j : ℕ) : WithTop ℕ∞) ≤ ((Kt : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hj
  have hS0 : 0 ≤ ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (mul_nonneg (inv_nonneg.2 hc.le)
      (pow_nonneg (mul_nonneg hεc hρ.le) _)) (pow_nonneg (inv_nonneg.2 hRχ.le) _)
  -- one entry
  have hentry : ∀ (β : DerivativeWord2 (d.1 - 1)) (k' : Fin 2),
      ‖iteratedFDeriv ℝ j (fun x => gluedKernel kset ϖ c ρ εc (N + D) chart label s₀ s₁
        (entryLetter Lb r v u) (d.1 - 1) β k' t x) x‖ ≤
      C₀ * Mb * (∑ k ∈ kset, |ϖ k t|) *
        ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1) := by
    intro β k'
    have hb := norm_iteratedFDeriv_gluedKernel_le kset ϖ c ρ εc (N + D) chart label s₀ s₁
      (entryLetter Lb r v u) t j (d.1 - 1) β k' x
      (fun k => C₀ * (|ϖ k t| * Mb) *
        ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1))
      (fun k hk => (hpk k hk β k').of_le hjK)
      (fun k hk => by
        by_cases hwin : c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k)
        · exact hbound c ρ εc Rχ lam (|ϖ k t| * Mb) (chart k t) (label k t)
            (fun n d' α l => windowLetter (ϖ k) c (s₀ k) (s₁ k)
              (entryLetter Lb r v u k n d' α l) t)
            hc hρ hεc hRχ hlam (mul_nonneg (abs_nonneg _) hMb) (hchart k hk) (hlabel k hk)
            (hJBc k hk hwin) (hJBl k hk hwin)
            (fun n hn hnM d' hd hdn α l => hWC k hk n hn hnM d' hd hdn α l)
            (fun n hn hnM d' hd hdn α l i hi X => hWJ k hk n hn hnM d' hd hdn α l i hi X)
            d.1 hd2.1 hd2.2 β k' j hj x
        · rw [pulseKernel_of_notMem c ρ εc (N + D) (chart k t) (label k t) (ϖ k) (s₀ k) (s₁ k)
            (entryLetter Lb r v u k) hwin (d.1 - 1) β k', iteratedFDeriv_fun_zero,
            Pi.zero_apply, norm_zero]
          exact mul_nonneg (mul_nonneg hC₀ (mul_nonneg (abs_nonneg _) hMb)) hS0)
    refine hb.trans (le_of_eq ?_)
    have hk : ∀ k : ℤ, C₀ * (|ϖ k t| * Mb) *
        ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1) =
        (C₀ * Mb * ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1)) *
          |ϖ k t| := fun k => by ring
    rw [Finset.sum_congr rfl fun k _ => hk k, ← Finset.mul_sum]
    ring
  have hK : ∀ (β : DerivativeWord2 (d.1 - 1)) (k' : Fin 2), ContDiff ℝ (j : WithTop ℕ∞)
      (fun x => gluedKernel kset ϖ c ρ εc (N + D) chart label s₀ s₁
        (entryLetter Lb r v u) (d.1 - 1) β k' t x) := fun β k' =>
    (contDiff_gluedKernel kset ϖ c ρ εc (N + D) Kt chart label s₀ s₁ (entryLetter Lb r v u) t
      hchart hlabel (fun k hk n hn hnM d' hd hdn α l s hs => hLbC k hk n hn hnM d' hd hdn α l s hs)
      (d.1 - 1) β k').of_le hjK
  have h1 := norm_coefficientDerivativeArray_neg_arrayOp_le
    (K := fun x β k' => gluedKernel kset ϖ c ρ εc (N + D) chart label s₀ s₁
      (entryLetter Lb r v u) (d.1 - 1) β k' t x) j hK x
  refine h1.trans ?_
  have hX : 0 ≤ C₀ * Mb * (∑ k ∈ kset, |ϖ k t|) *
      ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₀ hMb)
      (Finset.sum_nonneg fun k _ => abs_nonneg _)) hS0
  have h2j : (2 : ℝ) ^ j ≤ 2 ^ Kt := pow_le_pow_right₀ (by norm_num) hj
  have h2d : (2 : ℝ) ^ (d.1 - 1) ≤ 2 ^ (N + D) := pow_le_pow_right₀ (by norm_num) (by omega)
  calc 2 ^ j * ∑ β : DerivativeWord2 (d.1 - 1), ∑ k' : Fin 2,
        ‖iteratedFDeriv ℝ j (fun x => gluedKernel kset ϖ c ρ εc (N + D) chart label s₀ s₁
          (entryLetter Lb r v u) (d.1 - 1) β k' t x) x‖
      ≤ 2 ^ j * ∑ _β : DerivativeWord2 (d.1 - 1), ∑ _k' : Fin 2,
          (C₀ * Mb * (∑ k ∈ kset, |ϖ k t|) *
            ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun k' _ =>
          hentry β k') (by positivity)
    _ = 2 ^ j * (2 ^ (d.1 - 1) * 2) * (C₀ * Mb * (∑ k ∈ kset, |ϖ k t|) *
          ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1)) := by
        rw [Finset.sum_const, Finset.sum_const, ChartTransport.card_derivativeWord2,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 2 ^ Kt * (2 ^ (N + D) * 2) * (C₀ * Mb * (∑ k ∈ kset, |ϖ k t|) *
          ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h2j
          (mul_le_mul_of_nonneg_right h2d (by norm_num)) (by positivity) (by positivity)) hX
    _ = 2 ^ Kt * (2 ^ (N + D) * 2) * C₀ * Mb * (∑ k ∈ kset, |ϖ k t|) *
          ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1) := by ring

end AVRegularity.CycleComparison.ActualMeans
end
