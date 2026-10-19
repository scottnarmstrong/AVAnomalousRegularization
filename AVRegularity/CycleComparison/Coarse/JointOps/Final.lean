-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Coarse.Meas.Pairing
public import AVRegularity.Statements.Intermediate.CycleComparison.CovPolyQ
public import AVRegularity.Statements.Intermediate.CycleComparison.CoarseFluxAdjoint

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse.JointOps

/-! Jointly measurable `C^r` families of fields, and the closure of the class under coordinate
derivatives, derivative words and the covariance operator and polynomials.

`JMF t₀ t₁ r Φ` says that `Φ` is jointly Borel measurable on `Set.Icc t₀ t₁ × Vec 2` and each
window slice `Φ s` is `C^r`. The lemmas track the order `r`. -/

section
/-- Jointly measurable family with `C^r` window slices. -/
def JMF {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (t₀ t₁ : ℝ) (r : ℕ) (Φ : ℝ → Vec 2 → F) : Prop :=
  JointlyMeas t₀ t₁ Φ ∧ ∀ s ∈ Set.Icc t₀ t₁, ContDiff ℝ (r : ℕ∞) (Φ s)

namespace JMF

variable {t₀ t₁ : ℝ} {r : ℕ}

section Basic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {Φ Ψ : ℝ → Vec 2 → F}

omit [FiniteDimensional ℝ F] [BorelSpace F] in
theorem mono {r' : ℕ} (h : JMF t₀ t₁ r' Φ) (hr : r ≤ r') : JMF t₀ t₁ r Φ :=
  ⟨h.1, fun s hs => (h.2 s hs).of_le (by exact_mod_cast hr)⟩

omit [FiniteDimensional ℝ F] [BorelSpace F] in
theorem continuous (h : JMF t₀ t₁ r Φ) {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) : Continuous (Φ s) :=
  (h.2 s hs).continuous

omit [FiniteDimensional ℝ F] [BorelSpace F] in
theorem const (c : F) : JMF t₀ t₁ r fun _ _ => c :=
  ⟨JointlyMeas.const c, fun _ _ => contDiff_const⟩

omit [FiniteDimensional ℝ F] in
/-- A time-independent smooth field. -/
theorem of_contDiff {φ : Vec 2 → F} (h : ContDiff ℝ (⊤ : ℕ∞) φ) : JMF t₀ t₁ r fun _ x => φ x :=
  ⟨JointlyMeas.of_continuous h.continuous, fun _ _ => h.of_le (by exact_mod_cast le_top)⟩

theorem add (hΦ : JMF t₀ t₁ r Φ) (hΨ : JMF t₀ t₁ r Ψ) : JMF t₀ t₁ r fun s x => Φ s x + Ψ s x :=
  ⟨hΦ.1.add hΨ.1, fun s hs => (hΦ.2 s hs).add (hΨ.2 s hs)⟩

theorem sub (hΦ : JMF t₀ t₁ r Φ) (hΨ : JMF t₀ t₁ r Ψ) : JMF t₀ t₁ r fun s x => Φ s x - Ψ s x :=
  ⟨hΦ.1.sub hΨ.1, fun s hs => (hΦ.2 s hs).sub (hΨ.2 s hs)⟩

omit [FiniteDimensional ℝ F] in
theorem neg (hΦ : JMF t₀ t₁ r Φ) : JMF t₀ t₁ r fun s x => -Φ s x :=
  ⟨hΦ.1.neg, fun s hs => (hΦ.2 s hs).neg⟩

theorem sum {ι : Type*} (S : Finset ι) {Ψ : ι → ℝ → Vec 2 → F}
    (h : ∀ i ∈ S, JMF t₀ t₁ r (Ψ i)) : JMF t₀ t₁ r fun s x => ∑ i ∈ S, Ψ i s x :=
  ⟨JointlyMeas.sum S fun i hi => (h i hi).1,
    fun s hs => ContDiff.sum fun i hi => (h i hi).2 s hs⟩

/-- Real scalar multiples by a function of time which is measurable on the window. -/
theorem smul_time {c : ℝ → ℝ} (hc : Measurable fun s : Set.Icc t₀ t₁ => c s)
    (hΦ : JMF t₀ t₁ r Φ) : JMF t₀ t₁ r fun s x => c s • Φ s x :=
  ⟨hΦ.1.smul hc, fun s hs => (hΦ.2 s hs).const_smul _⟩

/-- Nonzero-order coordinate derivative: `r + 1 → r`. -/
theorem dbasis (hΦ : JMF t₀ t₁ (r + 1) Φ) (i : Fin 2) :
    JMF t₀ t₁ r fun s x => fderiv ℝ (Φ s) x (basisVec i) := by
  refine ⟨JointlyMeas.fderiv_basis hΦ.1
    (fun s hs => (hΦ.2 s hs).differentiable (by exact_mod_cast Nat.succ_ne_zero r)) i,
    fun s hs => ?_⟩
  have := (hΦ.2 s hs).fderiv_right (m := (r : ℕ∞)) (by exact_mod_cast le_refl (r + 1))
  exact this.clm_apply contDiff_const

/-- Derivative along a list of directions, innermost last. -/
theorem foldr_word (l : List (Fin 2)) :
    ∀ (r : ℕ) (Φ : ℝ → Vec 2 → F), JMF t₀ t₁ (r + l.length) Φ →
      JMF t₀ t₁ r fun s => l.foldr (fun i g' => fun x => fderiv ℝ g' x (basisVec i)) (Φ s) := by
  induction l with
  | nil => intro r Φ h; simpa using h
  | cons i l ih =>
    intro r Φ h
    have h1 := ih (r + 1) Φ (h.mono (by simp only [List.length_cons]; omega))
    exact h1.dbasis i

theorem word {m : ℕ} (α : DerivativeWord2 m) (hΦ : JMF t₀ t₁ (r + m) Φ) :
    JMF t₀ t₁ r fun s => AVRegularity.orderedDerivativeRev α (Φ s) := by
  have := foldr_word (List.ofFn α) r Φ (by simpa using hΦ)
  exact this

end Basic

section Cov

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {Φ : ℝ → Vec 2 → F}
  {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ}

/-- The covariance operator, `r + 2 → r`, for window-measurable matrix entries. -/
theorem cov_op (hH : ∀ i j, Measurable fun s : Set.Icc t₀ t₁ => Hc s i j)
    (hΦ : JMF t₀ t₁ (r + 2) Φ) :
    JMF t₀ t₁ r fun s => AVRegularity.covOperator (Hc s) (Φ s) := by
  unfold AVRegularity.covOperator
  have : ∀ i j : Fin 2, JMF t₀ t₁ r fun s x =>
      Hc s i j • fderiv ℝ (fun y => fderiv ℝ (Φ s) y (basisVec j)) x (basisVec i) :=
    fun i j => ((hΦ.dbasis j).dbasis i).smul_time (hH i j)
  exact JMF.sum _ fun i _ => JMF.sum _ fun j _ => this i j

/-- Iterates of the covariance operator, `r + 2 l → r`. -/
theorem cov_iter (hH : ∀ i j, Measurable fun s : Set.Icc t₀ t₁ => Hc s i j) :
    ∀ (l r : ℕ) (Φ : ℝ → Vec 2 → F), JMF t₀ t₁ (r + 2 * l) Φ →
      JMF t₀ t₁ r fun s => (AVRegularity.covOperator (Hc s))^[l] (Φ s) := by
  intro l
  induction l with
  | zero => intro r Φ h; simpa using h
  | succ l ih =>
    intro r Φ h
    have h1 : JMF t₀ t₁ (r + 2 * l) fun s => AVRegularity.covOperator (Hc s) (Φ s) :=
      cov_op hH (h.mono (by omega))
    exact ih r _ h1

theorem cov_polyP (hH : ∀ i j, Measurable fun s : Set.Icc t₀ t₁ => Hc s i j) (p : ℕ)
    (hΦ : JMF t₀ t₁ (r + 2 * p) Φ) :
    JMF t₀ t₁ r fun s => AVRegularity.covPolyP (Hc s) p (Φ s) := by
  unfold AVRegularity.covPolyP
  have h : JMF t₀ t₁ r fun s x => ∑ l ∈ Finset.range (p + 1),
      ((l.factorial : ℝ)⁻¹) • (AVRegularity.covOperator (Hc s))^[l] (Φ s) x := by
    refine JMF.sum _ fun l hl => ?_
    have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have := cov_iter hH l r Φ (hΦ.mono (by omega))
    exact ⟨this.1.smul measurable_const, fun s hs => (this.2 s hs).const_smul _⟩
  convert h using 2 with s
  funext x
  simp [Finset.sum_apply]

theorem cov_polyQ (hH : ∀ i j, Measurable fun s : Set.Icc t₀ t₁ => Hc s i j) (p : ℕ)
    (hΦ : JMF t₀ t₁ (r + 2 * p) Φ) :
    JMF t₀ t₁ r fun s => AVRegularity.covPolyQ (Hc s) p (Φ s) := by
  unfold AVRegularity.covPolyQ
  have h : JMF t₀ t₁ r fun s x => ∑ l ∈ Finset.range (p + 1),
      (((-1 : ℝ) ^ l / (l.factorial : ℝ))) • (AVRegularity.covOperator (Hc s))^[l] (Φ s) x := by
    refine JMF.sum _ fun l hl => ?_
    have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have := cov_iter hH l r Φ (hΦ.mono (by omega))
    exact ⟨this.1.smul measurable_const, fun s hs => (this.2 s hs).const_smul _⟩
  convert h using 2 with s
  funext x
  simp [Finset.sum_apply]

end Cov

end JMF
end

/-! Jointly measurable `C^r` families: multiplication by coefficients, the adjoint of `CLM`
coefficients, the commutator adjoint, the word adjoint and the flux adjoints. -/

section
namespace JMF

variable {t₀ t₁ : ℝ} {r : ℕ}

section Comp

variable {G F H : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G]
  [BorelSpace G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
  [BorelSpace F]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H]
  [BorelSpace H]

omit [FiniteDimensional ℝ G] [FiniteDimensional ℝ H] in
/-- Composition with a smooth map. -/
theorem comp₁ {Φ : ℝ → Vec 2 → G} (L : G → H) (hL : ContDiff ℝ (⊤ : ℕ∞) L)
    (h : JMF t₀ t₁ r Φ) : JMF t₀ t₁ r fun s x => L (Φ s x) :=
  ⟨hL.continuous.measurable.comp h.1, fun s hs =>
    (hL.of_le (by exact_mod_cast le_top)).comp (h.2 s hs)⟩

omit [FiniteDimensional ℝ G] [FiniteDimensional ℝ H] in
/-- Composition with a smooth map of two arguments. -/
theorem comp₂ {Φ : ℝ → Vec 2 → G} {Ψ : ℝ → Vec 2 → F} (Λ : G → F → H)
    (hΛ : ContDiff ℝ (⊤ : ℕ∞) fun p : G × F => Λ p.1 p.2)
    (h₁ : JMF t₀ t₁ r Φ) (h₂ : JMF t₀ t₁ r Ψ) : JMF t₀ t₁ r fun s x => Λ (Φ s x) (Ψ s x) :=
  ⟨hΛ.continuous.measurable.comp (h₁.1.prodMk h₂.1), fun s hs =>
    (hΛ.of_le (by exact_mod_cast le_top)).comp ((h₁.2 s hs).prodMk (h₂.2 s hs))⟩

/-- Scalar coefficient times a vector field. -/
theorem smul_coeff {c : ℝ → Vec 2 → ℝ} {Φ : ℝ → Vec 2 → F} (hc : JMF t₀ t₁ r c)
    (hΦ : JMF t₀ t₁ r Φ) : JMF t₀ t₁ r fun s x => c s x • Φ s x :=
  comp₂ (fun a v => a • v) (contDiff_fst.smul contDiff_snd) hc hΦ

end Comp

section Real

variable {c Φ : ℝ → Vec 2 → ℝ}

theorem time_mul {c : ℝ → ℝ} (hc : Measurable fun s : Set.Icc t₀ t₁ => c s)
    (hΦ : JMF t₀ t₁ r Φ) : JMF t₀ t₁ r fun s x => c s * Φ s x := by
  simpa using hΦ.smul_time hc

theorem mul_time {c : ℝ → ℝ} (hc : Measurable fun s : Set.Icc t₀ t₁ => c s)
    (hΦ : JMF t₀ t₁ r Φ) : JMF t₀ t₁ r fun s x => Φ s x * c s := by
  simpa only [mul_comm] using time_mul hc hΦ

end Real

section Clm

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
  [BorelSpace F]

omit [FiniteDimensional ℝ F] in
/-- A coefficient `CLM` applied to a field. -/
theorem clm_apply {A : ℝ → Vec 2 → (E →L[ℝ] F)} {Φ : ℝ → Vec 2 → E} (hA : JMF t₀ t₁ r A)
    (hΦ : JMF t₀ t₁ r Φ) : JMF t₀ t₁ r fun s x => A s x (Φ s x) :=
  comp₂ (fun T v => T v) (contDiff_fst.clm_apply contDiff_snd) hA hΦ

end Clm

section Adjoint

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
  [BorelSpace F] [CompleteSpace F]

/-- The adjoint as a continuous linear map between spaces of operators. -/
def adjointCLM : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) where
  toFun := ContinuousLinearMap.adjoint
  map_add' := map_add _
  map_smul' c x := by simp
  cont := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).continuous

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The pointwise adjoint of a coefficient `CLM`. -/
theorem adjoint_coeff {A : ℝ → Vec 2 → (E →L[ℝ] F)} (hA : JMF t₀ t₁ r A) :
    JMF t₀ t₁ r fun s x => ContinuousLinearMap.adjoint (A s x) :=
  comp₁ (fun T => ContinuousLinearMap.adjoint T) (adjointCLM (E := E) (F := F)).contDiff hA

omit [FiniteDimensional ℝ E] in
/-- The adjoint of a coefficient applied to a field. -/
theorem adjoint_apply {A : ℝ → Vec 2 → (E →L[ℝ] F)} {Φ : ℝ → Vec 2 → F} (hA : JMF t₀ t₁ r A)
    (hΦ : JMF t₀ t₁ r Φ) : JMF t₀ t₁ r fun s x => ContinuousLinearMap.adjoint (A s x) (Φ s x) :=
  clm_apply (adjoint_coeff hA) hΦ

end Adjoint

section Words

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A coordinate of a `PiLp` field. -/
theorem proj {ι : Type*} [Fintype ι] {Φ : ℝ → Vec 2 → PiLp 2 (fun _ : ι => E)}
    (hΦ : JMF t₀ t₁ r Φ) (k : ι) : JMF t₀ t₁ r fun s x => Φ s x k :=
  by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (PiLp.proj 2 (fun _ : ι => E) k) :=
    ContinuousLinearMap.contDiff _
  exact comp₁ (fun v : PiLp 2 (fun _ : ι => E) => v k) hp hΦ

/-- The word adjoint, `r + m → r`. -/
theorem word_adjoint {m : ℕ} {G : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => E)}
    (hG : JMF t₀ t₁ (r + m) G) :
    JMF t₀ t₁ r fun s => AVRegularity.wordAdjoint m (G s) := by
  have h : JMF t₀ t₁ r fun s x => ∑ α : DerivativeWord2 m,
      AVRegularity.orderedDerivativeRev α (fun y => G s y α) x :=
    JMF.sum _ fun α _ => JMF.word α (hG.proj α)
  have h2 := h.smul_time (c := fun _ => (-1 : ℝ) ^ m) measurable_const
  exact h2

end Words

section Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_tensorFluxAdjoint {m : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) fun p : (PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => ℝ)) × PiLp 2 (fun _ : Fin 2 => E) =>
      AVRegularity.tensorFluxAdjoint p.1 p.2 := by
  unfold AVRegularity.tensorFluxAdjoint
  refine PiLp.contDiff_toLp.comp (contDiff_pi.2 fun α => ?_)
  refine ContDiff.sum fun k _ => ?_
  have hpℝ : ContDiff ℝ (⊤ : ℕ∞) (PiLp.proj 2 (fun _ : Fin 2 => ℝ) k) :=
    ContinuousLinearMap.contDiff _
  have hpE : ContDiff ℝ (⊤ : ℕ∞) (PiLp.proj 2 (fun _ : Fin 2 => E) k) :=
    ContinuousLinearMap.contDiff _
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun p : (PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => ℝ)) × PiLp 2 (fun _ : Fin 2 => E) =>
      p.1 (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k :=
    hpℝ.comp (contDiff_fst.clm_apply contDiff_const)
  exact h1.smul (hpE.comp contDiff_snd)

theorem tensor_flux {m : ℕ}
    {A : ℝ → Vec 2 → (PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))}
    {ψ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} (hA : JMF t₀ t₁ r A) (hψ : JMF t₀ t₁ r ψ) :
    JMF t₀ t₁ r fun s x => AVRegularity.tensorFluxAdjoint (A s x) (ψ s x) :=
  comp₂ (fun a v => AVRegularity.tensorFluxAdjoint a v) contDiff_tensorFluxAdjoint hA hψ

/-- The diagonal flux adjoint, `r + D → r`. -/
theorem diagonal_flux (D : ℕ)
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {ψ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)}
    (hA : ∀ d, JMF t₀ t₁ (r + D) (AD d)) (hψ : JMF t₀ t₁ (r + D) ψ) :
    JMF t₀ t₁ r fun s => AVRegularity.diagonalFluxAdjoint D AD s (ψ s) := by
  have hd : ∀ d : Finset.Icc 2 D, d.1 - 1 ≤ D := fun d => by have := (Finset.mem_Icc.mp d.2).2; omega
  have h : JMF t₀ t₁ r fun s x => ∑ d : Finset.Icc 2 D,
      AVRegularity.wordAdjoint (d.1 - 1) (fun y => AVRegularity.tensorFluxAdjoint (AD d s y) (ψ s y)) x := by
    refine JMF.sum _ fun d _ => word_adjoint ?_
    exact tensor_flux ((hA d).mono (by have := hd d; omega)) (hψ.mono (by have := hd d; omega))
  exact h

end Tensor

section Edge

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
  [BorelSpace F] [CompleteSpace F]

/-- The word adjoint of the adjoint of a coefficient applied to a field. -/
theorem word_adjoint_adjoint {m : ℕ}
    {A : ℝ → Vec 2 → ((PiLp 2 (fun _ : DerivativeWord2 m => E)) →L[ℝ] F)} {ψ : ℝ → Vec 2 → F}
    (hA : JMF t₀ t₁ (r + m) A) (hψ : JMF t₀ t₁ (r + m) ψ) :
    JMF t₀ t₁ r fun s =>
      AVRegularity.wordAdjoint m (fun y => ContinuousLinearMap.adjoint (A s y) (ψ s y)) :=
  word_adjoint (adjoint_apply hA hψ)

end Edge

end JMF
end

/-! Jointly measurable `C^r` families: the commutator coefficient and the commutator adjoint. -/

section
namespace JMF

variable {t₀ t₁ : ℝ} {r : ℕ} {b : ℝ → Vec 2 → Vec 2} {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ}

/-- A jointly measurable drift with smooth window slices is `JMF` of every order. -/
theorem of_smooth (hb : JointlyMeas t₀ t₁ b)
    (hbs : ∀ s ∈ Set.Icc t₀ t₁, ContDiff ℝ (⊤ : ℕ∞) (b s)) (n : ℕ) : JMF t₀ t₁ n b :=
  ⟨hb, fun s hs => (hbs s hs).of_le (by exact_mod_cast le_top)⟩

/-- Entries of the commutator coefficient, of every order. -/
theorem comm_coeff (hbj : ∀ n, JMF t₀ t₁ n b)
    (hH : ∀ i j, Measurable fun s : Set.Icc t₀ t₁ => Hc s i j) (n : ℕ) (i j : Fin 2) :
    JMF t₀ t₁ n fun s y => AVRegularity.commutatorMatrix b (Hc s) s y i j := by
  have hk : ∀ (k : Fin 2) (c : Fin 2), JMF t₀ t₁ n fun s y => fderiv ℝ (b s) y (basisVec k) c :=
    fun k c => comp₁ (fun v : Vec 2 => v c) (contDiff_apply ℝ ℝ c) ((hbj (n + 1)).dbasis k)
  have h : JMF t₀ t₁ n fun s y => ∑ k : Fin 2,
      (fderiv ℝ (b s) y (basisVec k) i * Hc s k j + Hc s i k * fderiv ℝ (b s) y (basisVec k) j) :=
    JMF.sum _ fun k _ => ((hk k i).mul_time (hH k j)).add ((hk k j).time_mul (hH i k))
  exact h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The commutator adjoint, `r + 1 → r`. -/
theorem comm_adjoint (hbj : ∀ n, JMF t₀ t₁ n b)
    (hH : ∀ i j, Measurable fun s : Set.Icc t₀ t₁ => Hc s i j)
    {ψ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} (hψ : JMF t₀ t₁ (r + 1) ψ) :
    JMF t₀ t₁ r fun s => AVRegularity.commutatorAdjoint b (Hc s) s (ψ s) := by
  have h : JMF t₀ t₁ r fun s x => ∑ j : Fin 2,
      fderiv ℝ (fun y => ∑ k : Fin 2,
        (AVRegularity.commutatorMatrix b (Hc s) s y k j) • ψ s y k) x (basisVec j) := by
    refine JMF.sum _ fun j _ => ?_
    have : JMF t₀ t₁ (r + 1) fun s y => ∑ k : Fin 2,
        (AVRegularity.commutatorMatrix b (Hc s) s y k j) • ψ s y k :=
      JMF.sum _ fun k _ => smul_coeff (comm_coeff hbj hH (r + 1) k j) (hψ.proj k)
    exact this.dbasis j
  exact h

end JMF
end

/-! Joint measurability in time and space of the test-field operators of the coarse response
fluxes, applied to a fixed smooth test field.

`jo_covarianceMatrix_entries_measurable` gives window-measurability of the covariance matrix from
the premises `J_meas` and `J_bdd`. `jo_coarseFluxAdjoint_jointlyMeas` is the diagonal and
commutator part and `jo_edgeFlux_jointlyMeas` is the edge part. -/

/-- The entries of the covariance matrix are window-measurable. -/
theorem jo_covarianceMatrix_entries_measurable {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) (B : ℝ)
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hJ : ∀ i j, Measurable fun t => Jm t i j)
    {M : ℝ} (hM : ∀ t ∈ Set.Icc t₀ t₁, ∀ i j, |Jm t i j| ≤ M) (i j : Fin 2) :
    Measurable fun s : Set.Icc t₀ t₁ => covarianceMatrix Jm B t₀ s i j := by
  have hc := (continuousOn_covarianceMatrix h B hJ hM).domRestrict
  have : Continuous fun s : Set.Icc t₀ t₁ => covarianceMatrix Jm B t₀ s i j :=
    (continuous_apply j).comp ((continuous_apply i).comp hc)
  exact this.measurable

/-- (D1) The negated coarse flux adjoint, applied to `𝖰_p ψ`, is jointly measurable in time and
space with continuous window slices. -/
theorem jo_coarseFluxAdjoint_jointlyMeas {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {t₀ t₁ B : ℝ} (h : t₀ ≤ t₁) {b : ℝ → Vec 2 → Vec 2} {D p N : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hb : Measurable fun q : Set.Icc t₀ t₁ × Vec 2 => b q.1 q.2)
    (hbs : ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (⊤ : ℕ∞) (b t))
    (hAD : ∀ d, Measurable fun q : Set.Icc t₀ t₁ × Vec 2 => AD d q.1 q.2)
    (hADs : ∀ d, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (N : ℕ) (AD d t))
    (hJ : ∀ i j, Measurable fun t => Jm t i j) {M : ℝ}
    (hM : ∀ t ∈ Set.Icc t₀ t₁, ∀ i j, |Jm t i j| ≤ M) (hN : 2 * p + D ≤ N)
    {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    JointlyMeas t₀ t₁ (fun s => -(AVRegularity.coarseFluxAdjoint D b AD
        (covarianceMatrix Jm B t₀ s) p s
        (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p ψ))) ∧
      ∀ s ∈ Set.Icc t₀ t₁, Continuous (fun x => -(AVRegularity.coarseFluxAdjoint D b AD
        (covarianceMatrix Jm B t₀ s) p s
        (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p ψ) x)) := by
  set Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ := covarianceMatrix Jm B t₀ with hHc
  have hH : ∀ i j, Measurable fun s : Set.Icc t₀ t₁ => Hc s i j :=
    jo_covarianceMatrix_entries_measurable h B hJ hM
  have hbj : ∀ n, JMF t₀ t₁ n b := JMF.of_smooth hb hbs
  have hψJ : ∀ n, JMF t₀ t₁ n fun _ x => ψ x := fun n => JMF.of_contDiff hψ
  -- `𝖰_p ψ` and the iterates `𝒞^a 𝖰_p ψ` are of every order
  have hQ : ∀ n, JMF t₀ t₁ n fun s => AVRegularity.covPolyQ (Hc s) p ψ :=
    fun n => JMF.cov_polyQ hH p (hψJ (n + 2 * p))
  have hQa : ∀ a n, JMF t₀ t₁ n fun s => (AVRegularity.covOperator (Hc s))^[a]
      (AVRegularity.covPolyQ (Hc s) p ψ) :=
    fun a n => JMF.cov_iter hH a n _ (hQ (n + 2 * a))
  -- the commutator terms
  have hA : JMF t₀ t₁ 0 fun s x => ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) •
      ∑ a ∈ Finset.range l, (AVRegularity.covOperator (Hc s))^[l - 1 - a]
        (AVRegularity.commutatorAdjoint b (Hc s) s
          ((AVRegularity.covOperator (Hc s))^[a] (AVRegularity.covPolyQ (Hc s) p ψ))) x := by
    refine JMF.sum _ fun l _ => ?_
    have h1 : JMF t₀ t₁ 0 fun s x => ∑ a ∈ Finset.range l,
        (AVRegularity.covOperator (Hc s))^[l - 1 - a]
          (AVRegularity.commutatorAdjoint b (Hc s) s
            ((AVRegularity.covOperator (Hc s))^[a] (AVRegularity.covPolyQ (Hc s) p ψ))) x := by
      refine JMF.sum _ fun a _ => ?_
      have h2 := JMF.comm_adjoint (r := 2 * (l - 1 - a)) hbj hH (hQa a _)
      exact JMF.cov_iter hH (l - 1 - a) 0 _ (by simpa using h2)
    exact ⟨h1.1.smul measurable_const, fun s hs => (h1.2 s hs).const_smul _⟩
  -- the diagonal term
  have hdiag : JMF t₀ t₁ (2 * p) fun s =>
      AVRegularity.diagonalFluxAdjoint D AD s (AVRegularity.covPolyQ (Hc s) p ψ) :=
    JMF.diagonal_flux D (fun d => ⟨hAD d, fun s hs =>
      (hADs d s hs).of_le (by exact_mod_cast hN)⟩) (hQ _)
  have hP := JMF.cov_polyP hH p (r := 0) (hdiag.mono (by omega))
  have hF : JMF t₀ t₁ 0 fun s => -(AVRegularity.coarseFluxAdjoint D b AD (Hc s) p s
      (AVRegularity.covPolyQ (Hc s) p ψ)) :=
    by
    convert (hA.sub hP).neg using 3 with s
    simp [AVRegularity.coarseFluxAdjoint, Finset.sum_apply]
  exact ⟨hF.1, fun s hs => (hF.2 s hs).continuous⟩

/-- (D2) The edge flux term `𝖯_p F_E^* 𝖰_p ψ` of a pair `(v,u)` is jointly measurable in time and
space with continuous window slices. -/
theorem jo_edgeFlux_jointlyMeas {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {t₀ t₁ B : ℝ} (hw : t₀ ≤ t₁) {D H p N : ℕ}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (v u : ι)
    (hCE : ∀ ρ ∈ Finset.Icc 1 H, ∀ d,
      Measurable fun q : Set.Icc t₀ t₁ × Vec 2 => CE ρ v u d q.1 q.2)
    (hCEs : ∀ ρ ∈ Finset.Icc 1 H, ∀ d, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (N : ℕ) (CE ρ v u d t))
    (hJ : ∀ i j, Measurable fun t => Jm t i j) {M : ℝ}
    (hM : ∀ t ∈ Set.Icc t₀ t₁, ∀ i j, |Jm t i j| ≤ M) (hN : 2 * p + D ≤ N)
    {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    JointlyMeas t₀ t₁ (fun s => AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
        (fun x => ∑ ρ ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
          AVRegularity.wordAdjoint (d.1 - 1) (fun y => ContinuousLinearMap.adjoint
            (CE ρ v u d s y) (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p ψ y)) x)) ∧
      ∀ s ∈ Set.Icc t₀ t₁, Continuous (fun x => AVRegularity.covPolyP
        (covarianceMatrix Jm B t₀ s) p
        (fun x => ∑ ρ ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
          AVRegularity.wordAdjoint (d.1 - 1) (fun y => ContinuousLinearMap.adjoint
            (CE ρ v u d s y) (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p ψ y)) x) x) := by
  set Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ := covarianceMatrix Jm B t₀ with hHc
  have hH : ∀ i j, Measurable fun s : Set.Icc t₀ t₁ => Hc s i j :=
    jo_covarianceMatrix_entries_measurable hw B hJ hM
  have hψJ : ∀ n, JMF t₀ t₁ n fun _ x => ψ x := fun n => JMF.of_contDiff hψ
  have hQ : ∀ n, JMF t₀ t₁ n fun s => AVRegularity.covPolyQ (Hc s) p ψ :=
    fun n => JMF.cov_polyQ hH p (hψJ (n + 2 * p))
  have hE : JMF t₀ t₁ (2 * p) fun s x => ∑ ρ ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
      AVRegularity.wordAdjoint (d.1 - 1) (fun y => ContinuousLinearMap.adjoint
        (CE ρ v u d s y) (AVRegularity.covPolyQ (Hc s) p ψ y)) x := by
    refine JMF.sum _ fun ρ hρ => JMF.sum _ fun d _ => ?_
    have hd : d.1 - 1 ≤ D := by have := (Finset.mem_Icc.mp d.2).2; omega
    exact JMF.word_adjoint_adjoint ⟨hCE ρ hρ d, fun s hs =>
      (hCEs ρ hρ d s hs).of_le (by exact_mod_cast (by omega : 2 * p + (d.1 - 1) ≤ N))⟩ (hQ _)
  have hP := JMF.cov_polyP hH p (r := 0) (hE.mono (by omega))
  exact ⟨hP.1, fun s hs => (hP.2 s hs).continuous⟩

end AVRegularity.CycleComparison.Coarse.JointOps
end
