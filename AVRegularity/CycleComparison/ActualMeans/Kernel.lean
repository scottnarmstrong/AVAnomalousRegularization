-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.Statements.Intermediate.CycleReference.JacMatrix
public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivative

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.ActualMeans

/-! The chain rule for ordered derivative words under a chart `Φ` of the plane:
`∂^α (g ∘ Φ) = ∑_β P_{α,β} · (∂^β g) ∘ Φ`, with coefficients `P_{α,β}` built from the derivatives
of `Φ` by the recursion `P_{αi,βj} = ∂_i P_{α,βj} + P_{α,β} ∂_iΦ_j`. The chart jets pay the chain
rule when the tested order is lowered from `d` to `d'`. The coefficient `P_{α,β}` vanishes unless
`1 ≤ |β| ≤ |α|` (or `α = β = ∅`). -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The chain-rule coefficient `P_{α,β}` of the chart `Φ`: the coefficient of `(∂^β g) ∘ Φ` in
`∂^α (g ∘ Φ)`. -/
def chainCoeff (Φ : Vec 2 → Vec 2) :
    (m : ℕ) → DerivativeWord2 m → (m' : ℕ) → DerivativeWord2 m' → Vec 2 → ℝ
  | 0, _, m', _ => fun _ => if m' = 0 then 1 else 0
  | m + 1, α, 0, β => fun y =>
      fderiv ℝ (chainCoeff Φ m (fun i => α i.castSucc) 0 β) y (basisVec (α (Fin.last m)))
  | m + 1, α, m' + 1, β => fun y =>
      fderiv ℝ (chainCoeff Φ m (fun i => α i.castSucc) (m' + 1) β) y
          (basisVec (α (Fin.last m))) +
        chainCoeff Φ m (fun i => α i.castSucc) m' (fun i => β i.castSucc) y *
          jacMatrix Φ y (β (Fin.last m')) (α (Fin.last m))

theorem chainCoeff_zero (Φ : Vec 2 → Vec 2) (α : DerivativeWord2 0) (m' : ℕ)
    (β : DerivativeWord2 m') :
    chainCoeff Φ 0 α m' β = fun _ => if m' = 0 then 1 else 0 := rfl

theorem chainCoeff_succ_zero (Φ : Vec 2 → Vec 2) {m : ℕ} (α : DerivativeWord2 (m + 1))
    (β : DerivativeWord2 0) :
    chainCoeff Φ (m + 1) α 0 β = fun y =>
      fderiv ℝ (chainCoeff Φ m (fun i => α i.castSucc) 0 β) y (basisVec (α (Fin.last m))) := rfl

theorem chainCoeff_succ_succ (Φ : Vec 2 → Vec 2) {m m' : ℕ} (α : DerivativeWord2 (m + 1))
    (β : DerivativeWord2 (m' + 1)) :
    chainCoeff Φ (m + 1) α (m' + 1) β = fun y =>
      fderiv ℝ (chainCoeff Φ m (fun i => α i.castSucc) (m' + 1) β) y
          (basisVec (α (Fin.last m))) +
        chainCoeff Φ m (fun i => α i.castSucc) m' (fun i => β i.castSucc) y *
          jacMatrix Φ y (β (Fin.last m')) (α (Fin.last m)) := rfl

/-- No derivative of `g` of order above `|α|` occurs in `∂^α (g ∘ Φ)`. -/
theorem chainCoeff_eq_zero_of_lt (Φ : Vec 2 → Vec 2) :
    ∀ (m : ℕ) (α : DerivativeWord2 m) (m' : ℕ) (β : DerivativeWord2 m'), m < m' →
      chainCoeff Φ m α m' β = 0 := by
  intro m
  induction m with
  | zero =>
    intro α m' β hlt
    rw [chainCoeff_zero]
    funext y
    simp [Nat.pos_iff_ne_zero.mp hlt]
  | succ m ih =>
    intro α m' β hlt
    obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
    rw [chainCoeff_succ_succ, ih _ (m'' + 1) β (by omega), ih _ m'' _ (by omega)]
    funext y
    simp

/-- For a nonempty word `α`, the undifferentiated `g ∘ Φ` does not occur in `∂^α (g ∘ Φ)`. -/
theorem chainCoeff_succ_zero_eq_zero (Φ : Vec 2 → Vec 2) :
    ∀ (m : ℕ) (α : DerivativeWord2 (m + 1)) (β : DerivativeWord2 0),
      chainCoeff Φ (m + 1) α 0 β = 0 := by
  intro m
  induction m with
  | zero =>
    intro α β
    rw [chainCoeff_succ_zero, chainCoeff_zero]
    funext y
    simp
  | succ m ih =>
    intro α β
    rw [chainCoeff_succ_zero, ih]
    funext y
    simp

/-! ### Smoothness, jointly in a parameter -/

section Joint

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A directional derivative in the second variable of a jointly smooth map is jointly smooth. -/
theorem contDiff_fderiv_snd_apply {F : P → Vec 2 → G}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun q : P × Vec 2 => F q.1 q.2)) (e : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : P × Vec 2 => fderiv ℝ (F q.1) q.2 e) := by
  have hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry fun (q : P × Vec 2) (y : Vec 2) => F q.1 y) :=
    hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun q : P × Vec 2 => fderiv ℝ (F q.1) q.2) :=
    ContDiff.fderiv (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hu contDiff_snd (by simp)
  exact hd.clm_apply contDiff_const

/-- The Jacobian entries of a jointly smooth family of charts are jointly smooth. -/
theorem contDiff_jacMatrix_joint {Φ : P → Vec 2 → Vec 2}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) (fun q : P × Vec 2 => Φ q.1 q.2)) (a b : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : P × Vec 2 => jacMatrix (Φ q.1) q.2 a b) := by
  have h := contDiff_pi.1 (contDiff_fderiv_snd_apply hΦ (basisVec b)) a
  simpa only [jacMatrix, Matrix.of_apply] using h

/-- The chain-rule coefficients of a jointly smooth family of charts are jointly smooth. -/
theorem contDiff_chainCoeff_joint {Φ : P → Vec 2 → Vec 2}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) (fun q : P × Vec 2 => Φ q.1 q.2)) :
    ∀ (m : ℕ) (α : DerivativeWord2 m) (m' : ℕ) (β : DerivativeWord2 m'),
      ContDiff ℝ (⊤ : ℕ∞) (fun q : P × Vec 2 => chainCoeff (Φ q.1) m α m' β q.2) := by
  intro m
  induction m with
  | zero =>
    intro α m' β
    simp only [chainCoeff_zero]
    exact contDiff_const
  | succ m ih =>
    intro α m' β
    cases m' with
    | zero =>
      simp only [chainCoeff_succ_zero]
      exact contDiff_fderiv_snd_apply
        (F := fun p => chainCoeff (Φ p) m (fun i => α i.castSucc) 0 β)
        (ih (fun i => α i.castSucc) 0 β) (basisVec (α (Fin.last m)))
    | succ m' =>
      simp only [chainCoeff_succ_succ]
      exact (contDiff_fderiv_snd_apply
        (F := fun p => chainCoeff (Φ p) m (fun i => α i.castSucc) (m' + 1) β)
        (ih (fun i => α i.castSucc) (m' + 1) β) (basisVec (α (Fin.last m)))).add
        ((ih (fun i => α i.castSucc) m' (fun i => β i.castSucc)).mul
          (contDiff_jacMatrix_joint hΦ (β (Fin.last m')) (α (Fin.last m))))

end Joint

/-- The chain-rule coefficients of a smooth chart are smooth. -/
theorem contDiff_chainCoeff {Φ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (m : ℕ)
    (α : DerivativeWord2 m) (m' : ℕ) (β : DerivativeWord2 m') :
    ContDiff ℝ (⊤ : ℕ∞) (chainCoeff Φ m α m' β) := by
  have hj : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => (fun _ : ℝ => Φ) q.1 q.2) :=
    hΦ.comp contDiff_snd
  have h := (contDiff_chainCoeff_joint (Φ := fun _ : ℝ => Φ) hj m α m' β).comp
    ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)
  exact h

/-- The Jacobian entries of a smooth chart are smooth. -/
theorem contDiff_jacMatrix {Φ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (a b : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => jacMatrix Φ y a b) := by
  have hj : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => (fun _ : ℝ => Φ) q.1 q.2) :=
    hΦ.comp contDiff_snd
  have h := (contDiff_jacMatrix_joint (Φ := fun _ : ℝ => Φ) hj a b).comp
    ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)
  exact h

/-- Ordered derivatives of a smooth function are smooth. -/
theorem contDiff_top_orderedDerivative {m : ℕ} (β : DerivativeWord2 m) {g : Vec 2 → E}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (orderedDerivative β g) :=
  contDiff_infty.2 fun p =>
    ChartTransport.contDiff_orderedDerivative (p := p) β (hg.of_le (by exact_mod_cast le_top))

/-! ### The chain rule -/

/-- Summing over words of length `m + 1` is summing over their initial words and last letters. -/
theorem sum_word_succ {A : Type*} [AddCommMonoid A] {m : ℕ} (F : DerivativeWord2 (m + 1) → A) :
    ∑ β : DerivativeWord2 (m + 1), F β =
      ∑ β : DerivativeWord2 m, ∑ j : Fin 2, F (Fin.snoc β j) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin 2)).sum_comp F, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

/-- The column `∂_i Φ` of the Jacobian in the standard basis. -/
theorem fderiv_basisVec_eq_sum (Φ : Vec 2 → Vec 2) (y : Vec 2) (i : Fin 2) :
    fderiv ℝ Φ y (basisVec i) = ∑ j : Fin 2, jacMatrix Φ y j i • basisVec j :=
  ChartTransport.vec2_eq_sum_basisVec (fderiv ℝ Φ y (basisVec i))

/-- One step of the chain rule: `∂_i (p · H ∘ Φ) = ∂_i p · H ∘ Φ + p ∑_j ∂_iΦ_j (∂_j H) ∘ Φ`. -/
theorem fderiv_smul_comp_chart {Φ : Vec 2 → Vec 2} (hΦ : Differentiable ℝ Φ) {p : Vec 2 → ℝ}
    (hp : Differentiable ℝ p) {H : Vec 2 → E} (hH : Differentiable ℝ H) (y : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun y' => p y' • H (Φ y')) y (basisVec i) =
      fderiv ℝ p y (basisVec i) • H (Φ y) +
        p y • ∑ j : Fin 2, jacMatrix Φ y j i • fderiv ℝ H (Φ y) (basisVec j) := by
  have hHΦ : DifferentiableAt ℝ (fun y' => H (Φ y')) y := (hH (Φ y)).comp y (hΦ y)
  have hcomp : fderiv ℝ (fun y' => H (Φ y')) y (basisVec i) =
      ∑ j : Fin 2, jacMatrix Φ y j i • fderiv ℝ H (Φ y) (basisVec j) := by
    have h1 : fderiv ℝ (fun y' => H (Φ y')) y = (fderiv ℝ H (Φ y)).comp (fderiv ℝ Φ y) :=
      fderiv_comp y (hH (Φ y)) (hΦ y)
    rw [h1, ContinuousLinearMap.comp_apply, fderiv_basisVec_eq_sum Φ y i, map_sum]
    exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
  have hfs : fderiv ℝ (fun y' => p y' • H (Φ y')) y (basisVec i) =
      p y • fderiv ℝ (fun y' => H (Φ y')) y (basisVec i) +
        fderiv ℝ p y (basisVec i) • H (Φ y) := by
    rw [fderiv_fun_smul (hp y) hHΦ]
    rfl
  rw [hfs, hcomp]
  exact add_comm _ _

/-- Bookkeeping for the chain-rule induction: `t₀ = a₀`, `t_{k+1} = a_{k+1} + b_k`, `b_M = 0`. -/
theorem sum_range_shift_decomp {A : Type*} [AddCommGroup A] (M : ℕ) (a b t : ℕ → A)
    (h0 : t 0 = a 0) (hS : ∀ k, t (k + 1) = a (k + 1) + b k) (hM : b M = 0) :
    ∑ k ∈ Finset.range (M + 1), a k + ∑ k ∈ Finset.range (M + 1), b k =
      ∑ k ∈ Finset.range (M + 1), t k := by
  rw [Finset.sum_range_succ' t, Finset.sum_range_succ' a, Finset.sum_range_succ b, hM, h0,
    Finset.sum_congr rfl fun k _ => hS k, Finset.sum_add_distrib]
  abel

/-- **Chain rule for ordered derivative words.** For `|α| ≤ M`,
`∂^α (g ∘ Φ)(y) = ∑_{m' ≤ M} ∑_{|β| = m'} P_{α,β}(y) (∂^β g)(Φ y)`. -/
theorem orderedDerivative_comp_chart {Φ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {g : Vec 2 → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (M : ℕ) :
    ∀ (m : ℕ), m ≤ M → ∀ α : DerivativeWord2 m,
      orderedDerivative α (fun y => g (Φ y)) = fun y =>
        ∑ m' ∈ Finset.range (M + 1), ∑ β : DerivativeWord2 m',
          chainCoeff Φ m α m' β y • orderedDerivative β g (Φ y) := by
  intro m
  induction m with
  | zero =>
    intro _ α
    funext y
    rw [orderedDerivative_zero, Finset.sum_eq_single 0]
    · rw [Fintype.sum_unique, chainCoeff_zero, orderedDerivative_zero]
      simp
    · intro m' _ hm'
      refine Finset.sum_eq_zero fun β _ => ?_
      rw [chainCoeff_zero]
      simp [hm']
    · intro hmem
      exact absurd (Finset.mem_range.2 (Nat.succ_pos M)) hmem
  | succ m ih =>
    intro hm α
    have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
    have hP : ∀ (m' : ℕ) (β : DerivativeWord2 m'),
        Differentiable ℝ (chainCoeff Φ m (fun i => α i.castSucc) m' β) :=
      fun m' β => (contDiff_chainCoeff hΦ m _ m' β).differentiable (by simp)
    have hH : ∀ (m' : ℕ) (β : DerivativeWord2 m'), Differentiable ℝ (orderedDerivative β g) :=
      fun m' β => (contDiff_top_orderedDerivative β hg).differentiable (by simp)
    rw [orderedDerivative_succ α (fun y => g (Φ y)), ih (by omega) (fun i => α i.castSucc)]
    funext y
    have hterm : ∀ (m' : ℕ) (β : DerivativeWord2 m'), HasFDerivAt
        (fun y' => chainCoeff Φ m (fun i => α i.castSucc) m' β y' • orderedDerivative β g (Φ y'))
        (fderiv ℝ (fun y' => chainCoeff Φ m (fun i => α i.castSucc) m' β y' •
          orderedDerivative β g (Φ y')) y) y :=
      fun m' β => (((hP m' β) y).smul (((hH m' β) (Φ y)).comp y (hΦd y))).hasFDerivAt
    have hsum : HasFDerivAt
        (fun y' => ∑ m' ∈ Finset.range (M + 1), ∑ β : DerivativeWord2 m',
          chainCoeff Φ m (fun i => α i.castSucc) m' β y' • orderedDerivative β g (Φ y'))
        (∑ m' ∈ Finset.range (M + 1), ∑ β : DerivativeWord2 m',
          fderiv ℝ (fun y' => chainCoeff Φ m (fun i => α i.castSucc) m' β y' •
            orderedDerivative β g (Φ y')) y) y :=
      HasFDerivAt.fun_sum fun m' _ => HasFDerivAt.fun_sum fun β _ => hterm m' β
    have hd : ∀ (m' : ℕ) (β : DerivativeWord2 m'),
        fderiv ℝ (fun y' => chainCoeff Φ m (fun i => α i.castSucc) m' β y' •
          orderedDerivative β g (Φ y')) y (basisVec (α (Fin.last m))) =
        fderiv ℝ (chainCoeff Φ m (fun i => α i.castSucc) m' β) y (basisVec (α (Fin.last m))) •
            orderedDerivative β g (Φ y) +
          chainCoeff Φ m (fun i => α i.castSucc) m' β y •
            ∑ j : Fin 2, jacMatrix Φ y j (α (Fin.last m)) •
              fderiv ℝ (orderedDerivative β g) (Φ y) (basisVec j) :=
      fun m' β => fderiv_smul_comp_chart hΦd (hP m' β) (hH m' β) y (α (Fin.last m))
    have hjac : ∀ (m' : ℕ) (β : DerivativeWord2 m') (j : Fin 2),
        orderedDerivative (Fin.snoc β j : DerivativeWord2 (m' + 1)) g (Φ y) =
          fderiv ℝ (orderedDerivative β g) (Φ y) (basisVec j) := by
      intro m' β j
      rw [orderedDerivative_succ (Fin.snoc β j : DerivativeWord2 (m' + 1)) g]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [hsum.fderiv]
    simp only [_root_.sum_apply, hd, Finset.sum_add_distrib]
    refine sum_range_shift_decomp M _ _ _ ?_ ?_ ?_
    · exact Finset.sum_congr rfl fun β _ => rfl
    · intro m'
      rw [sum_word_succ (fun β' : DerivativeWord2 (m' + 1) =>
          chainCoeff Φ (m + 1) α (m' + 1) β' y • orderedDerivative β' g (Φ y)),
        sum_word_succ (fun β' : DerivativeWord2 (m' + 1) =>
          fderiv ℝ (chainCoeff Φ m (fun i => α i.castSucc) (m' + 1) β') y
            (basisVec (α (Fin.last m))) • orderedDerivative β' g (Φ y)),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [chainCoeff_succ_succ, hjac m' β j, smul_smul]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, add_smul]
    · refine Finset.sum_eq_zero fun β _ => ?_
      rw [chainCoeff_eq_zero_of_lt Φ m _ M β (by omega)]
      simp
end

/-! The Eulerian kernels of the actual means.

For one pulse with chart `Φ`, label map `Ψ = Φ⁻¹` and dimensional chart-frame letters
`c⁻¹ ε_c^n ρ^d L_{n,d,α}`, exact Piola transport and the chain rule for ordered words give the
coefficient of `∂^β a` in the Eulerian flux:
`∑_n c⁻¹ε_c^n ∑_l (∂_lΦ_{k'})∘Ψ ∑_d ρ^d ∑_α (P_{α,β}∘Ψ) L_{n,d,α,l}(ρ⁻¹Ψ)` (`pulseKernel`).
The glued kernel is the sum over the pulses of the kernels of the letters cut off to the lift
windows and weighted by the partition (`windowLetter`, `gluedKernel`). -/

section
section Generic

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The letter `L` at the cell time `c⁻¹ t`, weighted by the partition function `ϖ`, inside the
lift window `[s₀, s₁]`; zero outside. -/
def windowLetter (ϖ : ℝ → ℝ) (c s₀ s₁ : ℝ) (L : ℝ → Vec 2 → G) (t : ℝ) (X : Vec 2) : G :=
  open Classical in if c⁻¹ * t ∈ Set.Icc s₀ s₁ then ϖ t • L (c⁻¹ * t) X else 0

theorem windowLetter_of_mem {ϖ : ℝ → ℝ} {c s₀ s₁ : ℝ} (L : ℝ → Vec 2 → G) {t : ℝ}
    (ht : c⁻¹ * t ∈ Set.Icc s₀ s₁) (X : Vec 2) :
    windowLetter ϖ c s₀ s₁ L t X = ϖ t • L (c⁻¹ * t) X := by
  simp only [windowLetter, ite_eq_left ht]

theorem windowLetter_of_notMem {ϖ : ℝ → ℝ} {c s₀ s₁ : ℝ} (L : ℝ → Vec 2 → G) {t : ℝ}
    (ht : c⁻¹ * t ∉ Set.Icc s₀ s₁) (X : Vec 2) : windowLetter ϖ c s₀ s₁ L t X = 0 := by
  simp only [windowLetter, ite_eq_right ht]

/-- Where the partition function is supported in the window, the cutoff is invisible. -/
theorem windowLetter_eq_smul {ϖ : ℝ → ℝ} {c s₀ s₁ : ℝ} (L : ℝ → Vec 2 → G) {t : ℝ}
    (hsupp : ϖ t ≠ 0 → c⁻¹ * t ∈ Set.Icc s₀ s₁) (X : Vec 2) :
    windowLetter ϖ c s₀ s₁ L t X = ϖ t • L (c⁻¹ * t) X := by
  by_cases ht : c⁻¹ * t ∈ Set.Icc s₀ s₁
  · exact windowLetter_of_mem L ht X
  · have h0 : ϖ t = 0 := by
      by_contra hne
      exact ht (hsupp hne)
    rw [windowLetter_of_notMem L ht X, h0, zero_smul]

/-- The kernel of one pulse at a fixed time: the coefficient of `∂^β a` in the component `k'` of
the Eulerian flux, for the chart `chart`, its inverse `label` and the letters `W n d α l` (functions
of the slow label `X = ρ⁻¹ y`). -/
def pulseKernel (c ρ εc : ℝ) (M : ℕ) (chart label : Vec 2 → Vec 2)
    (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G)
    (m' : ℕ) (β : DerivativeWord2 m') (k' : Fin 2) (x : Vec 2) : G :=
  ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix chart (label x) k' l •
    ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
      chainCoeff chart (d - 1) α m' β (label x) • W n d α l (ρ⁻¹ • label x)

/-- A continuous linear map commutes with the pulse kernel. -/
theorem clm_pulseKernel {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
    (φ : G →L[ℝ] G') (c ρ εc : ℝ) (M : ℕ) (chart label : Vec 2 → Vec 2)
    (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G)
    (m' : ℕ) (β : DerivativeWord2 m') (k' : Fin 2) (x : Vec 2) :
    φ (pulseKernel c ρ εc M chart label W m' β k' x) =
      pulseKernel c ρ εc M chart label (fun n d α l X => φ (W n d α l X)) m' β k' x := by
  simp only [pulseKernel, map_sum, map_smul]

/-- The glued kernel: the sum over the pulses of the kernels of the windowed letters. -/
def gluedKernel (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) (M : ℕ)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
    (L : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → G)
    (m' : ℕ) (β : DerivativeWord2 m') (k' : Fin 2) (t : ℝ) (x : Vec 2) : G :=
  ∑ k ∈ kset, pulseKernel c ρ εc M (chart k t) (label k t)
    (fun n d α l => windowLetter (ϖ k) c (s₀ k) (s₁ k) (L k n d α l) t) m' β k' x

end Generic

/-! ### Operators between word arrays -/

section Array

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The operator `L ↦ e_{k'} ∘ L ∘ π_β` placing an entry in a word-array operator. -/
def arrayEntryL (m : ℕ) (β : DerivativeWord2 m) (k' : Fin 2) :
    (F →L[ℝ] G) →L[ℝ]
      (PiLp 2 (fun _ : DerivativeWord2 m => F) →L[ℝ] PiLp 2 (fun _ : Fin 2 => G)) :=
  (ContinuousLinearMap.compL ℝ (PiLp 2 (fun _ : DerivativeWord2 m => F)) G
      (PiLp 2 (fun _ : Fin 2 => G))
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => G)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 2 => G) k'))).comp
    ((ContinuousLinearMap.compL ℝ (PiLp 2 (fun _ : DerivativeWord2 m => F)) F G).flip
      (PiLp.proj 2 (fun _ : DerivativeWord2 m => F) β))

theorem arrayEntryL_apply (m : ℕ) (β : DerivativeWord2 m) (k' : Fin 2) (L : F →L[ℝ] G)
    (w : PiLp 2 (fun _ : DerivativeWord2 m => F)) (k : Fin 2) :
    arrayEntryL m β k' L w k = if k = k' then L (w β) else 0 := by
  simp only [arrayEntryL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearEquiv.coe_coe, PiLp.proj_apply,
    PiLp.continuousLinearEquiv_symm_apply, ContinuousLinearMap.single_apply, PiLp.toLp_apply,
    Pi.single_apply]

theorem norm_arrayEntryL_apply_le (m : ℕ) (β : DerivativeWord2 m) (k' : Fin 2) (L : F →L[ℝ] G) :
    ‖arrayEntryL m β k' L‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_
  have he : arrayEntryL m β k' L w = PiLp.single 2 k' (L (w β)) := by
    apply PiLp.ext
    intro k
    rw [arrayEntryL_apply]
    exact (Pi.single_apply k' (L (w β)) k).symm
  rw [he, PiLp.norm_single]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le w β) (norm_nonneg _))

/-- The operator between word arrays with entries `K β k'`. -/
def arrayOp {m : ℕ} (K : DerivativeWord2 m → Fin 2 → (F →L[ℝ] G)) :
    PiLp 2 (fun _ : DerivativeWord2 m => F) →L[ℝ] PiLp 2 (fun _ : Fin 2 => G) :=
  ∑ β : DerivativeWord2 m, ∑ k' : Fin 2, arrayEntryL m β k' (K β k')

theorem arrayOp_apply {m : ℕ} (K : DerivativeWord2 m → Fin 2 → (F →L[ℝ] G))
    (w : PiLp 2 (fun _ : DerivativeWord2 m => F)) (k : Fin 2) :
    arrayOp K w k = ∑ β : DerivativeWord2 m, K β k (w β) := by
  have h1 : arrayOp K w =
      ∑ β : DerivativeWord2 m, ∑ k' : Fin 2, arrayEntryL m β k' (K β k') w := by
    simp only [arrayOp, _root_.sum_apply]
  rw [h1, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single k]
  · rw [arrayEntryL_apply, ite_eq_left rfl]
  · intro k' _ hk'
    rw [arrayEntryL_apply, ite_eq_right (Ne.symm hk')]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

end Array
end

end AVRegularity.CycleComparison.ActualMeans
end
