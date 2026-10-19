-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Coarse.Fact.FBoundOps
public import AVRegularity.CycleComparison.Coarse.Fact.GradWord

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! Factorial-norm bounds for the derivative words and the covariance polynomials.

Differentiation costs the reserve factor `(K + 1) / ρ ≤ Kc / ρ` per derivative. -/

/-- The constant of the covariance operator: `∑ |H_{ij}| · (Kc / ρ)²`. -/
def fbCovConst (ρ : ℝ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Kc : ℕ) : ℝ :=
  covBound Hc * ((Kc : ℝ) / ρ) ^ 2

theorem fbCovConst_nonneg {ρ : ℝ} (_hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Kc : ℕ) :
    0 ≤ fbCovConst ρ Hc Kc := by
  have := covBound_nonneg Hc
  unfold fbCovConst; positivity

theorem derivativeReserveFactor_one {ρ : ℝ} (hρ : 0 < ρ) (K : ℕ) :
    derivativeReserveFactor ρ K 1 = ((K : ℝ) + 1) / ρ := by
  unfold derivativeReserveFactor
  rw [pow_one, Nat.factorial_succ]
  push_cast
  have : (K.factorial : ℝ) ≠ 0 := by positivity
  have hρ' : ρ ≠ 0 := hρ.ne'
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {ρ : ℝ}

namespace TorusAdj.FBound

/-- The coordinate derivative costs `Kc / ρ`. -/
theorem coordDeriv (hρ : 0 < ρ) (i : Fin 2) (R Kc : ℕ) :
    (TorusAdj.coordDeriv (E := E) i R Kc).FBound ρ ((Kc : ℝ) / ρ) := fun K hK U => by
  change Real.sqrt (factorialNormSq ρ
    (-(derivativeTorusHk (K := K) (r := 1) (fun _ => i)) U).val) ≤ _
  rw [sqrt_fNSq_torus_neg]
  have h1 := derivativeTorusHk_factorialNorm_le (K := K) (r := 1) ρ hρ U
  have h2 : Real.sqrt (factorialNormSq ρ
      (derivativeTorusHk (K := K) (r := 1) (fun _ => i) U).val) ≤
      Real.sqrt (∑ a : DerivativeWord2 1,
        factorialNormSq ρ (derivativeTorusHk (K := K) a U).val) :=
    Real.sqrt_le_sqrt (Finset.single_le_sum
      (f := fun a : DerivativeWord2 1 => factorialNormSq ρ (derivativeTorusHk (K := K) a U).val)
      (fun a _ => factorialNormSq_nonneg _ _) (Finset.mem_univ (fun _ => i)))
  rw [derivativeReserveFactor_one hρ K] at h1
  have hK' : (K : ℝ) + 1 ≤ Kc := by exact_mod_cast hK
  exact (h2.trans h1).trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hK' hρ.le) (Real.sqrt_nonneg _))

theorem secondDeriv (hρ : 0 < ρ) (i j : Fin 2) (R Kc : ℕ) :
    (TorusAdj.secondDeriv (E := E) i j R Kc).FBound ρ (((Kc : ℝ) / ρ) ^ 2) := by
  have hc : (0 : ℝ) ≤ (Kc : ℝ) / ρ := by positivity
  have h := (FBound.comp (coordDeriv (E := E) hρ i R Kc) (coordDeriv (E := E) hρ j (R + 1) Kc) hc le_rfl le_rfl).mono
    le_rfl le_rfl (le_of_eq (one_mul (1 : ℝ)))
  unfold TorusAdj.secondDeriv
  exact h.mono_const (le_of_eq (sq _).symm)

/-- Ordered derivative words of length `m` cost `(Kc / ρ)^m`. -/
theorem orderedDerivativeRev (hρ : 0 < ρ) : ∀ {m : ℕ} (α : DerivativeWord2 m) (R Kc : ℕ),
    (TorusAdj.orderedDerivativeRev (E := E) α R Kc).FBound ρ (((Kc : ℝ) / ρ) ^ m)
  | 0, α, R, Kc => by
    have h := ((FBound.id (E := E) R Kc ρ).mono le_rfl le_rfl le_rfl).mono_const
      (le_of_eq (pow_zero ((Kc : ℝ) / ρ)).symm)
    exact FBound.ofOp _ h
  | m + 1, α, R, Kc => by
    have hc : (0 : ℝ) ≤ (Kc : ℝ) / ρ := by positivity
    have h := (FBound.comp (orderedDerivativeRev hρ (Fin.init α) R Kc)
      (coordDeriv (E := E) hρ (α (Fin.last m)) (R + m) Kc) hc le_rfl le_rfl).mono le_rfl le_rfl
      (le_of_eq (one_mul (1 : ℝ)))
    exact FBound.ofOp _ (h.mono_const (le_of_eq (pow_succ _ _).symm))

/-- The covariance operator costs `∑ |H_{ij}| (Kc/ρ)²`. -/
theorem covOp (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (R Kc : ℕ) : (TorusAdj.covOp (E := E) Hc hM R Kc).FBound ρ (fbCovConst ρ Hc Kc) := by
  have h := FBound.sum (Finset.univ : Finset (Fin 2)) (fun i =>
    FBound.sum (Finset.univ : Finset (Fin 2)) (fun j =>
      (secondDeriv (E := E) hρ i j R Kc).smul (Hc i j)))
  have h2 := h.mono_const (Cf' := fbCovConst ρ Hc Kc)
    (le_of_eq (by unfold fbCovConst covBound; simp only [Finset.sum_mul]))
  unfold TorusAdj.covOp
  exact FBound.ofOp _ (h2.mono le_rfl le_rfl (by simpa [covBound] using hM))

/-- The iterates `𝒞^l` cost `(∑ |H_{ij}| (Kc/ρ)²)^l`. -/
theorem covIter (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M) :
    ∀ (l R Kc : ℕ), (TorusAdj.covIter (E := E) Hc hM l R Kc).FBound ρ (fbCovConst ρ Hc Kc ^ l)
  | 0, R, Kc => by
    refine FBound.mono_const (Cf := 1) ?_ (le_of_eq (pow_zero _).symm)
    exact FBound.ofOrder _ ((FBound.id (E := E) R Kc ρ).mono le_rfl le_rfl (by simp))
  | l + 1, R, Kc => by
    have hc : 0 ≤ fbCovConst ρ Hc Kc ^ l := pow_nonneg (fbCovConst_nonneg hρ Hc Kc) l
    have h := FBound.comp (covOp (E := E) hρ Hc hM R Kc) (covIter hρ Hc hM l (R + 2) Kc) hc
      le_rfl le_rfl
    refine FBound.mono_const (Cf := fbCovConst ρ Hc Kc * fbCovConst ρ Hc Kc ^ l) ?_
      (le_of_eq (pow_succ' _ _).symm)
    exact FBound.ofOp _ (FBound.ofOrder _ (h.mono le_rfl le_rfl (by rw [pow_succ'])))

theorem sum_abs_inv_factorial_mul_pow (M : ℝ) (p : ℕ) :
    ∑ l ∈ Finset.range (p + 1), |((l.factorial : ℝ)⁻¹)| * M ^ l = covPolyConst M p := by
  unfold covPolyConst
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)), div_eq_mul_inv, mul_comm]

theorem sum_abs_alt_factorial_mul_pow (M : ℝ) (p : ℕ) :
    ∑ l ∈ Finset.range (p + 1), |((-1 : ℝ) ^ l / (l.factorial : ℝ))| * M ^ l =
      covPolyConst M p := by
  unfold covPolyConst
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ l.factorial), div_mul_eq_mul_div, one_mul]

/-- `𝖯_p` costs `∑_{l ≤ p} Cc^l / l!`. -/
theorem covPolyP (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (p R Kc : ℕ) :
    (TorusAdj.covPolyP (E := E) Hc hM p R Kc).FBound ρ (covPolyConst (fbCovConst ρ Hc Kc) p) := by
  have h := FBound.sumMem (Finset.range (p + 1)) (fun l hl =>
    ((covIter (E := E) hρ Hc hM l R Kc).liftOrder (pow_nonneg (fbCovConst_nonneg hρ Hc Kc) l)
      (Nat.mul_le_mul_left 2 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)))).smul
        ((l.factorial : ℝ)⁻¹))
  have h2 := h.mono_const (le_of_eq (sum_abs_inv_factorial_mul_pow _ p))
  unfold TorusAdj.covPolyP
  exact FBound.ofOp _ (h2.mono le_rfl le_rfl (le_of_eq (sum_abs_inv_factorial_mul_pow M p)))

/-- `𝖰_p` costs `∑_{l ≤ p} Cc^l / l!`. -/
theorem covPolyQ (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (p R Kc : ℕ) :
    (TorusAdj.covPolyQ (E := E) Hc hM p R Kc).FBound ρ (covPolyConst (fbCovConst ρ Hc Kc) p) := by
  have h := FBound.sumMem (Finset.range (p + 1)) (fun l hl =>
    ((covIter (E := E) hρ Hc hM l R Kc).liftOrder (pow_nonneg (fbCovConst_nonneg hρ Hc Kc) l)
      (Nat.mul_le_mul_left 2 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)))).smul
        (((-1 : ℝ) ^ l / (l.factorial : ℝ))))
  have h2 := h.mono_const (le_of_eq (sum_abs_alt_factorial_mul_pow _ p))
  unfold TorusAdj.covPolyQ
  exact FBound.ofOp _ (h2.mono le_rfl le_rfl (le_of_eq (sum_abs_alt_factorial_mul_pow M p)))

end TorusAdj.FBound

end AVRegularity.CycleComparison.Coarse
end
end

section
section
/-! Closure properties of the gradient-form adjoints `GAdj`, and the divergence-form constructor
`GAdj.ofDiv`: an operator `T = ∑ⱼ ∂ⱼ ∘ Sⱼ` with `Sⱼ` of order `m'` has the adjoint
`-∑ⱼ Sⱼ^* ∂ⱼ`, bounded by the gradient of the input. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleComparison.Coarse

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- The pairing of the value jet of a finite sum with a continuous field. -/
theorem gcellInner_tval_finsetSum {ι : Type*} {K : ℕ} (s : Finset ι) (V : ι → TorusHk K E)
    {ψ : Vec 2 → E} (hψ : Continuous ψ) :
    cellInner (tval (∑ i ∈ s, V i)) ψ = ∑ i ∈ s, cellInner (tval (V i)) ψ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact cellInner_tval_zero ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, cellInner_tval_add _ _ hψ, ih]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- The cell pairing with a finite sum of fields. -/
theorem gcellInner_finsetSum_right {ι : Type*} (s : Finset ι) (g : Vec 2 → E)
    (f : ι → Vec 2 → E)
    (h : ∀ i ∈ s, Integrable (fun x => inner ℝ (g x) (f i x))
      (volume.restrict AVenhance.unitCube)) :
    cellInner g (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cellInner g (f i) := by
  unfold cellInner
  simp_rw [inner_sum]
  exact integral_finsetSum s h

theorem gradNormSq_torusCast {K₁ K₂ : ℕ} (ρ : ℝ) (h : K₁ = K₂) (U : TorusHk (K₁ + 1) E) :
    gradNormSq (K := K₂) ρ (torusCast (by omega : K₁ + 1 = K₂ + 1) U) =
      gradNormSq (K := K₁) ρ U := by
  subst h; rfl

theorem gradNormSq_nonneg {K : ℕ} (ρ : ℝ) (U : TorusHk (K + 1) E) :
    0 ≤ gradNormSq (K := K) ρ U :=
  Finset.sum_nonneg fun _ _ => factorialNormSq_nonneg _ _

namespace GAdj

variable {T T' : (Vec 2 → F) → (Vec 2 → E)} {m' Kc : ℕ} {ρ Cg Cg' : ℝ}

/-- Transport along equality of operators on smooth periodic fields. -/
def ofOp (h : ∀ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ → T ψ = T' ψ)
    (G : GAdj T m' Kc ρ Cg) : GAdj T' m' Kc ρ Cg where
  adj := G.adj
  gbound := G.gbound
  ident K hK U ψ hs hp := by rw [G.ident K hK U ψ hs hp, h ψ hs hp]

/-- Larger constants remain admissible (the constant enters nonnegatively). -/
def mono (G : GAdj T m' Kc ρ Cg) (hC : Cg ≤ Cg') : GAdj T m' Kc ρ Cg' where
  adj := G.adj
  gbound K hK U :=
    (G.gbound K hK U).trans (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _))
  ident := G.ident

/-- Sum of two operators. -/
def add (G : GAdj T m' Kc ρ Cg) (G' : GAdj T' m' Kc ρ Cg')
    (hT : ∀ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      Continuous (T ψ))
    (hT' : ∀ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      Continuous (T' ψ)) :
    GAdj (fun ψ x => T ψ x + T' ψ x) m' Kc ρ (Cg + Cg') where
  adj K hK := G.adj K hK + G'.adj K hK
  gbound K hK U := by
    rw [add_apply]
    refine (sqrt_fNSq_torus_add_le ρ _ _).trans ?_
    rw [add_mul]
    exact add_le_add (G.gbound K hK U) (G'.gbound K hK U)
  ident K hK U ψ hs hp := by
    have hc : Continuous ψ := hs.continuous
    change cellInner (tval (G.adj K hK U + G'.adj K hK U)) ψ = _
    rw [cellInner_tval_add _ _ hc, G.ident K hK U ψ hs hp, G'.ident K hK U ψ hs hp]
    exact (cellInner_add_right _ (integrable_tval_inner U (hT ψ hs hp))
      (integrable_tval_inner U (hT' ψ hs hp))).symm

/-- Negative of an operator. -/
def neg (G : GAdj T m' Kc ρ Cg) : GAdj (fun ψ x => -T ψ x) m' Kc ρ Cg where
  adj K hK := -G.adj K hK
  gbound K hK U := by
    rw [neg_apply, sqrt_fNSq_torus_neg]
    exact G.gbound K hK U
  ident K hK U ψ hs hp := by
    change cellInner (tval (-G.adj K hK U)) ψ = _
    rw [cellInner_tval_neg, G.ident K hK U ψ hs hp]
    exact (cellInner_neg_right _ _).symm

/-- Real multiple of an operator. -/
def smul (c : ℝ) (G : GAdj T m' Kc ρ Cg) : GAdj (fun ψ x => c • T ψ x) m' Kc ρ (|c| * Cg) where
  adj K hK := (torusSmulCLM c).comp (G.adj K hK)
  gbound K hK U := by
    change Real.sqrt (factorialNormSq ρ (c • G.adj K hK U).val) ≤ _
    rw [sqrt_fNSq_torus_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (G.gbound K hK U) (abs_nonneg c)
  ident K hK U ψ hs hp := by
    change cellInner (tval (c • G.adj K hK U)) ψ = _
    rw [cellInner_tval_smul, G.ident K hK U ψ hs hp]
    exact (cellInner_smul_right _ _ _).symm

/-- Finite sum of operators. -/
def sum {ι : Type*} (s : Finset ι) {T : ι → (Vec 2 → F) → (Vec 2 → E)} {C : ι → ℝ}
    (G : ∀ i, GAdj (T i) m' Kc ρ (C i))
    (hT : ∀ i (ψ : Vec 2 → F), ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      Continuous (T i ψ)) :
    GAdj (fun ψ x => ∑ i ∈ s, T i ψ x) m' Kc ρ (∑ i ∈ s, C i) where
  adj K hK := ∑ i ∈ s, (G i).adj K hK
  gbound K hK U := by
    rw [sum_apply]
    refine (sqrt_fNSq_torus_sum_le ρ s _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => (G i).gbound K hK U
  ident K hK U ψ hs hp := by
    rw [show tval ((∑ i ∈ s, (G i).adj K hK) U) = tval (∑ i ∈ s, (G i).adj K hK U) by
      rw [sum_apply]]
    rw [gcellInner_tval_finsetSum _ _ hs.continuous]
    rw [gcellInner_finsetSum_right s _ _ (fun i _ => integrable_tval_inner U (hT i ψ hs hp))]
    exact Finset.sum_congr rfl fun i _ => (G i).ident K hK U ψ hs hp

end GAdj

section Div

variable [FiniteDimensional ℝ E]

/-- Divergence form: `T = ∑ⱼ ∂ⱼ ∘ Sⱼ` with `Sⱼ` of order `m'` and factorial-bounded adjoints has a
gradient-form adjoint `-∑ⱼ Sⱼ^* ∂ⱼ` of order `m' + 1`. The constants `Cf j` must be nonnegative. -/
def GAdj.ofDiv {S : Fin 2 → (Vec 2 → F) → (Vec 2 → E)} {m' R Kc : ℕ} {C : Fin 2 → ℝ}
    (hR : 1 ≤ R) (A : ∀ j, TorusAdj (S j) m' R Kc (C j)) (ρ : ℝ) {Cf : Fin 2 → ℝ}
    (hF : ∀ j, (A j).FBound ρ (Cf j)) (hCf : ∀ j, 0 ≤ Cf j)
    {T : (Vec 2 → F) → (Vec 2 → E)}
    (hT : ∀ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      T ψ = fun x => ∑ j, fderiv ℝ (S j ψ) x (basisVec j)) :
    GAdj T m' Kc ρ (∑ j, Cf j) where
  adj K hK := -(∑ j, ((A j).adj K (by omega)).comp
    (derivativeTorusHk (K := K + m') (r := 1) (fun _ => j)))
  gbound K hK U := by
    rw [neg_apply, sqrt_fNSq_torus_neg, sum_apply]
    refine (sqrt_fNSq_torus_sum_le ρ _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (hF j K (by omega) _).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (hCf j)
    exact Finset.single_le_sum (f := fun j : Fin 2 => factorialNormSq ρ
      (derivativeTorusHk (K := K + m') (r := 1) (fun _ => j) U).val)
      (fun i _ => factorialNormSq_nonneg _ _) (Finset.mem_univ j)
  ident K hK U ψ hs hp := by
    have hm : ∀ j, ContDiff ℝ ((1 : ℕ) : ℕ∞) (S j ψ) ∧ AVenhance.IsZ2Periodic (S j ψ) :=
      fun j => (A j).maps 1 hR ψ (hs.of_le (by exact_mod_cast le_top)) hp
    have hcont : ∀ j, Continuous (fun x => fderiv ℝ (S j ψ) x (basisVec j)) := fun j =>
      ((hm j).1.continuous_fderiv (by simp)).clm_apply continuous_const
    rw [show tval ((-(∑ j, ((A j).adj K (by omega)).comp
        (derivativeTorusHk (K := K + m') (r := 1) (fun _ => j)))) U) =
        tval (-(∑ j, (A j).adj K (by omega)
          (derivativeTorusHk (K := K + m') (r := 1) (fun _ => j) U))) by
      rw [neg_apply, sum_apply]; rfl]
    rw [cellInner_tval_neg, gcellInner_tval_finsetSum _ _ hs.continuous, hT ψ hs hp,
      gcellInner_finsetSum_right _ _ _ (fun j _ => integrable_tval_inner U (hcont j)),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(A j).ident K (by omega) _ ψ (hs.of_le (by exact_mod_cast le_top)) hp,
      tval_derivativeTorusHk_single (K := K + m') U j,
      cellInner_firstDerivative_eq_neg (K := K + m') U j (hm j).1 (hm j).2, neg_neg]

end Div

end AVRegularity.CycleComparison.Coarse
end
end

section
/-! Precomposition of a gradient-form adjoint with a `TorusAdj`: if `T` has a `GAdj` of order
`m' + 1` and `T'` a `TorusAdj` of order `n` with a factorial bound, then `T ∘ T'` has a `GAdj` of
order `(n + m') + 1` with adjoint `A^* ∘ T^*`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleComparison.Coarse

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [NormedAddCommGroup G]
  [InnerProductSpace ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

/-- `GAdj` of `T ∘ T'`. The operator `T'` must map smooth periodic fields to smooth periodic
fields (a finite-regularity `TorusAdj` does not record this). -/
def GAdj.precomp {T : (Vec 2 → G) → (Vec 2 → E)} {T' : (Vec 2 → F) → (Vec 2 → G)}
    {m' n R Kc : ℕ} {ρ Cg C' Cf' : ℝ} (Gd : GAdj T m' Kc ρ Cg) (A : TorusAdj T' n R Kc C')
    (hF : A.FBound ρ Cf') (hCf' : 0 ≤ Cf')
    (hS : ∀ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      ContDiff ℝ (⊤ : ℕ∞) (T' ψ) ∧ AVenhance.IsZ2Periodic (T' ψ)) :
    GAdj (fun ψ => T (T' ψ)) (n + m') Kc ρ (Cf' * Cg) where
  adj K hK := (A.adj K (by omega)).comp
    ((Gd.adj (K + n) (by omega)).comp
      (torusCast (by omega : K + (n + m' + 1) = K + n + (m' + 1))))
  gbound K hK U := by
    have hKn : K + n ≤ Kc := by omega
    have hKm : K + n + (m' + 1) ≤ Kc := by omega
    set V := torusCast (E := E) (by omega : K + (n + m' + 1) = K + n + (m' + 1)) U with hV
    have h1 := hF K hKn (Gd.adj (K + n) hKm V)
    have h2 := Gd.gbound (K + n) hKm V
    have h3 : gradNormSq (K := K + n + m') ρ V = gradNormSq (K := K + (n + m')) ρ U :=
      gradNormSq_torusCast ρ (by omega : K + (n + m') = K + n + m') U
    rw [h3] at h2
    change Real.sqrt (factorialNormSq ρ (A.adj K hKn (Gd.adj (K + n) hKm V)).val) ≤ _
    calc _ ≤ Cf' * Real.sqrt (factorialNormSq ρ (Gd.adj (K + n) hKm V).val) := h1
      _ ≤ Cf' * (Cg * Real.sqrt (gradNormSq (K := K + (n + m')) ρ U)) :=
          mul_le_mul_of_nonneg_left h2 hCf'
      _ = Cf' * Cg * Real.sqrt (gradNormSq (K := K + (n + m')) ρ U) := (mul_assoc _ _ _).symm
  ident K hK U ψ hs hp := by
    have hKn : K + n ≤ Kc := by omega
    have hKm : K + n + (m' + 1) ≤ Kc := by omega
    obtain ⟨hs', hp'⟩ := hS ψ hs hp
    change cellInner (tval (A.adj K hKn (Gd.adj (K + n) hKm
      (torusCast (by omega : K + (n + m' + 1) = K + n + (m' + 1)) U)))) ψ = _
    rw [A.ident K hKn _ ψ (hs.of_le (by exact_mod_cast le_top)) hp,
      Gd.ident (K + n) hKm _ (T' ψ) hs' hp', tval_torusCast]

end AVRegularity.CycleComparison.Coarse
end
end
end
end

section
section
section
/-! Factorial-norm bounds for coefficient multiplication and the pointwise operators built on it:
constant operators, components, word adjoints, adjoint coefficients and tensor fluxes.

Multiplication by a coefficient `N` with derivative-array bounds `A l` costs
`∑_{l ≤ Kc} (ρ^l / l!) A l` (`fbMulConst`), by the factorial product bound
`TorusHk.mulCoefficient_factorialNorm_le`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleComparison.Coarse

/-- The factorial-norm constant `∑_{l ≤ Kc} (ρ^l / l!) A_l` of coefficient multiplication. -/
def fbMulConst (ρ : ℝ) (A : ℕ → ℝ) (Kc : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (Kc + 1), ρ ^ l / (l.factorial : ℝ) * A l

theorem fbMulConst_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) {A : ℕ → ℝ} {Kc : ℕ} (hA : ∀ l ≤ Kc, 0 ≤ A l) :
    0 ≤ fbMulConst ρ A Kc :=
  Finset.sum_nonneg fun l hl => mul_nonneg (by positivity)
    (hA l (Nat.le_of_lt_succ (Finset.mem_range.mp hl)))

theorem fbMulConst_constBound (ρ a : ℝ) (Kc : ℕ) : fbMulConst ρ (constBound a) Kc = a := by
  unfold fbMulConst
  rw [Finset.sum_range_succ']
  simp [constBound]

/-- The constant of the word adjoint `wordAdjoint m`: `2^m (Kc/ρ)^m`. -/
def fbWordConst (ρ : ℝ) (Kc m : ℕ) : ℝ := 2 ^ m * ((Kc : ℝ) / ρ) ^ m

theorem fbWordConst_nonneg {ρ : ℝ} (hρ : 0 < ρ) (Kc m : ℕ) : 0 ≤ fbWordConst ρ Kc m := by
  unfold fbWordConst; positivity

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {ρ : ℝ}

namespace TorusAdj.FBound

/-- Coefficient multiplication costs `∑_{l ≤ Kc} (ρ^l/l!) A_l`. -/
theorem mulOp (hρ : 0 ≤ ρ) {M : Vec 2 → F →L[ℝ] E} {N : Vec 2 → E →L[ℝ] F} {R Kc : ℕ}
    {hM : ContDiff ℝ (R : ℕ) M} {hMp : AVenhance.IsZ2Periodic M}
    {hN : ContDiff ℝ (Kc : ℕ) N} {hNp : AVenhance.IsZ2Periodic N}
    {hMN : ∀ x v w, inner ℝ (N x v) w = inner ℝ v (M x w)} {A : ℕ → ℝ}
    {hA : ∀ l ≤ Kc, ∀ x, ‖coefficientDerivativeArray N l x‖ ≤ A l} :
    (TorusAdj.mulOp R Kc hM hMp hN hNp hMN A hA).FBound ρ (fbMulConst ρ A Kc) :=
  fun K hK U => by
    have hKc : K ≤ Kc := by omega
    have h := U.mulCoefficient_factorialNorm_le (hN.of_le (by exact_mod_cast hKc)) hNp
      (A := fun l : Fin (K + 1) => A l.val)
      (fun l x => hA l.val ((Nat.le_of_lt_succ l.isLt).trans hKc) x) hρ
    have hnn : ∀ l ≤ Kc, 0 ≤ A l := fun l hl =>
      (ContinuousLinearMap.opNorm_nonneg _).trans (hA l hl 0)
    have hsum : ∑ l : Fin (K + 1), factorialRootWeight ρ l.val * A l.val ≤ fbMulConst ρ A Kc := by
      have e : ∑ l : Fin (K + 1), factorialRootWeight ρ l.val * A l.val =
          ∑ l ∈ Finset.range (K + 1), ρ ^ l / (l.factorial : ℝ) * A l :=
        Fin.sum_univ_eq_sum_range (fun l => ρ ^ l / (l.factorial : ℝ) * A l) (K + 1)
      rw [e]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (Nat.succ_le_succ hKc))
        (fun l hl _ => mul_nonneg (by positivity) (hnn l (Nat.le_of_lt_succ (Finset.mem_range.mp hl))))
    exact h.trans (mul_le_mul_of_nonneg_right hsum (Real.sqrt_nonneg _))

/-- A constant operator `L` costs `a ≥ ‖L'‖`. -/
theorem constOp (hρ : 0 ≤ ρ) {L : F →L[ℝ] E} {L' : E →L[ℝ] F}
    {hLL : ∀ v w, inner ℝ (L' v) w = inner ℝ v (L w)} {a : ℝ} {ha : ‖L'‖ ≤ a} {R Kc : ℕ} :
    (TorusAdj.constOp L L' hLL ha R Kc).FBound ρ a := by
  refine FBound.mono_const (Cf := fbMulConst ρ (constBound a) Kc) ?_
    (le_of_eq (fbMulConst_constBound ρ a Kc))
  unfold TorusAdj.constOp
  exact FBound.mono (FBound.mulOp hρ) le_rfl le_rfl _

theorem componentOp (hρ : 0 ≤ ρ) {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι) (R Kc : ℕ) :
    (TorusAdj.componentOp (E := E) α R Kc).FBound ρ 1 := by
  unfold TorusAdj.componentOp
  exact FBound.constOp hρ

/-- The adjoint coefficient multiplication costs `∑_{l ≤ Kc} (ρ^l/l!) B_l`. -/
theorem adjointCoeffOp (hρ : 0 ≤ ρ) {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompleteSpace Y] {C : Vec 2 → X →L[ℝ] Y} {R Kc : ℕ} {hCR : ContDiff ℝ (R : ℕ) C}
    {hCK : ContDiff ℝ (Kc : ℕ) C} {hp : AVenhance.IsZ2Periodic C} {B : ℕ → ℝ}
    {hB : ∀ l ≤ Kc, ∀ x, ‖coefficientDerivativeArray C l x‖ ≤ B l} :
    (TorusAdj.adjointCoeffOp C R Kc hCR hCK hp B hB).FBound ρ (fbMulConst ρ B Kc) := by
  unfold TorusAdj.adjointCoeffOp
  exact FBound.mulOp hρ

/-- The tensor flux costs `∑_{l ≤ Kc} (ρ^l/l!) 2^l (2^m 2) BA_l`. -/
theorem tensorFlux (hρ : 0 ≤ ρ) {m : ℕ}
    {A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {R Kc : ℕ} {hAR : ContDiff ℝ (R : ℕ) A} {hAK : ContDiff ℝ (Kc : ℕ) A}
    {hp : AVenhance.IsZ2Periodic A} {BA : ℕ → ℝ}
    {hBA : ∀ l ≤ Kc, ∀ x, ‖coefficientDerivativeArray A l x‖ ≤ BA l} :
    (TorusAdj.tensorFlux (E := E) A R Kc hAR hAK hp BA hBA).FBound ρ
      (fbMulConst ρ (tensorBound m BA) Kc) := by
  unfold TorusAdj.tensorFlux
  exact FBound.mulOp hρ

/-- The word adjoint `wordAdjoint m` costs `2^m (Kc/ρ)^m`. -/
theorem wordAdj (hρ : 0 < ρ) (m R Kc : ℕ) :
    (TorusAdj.wordAdj (E := E) m R Kc).FBound ρ (fbWordConst ρ Kc m) := by
  have h := FBound.sumMem (Finset.univ : Finset (DerivativeWord2 m)) (fun α _ =>
    FBound.ofOrder (Nat.add_zero m) (FBound.comp (orderedDerivativeRev (E := E) hρ α R Kc)
      (componentOp (E := E) hρ.le α (R + m) Kc) zero_le_one le_rfl le_rfl))
  unfold TorusAdj.wordAdj
  exact FBound.ofOp _ (((h.smul ((-1 : ℝ) ^ m)).mono le_rfl le_rfl _).mono_const (le_of_eq (by
    unfold fbWordConst
    rw [abs_pow, abs_neg, abs_one, one_pow, one_mul]
    simp [Finset.sum_const, Finset.card_univ, mul_comm])))

end TorusAdj.FBound

theorem coefficient_bound_nonneg {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {C : Vec 2 → X →L[ℝ] Y} {Kc : ℕ} {B : ℕ → ℝ}
    (hB : ∀ l ≤ Kc, ∀ x, ‖coefficientDerivativeArray C l x‖ ≤ B l) : ∀ l ≤ Kc, 0 ≤ B l :=
  fun l hl => (norm_nonneg _).trans (hB l hl 0)

end AVRegularity.CycleComparison.Coarse
end
end

section
/-! Factorial-norm bounds for the diagonal flux, the edge flux block, the commutator and the
coarse response fluxes, with explicit constants composed from the derivative and multiplication
bounds above. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleComparison.Coarse

/-- The factorial-norm constant of the diagonal flux adjoint. -/
def fbDiagConst (ρ : ℝ) (D Kc : ℕ) (BA : ℕ → ℕ → ℝ) : ℝ :=
  ∑ d : Finset.Icc 2 D,
    fbWordConst ρ Kc (d.1 - 1) * fbMulConst ρ (tensorBound (d.1 - 1) (BA d.1)) Kc

/-- The factorial-norm constant of the edge flux block. -/
def fbEdgeConst (ρ : ℝ) (D H Kc : ℕ) (BE : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
    fbWordConst ρ Kc (d.1 - 1) * fbMulConst ρ (BE r d.1) Kc

/-- The factorial-norm constant of the commutator flux adjoint. -/
def fbCommConst (ρ M : ℝ) (Kc : ℕ) (Bb : ℕ → ℝ) : ℝ :=
  2 * (((Kc : ℝ) / ρ) * fbMulConst ρ (commBound M Bb) Kc)

/-- The factorial-norm constant of the coarse response flux. -/
def fbCoarseConst (ρ : ℝ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Kc p : ℕ) (cc dg : ℝ) : ℝ :=
  coarseFluxConst (fbCovConst ρ Hc Kc) cc dg p

/-- The factorial-norm constant of the edge flux pair. -/
def fbEdgePairConst (ρ : ℝ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Kc p : ℕ) (ec : ℝ) : ℝ :=
  edgeFluxPairConst (fbCovConst ρ Hc Kc) p ec

theorem fbDiagConst_nonneg {ρ : ℝ} (hρ : 0 < ρ) {D Kc : ℕ} {BA : ℕ → ℕ → ℝ}
    (hB : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, 0 ≤ BA d.1 l) : 0 ≤ fbDiagConst ρ D Kc BA :=
  Finset.sum_nonneg fun d _ => mul_nonneg (fbWordConst_nonneg hρ _ _)
    (fbMulConst_nonneg hρ.le fun l hl => by
      have := hB d l hl
      unfold tensorBound; positivity)

theorem fbEdgeConst_nonneg {ρ : ℝ} (hρ : 0 < ρ) {D H Kc : ℕ} {BE : ℕ → ℕ → ℕ → ℝ}
    (hB : ∀ r, ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, 0 ≤ BE r d.1 l) : 0 ≤ fbEdgeConst ρ D H Kc BE :=
  Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun d _ => mul_nonneg (fbWordConst_nonneg hρ _ _)
    (fbMulConst_nonneg hρ.le (hB r d))

theorem commBound_nonneg {M : ℝ} (hM : 0 ≤ M) {Bb : ℕ → ℝ} {Kc : ℕ}
    (hB : ∀ l ≤ Kc, 0 ≤ Bb l) : ∀ l ≤ Kc, 0 ≤ commBound M Bb l := fun l hl => by
  have := hB l hl
  unfold commBound; positivity

theorem fbCommConst_nonneg {ρ : ℝ} (hρ : 0 < ρ) {M : ℝ} (hM : 0 ≤ M) {Bb : ℕ → ℝ} {Kc : ℕ}
    (hB : ∀ l ≤ Kc, 0 ≤ Bb l) : 0 ≤ fbCommConst ρ M Kc Bb := by
  have := fbMulConst_nonneg hρ.le (commBound_nonneg hM hB)
  unfold fbCommConst; positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {ρ : ℝ}

namespace TorusAdj.FBound

/-- The diagonal flux adjoint. -/
theorem diagFlux (hρ : 0 < ρ) (D : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (R Kc Q : ℕ) (hQR : R + D ≤ Q) (hQK : Kc ≤ Q)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    (TorusAdj.diagFlux (E := E) D AD s R Kc Q hQR hQK hA hp BA hBA).FBound ρ
      (fbDiagConst ρ D Kc BA) := by
  unfold TorusAdj.diagFlux
  refine FBound.ofOp _ (FBound.sum _ (fun d => FBound.liftOrder
    (FBound.comp (FBound.wordAdj (E := E) hρ _ R Kc) (FBound.tensorFlux hρ.le)
      (fbMulConst_nonneg hρ.le (fun l hl => ?_)) le_rfl le_rfl)
    (mul_nonneg (fbWordConst_nonneg hρ _ _) (fbMulConst_nonneg hρ.le (fun l hl => ?_))) _))
  all_goals
    have := coefficient_bound_nonneg (hBA d) l hl
    unfold tensorBound; positivity

/-- The edge flux block. -/
theorem edgeFluxBlock (hρ : 0 < ρ) {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompleteSpace Y] [FiniteDimensional ℝ Y] (D H : ℕ)
    (C : ℕ → ∀ d : Finset.Icc 2 D, Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => Y)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => X)))
    (R Kc Q : ℕ) (hQR : R + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (C r d)) (hp : ∀ r d, AVenhance.IsZ2Periodic (C r d))
    (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (C r d) l x‖ ≤ BE r d.1 l) :
    (TorusAdj.edgeFluxBlock D H C R Kc Q hQR hQK hC hp BE hBE).FBound ρ
      (fbEdgeConst ρ D H Kc BE) := by
  unfold TorusAdj.edgeFluxBlock
  refine FBound.sumMem _ (fun r _ => FBound.sum _ (fun d => FBound.liftOrder
    (FBound.comp (FBound.wordAdj (E := Y) hρ _ R Kc) (FBound.adjointCoeffOp hρ.le)
      (fbMulConst_nonneg hρ.le (coefficient_bound_nonneg (hBE r d))) le_rfl le_rfl)
    (mul_nonneg (fbWordConst_nonneg hρ _ _)
      (fbMulConst_nonneg hρ.le (coefficient_bound_nonneg (hBE r d)))) _))

/-- The commutator flux adjoint costs `2 (Kc/ρ) ∑_{l ≤ Kc} (ρ^l/l!) commBound_l`. -/
theorem commutator (hρ : 0 < ρ) (b : ℝ → Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ}
    (hM : covBound Hc ≤ M) (s : ℝ) (R Kc Q : ℕ) (hQR : R + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l) :
    (TorusAdj.commutator (E := E) b Hc hM s R Kc Q hQR hQK hb hp Bb hBb).FBound ρ
      (fbCommConst ρ M Kc Bb) := by
  have hBb0 : ∀ l ≤ Kc, 0 ≤ Bb l := fun l hl => (norm_nonneg _).trans (hBb l hl 0)
  have hM0 : 0 ≤ M := (covBound_nonneg Hc).trans hM
  have hmul := fbMulConst_nonneg hρ.le (commBound_nonneg hM0 hBb0)
  unfold TorusAdj.commutator
  refine FBound.mono_const (Cf := ∑ _j : Fin 2, ((Kc : ℝ) / ρ) * fbMulConst ρ (commBound M Bb) Kc)
    ?_ (le_of_eq (by unfold fbCommConst; simp [Finset.sum_const]))
  exact FBound.ofOp _ (FBound.mono (FBound.sum _ (fun j => FBound.ofOrder _
    (FBound.comp (FBound.coordDeriv (E := E) hρ j R Kc) (FBound.mulOp hρ.le)
      hmul le_rfl le_rfl))) le_rfl le_rfl _)

end TorusAdj.FBound

end AVRegularity.CycleComparison.Coarse
end
end
end

section
section
/-! The inner fluxes `Sⱼ` of the coarse response flux operators, in divergence form
`T = ∑ⱼ ∂ⱼ ∘ Sⱼ`, as `TorusAdj`, with the divergence identities below. The flux
`ψ ↦ -(F_p^* 𝖰_p ψ)` has
`Sⱼ ψ = -(∑_l (1/l!) ∑_a 𝒞^{l-1-a}(𝔑ⱼ · 𝒞^a 𝖰_p ψ) - 𝖯_p ∑_d W_{d-1,j}(A_d ⊗ id 𝖰_p ψ))`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleComparison.Coarse

/-- The constant of the divergence-form diagonal flux. -/
def diagDivConst (D Kc : ℕ) (BA : ℕ → ℕ → ℝ) : ℝ :=
  ∑ d : Finset.Icc 2 D, wordDivConst (d.1 - 1) Kc * tensorConst (d.1 - 1) Kc (BA d.1)

/-- The constant of the divergence-form edge flux. -/
def edgeDivConst (D H Kc : ℕ) (BE : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D, wordDivConst (d.1 - 1) Kc * mulConst (BE r d.1) Kc

/-- The constant of the inner flux `Sⱼ` of the coarse flux operator. -/
def coarseFluxDivConst (M cc dgd : ℝ) (p : ℕ) : ℝ :=
  (fluxConstA M cc p + covPolyConst M p * dgd) * covPolyConst M p

section Ops

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The inner commutator coefficient `φ ↦ ∑ₖ 𝔑_{kj} φ_k`, of order zero. -/
def TorusAdj.commInner (b : ℝ → Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ}
    (hM : covBound Hc ≤ M) (s : ℝ) (j : Fin 2) (R Kc Q : ℕ) (hQR : R + 1 ≤ Q)
    (hQK : Kc + 1 ≤ Q) (hb : ContDiff ℝ (Q : ℕ) (b s)) (hp : AVenhance.IsZ2Periodic (b s))
    (Bb : ℕ → ℝ) (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l) :
    TorusAdj (fun (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (x : Vec 2) =>
      commFluxMap E Hc j (fderiv ℝ (b s) x) (φ x)) 0 R Kc (mulConst (commBound M Bb) Kc) := by
  have hD : ∀ n : ℕ, n + 1 ≤ Q → ContDiff ℝ (n : ℕ) (fderiv ℝ (b s)) := fun n hn =>
    hb.fderiv_right (m := n) (by exact_mod_cast hn)
  have hDp : AVenhance.IsZ2Periodic (fderiv ℝ (b s)) :=
    fderiv_isZ2Periodic (hb.differentiable (by
      have : (1 : ℕ) ≤ Q := by omega
      exact_mod_cast (by omega : Q ≠ 0))) hp
  exact TorusAdj.mulOp (M := fun x => commFluxMap E Hc j (fderiv ℝ (b s) x))
    (N := fun x => commPrimalMap E Hc j (fderiv ℝ (b s) x)) R Kc
    (contDiff_clm_comp (commFluxMap E Hc j) (hD R hQR)) (isZ2Periodic_clm_comp _ hDp)
    (contDiff_clm_comp (commPrimalMap E Hc j) (hD Kc hQK)) (isZ2Periodic_clm_comp _ hDp)
    (fun x v w => inner_commPrimalVec Hc j _ v w) (commBound M Bb) (by
      intro l hl x
      have hl' : l + 1 ≤ Q := by omega
      refine (norm_array_clm_comp_le (commPrimalMap E Hc j) (fderiv ℝ (b s)) l
        (hD l hl') x).trans ?_
      unfold commBound
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul ((norm_commPrimalMap_le Hc j).trans
        (mul_le_mul_of_nonneg_left hM (by norm_num))) ?_ (norm_nonneg _) ?_
      · refine (norm_array_le_iteratedFDeriv _ l (hD l hl') x).trans ?_
        rw [norm_iteratedFDeriv_fderiv]
        exact mul_le_mul_of_nonneg_left (hBb l hl x) (by positivity)
      · linarith [covBound_nonneg Hc])

/-- The `j`-th inner term `𝒞^n(𝔑ⱼ · 𝒞^a φ)` of `𝒞^n 𝒥_H^* 𝒞^a φ`. -/
def commStepOp (b : ℝ → Vec 2 → Vec 2) (s : ℝ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2)
    (n a : ℕ) (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) : Vec 2 → E :=
  (AVRegularity.covOperator Hc)^[n]
    (fun x => commFluxMap E Hc j (fderiv ℝ (b s) x) (((AVRegularity.covOperator Hc)^[a] φ) x))

/-- One inner commutator term, as an operator of order `2p + D - 1`. -/
def TorusAdj.commStep (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (b : ℝ → Vec 2 → Vec 2) (s : ℝ) (j : Fin 2) (R Kc Q p D l a : ℕ) (hal : a < l) (hlp : l ≤ p)
    (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l) :
    TorusAdj (commStepOp (E := E) b s Hc j (l - 1 - a) a) (2 * p + D - 1) R Kc
      (M ^ (l - 1 - a) * (mulConst (commBound M Bb) Kc * M ^ a)) :=
  (((TorusAdj.covIter (E := E) Hc hM (l - 1 - a) R Kc).comp
    ((TorusAdj.commInner (E := E) b Hc hM s j (R + 2 * (l - 1 - a)) Kc Q (by omega) hQK hb hbp
      Bb hBb).comp
      (TorusAdj.covIter (E := PiLp 2 (fun _ : Fin 2 => E)) Hc hM a (R + 2 * (l - 1 - a)) Kc)
      le_rfl le_rfl) le_rfl le_rfl).liftOrder (by omega)).ofOp
    (by funext φ; rfl)

/-- The divergence-form diagonal flux: `φ ↦ ∑_d W_{d-1,j}(A_d ⊗ id φ)`, of order `D - 2`. -/
def TorusAdj.diagFluxDiv (D : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (j : Fin 2) (R Kc Q : ℕ) (hQR : R + D ≤ Q) (hQK : Kc ≤ Q)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    TorusAdj (fun (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (x : Vec 2) =>
      ∑ d : Finset.Icc 2 D, wordDivTerm (d.1 - 1) j
        (fun y => AVRegularity.tensorFluxAdjoint (AD d s y) (φ y)) x) (D - 2) R Kc
      (diagDivConst D Kc BA) :=
  (TorusAdj.sum (Finset.univ : Finset (Finset.Icc 2 D)) (fun d =>
    ((TorusAdj.wordDiv (E := E) (d.1 - 1) j R Kc).comp
      (TorusAdj.tensorFlux (E := E) (AD d s) (R + (d.1 - 1)) Kc
        ((hA d).of_le (by have := Finset.mem_Icc.mp d.2; exact_mod_cast (by omega)))
        ((hA d).of_le (by exact_mod_cast hQK)) (hp d) (BA d.1) (hBA d)) le_rfl
      (by omega)).liftOrder
      (by have := Finset.mem_Icc.mp d.2; omega : d.1 - 1 - 1 + 0 ≤ D - 2))).ofOp
    (by funext φ x; rfl)

/-- The operator `Sⱼ` of the divergence form of the coarse flux, before composing with `𝖰_p`. -/
def coarseFluxDivOp (D : ℕ) (b : ℝ → Vec 2 → Vec 2)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (s : ℝ) (j : Fin 2)
    (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) : Vec 2 → E :=
  fun x => (∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
      commStepOp b s Hc j (l - 1 - a) a φ x) -
    AVRegularity.covPolyP Hc p (fun x => ∑ d : Finset.Icc 2 D, wordDivTerm (d.1 - 1) j
      (fun y => AVRegularity.tensorFluxAdjoint (AD d s y) (φ y)) x) x

/-- The inner flux `Sⱼ` of the coarse flux operator, before composing with `𝖰_p`. -/
def TorusAdj.fluxDiv (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (b : ℝ → Vec 2 → Vec 2) (D p : ℕ) (hD : 1 ≤ D)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (j : Fin 2) (R Kc Q : ℕ) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    TorusAdj (coarseFluxDivOp (E := E) D b AD Hc p s j) (2 * p + D - 1) R Kc
      (fluxConstA M (mulConst (commBound M Bb) Kc) p +
        covPolyConst M p * diagDivConst D Kc BA) :=
  ((((TorusAdj.sumMem (Finset.Icc 1 p) fun l hl =>
        (TorusAdj.sumMem (Finset.range l) fun a ha =>
          TorusAdj.commStep (E := E) Hc hM b s j R Kc Q p D l a (Finset.mem_range.mp ha)
            (Finset.mem_Icc.mp hl).2 hQR hQK hb hbp Bb hBb).smul ((l.factorial : ℝ)⁻¹)).mono
      le_rfl le_rfl (le_of_eq (by
        unfold fluxConstA
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]))).sub
    (((TorusAdj.covPolyP (E := E) Hc hM p R Kc).comp
      (TorusAdj.diagFluxDiv (E := E) D AD s j (R + 2 * p) Kc Q (by omega) (by omega) hA hAp BA
        hBA) le_rfl le_rfl).liftOrder (by omega : 2 * p + (D - 2) ≤ 2 * p + D - 1))).ofOp
    (by
      funext φ x
      simp [coarseFluxDivOp])).mono le_rfl le_rfl (le_of_eq rfl)

/-- The inner flux `Sⱼ` of the coarse response flux `ψ ↦ -(F_p^* 𝖰_p ψ)`: order `4p + D - 1`. -/
def TorusAdj.coarseFluxDiv (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (b : ℝ → Vec 2 → Vec 2) (D p : ℕ) (hD : 1 ≤ D)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (j : Fin 2) (R Kc Q : ℕ) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      fun x => -(coarseFluxDivOp (E := E) D b AD Hc p s j (AVRegularity.covPolyQ Hc p ψ) x))
      (4 * p + D - 1) R Kc
      (coarseFluxDivConst M (mulConst (commBound M Bb) Kc) (diagDivConst D Kc BA) p) :=
  ((((TorusAdj.fluxDiv (E := E) Hc hM b D p hD AD s j R Kc Q
    hQR hQK hb hbp Bb hBb hA hAp BA hBA).comp
    (TorusAdj.covPolyQ (E := PiLp 2 (fun _ : Fin 2 => E)) Hc hM p (R + (2 * p + D - 1)) Kc)
    le_rfl le_rfl).neg.ofOrder (by omega : 2 * p + D - 1 + 2 * p = 4 * p + D - 1)).mono
    le_rfl le_rfl (le_of_eq rfl))


/-- The `(v,u)` block of the divergence-form edge flux at a fixed time: order `D - 2`. -/
def TorusAdj.edgeFluxBlockDiv {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompleteSpace Y] [FiniteDimensional ℝ Y] (D H : ℕ)
    (C : ℕ → ∀ d : Finset.Icc 2 D, Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => Y)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => X)))
    (j : Fin 2) (R Kc Q : ℕ) (hQR : R + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (C r d)) (hp : ∀ r d, AVenhance.IsZ2Periodic (C r d))
    (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (C r d) l x‖ ≤ BE r d.1 l) :
    TorusAdj (fun (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => X)) (x : Vec 2) =>
      ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D, wordDivTerm (d.1 - 1) j
        (fun y => ContinuousLinearMap.adjoint (C r d y) (ψ y)) x) (D - 2) R Kc
      (edgeDivConst D H Kc BE) :=
  TorusAdj.sumMem (Finset.Icc 1 H) fun r _ =>
    (TorusAdj.sum (Finset.univ : Finset (Finset.Icc 2 D)) (fun d =>
      ((TorusAdj.wordDiv (E := Y) (d.1 - 1) j R Kc).comp
        (TorusAdj.adjointCoeffOp (C r d) (R + (d.1 - 1)) Kc
          ((hC r d).of_le (by have := Finset.mem_Icc.mp d.2; exact_mod_cast (by omega)))
          ((hC r d).of_le (by exact_mod_cast hQK)) (hp r d) (BE r d.1) (hBE r d))
        le_rfl (by omega)).liftOrder
        (by have := Finset.mem_Icc.mp d.2; omega : d.1 - 1 - 1 + 0 ≤ D - 2)))

/-- The inner flux `Sⱼ` of the `(v,u)` block of the edge flux operator
`ψ ↦ 𝖯_p (F_E^* 𝖰_p ψ)_u`: order `4p + D - 1`. -/
def TorusAdj.edgeFluxPairDiv {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M) (D H p : ℕ) (hD : 1 ≤ D)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) (s : ℝ) (j : Fin 2) (R Kc Q : ℕ) (hQR : R + 2 * p + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (CE r v u d s))
    (hp : ∀ r d, AVenhance.IsZ2Periodic (CE r v u d s)) (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (CE r v u d s) l x‖ ≤ BE r d.1 l) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP Hc p (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
        wordDivTerm (d.1 - 1) j
          (fun y => ContinuousLinearMap.adjoint (CE r v u d s y)
            (AVRegularity.covPolyQ Hc p ψ y)) x)) (4 * p + D - 1) R Kc
      (edgeFluxPairConst M p (edgeDivConst D H Kc BE)) :=
  ((TorusAdj.covPolyP (E := h u) Hc hM p R Kc).comp
    ((TorusAdj.edgeFluxBlockDiv (X := h v) (Y := h u) D H (fun r d => CE r v u d s) j
      (R + 2 * p) Kc Q (by omega) hQK hC hp BE hBE).comp
      (TorusAdj.covPolyQ (E := PiLp 2 (fun _ : Fin 2 => h v)) Hc hM p
        (R + 2 * p + (D - 2)) Kc) le_rfl le_rfl) le_rfl le_rfl).liftOrder
    (by omega : 2 * p + (D - 2 + 2 * p) ≤ 4 * p + D - 1)

end Ops

end AVRegularity.CycleComparison.Coarse
end
end

section
/-! Factorial-norm bounds for the coarse response flux operators `coarseFlux` and `edgeFluxPair`,
and their commutator terms. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleComparison.Coarse

theorem covPolyConst_nonneg {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p Kc : ℕ) :
    0 ≤ covPolyConst (fbCovConst ρ Hc Kc) p :=
  Finset.sum_nonneg fun l _ => div_nonneg (pow_nonneg (fbCovConst_nonneg hρ Hc Kc) l)
    (Nat.cast_nonneg _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {ρ : ℝ}

namespace TorusAdj.FBound

/-- One term `𝒞^{l-1-a} 𝒥_H^* 𝒞^a` of the commutator part of the coarse flux. -/
theorem coarseCommTerm (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ}
    (hM : covBound Hc ≤ M) (b : ℝ → Vec 2 → Vec 2) (s : ℝ) (R Kc Q p D l a : ℕ) (hal : a < l)
    (hlp : l ≤ p) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l) :
    (TorusAdj.coarseCommTerm (E := E) Hc hM b s R Kc Q p D l a hal hlp hQR hQK hb hbp Bb
      hBb).FBound ρ
      (fbCovConst ρ Hc Kc ^ (l - 1 - a) * (fbCommConst ρ M Kc Bb * fbCovConst ρ Hc Kc ^ a)) := by
  have hc := fbCovConst_nonneg hρ Hc Kc
  have hBb0 : ∀ l ≤ Kc, 0 ≤ Bb l := fun l hl => (norm_nonneg _).trans (hBb l hl 0)
  have hcomm := fbCommConst_nonneg hρ ((covBound_nonneg Hc).trans hM) hBb0
  have h2 : 0 ≤ fbCommConst ρ M Kc Bb * fbCovConst ρ Hc Kc ^ a :=
    mul_nonneg hcomm (pow_nonneg hc a)
  unfold TorusAdj.coarseCommTerm
  exact FBound.liftOrder (FBound.comp (FBound.covIter (E := E) hρ Hc hM _ R Kc)
    (FBound.comp (FBound.commutator (E := E) hρ b Hc hM s _ Kc Q (by omega) hQK hb hbp Bb hBb)
      (FBound.covIter (E := PiLp 2 (fun _ : Fin 2 => E)) hρ Hc hM a _ Kc)
      (pow_nonneg hc a) le_rfl le_rfl) h2 le_rfl le_rfl)
    (mul_nonneg (pow_nonneg hc _) h2) _

/-- The commutator part `∑_l (1/l!) ∑_a 𝒞^{l-1-a} 𝒥_H^* 𝒞^a` of the coarse flux. -/
theorem coarseCommPart (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (b : ℝ → Vec 2 → Vec 2) (D p : ℕ) (s : ℝ) (R Kc Q : ℕ) (hQR : R + 2 * p + D + 2 ≤ Q)
    (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l) :
    (TorusAdj.sumMem (Finset.Icc 1 p) fun l hl =>
        (TorusAdj.sumMem (Finset.range l) fun a ha =>
          TorusAdj.coarseCommTerm (E := E) Hc hM b s R Kc Q p D l a (Finset.mem_range.mp ha)
            (Finset.mem_Icc.mp hl).2 hQR hQK hb hbp Bb hBb).smul ((l.factorial : ℝ)⁻¹)).FBound ρ
      (fluxConstA (fbCovConst ρ Hc Kc) (fbCommConst ρ M Kc Bb) p) := by
  refine FBound.mono_const (Cf := ∑ l ∈ Finset.Icc 1 p, |((l.factorial : ℝ)⁻¹)| *
    ∑ a ∈ Finset.range l, fbCovConst ρ Hc Kc ^ (l - 1 - a) *
      (fbCommConst ρ M Kc Bb * fbCovConst ρ Hc Kc ^ a)) ?_ (le_of_eq ?_)
  · exact FBound.sumMem _ (fun l hl => FBound.smul _
      (FBound.sumMem _ (fun a ha => FBound.coarseCommTerm hρ Hc hM b s R Kc Q p D l a
        (Finset.mem_range.mp ha) (Finset.mem_Icc.mp hl).2 hQR hQK hb hbp Bb hBb)))
  · unfold fluxConstA
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]

/-- The diagonal part `𝖯_p ∘ 𝒟` of the coarse flux. -/
theorem coarseDiagPart (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M) (D p : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (R Kc Q : ℕ) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    ((TorusAdj.covPolyP (E := E) Hc hM p R Kc).comp
      (TorusAdj.diagFlux (E := E) D AD s (R + 2 * p) Kc Q (by omega) (by omega) hA hAp BA hBA)
      le_rfl le_rfl).liftOrder (by omega : 2 * p + (D - 1) ≤ 2 * p + D) |>.FBound ρ
      (covPolyConst (fbCovConst ρ Hc Kc) p * fbDiagConst ρ D Kc BA) := by
  have hdg : 0 ≤ fbDiagConst ρ D Kc BA :=
    fbDiagConst_nonneg hρ (fun d l hl => coefficient_bound_nonneg (hBA d) l hl)
  have hkap := covPolyConst_nonneg hρ Hc p Kc
  exact FBound.liftOrder (FBound.comp (FBound.covPolyP (E := E) hρ Hc hM p R Kc)
      (FBound.diagFlux hρ D AD s (R + 2 * p) Kc Q (by omega) (by omega) hA hAp BA hBA) hdg
      le_rfl le_rfl) (mul_nonneg hkap hdg) _

/-- The coarse response flux. -/
theorem coarseFlux (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (b : ℝ → Vec 2 → Vec 2) (D p : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (R Kc Q : ℕ) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    (TorusAdj.coarseFlux (E := E) Hc hM b D p AD s R Kc Q hQR hQK hb hbp Bb hBb hA hAp BA
      hBA).FBound ρ
      (fbCoarseConst ρ Hc Kc p (fbCommConst ρ M Kc Bb) (fbDiagConst ρ D Kc BA)) := by
  have hdg : 0 ≤ fbDiagConst ρ D Kc BA :=
    fbDiagConst_nonneg hρ (fun d l hl => coefficient_bound_nonneg (hBA d) l hl)
  have hkap := covPolyConst_nonneg hρ Hc p Kc
  have h1 := coarseCommPart (E := E) hρ Hc hM b D p s R Kc Q hQR hQK hb hbp Bb hBb
  have h2 := coarseDiagPart (E := E) hρ Hc hM D p AD s R Kc Q hQR hQK hA hAp BA hBA
  have h3 := FBound.covPolyQ (E := PiLp 2 (fun _ : Fin 2 => E)) hρ Hc hM p (R + (2 * p + D)) Kc
  unfold TorusAdj.coarseFlux
  exact FBound.mono (FBound.ofOrder _ (FBound.neg (FBound.comp (FBound.ofOp _ (FBound.sub
    (FBound.mono h1 le_rfl le_rfl _) h2)) h3 hkap le_rfl le_rfl))) le_rfl le_rfl _

/-- The edge flux pair. -/
theorem edgeFluxPair {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M) (D H p : ℕ)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) (s : ℝ) (R Kc Q : ℕ) (hQR : R + 2 * p + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (CE r v u d s))
    (hp : ∀ r d, AVenhance.IsZ2Periodic (CE r v u d s)) (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (CE r v u d s) l x‖ ≤ BE r d.1 l) :
    (TorusAdj.edgeFluxPair Hc hM D H p CE v u s R Kc Q hQR hQK hC hp BE hBE).FBound ρ
      (fbEdgePairConst ρ Hc Kc p (fbEdgeConst ρ D H Kc BE)) := by
  have hec : 0 ≤ fbEdgeConst ρ D H Kc BE :=
    fbEdgeConst_nonneg hρ (fun r d l hl => coefficient_bound_nonneg (hBE r d) l hl)
  have hkap := covPolyConst_nonneg hρ Hc p Kc
  unfold TorusAdj.edgeFluxPair
  exact FBound.liftOrder (FBound.comp (FBound.covPolyP (E := h u) hρ Hc hM p R Kc)
    (FBound.comp (FBound.edgeFluxBlock (X := h v) (Y := h u) hρ D H (fun r d => CE r v u d s)
      (R + 2 * p) Kc Q (by omega) hQK hC hp BE hBE)
      (FBound.covPolyQ (E := PiLp 2 (fun _ : Fin 2 => h v)) hρ Hc hM p _ Kc)
      hkap le_rfl le_rfl) (mul_nonneg hec hkap) le_rfl le_rfl)
    (mul_nonneg hkap (mul_nonneg hec hkap)) _

end TorusAdj.FBound

end AVRegularity.CycleComparison.Coarse
end
end

section
/-! Divergence-form identities of the coarse response flux operators on smooth fields:
`ψ ↦ -(F_p^* 𝖰_p ψ)` equals `∑ⱼ ∂ⱼ Sⱼ ψ` and `ψ ↦ 𝖯_p (F_E^* 𝖰_p ψ)_u` equals `∑ⱼ ∂ⱼ Sⱼ ψ`,
with the inner fluxes `Sⱼ` above. Only finite regularity of the coefficients is used. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.CycleComparison.Coarse

section Coarse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_covPolyQ_smooth (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℕ) :
    ContDiff ℝ (r : WithTop ℕ∞) (AVRegularity.covPolyQ Hc p ψ) :=
  (ConstCoefOp.covPolyQ (E := E) Hc p).reg r ψ
    (contDiff_infty.mp hψ (r + 2 * p))

/-- One inner commutator term in divergence form. -/
theorem commStep_divRep (Hc : Matrix (Fin 2) (Fin 2) ℝ) (b : ℝ → Vec 2 → Vec 2) (s : ℝ)
    (n a Q : ℕ) (hQ : 2 * n + 2 ≤ Q) (hb : ContDiff ℝ (Q : ℕ) (b s))
    (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (hφ : ∀ r : ℕ, ContDiff ℝ (r : WithTop ℕ∞) φ) :
    DivRep ((AVRegularity.covOperator Hc)^[n]
        (AVRegularity.commutatorAdjoint b Hc s ((AVRegularity.covOperator Hc)^[a] φ)))
      (fun j => commStepOp b s Hc j n a φ) := by
  have hφ' : ∀ r : ℕ, ContDiff ℝ (r : WithTop ℕ∞) ((AVRegularity.covOperator Hc)^[a] φ) :=
    fun r => (ConstCoefOp.covIter (E := PiLp 2 (fun _ : Fin 2 => E)) Hc a).reg r φ (hφ _)
  have hD : ∀ k : ℕ, k + 1 ≤ Q → ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ (b s)) := fun k hk =>
    hb.fderiv_right (m := k) (by exact_mod_cast hk)
  have hg : ∀ j : Fin 2, ContDiff ℝ ((n * 2 + 1 : ℕ) : WithTop ℕ∞)
      (fun x => commFluxMap E Hc j (fderiv ℝ (b s) x) (((AVRegularity.covOperator Hc)^[a] φ) x)) :=
    fun j => (contDiff_clm_comp (commFluxMap E Hc j) (hD (n * 2 + 1) (by omega))).clm_apply
      (hφ' _)
  have hdr : DivRep (AVRegularity.commutatorAdjoint b Hc s ((AVRegularity.covOperator Hc)^[a] φ))
      (fun j x => commFluxMap E Hc j (fderiv ℝ (b s) x)
        (((AVRegularity.covOperator Hc)^[a] φ) x)) :=
    ⟨fun j => contDiff_mono_nat (by omega) (hg j), by funext x; rfl⟩
  exact DivRep.constCoef (ConstCoefOp.covIter (E := E) Hc n) hdr hg

/-- The diagonal flux in divergence form. -/
theorem diagFlux_divRep (Hc : Matrix (Fin 2) (Fin 2) ℝ) (D p : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (Q : ℕ) (hQ : 2 * p + D + 1 ≤ Q) (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s))
    (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (hφ : ∀ r : ℕ, ContDiff ℝ (r : WithTop ℕ∞) φ) :
    DivRep (AVRegularity.covPolyP Hc p (AVRegularity.diagonalFluxAdjoint D AD s φ))
      (fun j => AVRegularity.covPolyP Hc p (fun x => ∑ d : Finset.Icc 2 D,
        wordDivTerm (d.1 - 1) j (fun y => AVRegularity.tensorFluxAdjoint (AD d s y) (φ y)) x)) := by
  have hG : ∀ (d : Finset.Icc 2 D) (k : ℕ), k ≤ Q → ContDiff ℝ (k : WithTop ℕ∞)
      (fun y => AVRegularity.tensorFluxAdjoint (AD d s y) (φ y)) := fun d k hk =>
    (contDiff_clm_comp (tensorFluxAdjointMap E (d.1 - 1))
      ((hA d).of_le (by exact_mod_cast hk))).clm_apply (hφ k)
  have hin : DivRep (AVRegularity.diagonalFluxAdjoint D AD s φ)
      (fun j x => ∑ d : Finset.Icc 2 D, wordDivTerm (d.1 - 1) j
        (fun y => AVRegularity.tensorFluxAdjoint (AD d s y) (φ y)) x) :=
    DivRep.sum (Finset.univ : Finset (Finset.Icc 2 D)) (fun d _ => by
      have hd := Finset.mem_Icc.mp d.2
      exact wordAdjoint_divRep (by omega) _ (hG d _ (by omega)))
  refine DivRep.constCoef (ConstCoefOp.covPolyP (E := E) Hc p) hin fun j => ?_
  refine ContDiff.sum fun d _ => ?_
  have hd := Finset.mem_Icc.mp d.2
  exact contDiff_wordDivTerm (by omega) j (r := 2 * p + 1) (hG d _ (by omega))

theorem coarseFluxAdjoint_eq (Hc : Matrix (Fin 2) (Fin 2) ℝ) (b : ℝ → Vec 2 → Vec 2) (D p : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) :
    AVRegularity.coarseFluxAdjoint D b AD Hc p s φ =
      fun x => (∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
        ((AVRegularity.covOperator Hc)^[l - 1 - a]
          (AVRegularity.commutatorAdjoint b Hc s ((AVRegularity.covOperator Hc)^[a] φ))) x) -
        AVRegularity.covPolyP Hc p (AVRegularity.diagonalFluxAdjoint D AD s φ) x := by
  funext x
  simp [AVRegularity.coarseFluxAdjoint, Finset.sum_apply]

/-- The coarse flux operator in divergence form, on a smooth field. -/
theorem coarseFlux_divRep (Hc : Matrix (Fin 2) (Fin 2) ℝ) (b : ℝ → Vec 2 → Vec 2) (D p : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (Q : ℕ) (hQ : 2 * p + D + 2 ≤ Q) (hb : ContDiff ℝ (Q : ℕ) (b s))
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s))
    (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (hφ : ∀ r : ℕ, ContDiff ℝ (r : WithTop ℕ∞) φ) :
    DivRep (fun x => -(AVRegularity.coarseFluxAdjoint D b AD Hc p s φ x))
      (fun j x => -(coarseFluxDivOp D b AD Hc p s j φ x)) := by
  have hcomm : DivRep (fun x => ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) •
      ∑ a ∈ Finset.range l, ((AVRegularity.covOperator Hc)^[l - 1 - a]
        (AVRegularity.commutatorAdjoint b Hc s ((AVRegularity.covOperator Hc)^[a] φ))) x)
      (fun j x => ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) •
        ∑ a ∈ Finset.range l, commStepOp b s Hc j (l - 1 - a) a φ x) :=
    DivRep.sum (Finset.Icc 1 p) fun l hl => DivRep.smul _
      (DivRep.sum (Finset.range l) fun a ha =>
        commStep_divRep Hc b s (l - 1 - a) a Q (by
          have := Finset.mem_Icc.mp hl; have := Finset.mem_range.mp ha; omega) hb φ hφ)
  have hdiag := diagFlux_divRep Hc D p AD s Q (by omega) hA φ hφ
  rw [coarseFluxAdjoint_eq]
  exact (hcomm.sub hdiag).neg

end Coarse

section Edge

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, CompleteSpace (h i)]

/-- The edge flux operator in divergence form, on a smooth field. -/
theorem edgeFlux_divRep (Hc : Matrix (Fin 2) (Fin 2) ℝ) (D H p : ℕ)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) (s : ℝ) (Q : ℕ) (hQ : 2 * p + D + 1 ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (CE r v u d s))
    (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) (hφ : ∀ r : ℕ, ContDiff ℝ (r : WithTop ℕ∞) φ) :
    DivRep (AVRegularity.covPolyP Hc p (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
        AVRegularity.wordAdjoint (d.1 - 1)
          (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (φ y)) x))
      (fun j => AVRegularity.covPolyP Hc p (fun x => ∑ r ∈ Finset.Icc 1 H,
        ∑ d : Finset.Icc 2 D, wordDivTerm (d.1 - 1) j
          (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (φ y)) x)) := by
  have hG : ∀ (r : ℕ) (d : Finset.Icc 2 D) (k : ℕ), k ≤ Q → ContDiff ℝ (k : WithTop ℕ∞)
      (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (φ y)) := fun r d k hk =>
    (contDiff_clm_comp (adjointCLM (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u))
      (PiLp 2 (fun _ : Fin 2 => h v))) ((hC r d).of_le (by exact_mod_cast hk))).clm_apply (hφ k)
  have hin : DivRep (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
        AVRegularity.wordAdjoint (d.1 - 1)
          (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (φ y)) x)
      (fun j x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D, wordDivTerm (d.1 - 1) j
          (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (φ y)) x) :=
    DivRep.sum (Finset.Icc 1 H) fun r _ =>
      DivRep.sum (Finset.univ : Finset (Finset.Icc 2 D)) (fun d _ => by
        have hd := Finset.mem_Icc.mp d.2
        exact wordAdjoint_divRep (by omega) _ (hG r d _ (by omega)))
  refine DivRep.constCoef (ConstCoefOp.covPolyP (E := h u) Hc p) hin fun j => ?_
  refine ContDiff.sum fun r _ => ContDiff.sum fun d _ => ?_
  have hd := Finset.mem_Icc.mp d.2
  exact contDiff_wordDivTerm (by omega) j (r := 2 * p + 1) (hG r d _ (by omega))

end Edge

end AVRegularity.CycleComparison.Coarse
end
end
end
end
