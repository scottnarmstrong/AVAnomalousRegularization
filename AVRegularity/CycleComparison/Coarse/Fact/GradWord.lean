-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Coarse.Adj.Coarse
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.Int.Star

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! Constant-coefficient operators commute with the coordinate derivatives.

The covariance operator `𝒞`, its iterates and the polynomials `𝖯_p`, `𝖰_p` are additive,
homogeneous, lower the regularity by their order, and commute with every `∂_j` on fields of
sufficiently high regularity. These facts are packaged in `ConstCoefOp N T` for an operator `T`
of order `N`, and `ConstCoefOp.div` moves such an operator inside a divergence. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem partialOp_apply (i : Fin 2) (g : Vec 2 → E) (x : Vec 2) :
    partialOp i g x = fderiv ℝ g x (basisVec i) := rfl

theorem contDiff_partialOp {k : ℕ} {g : Vec 2 → E}
    (hg : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g) (i : Fin 2) :
    ContDiff ℝ (k : WithTop ℕ∞) (partialOp i g) :=
  (hg.fderiv_right (by exact_mod_cast le_rfl)).clm_apply contDiff_const

theorem partialOp_partialOp {g : Vec 2 → E} (hg : ContDiff ℝ 2 g) (i j : Fin 2) (x : Vec 2) :
    partialOp i (partialOp j g) x = fderiv ℝ (fderiv ℝ g) x (basisVec i) (basisVec j) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (basisVec j) x)
  change (fderiv ℝ (fun y => fderiv ℝ g y (basisVec j)) x) (basisVec i) = _
  rw [h.fderiv]
  simp

theorem partialOp_comm {g : Vec 2 → E} (hg : ContDiff ℝ 2 g) (i j : Fin 2) :
    partialOp i (partialOp j g) = partialOp j (partialOp i g) := by
  funext x
  rw [partialOp_partialOp hg, partialOp_partialOp hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

theorem partialOp_sum {ι : Type*} (j : Fin 2) (s : Finset ι) (f : ι → Vec 2 → E)
    (hf : ∀ i ∈ s, ContDiff ℝ 1 (f i)) :
    partialOp j (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, partialOp j (f i) x := by
  funext x
  change fderiv ℝ (fun x => ∑ i ∈ s, f i x) x (basisVec j) = _
  rw [fderiv_fun_sum (fun i hi => (hf i hi).differentiable one_ne_zero x)]
  simp [partialOp_apply]

theorem partialOp_smul (j : Fin 2) (c : ℝ) {f : Vec 2 → E} (hf : ContDiff ℝ 1 f) :
    partialOp j (fun x => c • f x) = fun x => c • partialOp j f x := by
  funext x
  change fderiv ℝ (fun x => c • f x) x (basisVec j) = _
  rw [fderiv_fun_const_smul (hf.differentiable one_ne_zero x)]
  rfl

theorem covOperator_eq (Hc : Matrix (Fin 2) (Fin 2) ℝ) (f : Vec 2 → E) :
    AVRegularity.covOperator Hc f =
      fun x => ∑ i : Fin 2, ∑ j : Fin 2, Hc i j • partialOp i (partialOp j f) x := rfl

theorem contDiff_covOperator (Hc : Matrix (Fin 2) (Fin 2) ℝ) {r : ℕ} {f : Vec 2 → E}
    (hf : ContDiff ℝ ((r + 2 : ℕ) : WithTop ℕ∞) f) :
    ContDiff ℝ (r : WithTop ℕ∞) (AVRegularity.covOperator Hc f) := by
  rw [covOperator_eq]
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.const_smul _ ?_
  exact contDiff_partialOp (contDiff_partialOp (k := r + 1) hf j) i

theorem covOperator_sum {ι : Type*} (Hc : Matrix (Fin 2) (Fin 2) ℝ) (s : Finset ι)
    (f : ι → Vec 2 → E) (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) :
    AVRegularity.covOperator Hc (fun x => ∑ t ∈ s, f t x) =
      fun x => ∑ t ∈ s, AVRegularity.covOperator Hc (f t) x := by
  have h1 : ∀ j : Fin 2, ∀ t ∈ s, ContDiff ℝ 1 (partialOp j (f t)) := fun j t ht =>
    contDiff_partialOp (k := 1) (hf t ht) j
  have hj : ∀ j : Fin 2, partialOp j (fun x => ∑ t ∈ s, f t x) =
      fun x => ∑ t ∈ s, partialOp j (f t) x := fun j =>
    partialOp_sum j s f (fun t ht => (hf t ht).of_le (by norm_num))
  have hij : ∀ i j : Fin 2, partialOp i (fun x => ∑ t ∈ s, partialOp j (f t) x) =
      fun x => ∑ t ∈ s, partialOp i (partialOp j (f t)) x := fun i j =>
    partialOp_sum i s (fun t => partialOp j (f t)) (h1 j)
  funext x
  rw [covOperator_eq]
  simp only [hj, hij]
  simp only [covOperator_eq, Finset.smul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem covOperator_smul (Hc : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) {f : Vec 2 → E}
    (hf : ContDiff ℝ 2 f) :
    AVRegularity.covOperator Hc (fun x => c • f x) =
      fun x => c • AVRegularity.covOperator Hc f x := by
  have hj : ∀ j : Fin 2, partialOp j (fun x => c • f x) = fun x => c • partialOp j f x :=
    fun j => partialOp_smul j c (hf.of_le (by norm_num))
  have hij : ∀ i j : Fin 2, partialOp i (fun x => c • partialOp j f x) =
      fun x => c • partialOp i (partialOp j f) x := fun i j =>
    partialOp_smul i c (contDiff_partialOp (k := 1) hf j)
  funext x
  rw [covOperator_eq]
  simp only [hj, hij]
  simp only [covOperator_eq, Finset.smul_sum, smul_comm c]

theorem partialOp_three {f : Vec 2 → E} (hf : ContDiff ℝ 3 f) (m i j : Fin 2) :
    partialOp m (partialOp i (partialOp j f)) = partialOp i (partialOp j (partialOp m f)) := by
  have h1 : ContDiff ℝ 2 (partialOp j f) := contDiff_partialOp (k := 2) hf j
  rw [partialOp_comm h1 m i, partialOp_comm (hf.of_le (by norm_num)) m j]

theorem partialOp_covOperator (Hc : Matrix (Fin 2) (Fin 2) ℝ) (m : Fin 2) {f : Vec 2 → E}
    (hf : ContDiff ℝ 3 f) :
    partialOp m (AVRegularity.covOperator Hc f) =
      AVRegularity.covOperator Hc (partialOp m f) := by
  have h1 : ∀ j, ContDiff ℝ 2 (partialOp j f) := fun j =>
    contDiff_partialOp (k := 2) hf j
  have h2 : ∀ i j, ContDiff ℝ 1 (partialOp i (partialOp j f)) := fun i j =>
    contDiff_partialOp (k := 1) (h1 j) i
  rw [covOperator_eq Hc f]
  rw [partialOp_sum m Finset.univ (fun i x => ∑ j : Fin 2, Hc i j • partialOp i (partialOp j f) x)
    (fun i _ => ContDiff.sum fun j _ => ContDiff.const_smul _ (h2 i j))]
  funext x
  rw [covOperator_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [partialOp_sum m Finset.univ (fun j x => Hc i j • partialOp i (partialOp j f) x)
    (fun j _ => ContDiff.const_smul _ (h2 i j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [partialOp_smul m _ (h2 i j), partialOp_three hf]

theorem contDiff_mono_nat {a b : ℕ} (h : a ≤ b) {f : Vec 2 → E}
    (hf : ContDiff ℝ (b : WithTop ℕ∞) f) : ContDiff ℝ (a : WithTop ℕ∞) f :=
  hf.of_le (by exact_mod_cast h)

/-- An operator of order `N` with constant coefficients: additive and homogeneous on `C^N` fields,
lowers the regularity by `N`, and commutes with every `∂_j` on `C^{N+1}` fields. -/
structure ConstCoefOp (N : ℕ) (T : (Vec 2 → E) → (Vec 2 → E)) : Prop where
  /-- Regularity. -/
  reg : ∀ (r : ℕ) (f : Vec 2 → E), ContDiff ℝ ((r + N : ℕ) : WithTop ℕ∞) f →
    ContDiff ℝ (r : WithTop ℕ∞) (T f)
  /-- Additivity over finite sums. -/
  sum : ∀ {ι : Type} (s : Finset ι) (f : ι → Vec 2 → E),
    (∀ i ∈ s, ContDiff ℝ (N : WithTop ℕ∞) (f i)) →
    T (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, T (f i) x
  /-- Homogeneity. -/
  smul : ∀ (c : ℝ) (f : Vec 2 → E), ContDiff ℝ (N : WithTop ℕ∞) f →
    T (fun x => c • f x) = fun x => c • T f x
  /-- Commutation with the coordinate derivatives. -/
  comm : ∀ (j : Fin 2) (f : Vec 2 → E), ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) f →
    T (partialOp j f) = partialOp j (T f)

namespace ConstCoefOp

variable {N N₁ N₂ N' : ℕ} {T T' T₁ T₂ : (Vec 2 → E) → (Vec 2 → E)}

theorem id : ConstCoefOp (E := E) 0 (fun f => f) where
  reg r f hf := by simpa using hf
  sum _ _ _ := rfl
  smul _ _ _ := rfl
  comm _ _ _ := rfl

theorem ofEq (h : T = T') (hT : ConstCoefOp N T) : ConstCoefOp N T' := by
  subst h; exact hT

theorem mono (hT : ConstCoefOp N T) (hN : N ≤ N') : ConstCoefOp N' T where
  reg r f hf := hT.reg r f (contDiff_mono_nat (by omega) hf)
  sum s f hf := hT.sum s f fun i hi => contDiff_mono_nat hN (hf i hi)
  smul c f hf := hT.smul c f (contDiff_mono_nat hN hf)
  comm j f hf := hT.comm j f (contDiff_mono_nat (by omega) hf)

theorem comp (h₁ : ConstCoefOp N₁ T₁) (h₂ : ConstCoefOp N₂ T₂) :
    ConstCoefOp (N₁ + N₂) (fun f => T₁ (T₂ f)) where
  reg r f hf := h₁.reg r _ (h₂.reg (r + N₁) f (by rwa [Nat.add_assoc]))
  sum s f hf := by
    have e1 := h₂.sum s f fun i hi => contDiff_mono_nat (Nat.le_add_left _ _) (hf i hi)
    have hT2 : ∀ i ∈ s, ContDiff ℝ (N₁ : WithTop ℕ∞) (T₂ (f i)) := fun i hi =>
      h₂.reg N₁ (f i) (by simpa [Nat.add_comm] using hf i hi)
    show T₁ (T₂ (fun x => ∑ i ∈ s, f i x)) = _
    rw [e1]
    exact h₁.sum s (fun i => T₂ (f i)) hT2
  smul c f hf := by
    have e1 := h₂.smul c f (contDiff_mono_nat (Nat.le_add_left _ _) hf)
    have hT2 : ContDiff ℝ (N₁ : WithTop ℕ∞) (T₂ f) :=
      h₂.reg N₁ f (by simpa [Nat.add_comm] using hf)
    show T₁ (T₂ (fun x => c • f x)) = _
    rw [e1]
    exact h₁.smul c (T₂ f) hT2
  comm j f hf := by
    have a : T₂ (partialOp j f) = partialOp j (T₂ f) :=
      h₂.comm j f (contDiff_mono_nat (by omega) hf)
    have b : ContDiff ℝ ((N₁ + 1 : ℕ) : WithTop ℕ∞) (T₂ f) :=
      h₂.reg (N₁ + 1) f (contDiff_mono_nat (by omega) hf)
    show T₁ (T₂ (partialOp j f)) = partialOp j (T₁ (T₂ f))
    rw [a]
    exact h₁.comm j (T₂ f) b

theorem iter (hT : ConstCoefOp N T) : ∀ n : ℕ, ConstCoefOp (n * N) (T^[n])
  | 0 => (ConstCoefOp.id (E := E)).mono (by simp)
  | n + 1 => by
    refine ((hT.comp (iter hT n)).mono (le_of_eq (by rw [Nat.add_one_mul, Nat.add_comm]))).ofEq ?_
    funext f
    exact (Function.iterate_succ_apply' T n f).symm

theorem sumOp {ι : Type} (s : Finset ι) (c : ι → ℝ) {T : ι → (Vec 2 → E) → (Vec 2 → E)}
    (h : ∀ i ∈ s, ConstCoefOp N (T i)) :
    ConstCoefOp N (fun f x => ∑ i ∈ s, c i • T i f x) where
  reg r f hf := ContDiff.sum fun i hi => ContDiff.const_smul _ ((h i hi).reg r f hf)
  sum {κ} s' f hf := by
    funext x
    have e : ∀ i ∈ s, T i (fun x => ∑ k ∈ s', f k x) = fun x => ∑ k ∈ s', T i (f k) x :=
      fun i hi => (h i hi).sum s' f hf
    calc ∑ i ∈ s, c i • T i (fun x => ∑ k ∈ s', f k x) x
        = ∑ i ∈ s, c i • ∑ k ∈ s', T i (f k) x :=
          Finset.sum_congr rfl fun i hi => by rw [e i hi]
      _ = ∑ k ∈ s', ∑ i ∈ s, c i • T i (f k) x := by
          simp_rw [Finset.smul_sum]; exact Finset.sum_comm
  smul a f hf := by
    funext x
    have e : ∀ i ∈ s, T i (fun x => a • f x) = fun x => a • T i f x :=
      fun i hi => (h i hi).smul a f hf
    calc ∑ i ∈ s, c i • T i (fun x => a • f x) x = ∑ i ∈ s, a • (c i • T i f x) :=
          Finset.sum_congr rfl fun i hi => by rw [e i hi]; exact smul_comm _ _ _
      _ = a • ∑ i ∈ s, c i • T i f x := (Finset.smul_sum).symm
  comm j f hf := by
    have hr : ∀ i ∈ s, ContDiff ℝ 1 (T i f) := fun i hi =>
      (h i hi).reg 1 f (contDiff_mono_nat (by omega) hf)
    show (fun x => ∑ i ∈ s, c i • T i (partialOp j f) x) =
      partialOp j (fun x => ∑ i ∈ s, c i • T i f x)
    rw [partialOp_sum j s (fun i x => c i • T i f x)
      (fun i hi => ContDiff.const_smul _ (hr i hi))]
    funext x
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [partialOp_smul j (c i) (hr i hi), (h i hi).comm j f hf]

/-- A constant-coefficient operator moves inside a divergence. -/
theorem div (hU : ConstCoefOp N T) {g : Fin 2 → Vec 2 → E}
    (hg : ∀ j, ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (g j)) {f : Vec 2 → E}
    (h : f = fun x => ∑ j, partialOp j (g j) x) :
    T f = fun x => ∑ j, partialOp j (T (g j)) x := by
  subst h
  rw [hU.sum Finset.univ (fun j => partialOp j (g j))
    (fun j _ => contDiff_mono_nat (le_refl _) (contDiff_partialOp (hg j) j))]
  funext x
  exact Finset.sum_congr rfl fun j _ => by rw [hU.comm j (g j) (hg j)]

theorem covOperator (Hc : Matrix (Fin 2) (Fin 2) ℝ) :
    ConstCoefOp (E := E) 2 (AVRegularity.covOperator Hc) where
  reg r f hf := contDiff_covOperator Hc hf
  sum s f hf := covOperator_sum Hc s f hf
  smul c f hf := covOperator_smul Hc c hf
  comm j f hf := (partialOp_covOperator Hc j (by exact_mod_cast hf)).symm

theorem covIter (Hc : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) :
    ConstCoefOp (E := E) (n * 2) ((AVRegularity.covOperator Hc)^[n]) :=
  (covOperator Hc).iter n

theorem covPolyP (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) :
    ConstCoefOp (E := E) (2 * p) (AVRegularity.covPolyP Hc p) :=
  (ConstCoefOp.sumOp (Finset.range (p + 1)) (fun l => ((l.factorial : ℝ)⁻¹))
    (fun l hl => (covIter (E := E) Hc l).mono (by
      have := Finset.mem_range.mp hl; nlinarith))).ofEq (by
    funext f x; simp [AVRegularity.covPolyP])

theorem covPolyQ (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) :
    ConstCoefOp (E := E) (2 * p) (AVRegularity.covPolyQ Hc p) :=
  (ConstCoefOp.sumOp (Finset.range (p + 1)) (fun l => (((-1 : ℝ) ^ l / (l.factorial : ℝ))))
    (fun l hl => (covIter (E := E) Hc l).mono (by
      have := Finset.mem_range.mp hl; nlinarith))).ofEq (by
    funext f x; simp [AVRegularity.covPolyQ])

end ConstCoefOp

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! The word adjoint in divergence form. For `m ≥ 1`,
`wordAdjoint m G = ∑ⱼ ∂ⱼ (wordDivTerm m j G)` with
`wordDivTerm (n+1) j G = (-1)^(n+1) ∑_{α'} ∂^{rev α'} (G · (j, α'))`, and `wordDivTerm m j` is a
`TorusAdj` of order `m - 1`. -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem orderedDerivativeRev_zero (α : DerivativeWord2 0) (g : Vec 2 → E) :
    AVRegularity.orderedDerivativeRev α g = g := by
  simp [AVRegularity.orderedDerivativeRev]

theorem contDiff_orderedDerivativeRev : ∀ {m : ℕ} (α : DerivativeWord2 m) (k : ℕ) {g : Vec 2 → E},
    ContDiff ℝ ((k + m : ℕ) : WithTop ℕ∞) g →
      ContDiff ℝ (k : WithTop ℕ∞) (AVRegularity.orderedDerivativeRev α g)
  | 0, α, k, g, hg => by
    rw [orderedDerivativeRev_zero]; simpa using hg
  | m + 1, α, k, g, hg => by
    rw [orderedDerivativeRev_succ]
    exact contDiff_orderedDerivativeRev (Fin.init α) k
      (contDiff_partialOp (k := k + m) (by simpa [Nat.add_assoc] using hg) _)

theorem orderedDerivativeRev_cons {n : ℕ} (j : Fin 2) (α' : DerivativeWord2 n) (g : Vec 2 → E) :
    AVRegularity.orderedDerivativeRev (Fin.cons j α' : Fin (n + 1) → Fin 2) g =
      partialOp j (AVRegularity.orderedDerivativeRev α' g) := by
  unfold AVRegularity.orderedDerivativeRev
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, List.foldr_cons]
  rfl

/-- The `j`-th inner flux of `wordAdjoint m`: `wordAdjoint m G = ∑ⱼ ∂ⱼ (wordDivTerm m j G)`. -/
def wordDivTerm : ∀ (m : ℕ) (_ : Fin 2) (_ : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => E)),
    Vec 2 → E
  | 0, _, _ => fun _ => 0
  | n + 1, j, G => fun x => ((-1 : ℝ) ^ (n + 1)) • ∑ α' : DerivativeWord2 n,
      AVRegularity.orderedDerivativeRev α'
        (fun y => G y (Fin.cons j α' : Fin (n + 1) → Fin 2)) x

theorem wordAdjoint_div {m : ℕ} (hm : 1 ≤ m)
    (G : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => E))
    (hG : ContDiff ℝ (m : WithTop ℕ∞) G) :
    AVRegularity.wordAdjoint m G = fun x => ∑ j, partialOp j (wordDivTerm m j G) x := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hc : ∀ (α : DerivativeWord2 (n + 1)), ContDiff ℝ ((1 + n : ℕ) : WithTop ℕ∞)
      (fun y => G y α) := fun α =>
    ((PiLp.proj 2 (fun _ : DerivativeWord2 (n + 1) => E) α).contDiff.comp
      (contDiff_mono_nat (by omega) hG))
  have hr : ∀ (j : Fin 2) (α' : DerivativeWord2 n), ContDiff ℝ 1
      (AVRegularity.orderedDerivativeRev α'
        (fun y => G y (Fin.cons j α' : Fin (n + 1) → Fin 2))) := fun j α' => by
    have := contDiff_orderedDerivativeRev α' 1 (hc (Fin.cons j α'))
    simpa using this
  funext x
  have hsum : ∀ F : DerivativeWord2 (n + 1) → E, ∑ α, F α = ∑ j : Fin 2, ∑ α' : DerivativeWord2 n,
      F (Fin.cons j α' : Fin (n + 1) → Fin 2) := fun F => by
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => Fin 2)) F, Fintype.sum_prod_type]
    rfl
  unfold AVRegularity.wordAdjoint
  have hsum' := hsum (fun α => AVRegularity.orderedDerivativeRev α (fun y => G y α) x)
  simp only at hsum'
  rw [hsum', Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = partialOp j (fun x => ((-1 : ℝ) ^ (n + 1)) • ∑ α' : DerivativeWord2 n,
      AVRegularity.orderedDerivativeRev α'
        (fun y => G y (Fin.cons j α' : Fin (n + 1) → Fin 2)) x) x
  rw [partialOp_smul j _ (ContDiff.sum fun α' _ => hr j α'),
    partialOp_sum j Finset.univ _ (fun α' _ => hr j α')]
  simp only [orderedDerivativeRev_cons, Finset.smul_sum]

theorem contDiff_wordDivTerm {m : ℕ} (hm : 1 ≤ m) (j : Fin 2)
    {G : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => E)} {r : ℕ}
    (hG : ContDiff ℝ ((r + (m - 1) : ℕ) : WithTop ℕ∞) G) :
    ContDiff ℝ (r : WithTop ℕ∞) (wordDivTerm m j G) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine ContDiff.const_smul _ (ContDiff.sum fun α' _ => ?_)
  have hc : ContDiff ℝ ((r + n : ℕ) : WithTop ℕ∞)
      (fun y => G y (Fin.cons j α' : Fin (n + 1) → Fin 2)) :=
    (PiLp.proj 2 (fun _ : DerivativeWord2 (n + 1) => E)
      (Fin.cons j α' : Fin (n + 1) → Fin 2)).contDiff.comp (by simpa using hG)
  exact contDiff_orderedDerivativeRev α' r hc

/-- `X = ∑ⱼ ∂ⱼ Yⱼ` with `Yⱼ ∈ C¹`. -/
def DivRep (X : Vec 2 → E) (Y : Fin 2 → Vec 2 → E) : Prop :=
  (∀ j, ContDiff ℝ 1 (Y j)) ∧ X = fun x => ∑ j, partialOp j (Y j) x

namespace DivRep

variable {X X' : Vec 2 → E} {Y Y' : Fin 2 → Vec 2 → E}

theorem sum {ι : Type*} (s : Finset ι) {X : ι → Vec 2 → E} {Y : ι → Fin 2 → Vec 2 → E}
    (h : ∀ i ∈ s, DivRep (X i) (Y i)) :
    DivRep (fun x => ∑ i ∈ s, X i x) (fun j x => ∑ i ∈ s, Y i j x) := by
  refine ⟨fun j => ContDiff.sum fun i hi => (h i hi).1 j, ?_⟩
  have e : ∀ j, partialOp j (fun x => ∑ i ∈ s, Y i j x) =
      fun x => ∑ i ∈ s, partialOp j (Y i j) x := fun j =>
    partialOp_sum j s (fun i => Y i j) (fun i hi => (h i hi).1 j)
  funext x
  simp only [e]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i hi => congrFun (h i hi).2 x

theorem smul (c : ℝ) (h : DivRep X Y) : DivRep (fun x => c • X x) (fun j x => c • Y j x) := by
  refine ⟨fun j => (h.1 j).const_smul c, ?_⟩
  have e : ∀ j, partialOp j (fun x => c • Y j x) = fun x => c • partialOp j (Y j) x := fun j =>
    partialOp_smul j c (h.1 j)
  funext x
  simp only [e]
  rw [← Finset.smul_sum, ← congrFun h.2 x]

theorem neg (h : DivRep X Y) : DivRep (fun x => -X x) (fun j x => -Y j x) := by
  have := h.smul (-1)
  simpa using this

theorem add (h : DivRep X Y) (h' : DivRep X' Y') :
    DivRep (fun x => X x + X' x) (fun j x => Y j x + Y' j x) := by
  have := DivRep.sum (Finset.univ : Finset (Fin 2)) (X := fun i : Fin 2 => if i = 0 then X else X')
    (Y := fun i : Fin 2 => if i = 0 then Y else Y') (fun i _ => by
      fin_cases i <;> simp [h, h'])
  simpa [Fin.sum_univ_two] using this

theorem sub (h : DivRep X Y) (h' : DivRep X' Y') :
    DivRep (fun x => X x - X' x) (fun j x => Y j x - Y' j x) := by
  have := h.add h'.neg
  simpa [sub_eq_add_neg] using this

theorem constCoef {N : ℕ} {U : (Vec 2 → E) → (Vec 2 → E)} (hU : ConstCoefOp N U)
    (h : DivRep X Y) (hY : ∀ j, ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (Y j)) :
    DivRep (U X) (fun j => U (Y j)) :=
  ⟨fun j => by simpa [Nat.add_comm] using hU.reg 1 (Y j) (contDiff_mono_nat (by omega) (hY j)),
    hU.div hY h.2⟩

end DivRep

theorem wordAdjoint_divRep {m : ℕ} (hm : 1 ≤ m)
    (G : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => E))
    (hG : ContDiff ℝ (m : WithTop ℕ∞) G) :
    DivRep (AVRegularity.wordAdjoint m G) (fun j => wordDivTerm m j G) :=
  ⟨fun j => contDiff_wordDivTerm hm j (r := 1) (by simpa [Nat.add_sub_cancel' hm,
      Nat.add_comm] using hG), wordAdjoint_div hm G hG⟩

end Smooth

section Adj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The constant of `wordDivTerm m j`. -/
def wordDivConst (m Kc : ℕ) : ℝ := 2 ^ (m - 1) * (Kc.factorial : ℝ)

/-- `wordDivTerm m j` is a `TorusAdj` of order `m - 1`. -/
def TorusAdj.wordDiv : ∀ (m : ℕ) (j : Fin 2) (R Kc : ℕ),
    TorusAdj (wordDivTerm (E := E) m j) (m - 1) R Kc (wordDivConst m Kc)
  | 0, j, R, Kc => ((TorusAdj.zero (m := 0) R Kc).mono le_rfl le_rfl (by
      unfold wordDivConst; positivity)).ofOp (by funext G; rfl)
  | n + 1, j, R, Kc =>
    (((TorusAdj.sumMem (Finset.univ : Finset (DerivativeWord2 n)) (fun α' _ =>
      ((TorusAdj.orderedDerivativeRev (E := E) α' R Kc).comp
        (TorusAdj.componentOp (E := E) (Fin.cons j α' : Fin (n + 1) → Fin 2) (R + n) Kc)
        le_rfl le_rfl).ofOrder (Nat.add_zero n))).smul ((-1 : ℝ) ^ (n + 1))).mono le_rfl le_rfl
      (le_of_eq (by
        unfold wordDivConst
        simp [Finset.sum_const, Finset.card_univ, mul_comm]))).ofOp
      (by funext G x; rfl)

end Adj

end AVRegularity.CycleComparison.Coarse
end
