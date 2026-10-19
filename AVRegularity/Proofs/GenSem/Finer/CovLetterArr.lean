-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.Mean
import AVRegularity.Proofs.GenSem.CoeffArr.MonoSource
public import AVRegularity.Proofs.GenSem.Op.Chart
public import AVRegularity.Proofs.GenSem.LiftGen.Drift
import AVRegularity.Proofs.GenSem.Op.FamChart
import AVRegularity.Proofs.GenSem.Jet.Chart

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory Set
namespace AVRegularity.Providers.GenSem

/-! **The path mean flux as an array operator at every label.** For a smooth test field `f`,
`pathMeanFlux D m ρ Q Cc n t f y κ = applyArr n (pmArr …) f y 0`, where the entry of order `r` and
word `α` at the label `y` is `c₀ ρ^r ⟨fluxXArr … r α (ρ⁻¹ y) ·⟩` (`pathMeanFlux_applyArr`). The
entries are `C^r` in the label when the lift data are `C^{r + Dm + 2}` (`contDiff_pmArr`), and, on
the lift setup, they are covariant: the entry at the label `y` of the chain `A` is a family
denotation at the recentered chain `A^{[y]}` (`LiftGenSetup.jetRep_pmArr'`: jets of every order
at `0` are represented, through `dSlowFam`). -/

/-! ### Dilations -/

/-- Ordered derivatives of a dilated field, with a constant factor. -/
theorem orderedDerivative_const_mul_comp_smul (c : ℝ) : ∀ {m : ℕ} (α : DerivativeWord2 m)
    {g : Vec 2 → ℝ} (a : ℝ), ContDiff ℝ (m : WithTop ℕ∞) g →
      orderedDerivative α (fun x => a * g (c • x)) =
        fun x => a * c ^ m * orderedDerivative α g (c • x) := by
  intro m
  induction m with
  | zero =>
    intro α g a _
    have : α = Fin.elim0 := Subsingleton.elim _ _
    subst this
    funext x
    simp [orderedDerivative]
  | succ m ih =>
    intro α g a hg
    have hd : ∀ x, fderiv ℝ (fun x => a * g (c • x)) x (basisVec (α 0)) =
        (a * c) * fderiv ℝ g (c • x) (basisVec (α 0)) := by
      intro x
      have h1 : HasFDerivAt (fun x : Vec 2 => g (c • x))
          ((fderiv ℝ g (c • x)).comp (c • ContinuousLinearMap.id ℝ (Vec 2))) x :=
        ((hg.differentiable (by simp)) (c • x)).hasFDerivAt.comp x
          ((hasFDerivAt_id x).const_smul c)
      rw [(h1.const_mul a).fderiv]
      simp only [smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
      ring
    have h1 : (fun x => fderiv ℝ (fun x => a * g (c • x)) x (basisVec (α 0))) =
        fun x => (a * c) * (fun y => fderiv ℝ g y (basisVec (α 0))) (c • x) := funext hd
    rw [orderedDerivative_succ, h1, ih (fun i => α i.succ) (a * c) (contDiff_dirDeriv_nat hg _)]
    funext x
    rw [orderedDerivative_succ, pow_succ]
    ring

/-- Ordered derivatives of a dilated field. -/
theorem orderedDerivative_comp_smul (c : ℝ) {m : ℕ} (α : DerivativeWord2 m) {g : Vec 2 → ℝ}
    (hg : ContDiff ℝ (m : WithTop ℕ∞) g) (x : Vec 2) :
    orderedDerivative α (fun x => g (c • x)) x = c ^ m * orderedDerivative α g (c • x) := by
  have h := congrFun (orderedDerivative_const_mul_comp_smul c α 1 hg) x
  simp only [one_mul] at h
  exact h

/-! ### The array of the path mean flux -/

variable {h Dm : ℕ}

/-- The array of the component `κ` of the path mean flux, at the label `y` (constant in the second
variable). -/
def pmArr (D : OCData) (m : ℕ) (ρ : ℝ) (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ) (κ : Fin 2) : CArr :=
  fun r α y _ => -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) *
    ρ ^ r * fieldCellMean (fun z =>
      fluxXArr Q Cc 0 h n ((D.cellScaleSq m)⁻¹ * t) (Fin.last h) κ r α (ρ⁻¹ • y) z)

theorem arrSupp_pmArr (D : OCData) (m : ℕ) (ρ : ℝ)
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ) (κ : Fin 2) :
    ArrSupp (n - 1) (pmArr D m ρ Q Cc n t κ) := by
  intro r hr α
  funext y z
  have : fluxXArr Q Cc 0 h n ((D.cellScaleSq m)⁻¹ * t) (Fin.last h) κ r α = 0 :=
    arrSupp_fluxXArr Q Cc 0 h n _ _ κ r hr α
  simp [pmArr, this, fieldCellMean]

/-- **The path mean flux is the applied array `pmArr`** at every label, for test fields of class
`C^{n + Dm}` and lift data of class `C^{Dm+2}`. -/
theorem pathMeanFlux_applyArr (D : OCData) (m : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0)
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ)
    (hreg : LiftRegular Q Cc (0 : Fin (h + 1)) ((D.cellScaleSq m)⁻¹ * t) h n (Dm + 2))
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ ((n + Dm : ℕ) : WithTop ℕ∞) f) (y : Vec 2) (κ : Fin 2) :
    pathMeanFlux D m ρ Q Cc n t f y κ = applyArr n (pmArr D m ρ Q Cc n t κ) f y 0 := by
  set s := (D.cellScaleSq m)⁻¹ * t with hs
  set c₀ := -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ)
    with hc₀
  set X := ρ⁻¹ • y with hX
  have hρX : ρ • X = y := by rw [hX, smul_smul, mul_inv_cancel₀ hρ, one_smul]
  have ha : ContDiff ℝ ((n + Dm : ℕ) : WithTop ℕ∞) (fun X : Vec 2 => f (ρ • X)) :=
    hf.comp (contDiff_const_smul ρ)
  have hA0 : ∀ u, ArrSmooth 0 (fluxXArr Q Cc 0 h n s u κ) := fun u =>
    arrSmooth_fluxXArr Q Cc 0 (r := 0) (hreg.mono le_rfl le_rfl (by omega)) u κ
  have hψ : ∀ z u, liftFluxX Q Cc
      (fun _ (X : Vec 2) => (Pi.single (0 : Fin (h + 1)) (f (ρ • X)) : Fin (h + 1) → ℝ))
      h n s X z κ u = applyArr n (fluxXArr Q Cc 0 h n s u κ) (fun X => f (ρ • X)) X z :=
    fun z u => liftFluxX_applyArr Q Cc 0 hreg ha X z κ u
  have hcont : Continuous (fun z => liftFluxX Q Cc
      (fun _ (X : Vec 2) => (Pi.single (0 : Fin (h + 1)) (f (ρ • X)) : Fin (h + 1) → ℝ))
      h n s X z κ) := by
    refine continuous_pi fun u => ?_
    have e : (fun z => liftFluxX Q Cc
        (fun _ (X : Vec 2) => (Pi.single (0 : Fin (h + 1)) (f (ρ • X)) : Fin (h + 1) → ℝ))
        h n s X z κ u) = fun z => applyArr n (fluxXArr Q Cc 0 h n s u κ) (fun X => f (ρ • X)) X z :=
      funext fun z => hψ z u
    rw [e]
    exact continuous_applyArr_z (hA0 u) _ X
  have hint := integrableOn_unitCube_of_continuous hcont
  have hcomm := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (h + 1) => ℝ)
    (Fin.last h)).integral_comp_comm hint
  simp only [ContinuousLinearMap.proj_apply] at hcomm
  -- the entries are continuous in the fast variable
  have hcz : ∀ r (α : DerivativeWord2 r),
      Continuous (fun z => fluxXArr Q Cc 0 h n s (Fin.last h) κ r α X z) := fun r α =>
    ((hA0 (Fin.last h)).continuous r α).comp (continuous_const.prodMk continuous_id)
  have hterm : ∀ z, applyArr n (fluxXArr Q Cc 0 h n s (Fin.last h) κ) (fun X => f (ρ • X)) X z =
      ∑ r ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 r,
        fluxXArr Q Cc 0 h n s (Fin.last h) κ r α X z * (ρ ^ r * orderedDerivative α f y) := by
    intro z
    unfold applyArr
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun α _ => ?_
    have hrn : r ≤ n + Dm := by simp at hr; omega
    rw [orderedDerivative_comp_smul ρ α (hf.of_le (by exact_mod_cast hrn)) X, hρX]
  have hmean : fieldCellMean (fun z => liftFluxX Q Cc
      (fun _ (X : Vec 2) => (Pi.single (0 : Fin (h + 1)) (f (ρ • X)) : Fin (h + 1) → ℝ))
      h n s X z κ) (Fin.last h) =
      ∑ r ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 r,
        fieldCellMean (fun z => fluxXArr Q Cc 0 h n s (Fin.last h) κ r α X z) *
          (ρ ^ r * orderedDerivative α f y) := by
    unfold fieldCellMean
    rw [← hcomm]
    simp only [hψ, hterm]
    rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun α _ =>
      (integrableOn_unitCube_of_continuous (hcz r α)).mul_const _]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_finsetSum _ fun α _ => (integrableOn_unitCube_of_continuous (hcz r α)).mul_const _]
    exact Finset.sum_congr rfl fun α _ => integral_mul_const _ _
  unfold pathMeanFlux
  change c₀ * fieldCellMean (fun z => liftFluxX Q Cc
      (fun _ (X : Vec 2) => (Pi.single (0 : Fin (h + 1)) (f (ρ • X)) : Fin (h + 1) → ℝ))
      h n s X z κ) (Fin.last h) = _
  rw [hmean]
  unfold applyArr pmArr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

/-- The entries of `pmArr` are `C^r` in the label, for lift data of class `C^{r + Dm + 2}`. -/
theorem contDiff_pmArr (D : OCData) (m : ℕ) (ρ : ℝ)
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ) (κ : Fin 2) {r : ℕ}
    (hreg : LiftRegular Q Cc (0 : Fin (h + 1)) ((D.cellScaleSq m)⁻¹ * t) h n (r + Dm + 2))
    (j : ℕ) (α : DerivativeWord2 j) :
    ContDiff ℝ (r : WithTop ℕ∞) (fun y => pmArr D m ρ Q Cc n t κ j α y 0) := by
  have hA := (arrSmooth_def.mp (arrSmooth_fluxXArr Q Cc 0 hreg (Fin.last h) κ)) j α
  have hc : ContDiff ℝ (r : WithTop ℕ∞) (Function.uncurry fun (y z : Vec 2) =>
      fluxXArr Q Cc 0 h n ((D.cellScaleSq m)⁻¹ * t) (Fin.last h) κ j α (ρ⁻¹ • y) z) :=
    hA.comp ((contDiff_const_smul ρ⁻¹).comp contDiff_fst |>.prodMk contDiff_snd)
  have hm : ContDiff ℝ (r : WithTop ℕ∞) (fun y => fieldCellMean (fun z =>
      fluxXArr Q Cc 0 h n ((D.cellScaleSq m)⁻¹ * t) (Fin.last h) κ j α (ρ⁻¹ • y) z)) := by
    have := PathDecomp.contDiff_fieldCellMean (r := r) (Φ := fun (y z : Vec 2) =>
      fluxXArr Q Cc 0 h n ((D.cellScaleSq m)⁻¹ * t) (Fin.last h) κ j α (ρ⁻¹ • y) z)
      (by exact_mod_cast hc)
    exact_mod_cast this
  exact contDiff_const.mul hm

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public noncomputable section
section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Operator facts for the covariance letter.**
* `covOperator_component`, `covOperator_iterate_component`: the covariance operator on flux
  fields acts componentwise (for `C^{2a}` fields).
* `contDiff_covOperator_iterate`: the iterates lose two orders each.
* `covOperator_iterate_eq_nat`: iterates as array operators for `C^{2a}` fields (finite order
  version of `covOperator_iterate_eq`). -/

/-! ### The covariance operator on flux fields -/

theorem contDiff_covOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Matrix (Fin 2) (Fin 2) ℝ) {r : ℕ} {f : Vec 2 → E}
    (hf : ContDiff ℝ ((r + 2 : ℕ) : WithTop ℕ∞) f) :
    ContDiff ℝ (r : WithTop ℕ∞) (covOperator H f) := by
  unfold covOperator
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.const_smul _ ?_
  exact contDiff_dirDeriv_nat (contDiff_dirDeriv_nat (r := r + 1) hf j) i

theorem contDiff_covOperator_iterate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Matrix (Fin 2) (Fin 2) ℝ) {r : ℕ} :
    ∀ (a : ℕ) {f : Vec 2 → E}, ContDiff ℝ ((2 * a + r : ℕ) : WithTop ℕ∞) f →
      ContDiff ℝ (r : WithTop ℕ∞) ((covOperator H)^[a] f)
  | 0, f, hf => by simpa using hf
  | a + 1, f, hf => by
      rw [Function.iterate_succ_apply']
      refine contDiff_covOperator H (contDiff_covOperator_iterate H a ?_)
      rwa [show 2 * a + (r + 2) = 2 * (a + 1) + r by ring]

/-- The covariance operator on a `C²` flux field acts componentwise. -/
theorem covOperator_component (H : Matrix (Fin 2) (Fin 2) ℝ) {V : Vec 2 → Vec 2}
    (hV : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) V) (x : Vec 2) (c : Fin 2) :
    covOperator H V x c = covOperator H (fun y => V y c) x := by
  unfold covOperator
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hF : Differentiable ℝ (fun y => fderiv ℝ V y (basisVec j)) :=
    (contDiff_dirDeriv_nat (r := 1) hV j).differentiable (by simp)
  rw [← fderiv_component (hF x) c i]
  have e : (fun y' => fderiv ℝ V y' (basisVec j) c) =
      fun y => fderiv ℝ (fun y => V y c) y (basisVec j) :=
    funext fun y => (fderiv_component ((hV.differentiable (by simp)) y) c j).symm
  rw [e]

theorem covOperator_iterate_component (H : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ (a : ℕ) {V : Vec 2 → Vec 2}, ContDiff ℝ ((2 * a : ℕ) : WithTop ℕ∞) V → ∀ (x : Vec 2) (c : Fin 2),
      (covOperator H)^[a] V x c = (covOperator H)^[a] (fun y => V y c) x
  | 0, V, _, x, c => rfl
  | a + 1, V, hV, x, c => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have h2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) ((covOperator H)^[a] V) :=
        contDiff_covOperator_iterate H a (by rwa [show 2 * a + 2 = 2 * (a + 1) by ring])
      rw [covOperator_component H h2 x c]
      congr 1
      funext y
      exact covOperator_iterate_component H a
        (hV.of_le (by exact_mod_cast (by omega : 2 * a ≤ 2 * (a + 1)))) y c

/-- **Iterates of `covOperator` as array operators, finite order.** -/
theorem covOperator_iterate_eq_nat (H : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ (a : ℕ) {f : Vec 2 → ℝ}, ContDiff ℝ ((2 * a : ℕ) : WithTop ℕ∞) f → ∀ (x z : Vec 2),
      (covOperator H)^[a] f x = applyArr (2 * a) (covArrPow H a) f x z
  | 0, f, _, x, z => by simp [applyArr_unitArr, covArrPow]
  | a + 1, f, hf, x, z => by
      have hf2 : ContDiff ℝ ((2 * a + 2 : ℕ) : WithTop ℕ∞) f := by
        rwa [show 2 * a + 2 = 2 * (a + 1) by ring]
      have ih : (covOperator H)^[a] f = fun X => applyArr (2 * a) (covArrPow H a) f X 0 :=
        funext fun X => covOperator_iterate_eq_nat H a
          (hf.of_le (by exact_mod_cast (by omega : 2 * a ≤ 2 * (a + 1)))) X 0
      rw [Function.iterate_succ_apply', ih, covOperator_eq_applyArr H _ x z,
        applyArr_comp 2 (2 * a) (covArr H) (covArrPow H a) f 0
          hf2 (covArrPow_slowSmooth H 2 a) (covArrPow_supp H a)]
      rw [show 2 + 2 * a = 2 * (a + 1) by ring]
      rfl

/-! **Family-sort representations.** `V.FamURep ψ c`: the family expression `c`
(sort `.fam`, scheduled, from the seed) denotes one function `fc` with `ψ l = fc (time l) (base l)`
for every index `l` of the window. Closure under constants, sums, products; the mean at the
offset `0` of a uniformly represented cell function (`URep.mean0`), the mean of a restricted
context expression (`famURep_meanRestrict`), and the restriction of a context expression to a
cell function (`urep_restrict`). -/

section
namespace UEnv

variable {Λ : Type} {V : UEnv Λ}

/-- `ψ` is represented by the family expression `c`: scheduled, from the seed, one denotation
`fc`, `ψ l = fc (time l) (base l)` on the window. -/
def FamURep (V : UEnv Λ) (ψ : Λ → ℝ) (c : Gen .fam V.E.i V.E.p) : Prop :=
  Gen.IsScheduled V.E.D c ∧ Gen.FromSeed V.E.𝒮 c ∧
    ∃ fc : GenSort.Sem .fam, Gen.Denotes V.E.D V.E.bw V.E.j₀ c fc ∧
      ∀ l ∈ V.W, ψ l = fc (V.time l) (V.base l)

theorem FamURep.congr {ψ ψ' : Λ → ℝ} {c : Gen .fam V.E.i V.E.p} (h : V.FamURep ψ c)
    (hψ : ∀ l ∈ V.W, ψ' l = ψ l) : V.FamURep ψ' c := by
  obtain ⟨hs, hf, fc, hd, hv⟩ := h
  exact ⟨hs, hf, fc, hd, fun l hl => (hψ l hl).trans (hv l hl)⟩

theorem famURep_const (V : UEnv Λ) (a : ℝ) :
    V.FamURep (fun _ => a) (Gen.time (s := .fam) (i := V.E.i) (p := V.E.p) (.const a)) :=
  ⟨.timeConst a, .time _, GenSort.ofTime .fam (TimeLetter.eval V.E.D (.const a)), .time _,
    fun _ _ => rfl⟩

theorem FamURep.add {ψ φ : Λ → ℝ} {a b : Gen .fam V.E.i V.E.p} (ha : V.FamURep ψ a)
    (hb : V.FamURep φ b) : V.FamURep (fun l => ψ l + φ l) (Gen.add a b) := by
  obtain ⟨sa, fa, f, hf, hψ⟩ := ha
  obtain ⟨sb, fb, g, hg, hφ⟩ := hb
  refine ⟨.add sa sb, .add fa fb, GenSort.add .fam f g, .add hf hg, fun l hl => ?_⟩
  show ψ l + φ l = f (V.time l) (V.base l) + g (V.time l) (V.base l)
  rw [hψ l hl, hφ l hl]

theorem FamURep.mul {ψ φ : Λ → ℝ} {a b : Gen .fam V.E.i V.E.p} (ha : V.FamURep ψ a)
    (hb : V.FamURep φ b) : V.FamURep (fun l => ψ l * φ l) (Gen.mul a b) := by
  obtain ⟨sa, fa, f, hf, hψ⟩ := ha
  obtain ⟨sb, fb, g, hg, hφ⟩ := hb
  refine ⟨.mul sa sb, .mul fa fb, GenSort.mul .fam f g, .mul hf hg, fun l hl => ?_⟩
  show ψ l * φ l = f (V.time l) (V.base l) * g (V.time l) (V.base l)
  rw [hψ l hl, hφ l hl]

/-- Finite sums of family-represented functions are family-represented. -/
theorem FamURep.finsetSum {κ : Type*} (s : Finset κ) {ψ : κ → Λ → ℝ}
    (h : ∀ k ∈ s, ∃ c : Gen .fam V.E.i V.E.p, V.FamURep (ψ k) c) :
    ∃ c : Gen .fam V.E.i V.E.p, V.FamURep (fun l => ∑ k ∈ s, ψ k l) c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨_, (famURep_const V 0).congr fun _ _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨e₁, h₁⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨e₂, h₂⟩ := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    exact ⟨_, (h₁.add h₂).congr fun _ _ => by rw [Finset.sum_insert ha]⟩

/-- The restriction of a scheduled, seed-provenanced context expression to real phases is a
uniformly represented cell function, if its values agree with the denotation and are parallel
invariant. -/
theorem urep_restrict {e : Gen .ctx V.E.i V.E.p} (hs : Gen.IsScheduled V.E.D e)
    (hf : Gen.FromSeed V.E.𝒮 e) {f : GenSort.Sem .ctx}
    (hd : Gen.Denotes V.E.D V.E.bw V.E.j₀ e f) {φ : Λ → Vec 2 → Vec 2 → ℝ}
    (hv : ∀ l ∈ V.W, ∀ X ∈ V.U l, ∀ z,
      φ l X z = f (V.time l) ((V.base l).recenter V.E.D (V.E.ρ • X)) z)
    (hi : ∀ l ∈ V.W, ∀ X ∈ V.U l, ∀ z (s : ℝ),
      φ l X (z + s • basisVec (parIdx V.E.p)) = φ l X z) :
    V.URep φ (Gen.restrict e) :=
  ⟨.restrict hs, .restrict hf, f, .restrict hd, hv, hi⟩

/-- **The mean at the offset `0`.** If `φ` is uniformly represented by `e`, `0` is an admissible
offset at every index of the window and `ζ` is a fast profile (recentering by `ρ • 0` is the
identity), then `l ↦ ⟨φ l 0⟩` is family-represented by `Gen.mean e`. -/
theorem URep.mean0 (hζ : IsFastProfile V.E.D.ζ) {φ : Λ → Vec 2 → Vec 2 → ℝ}
    {e : Gen .cell V.E.i V.E.p} (h : V.URep φ e) (h0 : ∀ l ∈ V.W, (0 : Vec 2) ∈ V.U l) :
    V.FamURep (fun l => fieldCellMean (φ l 0)) (Gen.mean e) := by
  obtain ⟨hs, hf, f, hd, hv, -⟩ := h
  refine ⟨.mean hs, .mean hf, cellMeanSem f, .mean hd, fun l hl => ?_⟩
  have : φ l 0 = f (V.time l) ((V.base l).recenter V.E.D (V.E.ρ • (0 : Vec 2))) :=
    funext (hv l hl 0 (h0 l hl))
  simp only [fieldCellMean, this, smul_zero, recenter_zero V.E.D hζ]
  rfl

/-- The mean of a restricted context expression is family-represented. -/
theorem famURep_meanRestrict {e : Gen .ctx V.E.i V.E.p} (hs : Gen.IsScheduled V.E.D e)
    (hf : Gen.FromSeed V.E.𝒮 e) {f : GenSort.Sem .ctx}
    (hd : Gen.Denotes V.E.D V.E.bw V.E.j₀ e f) {ψ : Λ → ℝ}
    (hv : ∀ l ∈ V.W, ψ l = ∫ η in AVenhance.unitCube, f (V.time l) (V.base l) η) :
    V.FamURep ψ (Gen.mean (Gen.restrict e)) :=
  ⟨.mean (.restrict hs), .mean (.restrict hf), cellMeanSem f, .mean (.restrict hd), hv⟩

end UEnv
end

end AVRegularity.Providers.GenSem
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Providers.GenSem

/-! **The coefficients of the direct flux are family-represented.**
`directFlux_famRep`: for a generated old stage `G`, the entry
`fluxCoeff (directFlux G p c γ ords t) d I 0 κ` is `c_d ∑_σ ⟨a♭_{γ,d,I∘σ}(t, 0, ·)⟩_z` (component
`κ`), the mean of the old flux at the offset `0`; the old flux at the offset `0` is the generated
context function at the context `c.1.recenter 0 = c.1`. It is denoted by `const * ∑ mean (restrict e_σ)`,
one scheduled, seed-provenanced family expression for all admissible contexts and all times of
the output window. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The index type of the direct flux: an admissible context over the slot `p` of the level of `G`
and a time. -/
def directEnv (G : GenStage D hr Dm b j₀) (p : OddSlot) : UEnv (StageCtx D b j₀ G.level p × ℝ) where
  E := ⟨D, b, j₀, G.level, p.1, ⟨0, [], 0, []⟩, 1, 0, G.exports, ∅⟩
  time l := l.2
  base l := l.1.1
  U _ := Set.univ
  W := {l | l.2 ∈ ocPulseWindow D.α D.q D.Λ G.level p.1}

/-- A component of the cell mean of an integrable vector field. -/
theorem fieldCellMean_apply {F : Vec 2 → Vec 2} (hF : IntegrableOn F AVenhance.unitCube)
    (κ : Fin 2) : fieldCellMean F κ = ∫ z in AVenhance.unitCube, F z κ := by
  have hcomm := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) κ).integral_comp_comm
    hF
  simp only [ContinuousLinearMap.proj_apply] at hcomm
  exact hcomm.symm

/-- **The coefficients of the direct flux are family-represented.** Hypotheses: the stage `G` is
generated, `IsFastProfile D.ζ` (recentering by `0` is trivial), `1 ≤ d` and all orders in `ords`
are `≥ 1` (as in `fluxCoeff_directFlux`), and the old flux is integrable over the cell
(in `z`, at the offset `0`) at every context and output time, when `d ∈ ords` (without it the
vector cell mean is `0` by convention, while a component of it may not be). The family expression is
for the old level `G.level` and the slot `p`. -/
theorem directFlux_famRep (hζ : IsFastProfile D.ζ) (G : GenStage D hr Dm b j₀)
    (hG : G.IsGenerated) (p : OddSlot) {v u : CompIn G.comps} (γ : G.fam.Γ v u) (ords : Finset ℕ)
    (hords : ∀ d' ∈ ords, 1 ≤ d') {d : ℕ} (hd : 1 ≤ d) (I : DerivativeWord2 (d - 1)) (κ : Fin 2)
    (hint : d ∈ ords → ∀ (c : StageCtx D b j₀ G.level p),
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1, ∀ σ : Equiv.Perm (Fin (d - 1)),
        IntegrableOn (fun z => G.fam.flux p c v u γ d (I ∘ σ) t 0 z) AVenhance.unitCube) :
    ∃ c : Gen .fam G.level p.1, Gen.IsScheduled D c ∧ Gen.FromSeed G.exports c ∧
      ∃ fc : GenSort.Sem .fam, Gen.Denotes D b j₀ c fc ∧
        ∀ (cc : StageCtx D b j₀ G.level p), ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
          fluxCoeff (directFlux G p cc γ ords t) d I 0 κ = fc t cc.1 := by
  classical
  set V := directEnv G p with hV
  -- the mean of one old flux entry
  have hone : ∀ σ : Equiv.Perm (Fin (d - 1)), ∃ c : Gen .fam V.E.i V.E.p,
      V.FamURep (fun l => ∫ z in AVenhance.unitCube,
        G.fam.flux p l.1 v u γ d (I ∘ σ) l.2 0 z κ) c := by
    intro σ
    obtain ⟨f, ⟨e, hs, hf, hden⟩, hfl⟩ := hG p v u γ d (I ∘ σ) κ
    refine ⟨Gen.mean (Gen.restrict e), UEnv.famURep_meanRestrict hs hf hden fun l hl => ?_⟩
    have hz : ∀ z, G.fam.flux p l.1 v u γ d (I ∘ σ) l.2 0 z κ = f l.2 l.1.1 z := fun z => by
      rw [hfl l.1 l.2 hl 0 z]
      simp only [smul_zero, recenter_zero D hζ, l.1.2, ↓reduceIte]
    simp only [hz]
    rfl
  by_cases hdo : d ∈ ords
  · obtain ⟨c, hc⟩ := UEnv.FamURep.finsetSum (V := V) (Finset.univ : Finset (Equiv.Perm (Fin (d - 1))))
      (ψ := fun σ l => ∫ z in AVenhance.unitCube, G.fam.flux p l.1 v u γ d (I ∘ σ) l.2 0 z κ)
      fun σ _ => hone σ
    have hc' := (UEnv.famURep_const V (D.kap G.level * D.eps G.level ^ (d - 2) *
      ((d - 1).factorial : ℝ)⁻¹)).mul hc
    obtain ⟨hs, hf, fc, hden, hv⟩ := hc'
    refine ⟨_, hs, hf, fc, hden, fun cc t ht => ?_⟩
    refine Eq.trans ?_ (hv (cc, t) ht)
    have h1 := congrFun (fluxCoeff_directFlux G p cc γ ords hords t hd I) κ
    rw [h1]
    simp only [hdo, ↓reduceIte, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun σ _ => fieldCellMean_apply (hint hdo cc t ht σ) κ
  · obtain ⟨hs, hf, fc, hden, hv⟩ := UEnv.famURep_const V 0
    refine ⟨_, hs, hf, fc, hden, fun cc t ht => ?_⟩
    refine Eq.trans ?_ (hv (cc, t) ht)
    have h1 := congrFun (fluxCoeff_directFlux G p cc γ ords hords t hd I) κ
    rw [h1]
    simp [hdo]

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **The covariance letter as an array operator.** The finer output of the covariance
letter `𝖵_{n,h,a,a'}` on the base chain `A` (`SuccSource.fluxOp`, branch `letterCov`) is
`covLetterFlux`: the Piola pullback by the chart pair `(Φ, Φ⁻¹) = (A.famMap, A.famMapInv)` of
`c_{a,a'} 𝒞^a ∘ Φ_*(ℳ) ∘ 𝒞^{a'}`, with the path mean `ℳ` and the covariance operator `𝒞`.

`covLetterFlux_applyArr`: on smooth test fields it is the array operator with the arrays
`covFin` (order `2a + n + 2a'`), built from the path mean array `pmArr`, the push and pull arrays
of the chart pair (`chartArr`), and the constant arrays `covArrPow` of `𝒞`. The lift data are
required to be `C^{2a + Dm + 2}` (the outer `𝒞^a` differentiates the push-forward coefficients
`2a` times). -/

variable {h Dm : ℕ}

/-- The finer output of the covariance letter on the base chain `A` (as in `SuccSource.fluxOp`). -/
def covLetterFlux (D : OCData) (m : ℕ) (ρ s₀ : ℝ)
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n a a' : ℕ) (t : ℝ) (A : RealChain) :
    (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  pullFlux (A.famMap D t) (A.famMapInv D t) (fun g x =>
    ((a.factorial * a'.factorial : ℝ)⁻¹ * (-1) ^ a) •
      (SuccSource.covAtFlux D m s₀ t)^[a]
        (pushFlux (A.famMap D t) (A.famMapInv D t) (pathMeanFlux D m ρ Q Cc n t)
          ((SuccSource.covAt D m s₀ t)^[a'] g)) x)

/-- The covariance matrix of the covariance letter. -/
abbrev covMat (D : OCData) (m : ℕ) (s₀ t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t

/-- The push-forward arrays `Φ_*(ℳ)`. -/
def covB1 (D : OCData) (m : ℕ) (ρ : ℝ) (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ) (A : RealChain)
    (c : Fin 2) : CArr :=
  chartArr (fun x => jacMatrix (A.famMap D t) (A.famMapInv D t x)) (A.famMapInv D t)
    (A.famMap D t) n (fun κ => pmArr D m ρ Q Cc n t κ) c

/-- The arrays of `Φ_*(ℳ) ∘ 𝒞^{a'}`. -/
def covB2 (D : OCData) (m : ℕ) (ρ s₀ : ℝ) (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n a' : ℕ) (t : ℝ) (A : RealChain)
    (c : Fin 2) : CArr :=
  compArr n (covB1 D m ρ Q Cc n t A c) (covArrPow (covMat D m s₀ t) a') 0

/-- The arrays of `c_{a,a'} 𝒞^a ∘ Φ_*(ℳ) ∘ 𝒞^{a'}`. -/
def covB4 (D : OCData) (m : ℕ) (ρ s₀ : ℝ) (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n a a' : ℕ) (t : ℝ) (A : RealChain)
    (c : Fin 2) : CArr :=
  ((a.factorial * a'.factorial : ℝ)⁻¹ * (-1) ^ a) •
    compArr (2 * a) (covArrPow (covMat D m s₀ t) a) (covB2 D m ρ s₀ Q Cc n a' t A c) 0

/-- The arrays of the covariance letter (the pullback of `covB4`). -/
def covFin (D : OCData) (m : ℕ) (ρ s₀ : ℝ) (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n a a' : ℕ) (t : ℝ) (A : RealChain)
    (c : Fin 2) : CArr :=
  chartArr (fun x => (jacMatrix (A.famMap D t) x)⁻¹) (A.famMap D t) (A.famMapInv D t)
    (2 * a + (n + 2 * a')) (covB4 D m ρ s₀ Q Cc n a a' t A) c

/-! ### Support and slow regularity of chart arrays -/

theorem arrSupp_chartArr (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (N Ψ : Vec 2 → Vec 2) (K : ℕ)
    (A : Fin 2 → CArr) (c : Fin 2) : ArrSupp K (chartArr M N Ψ K A c) := by
  intro m' hm' γ
  funext p z
  simp only [chartArr, chartCoef, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun α _ => ?_, mul_zero]
  have hmK : m ≤ K := by simpa [Nat.lt_succ_iff] using hm
  rw [arrSupp_fdbArr Ψ α m' (by omega) γ]
  simp

theorem arrSlowSmooth_chartArr {r : ℕ} {M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {N Ψ : Vec 2 → Vec 2} (K : ℕ) {A : Fin 2 → CArr}
    (hM : ∀ c k, ContDiff ℝ (r : WithTop ℕ∞) (fun p => M p c k))
    (hN : ContDiff ℝ (r : WithTop ℕ∞) N) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hA : ∀ k m (α : DerivativeWord2 m), ContDiff ℝ (r : WithTop ℕ∞) (fun y => A k m α y 0))
    (c : Fin 2) : ArrSlowSmooth r (chartArr M N Ψ K A c) := by
  intro m' γ z
  simp only [chartArr, chartCoef]
  refine ContDiff.sum fun k _ => (hM c k).mul (ContDiff.sum fun m _ => ContDiff.sum fun α _ => ?_)
  exact ((hA k m α).comp hN).mul ((arrSlowSmooth_fdbArr hΨ r α m' γ 0).comp hN)

theorem arrSupp_covFin (D : OCData) (m : ℕ) (ρ s₀ : ℝ)
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n a a' : ℕ) (t : ℝ) (A : RealChain)
    (c : Fin 2) : ArrSupp (2 * a + (n + 2 * a')) (covFin D m ρ s₀ Q Cc n a a' t A c) :=
  arrSupp_chartArr _ _ _ _ _ c

/-! ### The identity -/

variable {D : OCData} {m : ℕ} {ρ s₀ : ℝ} {Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm}
  {Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)} {n a a' : ℕ} {t : ℝ}

theorem arrSlowSmooth_covB2 (A : RealChain)
    (hreg : LiftRegular Q Cc (0 : Fin (h + 1)) ((D.cellScaleSq m)⁻¹ * t) h n (2 * a + Dm + 2))
    (c : Fin 2) : ArrSlowSmooth (2 * a) (covB2 D m ρ s₀ Q Cc n a' t A c) := by
  have htopV : ∀ (r : ℕ) {g : Vec 2 → Vec 2}, ContDiff ℝ (⊤ : ℕ∞) g →
      ContDiff ℝ (r : WithTop ℕ∞) g := fun r _ hg => hg.of_le (by exact_mod_cast le_top)
  have htopR : ∀ (r : ℕ) {g : Vec 2 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) g →
      ContDiff ℝ (r : WithTop ℕ∞) g := fun r _ hg => hg.of_le (by exact_mod_cast le_top)
  have hinv : ContDiff ℝ ((2 * a : ℕ) : WithTop ℕ∞) (A.famMapInv D t) :=
    htopV (2 * a) (contDiff_famMapInv A t)
  have hjac : ∀ c k, ContDiff ℝ ((2 * a : ℕ) : WithTop ℕ∞)
      (fun p => jacMatrix (A.famMap D t) (A.famMapInv D t p) c k) := fun c k =>
    (htopR (2 * a) (contDiff_jacMatrix_entry (contDiff_famMap A t) c k)).comp hinv
  have hB1 : ArrSlowSmooth (2 * a) (covB1 D m ρ Q Cc n t A c) :=
    arrSlowSmooth_chartArr n hjac hinv (contDiff_famMap A t)
      (fun κ j α => contDiff_pmArr D m ρ Q Cc n t κ hreg j α) c
  exact arrSlowSmooth_compArr n hB1 (covArrPow_slowSmooth _ (2 * a + n) a') 0

/-- **The push-forward of the path mean flux** by the chart pair of `A` is the array operator
`covB1`, on smooth fields. -/
theorem push_pathMeanFlux_applyArr (hζ : IsFastProfile D.ζ) (hρ : ρ ≠ 0) (A : RealChain)
    (hreg : LiftRegular Q Cc (0 : Fin (h + 1)) ((D.cellScaleSq m)⁻¹ * t) h n (Dm + 2))
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : Vec 2) (c : Fin 2) :
    pushFlux (A.famMap D t) (A.famMapInv D t) (pathMeanFlux D m ρ Q Cc n t) f w c =
      applyArr n (covB1 D m ρ Q Cc n t A c) f w 0 := by
  have e1 : pushFlux (A.famMap D t) (A.famMapInv D t) (pathMeanFlux D m ρ Q Cc n t) f w =
      pushFlux (A.famMap D t) (A.famMapInv D t)
        (fun g' y k => applyArr n (pmArr D m ρ Q Cc n t k) g' y 0) f w := by
    unfold pushFlux
    congr 1
    funext k
    exact pathMeanFlux_applyArr D m hρ Q Cc n t hreg
      ((hf.comp (contDiff_famMap A t)).of_le (by exact_mod_cast le_top)) _ k
  rw [e1, pushFlux_famMap_applyArr hζ A t n _ hf w c]
  rfl

/-- **The covariance letter is an array operator** on smooth test fields. -/
theorem covLetterFlux_applyArr (hζ : IsFastProfile D.ζ) (hρ : ρ ≠ 0) (A : RealChain)
    (hreg : LiftRegular Q Cc (0 : Fin (h + 1)) ((D.cellScaleSq m)⁻¹ * t) h n (2 * a + Dm + 2))
    {u : Vec 2 → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (y : Vec 2) (c : Fin 2) :
    covLetterFlux D m ρ s₀ Q Cc n a a' t A u y c =
      applyArr (2 * a + (n + 2 * a')) (covFin D m ρ s₀ Q Cc n a a' t A c) u y 0 := by
  have hreg0 : LiftRegular Q Cc (0 : Fin (h + 1)) ((D.cellScaleSq m)⁻¹ * t) h n (Dm + 2) :=
    hreg.mono le_rfl le_rfl (by omega)
  have hB2 := arrSlowSmooth_covB2 (ρ := ρ) (s₀ := s₀) (a' := a') A hreg
  have htop : ∀ {f : Vec 2 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f → ∀ k : ℕ,
      ContDiff ℝ (k : WithTop ℕ∞) f := fun hf k => hf.of_le (by exact_mod_cast le_top)
  -- the inner operator on a smooth field `g`
  have step : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ∀ x,
      ((a.factorial * a'.factorial : ℝ)⁻¹ * (-1) ^ a) •
        (SuccSource.covAtFlux D m s₀ t)^[a] (pushFlux (A.famMap D t) (A.famMapInv D t)
          (pathMeanFlux D m ρ Q Cc n t) ((SuccSource.covAt D m s₀ t)^[a'] g)) x =
        fun k => applyArr (2 * a + (n + 2 * a')) (covB4 D m ρ s₀ Q Cc n a a' t A k) g x 0 := by
    intro g hg x
    rw [show SuccSource.covAtFlux D m s₀ t = covOperator (covMat D m s₀ t) from rfl,
      show SuccSource.covAt D m s₀ t = covOperator (covMat D m s₀ t) from rfl]
    set Hc := covMat D m s₀ t with hHc
    have hcov' : (covOperator Hc)^[a'] g = fun X => applyArr (2 * a') (covArrPow Hc a') g X 0 :=
      funext fun X => covOperator_iterate_eq Hc hg a' X 0
    have hh₁ : ContDiff ℝ (⊤ : ℕ∞) ((covOperator Hc)^[a'] g) :=
      contDiff_infty.mpr fun k => contDiff_covOperator_iterate Hc a' (htop hg _)
    have hV : ∀ w c', pushFlux (A.famMap D t) (A.famMapInv D t) (pathMeanFlux D m ρ Q Cc n t)
        ((covOperator Hc)^[a'] g) w c' =
        applyArr (n + 2 * a') (covB2 D m ρ s₀ Q Cc n a' t A c') g w 0 := by
      intro w c'
      rw [push_pathMeanFlux_applyArr hζ hρ A hreg0 hh₁ w c', hcov']
      exact opComp_flux_right n (2 * a') (fun c => covB1 D m ρ Q Cc n t A c) (covArrPow Hc a') g
        (htop hg _) (covArrPow_slowSmooth Hc n a') (covArrPow_supp Hc a') w c'
    set V := pushFlux (A.famMap D t) (A.famMapInv D t) (pathMeanFlux D m ρ Q Cc n t)
      ((covOperator Hc)^[a'] g) with hVdef
    have hVeq : V = fun w c' => applyArr (n + 2 * a') (covB2 D m ρ s₀ Q Cc n a' t A c') g w 0 :=
      funext fun w => funext fun c' => hV w c'
    have hVc : ∀ c', ContDiff ℝ ((2 * a : ℕ) : WithTop ℕ∞)
        (fun w => applyArr (n + 2 * a') (covB2 D m ρ s₀ Q Cc n a' t A c') g w 0) := fun c' =>
      contDiff_applyArr_slow (n + 2 * a') (2 * a) (htop hg _) (hB2 c') 0
    have hVs : ContDiff ℝ ((2 * a : ℕ) : WithTop ℕ∞) V := by
      rw [hVeq]
      exact contDiff_pi.2 fun c' => hVc c'
    funext c'
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [covOperator_iterate_component Hc a hVs x c']
    have e2 : (fun w => V w c') =
        fun w => applyArr (n + 2 * a') (covB2 D m ρ s₀ Q Cc n a' t A c') g w 0 :=
      funext fun w => hV w c'
    rw [e2, covOperator_iterate_eq_nat Hc a (hVc c') x 0,
      opComp_flux_left (2 * a) (n + 2 * a') (covArrPow Hc a)
        (fun c => covB2 D m ρ s₀ Q Cc n a' t A c) g (htop hg _) hB2
        (fun c => arrSupp_compArr n _ 0 (covArrPow_supp Hc a')) x c']
    rw [covB4, applyArr_smul]
    rfl
  have hg : ContDiff ℝ (⊤ : ℕ∞) (u ∘ A.famMapInv D t) := hu.comp (contDiff_famMapInv A t)
  have e3 : covLetterFlux D m ρ s₀ Q Cc n a a' t A u y =
      pullFlux (A.famMap D t) (A.famMapInv D t)
        (fun g x k => applyArr (2 * a + (n + 2 * a')) (covB4 D m ρ s₀ Q Cc n a a' t A k) g x 0)
        u y := by
    simp only [covLetterFlux, pullFlux]
    rw [step _ hg]
  rw [e3, pullFlux_famMap_applyArr hζ A t _ _ hu y c]
  rfl

end AVRegularity.Providers.GenSem
end
end
