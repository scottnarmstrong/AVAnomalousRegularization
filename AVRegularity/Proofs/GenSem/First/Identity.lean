-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.Finer.CovLetterArr
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVRegularity.Proofs.GenSem.Op.FamChart

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Providers.GenSem

/-! **D6c groundwork: generic array facts for the first source.**
* `JetRepG.comap`, `ArrJetG.comap`: represented jets pull back along a map of indices that maps
  represented functions to represented functions (restriction of the index set).
* `matGradArr M c`: the order-one array of `g ↦ (M x *ᵥ ∇g x) c`; `matGrad_applyArr`.
* `ArrJetG.add`, `ArrJetG.sum`, `ArrJetG.smul'`: closure of represented array jets.
* `polyArr Hc p w`: the array of `∑_{l ≤ p} w l • 𝒞^l` (covariance polynomials `P_p`, `Q_p`). -/

section comap

variable {Λ Λ' : Type*} {R : (Λ → ℝ) → Prop} {R' : (Λ' → ℝ) → Prop}

theorem JetRepG.comap (f : Λ' → Λ) (hf : ∀ F, R F → R' (fun l' => F (f l'))) :
    ∀ {r : ℕ} {g : Λ → Vec 2 → ℝ}, JetRepG R r g → JetRepG R' r (fun l' => g (f l'))
  | 0, _, hg => hf _ hg
  | _ + 1, _, hg => ⟨hf _ hg.1, fun j => JetRepG.comap f hf (hg.2 j)⟩

theorem ArrJetG.comap (f : Λ' → Λ) (hf : ∀ F, R F → R' (fun l' => F (f l'))) {r : ℕ}
    {B : Λ → CArr} (hB : ArrJetG R r B) : ArrJetG R' r (fun l' => B (f l')) := fun m α =>
  ⟨JetRepG.comap f hf (hB m α).1, fun l' => (hB m α).2 (f l')⟩

end comap

section closure

variable {Λ : Type*} {R : (Λ → ℝ) → Prop}

theorem ArrJetG.add (hR : RepAlg R) {r : ℕ} {A B : Λ → CArr} (hA : ArrJetG R r A)
    (hB : ArrJetG R r B) : ArrJetG R r (fun l => A l + B l) := fun m α =>
  ⟨(JetRepG.add hR (hA m α).2 (hB m α).2 (hA m α).1 (hB m α).1).congr_germ fun _ =>
      Filter.Eventually.of_forall fun _ => rfl,
    fun l => ((hA m α).2 l).add ((hB m α).2 l)⟩

theorem ArrJetG.zero (hR : RepAlg R) (r : ℕ) : ArrJetG R r (fun _ : Λ => (0 : CArr)) :=
  fun _ _ => ⟨(jetRepG_const hR r 0).congr_germ fun _ => Filter.Eventually.of_forall fun _ => rfl,
    fun _ => contDiff_const⟩

theorem ArrJetG.sum (hR : RepAlg R) {r : ℕ} {κ : Type*} (s : Finset κ) {A : κ → Λ → CArr}
    (hA : ∀ k ∈ s, ArrJetG R r (A k)) : ArrJetG R r (fun l => ∑ k ∈ s, A k l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ArrJetG.zero hR r
  | insert a s ha ih =>
    have := ArrJetG.add hR (hA a (Finset.mem_insert_self a s))
      (ih fun k hk => hA k (Finset.mem_insert_of_mem hk))
    simpa [Finset.sum_insert ha] using this

theorem ArrJetG.neg (hR : RepAlg R) {r : ℕ} {B : Λ → CArr} (hB : ArrJetG R r B) :
    ArrJetG R r (fun l => -B l) := fun m α =>
  ⟨(JetRepG.mul hR (fun _ => contDiff_const) (hB m α).2 (jetRepG_const hR r (-1))
      (hB m α).1).congr_germ fun _ => Filter.Eventually.of_forall fun _ => by
        simp only [Pi.neg_apply]; ring,
    fun l => ((hB m α).2 l).neg⟩

theorem ArrJetG.sub (hR : RepAlg R) {r : ℕ} {A B : Λ → CArr} (hA : ArrJetG R r A)
    (hB : ArrJetG R r B) : ArrJetG R r (fun l => A l - B l) := by
  have h := ArrJetG.add hR hA (ArrJetG.neg hR hB)
  simpa [sub_eq_add_neg] using h

/-- Scaling by a represented scalar (constant in the label). -/
theorem ArrJetG.smul' (hR : RepAlg R) {r : ℕ} {c : Λ → ℝ} (hc : R c) {B : Λ → CArr}
    (hB : ArrJetG R r B) : ArrJetG R r (fun l => c l • B l) := fun m α =>
  ⟨(JetRepG.mul hR (fun _ => contDiff_const) (hB m α).2 (jetRepG_labelConst hR hc r)
      (hB m α).1).congr_germ fun _ => Filter.Eventually.of_forall fun _ => rfl,
    fun l => contDiff_const.mul ((hB m α).2 l)⟩

end closure

/-! ### Slow regularity of arrays -/

theorem ArrSlowSmooth.add {r : ℕ} {A B : CArr} (hA : ArrSlowSmooth r A) (hB : ArrSlowSmooth r B) :
    ArrSlowSmooth r (A + B) := fun m α z => (hA m α z).add (hB m α z)

theorem ArrSlowSmooth.neg {r : ℕ} {A : CArr} (hA : ArrSlowSmooth r A) : ArrSlowSmooth r (-A) :=
  fun m α z => (hA m α z).neg

theorem ArrSlowSmooth.sub {r : ℕ} {A B : CArr} (hA : ArrSlowSmooth r A) (hB : ArrSlowSmooth r B) :
    ArrSlowSmooth r (A - B) := fun m α z => (hA m α z).sub (hB m α z)

theorem ArrSlowSmooth.smul {r : ℕ} (c : ℝ) {A : CArr} (hA : ArrSlowSmooth r A) :
    ArrSlowSmooth r (c • A) := fun m α z => contDiff_const.mul (hA m α z)

theorem ArrSlowSmooth.zero (r : ℕ) : ArrSlowSmooth r (0 : CArr) := fun _ _ _ => contDiff_const

theorem ArrSlowSmooth.sum {r : ℕ} {κ : Type*} (s : Finset κ) {A : κ → CArr}
    (hA : ∀ k ∈ s, ArrSlowSmooth r (A k)) : ArrSlowSmooth r (∑ k ∈ s, A k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ArrSlowSmooth.zero r
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hA a (Finset.mem_insert_self a s)).add (ih fun k hk => hA k (Finset.mem_insert_of_mem hk))

/-! ### Matrix times gradient -/

/-- The order-one array of `g ↦ (M x *ᵥ ∇g x) c`. -/
def matGradArr (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (c : Fin 2) : CArr
  | 1, α, x, _ => M x c (α 0)
  | _, _, _, _ => 0

theorem matGradArr_supp (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (c : Fin 2) :
    ArrSupp 1 (matGradArr M c) := by
  intro m hm α
  match m, hm with
  | m + 2, _ => rfl

theorem orderedDerivative_single (g : Vec 2 → ℝ) (α : DerivativeWord2 1) :
    orderedDerivative α g = fun y => fderiv ℝ g y (basisVec (α 0)) := by
  have : α = Fin.snoc (Fin.elim0 : Fin 0 → Fin 2) (α 0) := by
    funext k; fin_cases k; simp [Fin.snoc]
  rw [this, orderedDerivative_snoc, orderedDerivative_zero_word]
  simp [Fin.snoc]

theorem matGrad_applyArr (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : Vec 2 → ℝ) (x z : Vec 2)
    (c : Fin 2) : (M x).mulVec (gradField g x) c = applyArr 1 (matGradArr M c) g x z := by
  unfold applyArr
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  have h0 : ∀ α : DerivativeWord2 0, matGradArr M c 0 α x z = 0 := fun _ => rfl
  simp only [h0, zero_mul, Finset.sum_const_zero, zero_add]
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
  simp only [Matrix.mulVec, dotProduct, gradField, orderedDerivative_single]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

theorem arrJetG_matGradArr {Λ : Type*} {R : (Λ → ℝ) → Prop} (hR : RepAlg R) {r : ℕ}
    {M : Λ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hMj : ∀ a b, JetRepG R r (fun l x => M l x a b))
    (hMs : ∀ a b l, ContDiff ℝ (r : WithTop ℕ∞) (fun x => M l x a b)) (c : Fin 2) :
    ArrJetG R r (fun l => matGradArr (M l) c) := by
  intro m α
  cases m with
  | zero => exact ⟨(jetRepG_const hR r 0).congr_germ fun _ =>
      Filter.Eventually.of_forall fun _ => rfl, fun _ => contDiff_const⟩
  | succ m =>
    cases m with
    | zero => exact ⟨hMj c (α 0), fun l => hMs c (α 0) l⟩
    | succ m => exact ⟨(jetRepG_const hR r 0).congr_germ fun _ =>
        Filter.Eventually.of_forall fun _ => rfl, fun _ => contDiff_const⟩

/-! ### Covariance polynomials -/

/-- The array of `∑_{l ≤ p} w l • 𝒞^l` (order `2p`). -/
def polyArr (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (w : ℕ → ℝ) : CArr :=
  ∑ l ∈ Finset.range (p + 1), w l • covArrPow Hc l

theorem polyArr_supp (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (w : ℕ → ℝ) :
    ArrSupp (2 * p) (polyArr Hc p w) := by
  intro m hm α
  unfold polyArr
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_eq_zero fun l hl => ?_
  have hlp : l ≤ p := by simpa [Nat.lt_succ_iff] using hl
  rw [covArrPow_supp Hc l m (by omega) α, smul_zero]

theorem polyArr_slowSmooth (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (w : ℕ → ℝ) (r : ℕ) :
    ArrSlowSmooth r (polyArr Hc p w) := by
  intro m α z
  unfold polyArr
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact ContDiff.sum fun l _ => contDiff_const.mul (covArrPow_slowSmooth Hc r l m α z)

/-- A covariance polynomial as an array operator, on `C^{2p}` fields. -/
theorem covPoly_applyArr (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (w : ℕ → ℝ)
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x z : Vec 2) :
    (∑ l ∈ Finset.range (p + 1), w l • (covOperator Hc)^[l] f) x =
      applyArr (2 * p) (polyArr Hc p w) f x z := by
  unfold polyArr
  rw [applyArr_sum]
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlp : l ≤ p := by simpa [Nat.lt_succ_iff] using hl
  rw [Pi.smul_apply, applyArr_smul, Pi.smul_apply, Pi.smul_apply,
    covOperator_iterate_eq Hc hf l x z,
    applyArr_eq_of_supp (by omega : 2 * l ≤ 2 * p) (covArrPow_supp Hc l)]

theorem arrJetG_polyArr {Λ : Type*} {R : (Λ → ℝ) → Prop} (hR : RepAlg R)
    {H : Λ → Matrix (Fin 2) (Fin 2) ℝ} (hH : ∀ i j, R (fun l => H l i j)) (p : ℕ) (w : ℕ → ℝ)
    (r : ℕ) : ArrJetG R r (fun l => polyArr (H l) p w) := by
  unfold polyArr
  exact ArrJetG.sum hR _ fun l _ =>
    (ArrJetG.smul' hR (hR.const (w l)) (arrJetG_covArrPow hR hH l r))

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **D6c: the assembled diagonal mean flux as an array operator.** At the context `(ch, ζ)` of
level `m - 1` and the time `t`, the assembled grade-zero mean flux `K_n` (`diagMeanFluxCtx`) is the
array operator with the arrays `dmArr`: the sum over the scheduled finer slots `k` of
`ϖ_{m,k}(t) • (Ψ_k)_* K^lab_{n,k}` (push-forward arrays `covB1` of the path mean arrays of the
appended child `𝒜^♮_k`), for the admissible children. The flux `𝓕_A` (`diagFluxCtx`) is then the
array operator `dfArr` of order `N + 1`. -/

section
variable {D : OCData} {b : ℝ} {j₀ Dm m : ℕ} {ρ : ℝ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

/-- The grade-zero lift data of the appended child for the finer slot `k`. -/
abbrev diagQ (D : OCData) (Dm m : ℕ) (k : ℤ) (B : RealChain) (ρ : ℝ) :
    LiftOperatorData (Fin 1) (fun _ => ℝ) Dm :=
  familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k B ρ (fun _ _ _ => [])

/-- The push-forward arrays of the grade-zero label flux of the child appended for `k`. -/
def diagChildArr (D : OCData) (Dm m : ℕ) (ρ : ℝ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (k : ℤ) (n : ℕ) (t : ℝ)
    (B : RealChain) (c : Fin 2) : CArr :=
  covB1 D m ρ (diagQ D Dm m k B ρ) (Cc0 k B) n t B c

open scoped Classical in
/-- The arrays of `K_n` at the context `(ch, ζ)`, over the finite set `S` of scheduled slots. -/
def dmArr (D : OCData) (b : ℝ) (j₀ Dm m : ℕ) (ρ : ℝ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (S : Finset ℤ) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (n : ℕ) (c : Fin 2) : CArr :=
  ∑ k ∈ S, if IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ) then
    ocCutoff D.α D.q D.Λ m k t • diagChildArr D Dm m ρ Cc0 k n t (ch.appendChild D k t ζ) c else 0

theorem arrSupp_diagChildArr (D : OCData) (Dm m : ℕ) (ρ : ℝ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (k : ℤ) (n : ℕ) (t : ℝ)
    (B : RealChain) (c : Fin 2) : ArrSupp n (diagChildArr D Dm m ρ Cc0 k n t B c) :=
  arrSupp_chartArr _ _ _ _ _ c

theorem arrSupp_dmArr (S : Finset ℤ) (t : ℝ) (ch : RealChain) (ζ : Vec 2) (n : ℕ) (c : Fin 2) :
    ArrSupp n (dmArr D b j₀ Dm m ρ Cc0 S t ch ζ n c) := by
  classical
  unfold dmArr
  refine ArrSupp.sum _ fun k _ => ?_
  split_ifs
  · exact (arrSupp_diagChildArr D Dm m ρ Cc0 k n t _ c).smul _
  · exact ArrSupp.zero n

open scoped Classical in
/-- **The assembled mean flux is an array operator**, on smooth fields, when the scheduled finer
slots are the finite set `S` and the lifts of the admissible children are regular. -/
theorem diagMeanFluxCtx_applyArr (hζ : IsFastProfile D.ζ) (hρ : ρ ≠ 0) (t : ℝ) (ch : RealChain)
    (ζ : Vec 2) (n : ℕ) (S : Finset ℤ)
    (hS : ∀ k, k ∈ S ↔ Odd k ∧ IsScheduledIn D (m - 1) k ch.slot)
    (hreg : ∀ k ∈ S, IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ) →
      ocCutoff D.α D.q D.Λ m k t ≠ 0 →
      LiftRegular (diagQ D Dm m k (ch.appendChild D k t ζ) ρ) (Cc0 k (ch.appendChild D k t ζ))
        (0 : Fin 1) ((D.cellScaleSq m)⁻¹ * t) 0 n (Dm + 2))
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (c : Fin 2) :
    diagMeanFluxCtx D b j₀ Dm m ρ Cc0 t ch ζ n f x c =
      applyArr n (dmArr D b j₀ Dm m ρ Cc0 S t ch ζ n c) f x 0 := by
  have hfin : {k : ℤ | Odd k ∧ IsScheduledIn D (m - 1) k ch.slot} = (S : Set ℤ) := by
    ext k; simp [hS k]
  unfold diagMeanFluxCtx
  have e : (∑ᶠ (k : ℤ) (_ : Odd k ∧ IsScheduledIn D (m - 1) k ch.slot),
      (if IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ) then
        ocCutoff D.α D.q D.Λ m k t • pushFlux ((ch.appendChild D k t ζ).famMap D t)
          ((ch.appendChild D k t ζ).famMapInv D t)
          (diagLabelFlux D Dm m ρ Cc0 k (ch.appendChild D k t ζ) n t) f x else 0)) =
      ∑ k ∈ S, (if IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ) then
        ocCutoff D.α D.q D.Λ m k t • pushFlux ((ch.appendChild D k t ζ).famMap D t)
          ((ch.appendChild D k t ζ).famMapInv D t)
          (diagLabelFlux D Dm m ρ Cc0 k (ch.appendChild D k t ζ) n t) f x else 0) := by
    rw [← finsum_mem_coe_finset]
    refine finsum_congr fun k => ?_
    rw [show (k ∈ (S : Set ℤ)) = (Odd k ∧ IsScheduledIn D (m - 1) k ch.slot) from by
      rw [← hfin]; rfl]
  rw [e, Finset.sum_apply]
  unfold dmArr
  rw [applyArr_sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  split_ifs with hadm
  · rw [Pi.smul_apply, smul_eq_mul, applyArr_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hcut : ocCutoff D.α D.q D.Λ m k t = 0
    · rw [hcut, zero_mul, zero_mul]
    · congr 1
      exact push_pathMeanFlux_applyArr hζ hρ _ (hreg k hk hadm hcut) hf x c
  · simp [applyArr_zero]

/-- The arrays of `𝓕_A = (K_2 - 𝖩_m∇) + ∑_{n=3}^{N+1} K_n`. -/
def dfArr (D : OCData) (b : ℝ) (j₀ Dm m : ℕ) (ρ : ℝ) (N : ℕ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (S : Finset ℤ) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (c : Fin 2) : CArr :=
  (dmArr D b j₀ Dm m ρ Cc0 S t ch ζ 2 c -
      matGradArr (fun _ => ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t) c) +
    ∑ n ∈ Finset.Icc 3 (N + 1), dmArr D b j₀ Dm m ρ Cc0 S t ch ζ n c

theorem applyArr_sub' (K : ℕ) (A B : CArr) (a : Vec 2 → ℝ) :
    applyArr K (A - B) a = applyArr K A a - applyArr K B a := by
  funext X z
  simp only [applyArr, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- **`𝓕_A` is an array operator** of order `N + 1`, on smooth fields. -/
theorem diagFluxCtx_applyArr (hζ : IsFastProfile D.ζ) (hρ : ρ ≠ 0) (N : ℕ) (hN : 1 ≤ N) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (S : Finset ℤ)
    (hS : ∀ k, k ∈ S ↔ Odd k ∧ IsScheduledIn D (m - 1) k ch.slot)
    (hreg : ∀ n, 2 ≤ n → n ≤ N + 1 → ∀ k ∈ S,
      IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ) →
      ocCutoff D.α D.q D.Λ m k t ≠ 0 →
      LiftRegular (diagQ D Dm m k (ch.appendChild D k t ζ) ρ) (Cc0 k (ch.appendChild D k t ζ))
        (0 : Fin 1) ((D.cellScaleSq m)⁻¹ * t) 0 n (Dm + 2))
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (c : Fin 2) :
    diagFluxCtx D b j₀ Dm m ρ N Cc0 t ch ζ f x c =
      applyArr (N + 1) (dfArr D b j₀ Dm m ρ N Cc0 S t ch ζ c) f x 0 := by
  have hpad : ∀ n, n ≤ N + 1 → applyArr n (dmArr D b j₀ Dm m ρ Cc0 S t ch ζ n c) f x 0 =
      applyArr (N + 1) (dmArr D b j₀ Dm m ρ Cc0 S t ch ζ n c) f x 0 := fun n hn => by
    rw [applyArr_eq_of_supp hn (arrSupp_dmArr S t ch ζ n c)]
  unfold diagFluxCtx dfArr
  simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply]
  rw [applyArr_add, applyArr_sub', applyArr_sum]
  simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply]
  rw [diagMeanFluxCtx_applyArr hζ hρ t ch ζ 2 S hS (hreg 2 le_rfl (by omega)) hf x c, hpad 2 (by omega),
    matGrad_applyArr (fun _ => ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t) f x 0 c,
    applyArr_eq_of_supp (by omega : 1 ≤ N + 1) (matGradArr_supp _ c)]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_Icc.mp hn
  rw [diagMeanFluxCtx_applyArr hζ hρ t ch ζ n S hS (hreg n (by omega) hn'.2) hf x c,
    hpad n hn'.2]
end

/-! **D6c: the first source as an array operator.** At the context `(ch, ζ)` of level `m - 1` and
the time `t`, the first-source flux `firstSourceFlux` is, on smooth test fields, the array operator
with the arrays `fsArr` (order `2p + (N + 1 + 2p)`):
* the commutator flux `𝒥_H g = -(S_c H + H S_cᵀ)∇g` with the context strain `S_c` at the
  recentered contexts (`jhArr`, order one, coefficients from `strainAt`);
* `𝒞^a 𝒥_H 𝒞^{l-1-a}` (`eArr`), the assembled mean flux `𝓕_A P_p` (`dfArr` composed with the
  covariance polynomial `P_p`), their combination (`wArr`), `Q_p` of it, and the Piola pullback by
  the chart pair of the context family.

The hypotheses: the strain field `x ↦ S_c(x)` is `C^{4p}`; the lifts of the admissible appended
children are `C^{2p + Dm + 2}`; `N ≥ 1`. -/

section
/-- The context strain at the label `x` of the context `(ch, ζ)` of level `m - 1`. -/
def strainAt (D : OCData) (m : ℕ) (t : ℝ) (ch : RealChain) (ζ x : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  contextStrain D (m - 1) ch.slot t (ch.recenter D (ch.famMapInv D t x))
    (ζ + (D.eps (m - 1))⁻¹ • ch.famMapInv D t x)

/-- The matrix field of the commutator flux `𝒥_H`. -/
def jhMat (D : OCData) (m : ℕ) (s₀ t : ℝ) (ch : RealChain) (ζ : Vec 2) (x : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  strainAt D m t ch ζ x * covMat D m s₀ t + covMat D m s₀ t * Matrix.transpose (strainAt D m t ch ζ x)

/-- The arrays of `𝒥_H`. -/
def jhArr (D : OCData) (m : ℕ) (s₀ t : ℝ) (ch : RealChain) (ζ : Vec 2) (c : Fin 2) : CArr :=
  (-1 : ℝ) • matGradArr (jhMat D m s₀ t ch ζ) c

/-- The arrays of `𝒞^a 𝒥_H 𝒞^{l-1-a}`. -/
def eArr (D : OCData) (m : ℕ) (s₀ t : ℝ) (ch : RealChain) (ζ : Vec 2) (l a : ℕ) (c : Fin 2) :
    CArr :=
  compArr (2 * a) (covArrPow (covMat D m s₀ t) a)
    (compArr 1 (jhArr D m s₀ t ch ζ c) (covArrPow (covMat D m s₀ t) (l - 1 - a)) 0) 0

/-- The weights of `P_p`. -/
def wPcoef (l : ℕ) : ℝ := (l.factorial : ℝ)⁻¹

/-- The weights of `Q_p`. -/
def wQcoef (l : ℕ) : ℝ := (-1 : ℝ) ^ l / (l.factorial : ℝ)

/-- The arrays of `-∑_{l=1}^p (1/l!) ∑_{a<l} 𝒞^a 𝒥_H 𝒞^{l-1-a} + 𝓕_A P_p`. -/
def wArr (D : OCData) (b : ℝ) (j₀ Dm m : ℕ) (ρ : ℝ) (N p : ℕ) (s₀ : ℝ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (S : Finset ℤ) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (c : Fin 2) : CArr :=
  -(∑ l ∈ Finset.Icc 1 p, (l.factorial : ℝ)⁻¹ •
      ∑ a ∈ Finset.range l, eArr D m s₀ t ch ζ l a c) +
    compArr (N + 1) (dfArr D b j₀ Dm m ρ N Cc0 S t ch ζ c) (polyArr (covMat D m s₀ t) p wPcoef) 0

/-- The arrays of the first source (the pullback of `Q_p` of `wArr`). -/
def fsArr (D : OCData) (b : ℝ) (j₀ Dm m : ℕ) (ρ : ℝ) (N p : ℕ) (s₀ : ℝ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (S : Finset ℤ) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (c : Fin 2) : CArr :=
  chartArr (fun x => (jacMatrix (ch.famMap D t) x)⁻¹) (ch.famMap D t) (ch.famMapInv D t)
    (2 * p + (N + 1 + 2 * p))
    (fun k => compArr (2 * p) (polyArr (covMat D m s₀ t) p wQcoef)
      (wArr D b j₀ Dm m ρ N p s₀ Cc0 S t ch ζ k) 0) c

/-! ### Auxiliary facts -/

theorem arrSlowSmooth_matGradArr {r : ℕ} {M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hM : ∀ a b, ContDiff ℝ (r : WithTop ℕ∞) (fun x => M x a b)) (c : Fin 2) :
    ArrSlowSmooth r (matGradArr M c) := by
  intro m α z
  cases m with
  | zero => exact contDiff_const
  | succ m =>
    cases m with
    | zero => exact hM c (α 0)
    | succ m => exact contDiff_const

/-- A covariance polynomial as an array operator, on `C^{2p}` fields. -/
theorem covPoly_applyArr_nat (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (w : ℕ → ℝ)
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) f) (x z : Vec 2) :
    (∑ l ∈ Finset.range (p + 1), w l • (covOperator Hc)^[l] f) x =
      applyArr (2 * p) (polyArr Hc p w) f x z := by
  unfold polyArr
  rw [applyArr_sum]
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlp : l ≤ p := by simpa [Nat.lt_succ_iff] using hl
  rw [Pi.smul_apply, applyArr_smul, Pi.smul_apply, Pi.smul_apply,
    covOperator_iterate_eq_nat Hc l (hf.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * p))) x z,
    applyArr_eq_of_supp (by omega : 2 * l ≤ 2 * p) (covArrPow_supp Hc l)]

variable {D : OCData} {b : ℝ} {j₀ Dm m : ℕ} {ρ : ℝ} {N p : ℕ} {s₀ : ℝ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

theorem arrSlowSmooth_dmArr {r : ℕ} (S : Finset ℤ) (t : ℝ) (ch : RealChain) (ζ : Vec 2) (n : ℕ)
    (hreg : ∀ k ∈ S, IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ) →
      ocCutoff D.α D.q D.Λ m k t ≠ 0 →
      LiftRegular (diagQ D Dm m k (ch.appendChild D k t ζ) ρ) (Cc0 k (ch.appendChild D k t ζ))
        (0 : Fin 1) ((D.cellScaleSq m)⁻¹ * t) 0 n (r + Dm + 2)) (c : Fin 2) :
    ArrSlowSmooth r (dmArr D b j₀ Dm m ρ Cc0 S t ch ζ n c) := by
  classical
  unfold dmArr
  refine ArrSlowSmooth.sum _ fun k hk => ?_
  split_ifs with hadm
  · by_cases hcut : ocCutoff D.α D.q D.Λ m k t = 0
    · rw [hcut, zero_smul]
      exact ArrSlowSmooth.zero r
    refine ArrSlowSmooth.smul _ ?_
    set B := ch.appendChild D k t ζ
    have hinv : ContDiff ℝ (r : WithTop ℕ∞) (B.famMapInv D t) :=
      (contDiff_famMapInv B t).of_le (by exact_mod_cast le_top)
    have hjac : ∀ c k, ContDiff ℝ (r : WithTop ℕ∞)
        (fun p => jacMatrix (B.famMap D t) (B.famMapInv D t p) c k) := fun c k =>
      (((contDiff_jacMatrix_entry (contDiff_famMap B t) c k).of_le (by exact_mod_cast le_top) :
        ContDiff ℝ (r : WithTop ℕ∞) (fun y => jacMatrix (B.famMap D t) y c k))).comp hinv
    exact arrSlowSmooth_chartArr n hjac hinv (contDiff_famMap B t)
      (fun κ j α => contDiff_pmArr D m ρ _ _ n t κ (hreg k hk hadm hcut) j α) c
  · exact ArrSlowSmooth.zero r

theorem arrSlowSmooth_dfArr {r : ℕ} (hN : 1 ≤ N) (S : Finset ℤ) (t : ℝ) (ch : RealChain)
    (ζ : Vec 2) (hreg : ∀ n, 2 ≤ n → n ≤ N + 1 → ∀ k ∈ S,
      IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ) →
      ocCutoff D.α D.q D.Λ m k t ≠ 0 →
      LiftRegular (diagQ D Dm m k (ch.appendChild D k t ζ) ρ) (Cc0 k (ch.appendChild D k t ζ))
        (0 : Fin 1) ((D.cellScaleSq m)⁻¹ * t) 0 n (r + Dm + 2)) (c : Fin 2) :
    ArrSlowSmooth r (dfArr D b j₀ Dm m ρ N Cc0 S t ch ζ c) := by
  unfold dfArr
  refine ((arrSlowSmooth_dmArr S t ch ζ 2 (hreg 2 le_rfl (by omega)) c).sub
    (arrSlowSmooth_matGradArr (M := fun _ => ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t)
      (fun _ _ => contDiff_const) c)).add
    (ArrSlowSmooth.sum _ fun n hn => ?_)
  have hn' := Finset.mem_Icc.mp hn
  exact arrSlowSmooth_dmArr S t ch ζ n (hreg n (by omega) hn'.2) c
end

/-! **D6c: the first-source identity.** `firstSourceFlux … t ch ζ u y c =
applyArr (2p + (N + 1 + 2p)) (fsArr … c) u y 0` for smooth `u` (`firstSourceFlux_applyArr`). -/

section
/-- `Q_p` of a flux field whose components are array operators of order `K` on `g`. -/
theorem covPolyQ_component (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p K : ℕ) {V : Vec 2 → Vec 2}
    {B : Fin 2 → CArr} {g : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hV : ∀ c, (fun x => V x c) = fun x => applyArr K (B c) g x 0)
    (hB : ∀ c, ArrSlowSmooth (2 * p) (B c)) (hs : ∀ c, ArrSupp K (B c)) (x : Vec 2) (c : Fin 2) :
    covPolyQ Hc p V x c = applyArr (2 * p + K) (compArr (2 * p) (polyArr Hc p wQcoef) (B c) 0) g x 0 := by
  have hg' : ∀ k : ℕ, ContDiff ℝ (k : WithTop ℕ∞) g := fun k => hg.of_le (by exact_mod_cast le_top)
  have hVc : ∀ c, ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) (fun x => applyArr K (B c) g x 0) :=
    fun c => contDiff_applyArr_slow K (2 * p) (hg' _) (hB c) 0
  have hVs : ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) V :=
    contDiff_pi.2 fun c => by rw [hV c]; exact hVc c
  have e := covPoly_applyArr_nat Hc p wQcoef (hVc c) x 0
  rw [Finset.sum_apply] at e
  unfold covPolyQ
  rw [Finset.sum_apply, Finset.sum_apply]
  have hterm : ∀ l ∈ Finset.range (p + 1),
      ((((-1 : ℝ) ^ l / (l.factorial : ℝ))) • (covOperator Hc)^[l] V) x c =
        (wQcoef l • (covOperator Hc)^[l] (fun x => applyArr K (B c) g x 0)) x := by
    intro l hl
    have hlp : l ≤ p := by simpa [Nat.lt_succ_iff] using hl
    rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
      covOperator_iterate_component Hc l (hVs.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * p)))
        x c, hV c]
    rfl
  rw [Finset.sum_congr rfl hterm, e]
  exact opComp_eq (2 * p) K _ (B c) g (hg' _) (hB c) (hs c) x

variable {D : OCData} {b : ℝ} {j₀ Dm m : ℕ} {ρ : ℝ} {N p : ℕ} {s₀ : ℝ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

theorem jh_apply (t : ℝ) (ch : RealChain) (ζ : Vec 2) (h : Vec 2 → ℝ) (y : Vec 2) (c : Fin 2) :
    (-((jhMat D m s₀ t ch ζ y).mulVec (gradField h y))) c =
      applyArr 1 (jhArr D m s₀ t ch ζ c) h y 0 := by
  rw [Pi.neg_apply, matGrad_applyArr _ h y 0 c, jhArr, applyArr_smul, Pi.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- **The first source is an array operator** on smooth test fields. -/
theorem firstSourceFlux_applyArr (hζ : IsFastProfile D.ζ) (hρ : ρ ≠ 0) (hN : 1 ≤ N) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (S : Finset ℤ)
    (hS : ∀ k, k ∈ S ↔ Odd k ∧ IsScheduledIn D (m - 1) k ch.slot)
    (hstrain : ∀ a c, ContDiff ℝ ((4 * p : ℕ) : WithTop ℕ∞) (fun x => strainAt D m t ch ζ x a c))
    (hreg : ∀ n, 2 ≤ n → n ≤ N + 1 → ∀ k ∈ S,
      IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ) →
      ocCutoff D.α D.q D.Λ m k t ≠ 0 →
      LiftRegular (diagQ D Dm m k (ch.appendChild D k t ζ) ρ) (Cc0 k (ch.appendChild D k t ζ))
        (0 : Fin 1) ((D.cellScaleSq m)⁻¹ * t) 0 n (2 * p + Dm + 2))
    {u : Vec 2 → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (y : Vec 2) (c : Fin 2) :
    firstSourceFlux D b j₀ Dm m ρ N p s₀ Cc0 t ch ζ u y c =
      applyArr (2 * p + (N + 1 + 2 * p)) (fsArr D b j₀ Dm m ρ N p s₀ Cc0 S t ch ζ c) u y 0 := by
  set Hc := covMat D m s₀ t with hHc
  have htop : ∀ {f : Vec 2 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f → ∀ k : ℕ,
      ContDiff ℝ (k : WithTop ℕ∞) f := fun hf k => hf.of_le (by exact_mod_cast le_top)
  -- regularity and support of the commutator arrays
  have hjhM : ∀ a c', ContDiff ℝ ((4 * p : ℕ) : WithTop ℕ∞) (fun x => jhMat D m s₀ t ch ζ x a c') := by
    intro a c'
    simp only [jhMat, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact (ContDiff.sum fun j _ => (hstrain a j).mul contDiff_const).add
      (ContDiff.sum fun j _ => contDiff_const.mul (hstrain c' j))
  have hjh : ∀ c' r, r ≤ 4 * p → ArrSlowSmooth r (jhArr D m s₀ t ch ζ c') := fun c' r hr =>
    (arrSlowSmooth_matGradArr (fun a b => (hjhM a b).of_le (by exact_mod_cast hr)) c').smul (-1)
  have hE : ∀ c' bb r, r ≤ 4 * p →
      ArrSlowSmooth r (compArr 1 (jhArr D m s₀ t ch ζ c') (covArrPow Hc bb) 0) := fun c' bb r hr =>
    arrSlowSmooth_compArr 1 (hjh c' r hr) (covArrPow_slowSmooth Hc (r + 1) bb) 0
  have hEs : ∀ c' bb, ArrSupp (1 + 2 * bb)
      (compArr 1 (jhArr D m s₀ t ch ζ c') (covArrPow Hc bb) 0) := fun c' bb =>
    arrSupp_compArr 1 _ 0 (covArrPow_supp Hc bb)
  have heS : ∀ c' l a r, r + 2 * a ≤ 4 * p → ArrSlowSmooth r (eArr D m s₀ t ch ζ l a c') :=
    fun c' l a r hr => arrSlowSmooth_compArr (2 * a) (covArrPow_slowSmooth Hc r a)
      (hE c' (l - 1 - a) (r + 2 * a) hr) 0
  have heSupp : ∀ c' l a, ArrSupp (2 * a + (1 + 2 * (l - 1 - a))) (eArr D m s₀ t ch ζ l a c') :=
    fun c' l a => arrSupp_compArr (2 * a) _ 0 (hEs c' (l - 1 - a))
  -- the terms `𝒞^a 𝒥_H 𝒞^{l-1-a}`
  have hT : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ∀ l ∈ Finset.Icc 1 p, ∀ a ∈ Finset.range l,
      ∀ x c', (covOperator Hc)^[a] (fun x => -((jhMat D m s₀ t ch ζ x).mulVec
          (gradField ((covOperator Hc)^[l - 1 - a] g) x))) x c' =
        applyArr (2 * a + (1 + 2 * (l - 1 - a))) (eArr D m s₀ t ch ζ l a c') g x 0 := by
    intro g hg l hl a ha x c'
    have hlp := Finset.mem_Icc.mp hl
    have hal := Finset.mem_range.mp ha
    have hcov : (covOperator Hc)^[l - 1 - a] g =
        fun X => applyArr (2 * (l - 1 - a)) (covArrPow Hc (l - 1 - a)) g X 0 :=
      funext fun X => covOperator_iterate_eq Hc hg (l - 1 - a) X 0
    have hJ : ∀ c'', (fun y => (-((jhMat D m s₀ t ch ζ y).mulVec
        (gradField ((covOperator Hc)^[l - 1 - a] g) y))) c'') =
        fun y => applyArr (1 + 2 * (l - 1 - a))
          (compArr 1 (jhArr D m s₀ t ch ζ c'') (covArrPow Hc (l - 1 - a)) 0) g y 0 := by
      intro c''
      funext y
      rw [jh_apply, hcov]
      exact opComp_eq 1 (2 * (l - 1 - a)) _ _ g (htop hg _) (covArrPow_slowSmooth Hc 1 _)
        (covArrPow_supp Hc _) y
    have hVcs : ∀ c'', ContDiff ℝ ((2 * a : ℕ) : WithTop ℕ∞) (fun y => applyArr (1 + 2 * (l - 1 - a))
        (compArr 1 (jhArr D m s₀ t ch ζ c'') (covArrPow Hc (l - 1 - a)) 0) g y 0) := fun c'' =>
      contDiff_applyArr_slow _ (2 * a) (htop hg _) (hE c'' _ (2 * a) (by omega)) 0
    have hVs : ContDiff ℝ ((2 * a : ℕ) : WithTop ℕ∞) (fun x => -((jhMat D m s₀ t ch ζ x).mulVec
        (gradField ((covOperator Hc)^[l - 1 - a] g) x))) :=
      contDiff_pi.2 fun c'' => by rw [hJ c'']; exact hVcs c''
    rw [covOperator_iterate_component Hc a hVs x c', hJ c',
      covOperator_iterate_eq_nat Hc a (hVcs c') x 0]
    exact opComp_eq (2 * a) (1 + 2 * (l - 1 - a)) (covArrPow Hc a) _ g (htop hg _)
      (hE c' _ (2 * a) (by omega)) (hEs c' _) x
  -- the diagonal part `𝓕_A P_p`
  have hPg : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ContDiff ℝ (⊤ : ℕ∞) (covPolyP Hc p g) := by
    intro g hg
    have e : covPolyP Hc p g = fun x => ∑ l ∈ Finset.range (p + 1),
        ((l.factorial : ℝ)⁻¹) • (covOperator Hc)^[l] g x := by
      funext x; simp [covPolyP, Finset.sum_apply]
    rw [e]
    exact ContDiff.sum fun l _ => ContDiff.const_smul _
      (contDiff_infty.mpr fun k => contDiff_covOperator_iterate Hc l (htop hg _))
  have hdiag : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ∀ x c',
      diagFluxCtx D b j₀ Dm m ρ N Cc0 t ch ζ (covPolyP Hc p g) x c' =
        applyArr (N + 1 + 2 * p) (compArr (N + 1) (dfArr D b j₀ Dm m ρ N Cc0 S t ch ζ c')
          (polyArr Hc p wPcoef) 0) g x 0 := by
    intro g hg x c'
    have hPeq : covPolyP Hc p g = fun y => applyArr (2 * p) (polyArr Hc p wPcoef) g y 0 :=
      funext fun y => covPoly_applyArr Hc p wPcoef hg y 0
    rw [diagFluxCtx_applyArr hζ hρ N hN t ch ζ S hS
      (fun n h2 hn k hk ha hc => (hreg n h2 hn k hk ha hc).mono le_rfl le_rfl (by omega))
      (hPg g hg) x c', hPeq]
    exact opComp_eq (N + 1) (2 * p) _ _ g (htop hg _) (polyArr_slowSmooth Hc p wPcoef (N + 1))
      (polyArr_supp Hc p wPcoef) x
  -- the combination `wArr`
  have hW : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ∀ c', (fun x => (-(∑ l ∈ Finset.Icc 1 p,
      ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l, (covOperator Hc)^[a]
        (fun x => -((jhMat D m s₀ t ch ζ x).mulVec
          (gradField ((covOperator Hc)^[l - 1 - a] g) x))) x) +
      diagFluxCtx D b j₀ Dm m ρ N Cc0 t ch ζ (covPolyP Hc p g) x) c') =
      fun x => applyArr (N + 1 + 2 * p) (wArr D b j₀ Dm m ρ N p s₀ Cc0 S t ch ζ c') g x 0 := by
    intro g hg c'
    funext x
    unfold wArr
    simp only [applyArr_add, applyArr_neg, applyArr_sum, applyArr_smul, Pi.add_apply,
      Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hdiag g hg x c']
    congr 2
    refine Finset.sum_congr rfl fun l hl => ?_
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    have hlp := Finset.mem_Icc.mp hl
    have hal := Finset.mem_range.mp ha
    rw [hT g hg l hl a ha x c',
      applyArr_eq_of_supp (K' := N + 1 + 2 * p) (by omega) (heSupp c' l a)]
  have hWs : ∀ c', ArrSlowSmooth (2 * p) (wArr D b j₀ Dm m ρ N p s₀ Cc0 S t ch ζ c') := by
    intro c'
    unfold wArr
    refine (ArrSlowSmooth.sum _ fun l hl => (ArrSlowSmooth.sum _ fun a ha => ?_).smul _).neg.add
      (arrSlowSmooth_compArr (N + 1) (arrSlowSmooth_dfArr hN S t ch ζ hreg c')
        (polyArr_slowSmooth Hc p wPcoef _) 0)
    have hlp := Finset.mem_Icc.mp hl
    have hal := Finset.mem_range.mp ha
    exact heS c' l a (2 * p) (by omega)
  have hWsupp : ∀ c', ArrSupp (N + 1 + 2 * p) (wArr D b j₀ Dm m ρ N p s₀ Cc0 S t ch ζ c') := by
    intro c'
    unfold wArr
    refine (ArrSupp.neg (ArrSupp.sum _ fun l hl => ArrSupp.smul _ (ArrSupp.sum _ fun a ha => ?_))).add
      (arrSupp_compArr (N + 1) _ 0 (polyArr_supp Hc p wPcoef))
    have hlp := Finset.mem_Icc.mp hl
    have hal := Finset.mem_range.mp ha
    exact (heSupp c' l a).mono (by omega)
  -- the pullback
  have hg : ContDiff ℝ (⊤ : ℕ∞) (u ∘ ch.famMapInv D t) := hu.comp (contDiff_famMapInv ch t)
  have e3 : firstSourceFlux D b j₀ Dm m ρ N p s₀ Cc0 t ch ζ u y =
      pullFlux (ch.famMap D t) (ch.famMapInv D t) (fun g x k =>
        applyArr (2 * p + (N + 1 + 2 * p)) (compArr (2 * p) (polyArr Hc p wQcoef)
          (wArr D b j₀ Dm m ρ N p s₀ Cc0 S t ch ζ k) 0) g x 0) u y := by
    unfold firstSourceFlux pullFlux
    dsimp only
    congr 1
    funext k
    exact covPolyQ_component Hc p (N + 1 + 2 * p) hg (hW _ hg) hWs hWsupp _ k
  rw [e3, pullFlux_famMap_applyArr hζ ch t _ _ hu y c]
  rfl
end

end AVRegularity.Providers.GenSem
end
