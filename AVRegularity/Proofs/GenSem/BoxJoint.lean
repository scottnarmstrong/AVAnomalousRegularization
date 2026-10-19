-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivative
import AVRegularity.CycleReference.TestDriftIntegrability
public import AVRegularity.Definitions.Construction.Gen.ParShift
public import AVRegularity.Statements.Construction.IsFastProfile
import AVRegularity.Construction.ChainGeometry.Offset
import AVRegularity.CycleReference.ChartDerivativeBounded
import AVenhance.Statements.FlowDefs.FlowIsFlow
public import AVRegularity.Proofs.GenSem.BoxJoint.Main
import AVenhance.Infra.Flow.Laws
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! Ordered derivatives of the monomials of `fluxCoeff`.

`mono y I Y = ∏ j, (Y - y) (I j)` for a word `I : DerivativeWord2 r`. At the center `y`, the ordered
derivative of order `m` vanishes unless `m = r`, and for `m = r` it counts the permutations
`σ` with `α = I ∘ σ`. The proof goes through the closed form at an arbitrary point for the
sub-products `monoS y I S = ∏ j ∈ S, (Y - y) (I j)`. -/

/-- The monomial `Y ↦ ∏ j, (Y - y) (I j)`. -/
def mono (y : Vec 2) {r : ℕ} (I : DerivativeWord2 r) : Vec 2 → ℝ :=
  fun Y => ∏ j : Fin r, (Y - y) (I j)

/-- The sub-product of the monomial over the factors in `S`. -/
def monoS (y : Vec 2) {r : ℕ} (I : DerivativeWord2 r) (S : Finset (Fin r)) : Vec 2 → ℝ :=
  fun Y => ∏ j ∈ S, (Y - y) (I j)

theorem mono_eq_monoS (y : Vec 2) {r : ℕ} (I : DerivativeWord2 r) :
    mono y I = monoS y I Finset.univ := rfl

theorem ite_of_pos' {α : Type*} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_of_neg' {α : Type*} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

theorem contDiff_monoS (y : Vec 2) {r : ℕ} (I : DerivativeWord2 r) (S : Finset (Fin r)) :
    ContDiff ℝ ⊤ (monoS y I S) := by
  unfold monoS
  refine contDiff_prod fun j _ => ?_
  exact ((contDiff_apply ℝ ℝ (I j)).comp (contDiff_id.sub contDiff_const))

theorem contDiff_mono (y : Vec 2) {r : ℕ} (I : DerivativeWord2 r) :
    ContDiff ℝ ⊤ (mono y I) :=
  contDiff_monoS y I Finset.univ

theorem orderedDerivative_zero_word {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Vec 2 → E) : orderedDerivative (Fin.elim0 : DerivativeWord2 0) g = g := by
  simp [orderedDerivative]

theorem orderedDerivative_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (α : DerivativeWord2 (m + 1)) (g : Vec 2 → E) :
    orderedDerivative α g =
      orderedDerivative (fun i : Fin m => α i.succ) (fun x => fderiv ℝ g x (basisVec (α 0))) := by
  simp [orderedDerivative, List.ofFn_succ]

theorem contDiff_dirDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Vec 2 → E}
    (hg : ContDiff ℝ ⊤ g) (i : Fin 2) :
    ContDiff ℝ ⊤ (fun x => fderiv ℝ g x (basisVec i)) := by
  have h := hg.fderiv_right (m := ⊤) (by simp)
  exact h.clm_apply contDiff_const

/-- Ordered derivatives commute with finite sums of smooth functions. -/
theorem orderedDerivative_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) {m : ℕ} :
    ∀ (α : DerivativeWord2 m) (f : ι → Vec 2 → E), (∀ k, ContDiff ℝ ⊤ (f k)) →
      orderedDerivative α (fun x => ∑ k ∈ s, f k x) =
        fun x => ∑ k ∈ s, orderedDerivative α (f k) x := by
  induction m with
  | zero =>
    intro α f _
    have : α = Fin.elim0 := Subsingleton.elim _ _
    subst this
    simp [orderedDerivative_zero_word]
  | succ m ih =>
    intro α f hf
    have hd : ∀ k, Differentiable ℝ (f k) := fun k => (hf k).differentiable (by simp)
    have h1 : (fun x => fderiv ℝ (fun x => ∑ k ∈ s, f k x) x (basisVec (α 0))) =
        fun x => ∑ k ∈ s, fderiv ℝ (f k) x (basisVec (α 0)) := by
      funext x
      rw [fderiv_fun_sum (fun k _ => (hd k) x)]
      simp
    rw [orderedDerivative_succ, h1, ih (fun i => α i.succ)
      (fun k x => fderiv ℝ (f k) x (basisVec (α 0)))
      (fun k => contDiff_dirDeriv (hf k) _)]
    funext x
    simp only [orderedDerivative_succ]

theorem fderiv_monoS (y : Vec 2) {r : ℕ} (I : DerivativeWord2 r) (S : Finset (Fin r))
    (x : Vec 2) (i : Fin 2) :
    fderiv ℝ (monoS y I S) x (basisVec i) =
      ∑ k ∈ S.filter (fun k => I k = i), monoS y I (S.erase k) x := by
  classical
  have hj : ∀ j ∈ S, HasFDerivAt (fun x : Vec 2 => (x - y) (I j))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (I j)) x := by
    intro j _
    have h := hasFDerivAt_apply (𝕜 := ℝ) (I j) (x - y)
    simpa [Function.comp_def] using h.comp x ((hasFDerivAt_id x).sub_const y)
  have h := HasFDerivAt.finsetProd hj
  have h' : HasFDerivAt (monoS y I S) _ x := h
  rw [h'.fderiv]
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, basisVec_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

open Classical in
/-- Closed form at an arbitrary point: a sum over injective matchings of the letters of `α` with
factors in `S`, each leaving the product over the unmatched factors. -/
theorem orderedDerivative_monoS_apply (y : Vec 2) {r : ℕ} (I : DerivativeWord2 r) :
    ∀ {m : ℕ} (α : DerivativeWord2 m) (S : Finset (Fin r)) (x : Vec 2),
      orderedDerivative α (monoS y I S) x =
        ∑ φ : Fin m → Fin r,
          if (Function.Injective φ ∧ (∀ t, φ t ∈ S) ∧ ∀ t, I (φ t) = α t) then
            ∏ j ∈ S \ Finset.univ.image φ, (x - y) (I j) else 0 := by
  intro m
  induction m with
  | zero =>
    intro α S x
    have : α = Fin.elim0 := Subsingleton.elim _ _
    subst this
    simp [orderedDerivative_zero_word, monoS, Function.injective_of_subsingleton]
  | succ m ih =>
    intro α S x
    rw [orderedDerivative_succ]
    have h1 : (fun x => fderiv ℝ (monoS y I S) x (basisVec (α 0))) =
        fun x => ∑ k ∈ S.filter (fun k => I k = α 0), monoS y I (S.erase k) x :=
      funext fun x => fderiv_monoS y I S x _
    rw [h1, orderedDerivative_sum _ _ _ (fun k => contDiff_monoS y I _)]
    simp_rw [ih]
    have hf : S.filter (fun k => I k = α 0) =
        Finset.univ.filter (fun k => k ∈ S ∧ I k = α 0) := by
      ext k; simp
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin r)).sum_comp, Fintype.sum_prod_type, hf,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∈ S ∧ I k = α 0
    · rw [ite_of_pos' hk]
      refine Finset.sum_congr rfl fun ψ _ => ?_
      have hc : (Function.Injective (Fin.cons k ψ : Fin (m + 1) → Fin r) ∧
          (∀ t, (Fin.cons k ψ : Fin (m + 1) → Fin r) t ∈ S) ∧
          ∀ t, I ((Fin.cons k ψ : Fin (m + 1) → Fin r) t) = α t) ↔
          (Function.Injective ψ ∧ (∀ t, ψ t ∈ S.erase k) ∧ ∀ t, I (ψ t) = α t.succ) := by
        simp only [Fin.cons_injective_iff, Fin.forall_fin_succ,
          Fin.cons_zero, Fin.cons_succ, Finset.mem_erase, Set.mem_range]
        constructor
        · rintro ⟨⟨h1, h2⟩, ⟨_, h3⟩, _, h5⟩
          exact ⟨h2, fun t => ⟨fun e => h1 ⟨t, e⟩, h3 t⟩, h5⟩
        · rintro ⟨h2, h3, h5⟩
          exact ⟨⟨fun ⟨t, e⟩ => (h3 t).1 e, h2⟩, ⟨hk.1, fun t => (h3 t).2⟩, hk.2, h5⟩
      have e : (Fin.consEquiv (fun _ : Fin (m + 1) => Fin r)) (k, ψ) = Fin.cons k ψ := rfl
      rw [e]
      by_cases hψ : (Function.Injective ψ ∧ (∀ t, ψ t ∈ S.erase k) ∧ ∀ t, I (ψ t) = α t.succ)
      · rw [ite_of_pos' hψ, ite_of_pos' (hc.2 hψ)]
        congr 1
        ext j
        simp [Fin.exists_fin_succ, Finset.mem_erase]
        tauto
      · have hn := fun h => hψ (hc.1 h)
        rw [ite_of_neg' hψ]
        exact (ite_of_neg' hn).symm
    · rw [ite_of_neg' hk]
      refine (Finset.sum_eq_zero fun ψ _ => ?_).symm
      have hn : ¬ (Function.Injective (Fin.cons k ψ : Fin (m + 1) → Fin r) ∧
          (∀ t, (Fin.cons k ψ : Fin (m + 1) → Fin r) t ∈ S) ∧
          ∀ t, I ((Fin.cons k ψ : Fin (m + 1) → Fin r) t) = α t) := by
        rintro ⟨_, h2, h3⟩
        exact hk ⟨by simpa using h2 0, by simpa using h3 0⟩
      exact ite_of_neg' hn

open Classical in
/-- At the center: the ordered derivative of `mono y I` counts the bijective matchings. -/
theorem orderedDerivative_mono_center (y : Vec 2) {r m : ℕ} (I : DerivativeWord2 r)
    (α : DerivativeWord2 m) :
    orderedDerivative α (mono y I) y =
      ∑ φ : Fin m → Fin r,
        if (Function.Injective φ ∧ Function.Surjective φ ∧ ∀ t, I (φ t) = α t) then 1 else 0 := by
  rw [mono_eq_monoS, orderedDerivative_monoS_apply]
  refine Finset.sum_congr rfl fun φ _ => ?_
  by_cases hc : Function.Injective φ ∧ (∀ t, φ t ∈ (Finset.univ : Finset (Fin r))) ∧
      ∀ t, I (φ t) = α t
  · have hiff : (Function.Injective φ ∧ Function.Surjective φ ∧ ∀ t, I (φ t) = α t) ↔
        (Finset.univ \ Finset.univ.image φ = ∅) ∧ Function.Injective φ ∧ ∀ t, I (φ t) = α t := by
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨?_, h1, h3⟩
        ext j
        obtain ⟨t, rfl⟩ := h2 j
        simp
      · rintro ⟨h0, h1, h3⟩
        refine ⟨h1, fun j => ?_, h3⟩
        by_contra hj
        have : j ∈ Finset.univ \ Finset.univ.image φ := by simp; exact fun t => fun e => hj ⟨t, e⟩
        simp [h0] at this
    rw [ite_of_pos' hc]
    by_cases hs : Finset.univ \ Finset.univ.image φ = ∅
    · rw [ite_of_pos' (hiff.2 ⟨hs, hc.1, hc.2.2⟩), hs, Finset.prod_empty]
    · rw [ite_of_neg' (fun h => hs (hiff.1 h).1)]
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      exact Finset.prod_eq_zero hj (by simp)
  · rw [ite_of_neg' hc, ite_of_neg']
    rintro ⟨h1, h2, h3⟩
    exact hc ⟨h1, fun t => Finset.mem_univ _, h3⟩

open Classical in
/-- Order `r` at the center of a monomial of degree `r`: the number of permutations `σ` with
`α = I ∘ σ`. -/
theorem orderedDerivative_mono_self (y : Vec 2) {r : ℕ} (I : DerivativeWord2 r)
    (α : DerivativeWord2 r) :
    orderedDerivative α (mono y I) y =
      ∑ σ : Equiv.Perm (Fin r), if (∀ j, α j = I (σ j)) then 1 else 0 := by
  rw [orderedDerivative_mono_center]
  set F : (Fin r → Fin r) → ℝ := fun φ =>
    if (Function.Injective φ ∧ Function.Surjective φ ∧ ∀ t, I (φ t) = α t) then 1 else 0 with hF
  have hcoe : Function.Injective (fun σ : Equiv.Perm (Fin r) => (σ : Fin r → Fin r)) :=
    fun a b h => Equiv.ext (congrFun h)
  have h1 : ∑ σ : Equiv.Perm (Fin r), (if (∀ j, α j = I (σ j)) then (1 : ℝ) else 0) =
      ∑ φ ∈ Finset.univ.image (fun σ : Equiv.Perm (Fin r) => (σ : Fin r → Fin r)), F φ := by
    rw [Finset.sum_image (fun a _ b _ h => hcoe h)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hF]
    refine if_congr ?_ rfl rfl
    constructor
    · intro h; exact ⟨σ.injective, σ.surjective, fun t => (h t).symm⟩
    · rintro ⟨_, _, h⟩ j; exact (h j).symm
  rw [h1]
  refine (Finset.sum_subset (Finset.subset_univ _) fun φ _ hφ => ?_).symm
  refine ite_of_neg' ?_
  rintro ⟨h1, h2, _⟩
  exact hφ (Finset.mem_image.mpr ⟨Equiv.ofBijective φ ⟨h1, h2⟩, Finset.mem_univ _, rfl⟩)

/-- Orders `m ≠ r` vanish at the center. -/
theorem orderedDerivative_mono_of_ne (y : Vec 2) {r m : ℕ} (I : DerivativeWord2 r)
    (α : DerivativeWord2 m) (h : m ≠ r) : orderedDerivative α (mono y I) y = 0 := by
  classical
  rw [orderedDerivative_mono_center]
  refine Finset.sum_eq_zero fun φ _ => ?_
  rw [ite_of_neg']
  rintro ⟨h1, h2, _⟩
  have := Fintype.card_of_bijective ⟨h1, h2⟩
  simp at this
  exact h this

/-- The combination over words of order `r` of the ordered derivatives of the monomial at the
center: a sum over the permutations of `r` letters. -/
theorem sum_orderedDerivative_mono {E : Type*} [AddCommGroup E] [Module ℝ E] (y : Vec 2) {r : ℕ}
    (I : DerivativeWord2 r) (c : DerivativeWord2 r → E) :
    ∑ α : DerivativeWord2 r, orderedDerivative α (mono y I) y • c α =
      ∑ σ : Equiv.Perm (Fin r), c (I ∘ σ) := by
  classical
  have : ∀ α : DerivativeWord2 r, orderedDerivative α (mono y I) y • c α =
      ∑ σ : Equiv.Perm (Fin r), if α = I ∘ σ then c α else 0 := by
    intro α
    rw [orderedDerivative_mono_self, Finset.sum_smul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hh : (∀ j, α j = I (σ j)) ↔ α = I ∘ σ := ⟨fun h => funext h, fun h j => congrFun h j⟩
    simp only [hh]
    split_ifs <;> simp
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp

/-- The symmetrized form used by `fluxCoeff`. -/
theorem smul_sum_orderedDerivative_mono {E : Type*} [AddCommGroup E] [Module ℝ E] (y : Vec 2)
    {r : ℕ} (I : DerivativeWord2 r) (c : DerivativeWord2 r → E) :
    ((r.factorial : ℝ)⁻¹) • ∑ α : DerivativeWord2 r, orderedDerivative α (mono y I) y • c α =
      ((r.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin r), c (I ∘ σ) := by
  rw [sum_orderedDerivative_mono]

/-- Combinations of ordered derivatives of order `m ≠ r` vanish on the monomial at the center. -/
theorem sum_orderedDerivative_mono_of_ne {E : Type*} [AddCommGroup E] [Module ℝ E] (y : Vec 2)
    {r m : ℕ} (I : DerivativeWord2 r) (c : DerivativeWord2 m → E) (h : m ≠ r) :
    ∑ α : DerivativeWord2 m, orderedDerivative α (mono y I) y • c α = 0 :=
  Finset.sum_eq_zero fun α _ => by rw [orderedDerivative_mono_of_ne y I α h, zero_smul]

end AVRegularity.Providers.GenSem
end

section
namespace AVRegularity.Providers.GenSem

/-! **The anchor of the covariance primitive** (at any menu). The primitive
`∫_{s₀}^t (𝖩_m - B I)` at the anchor `s₀` is the scheduled primitive at the anchor `0` minus its
value at `s₀`, a time constant (`ocCovariance_anchor`). This lets the time letters of the cascade
(anchor `0`) represent the covariance at the terminal anchor `t_p`.
`kap_pos_of_cellScaleSq_pos` reads the positivity of the diffusivity off the cell time scale. -/

/-- **The covariance primitive at any anchor** is the primitive at the anchor `0` minus a time
constant. -/
theorem ocCovariance_anchor (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (m : ℕ)
    {ν : ℝ} (hν : 0 < ν) (B s₀ t : ℝ) (i j : Fin 2) :
    ocCovariance D.α D.q D.Λ D.ζ m ν B s₀ t i j =
      ocCovariance D.α D.q D.Λ D.ζ m ν B 0 t i j -
        ocCovariance D.α D.q D.Λ D.ζ m ν B 0 s₀ i j := by
  have hint : ∀ a c : ℝ, IntervalIntegrable
      (fun r => ocRefFlux D.α D.q D.Λ D.ζ m ν r i j - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
      MeasureTheory.volume a c :=
    fun a c => (CycleReference.refFlux_entry_intervalIntegrable hΛ hζ hν i j a c).sub
      intervalIntegrable_const
  simp only [ocCovariance, Matrix.of_apply]
  exact (intervalIntegral.integral_interval_sub_left (hint 0 t) (hint 0 s₀)).symm

/-- A positive cell time scale has a positive diffusivity. -/
theorem kap_pos_of_cellScaleSq_pos (D : OCData) {m : ℕ} (hc : 0 < D.cellScaleSq m) :
    0 < D.kap m := by
  by_contra h
  have h' : D.cellScaleSq m ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (not_lt.mp h)
  exact absurd hc (not_lt.mpr h')

end AVRegularity.Providers.GenSem
end
end
end

section
section
/-! Facade for the algebra of scalar coefficient arrays for applied fields. -/
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.ChainGeometry
namespace AVRegularity.Providers.GenSem

/-! Recentering identities of real chains.

Every family geometry `(𝔛, x_𝒜, s)` of a chain is a flow in the sense of `IsFlowGeom`
(`𝔛(u, 𝔛(w,x,r), w) = 𝔛(u,x,r)` and `𝔛(r,x,r) = x`); this needs the fast profile `ζ` to be a
fast profile so that the pulses are continuous and the displacement is additive in time.
Recentering by `h` leaves the flow component and the anchor of the last family unchanged and moves
its center point by `h`; it composes additively and is trivial at `h = 0`. -/

/-- The flow property of a family geometry. -/
def IsFlowGeom (g : ChainGeom) : Prop :=
  (∀ u w r x, g.1 u (g.1 w x r) w = g.1 u x r) ∧ ∀ r x, g.1 r x r = x

theorem isFlowGeom_base (D : OCData) (k : ℕ) (x : Vec 2) (s : ℝ) :
    IsFlowGeom (D.flowOf k, x, s) := by
  have hL := (D.hΦ k).vel_lipschitz
  have hX := AVenhance.flow_isFlow _ (D.hΦ k).vel_continuous hL
  refine ⟨fun u w r y => ?_, fun r y => ?_⟩
  · exact AVenhance.Infra.Flow.flow_group_law _ hL hX y r w u
  · exact hX.1 y r

/-- The inverse law of a flow geometry. -/
theorem IsFlowGeom.inv {g : ChainGeom} (hg : IsFlowGeom g) (a b : ℝ) (w : Vec 2) :
    g.1 a (g.1 b w a) b = w := by
  rw [hg.1 a b a w, hg.2]

/-- The relative displacement is additive in time. -/
theorem relDisp_add (D : OCData) (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (u w r : ℝ)
    (θ : Vec 2) :
    D.relDisp k pk u w θ + D.relDisp k pk w r θ = D.relDisp k pk u r θ := by
  have hc : Continuous (ocPulse D.α D.q D.Λ D.ζ k pk) := CycleReference.ocPulse_continuous hζ pk
  unfold OCData.relDisp
  rw [← smul_add, ← add_smul, add_comm,
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]

theorem relDisp_self (D : OCData) (k : ℕ) (pk : ℤ) (r : ℝ) (θ : Vec 2) :
    D.relDisp k pk r r θ = 0 := by
  simp [OCData.relDisp]

/-- Moving `θ` by a displacement does not change the displacement. -/
theorem relDisp_add_relDisp (D : OCData) (k : ℕ) (pk : ℤ) (u w r : ℝ) (θ : Vec 2) :
    D.relDisp k pk u w (θ + D.relDisp k pk w r θ) = D.relDisp k pk u w θ := by
  unfold OCData.relDisp
  by_cases he : D.eps k = 0
  · simp [he]
  · rw [smul_add, smul_inv_smul₀ he, ocShearVel_add_smul_self]

theorem isFlowGeom_childGeom (D : OCData) (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (s' : ℝ)
    (c : ChainChild) {g : ChainGeom} (hg : IsFlowGeom g) :
    IsFlowGeom (D.childGeom k pk s' c g) := by
  have h0 : D.eps k = 0 → ∀ u r θ, D.relDisp k pk u r θ = 0 := by
    intro he u r θ; simp [OCData.relDisp, he]
  refine ⟨fun u w r x => ?_, fun r x => ?_⟩
  · simp only [OCData.childGeom]
    set γ := c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)
    set Y := g.1 g.2.2 x r
    set θ := (D.eps k)⁻¹ • Y + γ
    have hz : g.1 g.2.2 (g.1 w (Y + D.eps k • D.relDisp k pk w r θ) g.2.2) w =
        Y + D.eps k • D.relDisp k pk w r θ := hg.inv _ _ _
    rw [hz]
    by_cases he : D.eps k = 0
    · simp only [h0 he, smul_zero, add_zero]
    · have harg : (D.eps k)⁻¹ • (Y + D.eps k • D.relDisp k pk w r θ) + γ =
          θ + D.relDisp k pk w r θ := by
        rw [smul_add, inv_smul_smul₀ he]
        simp only [θ]; abel
      rw [harg, relDisp_add_relDisp, add_assoc, ← smul_add, add_comm (D.relDisp k pk w r θ),
        relDisp_add D hζ]
  · simp only [OCData.childGeom]
    rw [relDisp_self, smul_zero, add_zero, hg.1 r g.2.2 r x, hg.2]

theorem isFlowGeom_geomAux (D : OCData) (hζ : IsFastProfile D.ζ) :
    ∀ (cs : List ChainChild) (k : ℕ) (sl : List ℤ) {g : ChainGeom},
      IsFlowGeom g → IsFlowGeom (D.geomAux k sl cs g)
  | [], k, sl, g, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | _ :: _ :: _ => exact hg
  | c :: cs, k, sl, g, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | pk :: pk1 :: rest =>
      exact isFlowGeom_geomAux D hζ cs (k + 1) (pk1 :: rest) (isFlowGeom_childGeom D hζ k pk _ c hg)

/-- Every family geometry of a real chain is a flow. -/
theorem isFlowGeom_geom (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) :
    IsFlowGeom (ch.geom D) :=
  isFlowGeom_geomAux D hζ _ _ _ (isFlowGeom_base D _ _ _)

theorem geomAux_nil (D : OCData) (k : ℕ) (sl : List ℤ) (g : ChainGeom) :
    D.geomAux k sl [] g = g := by
  match sl with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- The recentering displacement `R(h) = 𝔛(s, x' + h, s') - x_𝒜 - c` of a child with center `cen`
of a parent with geometry `g` and anchor `s'`, where `x' = 𝔛(s', x_𝒜 + cen, s)`. -/
def shiftOf (g : ChainGeom) (s' : ℝ) (cen h : Vec 2) : Vec 2 :=
  g.1 g.2.2 (g.1 s' (g.2.1 + cen) g.2.2 + h) s' - g.2.1 - cen

/-- The recentering displacement `R(h)` of the last child `c` of `ch`. -/
def recenterShift (D : OCData) (ch : RealChain) (c : ChainChild) (h : Vec 2) : Vec 2 :=
  shiftOf ((ch.dropLastChild).geom D) (D.slotAnchor (ch.lastLevel + 1) ch.slot) c.center h

theorem recenter_snoc (D : OCData) (ch : RealChain) (cs : List ChainChild) (c : ChainChild)
    (hc : ch.children = cs ++ [c]) (h : Vec 2) :
    ch.recenter D h = { ch with children := cs ++
      [⟨c.center + recenterShift D ch c h, c.phase + (D.eps ch.lastLevel)⁻¹ •
        recenterShift D ch c h⟩] } := by
  simp only [RealChain.recenter, recenterShift, shiftOf, hc, List.getLast?_concat, List.dropLast_concat]

theorem recenter_nil (D : OCData) (ch : RealChain) (hc : ch.children = []) (h : Vec 2) :
    ch.recenter D h = { ch with base := ch.base + h } := by
  simp [RealChain.recenter, hc]

/-- The child step of recentering, on geometries: the flow and the anchor are unchanged and the
center point moves by `h`. -/
theorem childGeom_recenter (D : OCData) (k : ℕ) (pk : ℤ) (s' : ℝ) (c : ChainChild)
    {g : ChainGeom} (hg : IsFlowGeom g) (h : Vec 2) :
    D.childGeom k pk s' ⟨c.center + (g.1 g.2.2 (g.1 s' (g.2.1 + c.center) g.2.2 + h) s' -
        g.2.1 - c.center), c.phase + (D.eps k)⁻¹ • (g.1 g.2.2
          (g.1 s' (g.2.1 + c.center) g.2.2 + h) s' - g.2.1 - c.center)⟩ g =
      ((D.childGeom k pk s' c g).1, (D.childGeom k pk s' c g).2.1 + h, s') := by
  have hγ : ∀ R : Vec 2, c.phase + (D.eps k)⁻¹ • R - (D.eps k)⁻¹ • (g.2.1 + (c.center + R)) =
      c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center) := by
    intro R; simp only [smul_add]; abel
  refine Prod.ext (funext fun u => funext fun x => funext fun r => ?_) (Prod.ext ?_ rfl)
  · simp only [OCData.childGeom]
    rw [hγ]
  · simp only [OCData.childGeom]
    have : g.2.1 + (c.center + (g.1 g.2.2 (g.1 s' (g.2.1 + c.center) g.2.2 + h) s' - g.2.1 -
        c.center)) = g.1 g.2.2 (g.1 s' (g.2.1 + c.center) g.2.2 + h) s' := by abel
    rw [this, hg.inv]

/-- The slots of a chain are the slots `𝗉_{j'}, …, 𝗉_i`: one more than the children. -/
def _root_.AVRegularity.RealChain.WellSlotted (ch : RealChain) : Prop := ch.slots.length = ch.children.length + 1

theorem geom_snoc (D : OCData) (ch : RealChain) (cs : List ChainChild) (c : ChainChild)
    (hc : ch.children = cs ++ [c]) (hl : ch.WellSlotted) :
    ch.geom D = D.childGeom ch.lastLevel (ch.slots.dropLast.getLastD 0)
      (D.slotAnchor (ch.lastLevel + 1) ch.slot) c ((ch.dropLastChild).geom D) := by
  have hl' : ch.slots.length = cs.length + 2 := by
    have := hl; simp only [RealChain.WellSlotted, hc, List.length_append, List.length_singleton]
      at this; omega
  obtain ⟨sl, p, hs⟩ : ∃ sl p, ch.slots = sl ++ [p] := by
    rcases List.eq_nil_or_concat ch.slots with h | ⟨L, b, h⟩
    · simp [h] at hl'
    · exact ⟨L, b, by simpa using h⟩
  have hsl : sl.length = cs.length + 1 := by
    have := hl'; rw [hs] at this; simp at this; omega
  have hhead : (sl ++ [p]).headD 0 = sl.headD 0 := by
    cases sl with
    | nil => simp at hsl
    | cons a t => rfl
  have hdl : (ch.dropLastChild).geom D = D.geomAux (ch.baseLevel + 1) sl cs
      (D.flowOf ch.baseLevel, ch.base, D.slotAnchor (ch.baseLevel + 1) (sl.headD 0)) := by
    simp only [RealChain.geom, RealChain.dropLastChild, hs, hc, List.dropLast_concat]
  have hll : ch.lastLevel = ch.baseLevel + 1 + cs.length := by
    simp only [RealChain.lastLevel, hc]; simp; omega
  rw [hdl]
  simp only [RealChain.geom, hs, hc, hhead]
  rw [geomAux_append D p c cs _ sl _ hsl]
  have hslot : ch.slot = p := by simp [RealChain.slot, hs]
  simp only [hll, hslot, List.dropLast_concat]

theorem geom_recenter (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain)
    (hl : ch.WellSlotted) (h : Vec 2) :
    (ch.recenter D h).geom D = ((ch.geom D).1, (ch.geom D).2.1 + h, (ch.geom D).2.2) := by
  rcases List.eq_nil_or_concat ch.children with hc | ⟨cs, c, hc⟩
  · rw [recenter_nil D ch hc]
    simp only [RealChain.geom, hc, geomAux_nil]
  · rw [List.concat_eq_append] at hc
    rw [recenter_snoc D ch cs c hc]
    have hl2 : ({ ch with children := cs ++
      [⟨c.center + recenterShift D ch c h, c.phase + (D.eps ch.lastLevel)⁻¹ •
        recenterShift D ch c h⟩] } : RealChain).WellSlotted := by
      simpa [RealChain.WellSlotted, hc] using hl
    rw [geom_snoc D _ cs _ rfl hl2, geom_snoc D ch cs c hc hl]
    have hd : ({ ch with children := cs ++
      [⟨c.center + recenterShift D ch c h, c.phase + (D.eps ch.lastLevel)⁻¹ •
        recenterShift D ch c h⟩] } : RealChain).dropLastChild = ch.dropLastChild := by
      simp [RealChain.dropLastChild, hc]
    have hll : ({ ch with children := cs ++
      [⟨c.center + recenterShift D ch c h, c.phase + (D.eps ch.lastLevel)⁻¹ •
        recenterShift D ch c h⟩] } : RealChain).lastLevel = ch.lastLevel := by
      simp [RealChain.lastLevel, hc]
    have hsl : ({ ch with children := cs ++
      [⟨c.center + recenterShift D ch c h, c.phase + (D.eps ch.lastLevel)⁻¹ •
        recenterShift D ch c h⟩] } : RealChain).slot = ch.slot := rfl
    rw [hd, hll, hsl]
    exact childGeom_recenter D _ _ _ c (isFlowGeom_geom D hζ _) h

theorem shiftOf_zero {g : ChainGeom} (hg : IsFlowGeom g) (s' : ℝ) (cen : Vec 2) :
    shiftOf g s' cen 0 = 0 := by
  simp only [shiftOf, add_zero, hg.inv]; abel

theorem shiftOf_comp {g : ChainGeom} (hg : IsFlowGeom g) (s' : ℝ) (cen h h' : Vec 2) :
    shiftOf g s' (cen + shiftOf g s' cen h) h' = shiftOf g s' cen (h + h') - shiftOf g s' cen h := by
  have e : g.1 s' (g.2.1 + (cen + shiftOf g s' cen h)) g.2.2 = g.1 s' (g.2.1 + cen) g.2.2 + h := by
    have : g.2.1 + (cen + shiftOf g s' cen h) = g.1 g.2.2 (g.1 s' (g.2.1 + cen) g.2.2 + h) s' := by
      simp only [shiftOf]; abel
    rw [this, hg.inv]
  simp only [shiftOf] at e ⊢
  rw [e, add_assoc]
  abel

/-- `ch.recenter D 0 = ch`. -/
theorem recenter_zero (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) :
    ch.recenter D 0 = ch := by
  rcases List.eq_nil_or_concat ch.children with hc | ⟨cs, c, hc⟩
  · rw [recenter_nil D ch hc]; simp
  · rw [List.concat_eq_append] at hc
    rw [recenter_snoc D ch cs c hc]
    have h0 : recenterShift D ch c 0 = 0 := shiftOf_zero (isFlowGeom_geom D hζ _) _ _
    rw [h0]
    simp [← hc]

/-- Recentering composes additively (a literal equality of chains). -/
theorem recenter_recenter (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) (h h' : Vec 2) :
    (ch.recenter D h).recenter D h' = ch.recenter D (h + h') := by
  rcases List.eq_nil_or_concat ch.children with hc | ⟨cs, c, hc⟩
  · rw [recenter_nil D ch hc, recenter_nil D _ (by simpa using hc), recenter_nil D ch hc]
    simp [add_assoc]
  · rw [List.concat_eq_append] at hc
    rw [recenter_snoc D ch cs c hc h, recenter_snoc D ch cs c hc (h + h')]
    set c' : ChainChild := ⟨c.center + recenterShift D ch c h, c.phase + (D.eps ch.lastLevel)⁻¹ •
        recenterShift D ch c h⟩ with hc'
    have hd : ({ ch with children := cs ++ [c'] } : RealChain).dropLastChild = ch.dropLastChild := by
      simp [RealChain.dropLastChild, hc]
    have hll : ({ ch with children := cs ++ [c'] } : RealChain).lastLevel = ch.lastLevel := by
      simp [RealChain.lastLevel, hc]
    rw [recenter_snoc D _ cs c' rfl h']
    have hsh : recenterShift D { ch with children := cs ++ [c'] } c' h' =
        recenterShift D ch c (h + h') - recenterShift D ch c h := by
      simp only [recenterShift, hd, hll]
      exact shiftOf_comp (isFlowGeom_geom D hζ _) _ _ _ _
    rw [hsh, hll]
    simp only [hc', RealChain.mk.injEq, true_and, List.append_cancel_left_eq,
      List.cons.injEq, ChainChild.mk.injEq, and_true]
    generalize recenterShift D ch c h = Rh
    generalize recenterShift D ch c (h + h') = Rhh
    constructor
    · abel
    · rw [smul_sub]; abel

theorem famJac_recenter (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain)
    (hl : ch.WellSlotted) (h : Vec 2) (u : ℝ) :
    (ch.recenter D h).famJac D u =
      jacMatrix (fun y => (ch.geom D).1 u y (ch.geom D).2.2) ((ch.geom D).2.1 + h) := by
  simp only [RealChain.famJac, geom_recenter D hζ ch hl h]

theorem famStrain_recenter (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain)
    (hl : ch.WellSlotted) (h : Vec 2) (u : ℝ) :
    (ch.recenter D h).famStrain D u =
      Matrix.of (fun a b => deriv (fun u' => jacMatrix
        (fun y => (ch.geom D).1 u' y (ch.geom D).2.2) ((ch.geom D).2.1 + h) a b) u) *
      (jacMatrix (fun y => (ch.geom D).1 u y (ch.geom D).2.2) ((ch.geom D).2.1 + h))⁻¹ := by
  simp only [RealChain.famStrain, famJac_recenter D hζ ch hl h]

theorem famMap_recenter (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain)
    (hl : ch.WellSlotted) (h : Vec 2) (u : ℝ) (v : Vec 2) :
    (ch.recenter D h).famMap D u v =
      (ch.geom D).1 u ((ch.geom D).2.1 + h + v) (ch.geom D).2.2 -
        (ch.geom D).1 u ((ch.geom D).2.1 + h) (ch.geom D).2.2 := by
  simp only [RealChain.famMap, geom_recenter D hζ ch hl h]

theorem famMapInv_recenter (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain)
    (hl : ch.WellSlotted) (h : Vec 2) (u : ℝ) (w : Vec 2) :
    (ch.recenter D h).famMapInv D u w =
      (ch.geom D).1 (ch.geom D).2.2 ((ch.geom D).1 u ((ch.geom D).2.1 + h) (ch.geom D).2.2 + w) u -
        ((ch.geom D).2.1 + h) := by
  simp only [RealChain.famMapInv, geom_recenter D hζ ch hl h]

/-- The recentered chain has the same levels and slots. -/
theorem recenter_baseLevel (D : OCData) (ch : RealChain) (h : Vec 2) :
    (ch.recenter D h).baseLevel = ch.baseLevel ∧ (ch.recenter D h).slots = ch.slots := by
  rcases List.eq_nil_or_concat ch.children with hc | ⟨cs, c, hc⟩
  · rw [recenter_nil D ch hc]; exact ⟨rfl, rfl⟩
  · rw [List.concat_eq_append] at hc
    rw [recenter_snoc D ch cs c hc]; exact ⟨rfl, rfl⟩

end AVRegularity.Providers.GenSem
end
end

section
/-! Facade: box regularity implies joint regularity (`IsBoxSmoothOn.contDiffOn_uncurry`). -/
end
end
