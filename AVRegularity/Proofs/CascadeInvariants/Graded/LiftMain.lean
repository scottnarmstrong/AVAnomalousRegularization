-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.CascadeInvariants.Graded.Fam
public import AVRegularity.Proofs.GenSem.LiftGen.Main

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.GenSem.UEnv

/-! **Ledger: the graded cell operators and source.** The quantitative form of the
representations of the cell operators in the module `GenSem.LiftGen.Drift`
(`URepArr.cellB1Arr`):
* `ℬ₁` raises the degree by one and `ℬ₂` by two, with sizes `cellB1C`, `cellB2C` built from the
  metric and normalized-drift letters and the slow cost (the drift enters only as `√η · 𝐛`, the
  drift letter: no Péclet number);
* graded arrays `URepGP` (grade `p` has degree `n + p`: each power of `η_cell` carries exactly one
  slow derivative); the graded derivative `dG` costs `dGK = 2π + |s|(S + 1)` and one fast weight;
* the edge flux `fluxG` and the source `sourceG` of an operator whose edge aggregates have sizes
  `Θ v u`: each edge contributes its size exactly once. -/

section
open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.Majorant

variable {V : UEnv (RealChain × ℝ)} {X : GCtx}

/-- The size of `ℬ₁` applied to an array of size `C`. -/
def cellB1C (X : GCtx) (η : ℝ) (C : ℝ≥0) : ℝ≥0 :=
  2 * (X.Kd * (X.S * C + C)) + Real.toNNReal |-Real.sqrt η| *
    (4 * (X.Kg * (Real.toNNReal (2 * Real.pi) * (X.S * C + C)) +
      (X.S * (X.Kg * (Real.toNNReal (2 * Real.pi) * C)) +
        X.Kg * (Real.toNNReal (2 * Real.pi) * C))))

/-- The size of `ℬ₂` applied to an array of size `C`. -/
def cellB2C (X : GCtx) (η : ℝ) (C : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal |-η| * (4 * (X.S * (X.Kg * (X.S * C + C)) + X.Kg * (X.S * C + C)))

/-- **`ℬ₁` raises the degree by one.** -/
theorem URepArrP.cellB1Arr (hX : X.Ok) (hV : V.Ok) (hS : slowC V X ≤ X.S) {η : ℝ}
    {G : RealChain → ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} {vel : RealChain → ℝ → Vec 2 → Vec 2}
    (hGr : ∀ i j, V.IsURepP X (fun l Y _ => G l.1 l.2 Y i j) 0 0 X.Kg)
    (hvr : ∀ k, V.IsURepP X (fun l _ z => Real.sqrt η * vel l.1 l.2 z k) 0 0 X.Kd)
    {B : RealChain × ℝ → CArr} {n w : ℕ} {C : ℝ≥0} (hB : V.URepArrP X B n w C)
    (hsupp : ∀ l ∈ V.W, ArrSupp n (B l)) (hB2 : ∀ l ∈ V.W, ArrSmooth 2 (B l))
    (hG1 : ∀ l ∈ V.W, ∀ i j,
      ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => G l.1 l.2 p.1 i j)) :
    V.URepArrP X (fun l => GenSem.cellB1Arr η (G l.1) (vel l.1) l.2 (B l)) (n + 1) (w + 1)
      (cellB1C X η C) := by
  unfold GenSem.cellB1Arr
  have hsl : ∀ j, V.URepArrP X (fun l => GenSem.slowArr j (B l)) (n + 1) w (X.S * C + C) :=
    fun j => hB.slowArr hX hV.hζ hV.hρ hV.hU hS hsupp
      (fun l hl => (hB2 l hl).slow.mono (by omega)) j
  have t1 : V.URepArrP X (fun l => ∑ k : Fin 2,
      GenSem.mulArr (fun _ z => Real.sqrt η * vel l.1 l.2 z k) (GenSem.slowArr k (B l))) (n + 1)
      (w + 1)
      (((Finset.univ : Finset (Fin 2)).card : ℝ≥0) * (X.Kd * (X.S * C + C))) :=
    URepArrP.sum_le hX _ fun k _ =>
      (URepArrP.mulArr hX (hvr k) (hsl k)).mono hX le_rfl
        (max_le (Nat.zero_le _) (Nat.le_succ _)) le_rfl
  have t2 : V.URepArrP X (fun l => ∑ i : Fin 2, ∑ j : Fin 2,
      (GenSem.mulArr (fun Y _ => G l.1 l.2 Y i j) (GenSem.fastArr i (GenSem.slowArr j (B l))) +
        GenSem.slowArr i (GenSem.mulArr (fun Y _ => G l.1 l.2 Y i j) (GenSem.fastArr j (B l)))))
      (n + 1) (w + 1)
      (((Finset.univ : Finset (Fin 2)).card : ℝ≥0) * (((Finset.univ : Finset (Fin 2)).card : ℝ≥0) *
        (X.Kg * (Real.toNNReal (2 * Real.pi) * (X.S * C + C)) +
          (X.S * (X.Kg * (Real.toNNReal (2 * Real.pi) * C)) +
            X.Kg * (Real.toNNReal (2 * Real.pi) * C))))) := by
    refine URepArrP.sum_le hX _ fun i _ => URepArrP.sum_le hX _ fun j _ => URepArrP.add hX
      ((URepArrP.mulArr hX (hGr i j) ((hsl j).fastArr hX i)).mono hX le_rfl
        (max_le (Nat.zero_le _) le_rfl) le_rfl) ?_
    refine ((URepArrP.mulArr hX (hGr i j) (hB.fastArr hX j)).slowArr hX hV.hζ hV.hρ hV.hU hS
      (fun l hl => arrSupp_mulArr _ (arrSupp_fastArr j (hsupp l hl))) (fun l hl => ?_) i).mono hX
      le_rfl (max_le (Nat.zero_le _) le_rfl) le_rfl
    exact (arrSmooth_mulArr (hG1 l hl i j) (arrSmooth_fastArr (r := 1) j (hB2 l hl))).slow
  refine (URepArrP.add hX t1 (t2.smul hX (-Real.sqrt η))).mono hX le_rfl le_rfl (le_of_eq ?_)
  simp only [cellB1C, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
  ring

/-- **`ℬ₂` raises the degree by two.** -/
theorem URepArrP.cellB2Arr (hX : X.Ok) (hV : V.Ok) (hS : slowC V X ≤ X.S) {η : ℝ}
    {G : RealChain → ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ}
    (hGr : ∀ i j, V.IsURepP X (fun l Y _ => G l.1 l.2 Y i j) 0 0 X.Kg)
    {B : RealChain × ℝ → CArr} {n w : ℕ} {C : ℝ≥0} (hB : V.URepArrP X B n w C)
    (hsupp : ∀ l ∈ V.W, ArrSupp n (B l)) (hB2 : ∀ l ∈ V.W, ArrSmooth 2 (B l))
    (hG1 : ∀ l ∈ V.W, ∀ i j,
      ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => G l.1 l.2 p.1 i j)) :
    V.URepArrP X (fun l => GenSem.cellB2Arr η (G l.1) l.2 (B l)) (n + 2) w (cellB2C X η C) := by
  unfold GenSem.cellB2Arr
  have hsl : ∀ j, V.URepArrP X (fun l => GenSem.slowArr j (B l)) (n + 1) w (X.S * C + C) :=
    fun j => hB.slowArr hX hV.hζ hV.hρ hV.hU hS hsupp
      (fun l hl => (hB2 l hl).slow.mono (by omega)) j
  have t : V.URepArrP X (fun l => ∑ i : Fin 2, ∑ j : Fin 2,
      GenSem.slowArr i (GenSem.mulArr (fun Y _ => G l.1 l.2 Y i j) (GenSem.slowArr j (B l))))
      (n + 2) w
      (((Finset.univ : Finset (Fin 2)).card : ℝ≥0) * (((Finset.univ : Finset (Fin 2)).card : ℝ≥0) *
        (X.S * (X.Kg * (X.S * C + C)) + X.Kg * (X.S * C + C)))) := by
    refine URepArrP.sum_le hX _ fun i _ => URepArrP.sum_le hX _ fun j _ => ?_
    refine ((URepArrP.mulArr hX (hGr i j) (hsl j)).slowArr hX hV.hζ hV.hρ hV.hU hS
      (fun l hl => arrSupp_mulArr _ (arrSupp_slowArr j (hsupp l hl))) (fun l hl => ?_) i).mono hX
      le_rfl (max_le (Nat.zero_le _) le_rfl) le_rfl
    exact (arrSmooth_mulArr (hG1 l hl i j) (arrSmooth_slowArr (r := 1) j (hB2 l hl))).slow
  refine (t.smul hX (-η)).mono hX le_rfl le_rfl (le_of_eq ?_)
  simp only [cellB2C, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
  ring

/-! ### Graded arrays -/

/-- **Graded arrays**: the grade `p` has degree `n + p`. -/
def URepGP (V : UEnv (RealChain × ℝ)) (X : GCtx) (P : RealChain × ℝ → ℕ → CArr) (n w : ℕ)
    (C : ℝ≥0) : Prop :=
  ∀ p, V.URepArrP X (fun l => P l p) (n + p) w C

theorem URepGP.mono (hX : X.Ok) {P : RealChain × ℝ → ℕ → CArr} {n w n' w' : ℕ} {C C' : ℝ≥0}
    (h : V.URepGP X P n w C) (hn : n ≤ n') (hw : w ≤ w') (hC : C ≤ C') :
    V.URepGP X P n' w' C' := fun p => (h p).mono hX (by omega) hw hC

theorem URepGP.zero (hX : X.Ok) (V : UEnv (RealChain × ℝ)) (n w : ℕ) :
    V.URepGP X (fun _ => 0) n w 0 := fun _ => urepArrP_zero hX V _ w

theorem URepGP.add (hX : X.Ok) {P Q : RealChain × ℝ → ℕ → CArr} {n w : ℕ} {C₁ C₂ : ℝ≥0}
    (hP : V.URepGP X P n w C₁) (hQ : V.URepGP X Q n w C₂) :
    V.URepGP X (fun l => P l + Q l) n w (C₁ + C₂) := fun p => (hP p).add hX (hQ p)

theorem URepGP.sum (hX : X.Ok) {β : Type*} (s : Finset β) {P : β → RealChain × ℝ → ℕ → CArr}
    {n w : ℕ} {C : β → ℝ≥0} (h : ∀ k ∈ s, V.URepGP X (P k) n w (C k)) :
    V.URepGP X (fun l => ∑ k ∈ s, P k l) n w (∑ k ∈ s, C k) := fun p =>
  (URepArrP.sum hX s fun k hk => h k hk p).congr fun l _ => by simp [Finset.sum_apply]

theorem URepGP.mulG (hX : X.Ok) {g : RealChain × ℝ → Vec 2 → Vec 2 → ℝ} {wg : ℕ} {Cg : ℝ≥0}
    (hg : V.IsURepP X g 0 wg Cg) {P : RealChain × ℝ → ℕ → CArr} {n w : ℕ} {C : ℝ≥0}
    (hP : V.URepGP X P n w C) :
    V.URepGP X (fun l => GenSem.mulG (g l) (P l)) n (max wg w) (Cg * C) := fun p =>
  URepArrP.mulArr hX hg (hP p)

theorem URepGP.constG (hX : X.Ok) {A : RealChain × ℝ → CArr} {n w : ℕ} {C : ℝ≥0}
    (hA : V.URepArrP X A n w C) : V.URepGP X (fun l => GenSem.constG (A l)) n w C := by
  intro p
  by_cases hp : p = 0
  · subst hp
    exact hA.congr fun l _ => by simp [GenSem.constG]
  · exact ((urepArrP_zero hX V _ w).mono hX le_rfl le_rfl (by simp)).congr fun l _ => by
      simp [GenSem.constG, hp]

/-- The cost of the graded derivative: `2π + |s|(S + 1)`. -/
def dGK (X : GCtx) (s : ℝ) : ℝ≥0 :=
  Real.toNNReal (2 * Real.pi) + Real.toNNReal |s| * (X.S + 1)

/-- **The graded derivative** `D = ∂_z + s ∂_X` costs `dGK` and one fast weight. -/
theorem URepGP.dG (hX : X.Ok) (hV : V.Ok) (hS : slowC V X ≤ X.S)
    {P : RealChain × ℝ → ℕ → CArr} {n w : ℕ} {C : ℝ≥0} (hP : V.URepGP X P n w C)
    (hsupp : ∀ l ∈ V.W, ∀ p, ArrSupp (n + p) (P l p)) (hs : ∀ l ∈ V.W, GSmooth 1 (P l)) (s : ℝ)
    (i : Fin 2) : V.URepGP X (fun l => GenSem.dG s i (P l)) n (w + 1) (dGK X s * C) := by
  intro p
  cases p with
  | zero =>
    refine ((hP 0).fastArr hX i).mono hX le_rfl le_rfl ?_
    unfold dGK
    rw [add_mul]
    exact le_self_add
  | succ p =>
    have h1 := ((hP (p + 1)).fastArr hX i)
    have h2 := (((hP p).slowArr hX hV.hζ hV.hρ hV.hU hS (fun l hl => hsupp l hl p)
      (fun l hl => (hs l hl p).slow) i).smul hX s).mono hX (show n + p + 1 ≤ n + (p + 1) by omega)
      (Nat.le_succ w) le_rfl
    refine (URepArrP.add hX h1 h2).mono hX le_rfl le_rfl (le_of_eq ?_)
    unfold dGK
    ring

/-- **The graded derivative along a word** of length `m` costs `dGK^m` and `m` fast weights. -/
theorem URepGP.dWordG (hX : X.Ok) (hV : V.Ok) (hS : slowC V X ≤ X.S) (s : ℝ) :
    ∀ {m : ℕ} (α : DerivativeWord2 m) {P : RealChain × ℝ → ℕ → CArr} {n w N : ℕ} {C : ℝ≥0},
      V.URepGP X P n w C → (∀ l ∈ V.W, GSupp n N (P l)) → (∀ l ∈ V.W, GSmooth m (P l)) →
      V.URepGP X (fun l => GenSem.dWordG s m α (P l)) n (w + m) (dGK X s ^ m * C)
  | 0, _, _, _, _, _, _, hP, _, _ => hP.mono hX le_rfl le_rfl (by simp)
  | m + 1, α, _, n, w, N, C, hP, hsupp, hs => by
    have h1 := hP.dG hX hV hS (fun l hl p => (hsupp l hl).1 p)
      (fun l hl p => (hs l hl p).mono (by omega)) s (α 0)
    have h2 := URepGP.dWordG hX hV hS s (fun i => α i.succ) h1
      (fun l hl => gSupp_dG s (α 0) (hsupp l hl))
      (fun l hl => gSmooth_dG (r := m) s (α 0) (hs l hl))
    refine h2.mono hX le_rfl (by omega) (le_of_eq ?_)
    ring

/-! ### The source operator -/

variable {ι : Type} [Fintype ι] {Dm : ℕ}

/-- **The edge flux**: each edge aggregate contributes its size `Θ v u` once. -/
theorem URepGP.fluxG (hX : X.Ok) (hV : V.Ok) (hS : slowC V X ≤ X.S)
    (edge : RealChain → ConstituentEdges Dm (fun _ : ι => ℝ)) (s : ℝ) (k : Fin 2)
    {A : ι → RealChain × ℝ → CArr} {K w : ℕ} {CA : ι → ℝ≥0}
    (hA : ∀ u, V.URepArrP X (A u) K w (CA u)) (hAsupp : ∀ l ∈ V.W, ∀ u, ArrSupp K (A u l))
    (hAs : ∀ l ∈ V.W, ∀ u, ArrSmooth Dm (A u l)) {wE : ℕ} {Θ : ι → ι → ℝ≥0}
    (hE : ∀ (v u : ι) (d : Finset.Icc 2 Dm) α k', V.IsURepP X (fun l Y z =>
      ((edge l.1 v u d).map fun γ => γ.map 1 * γ.coeff α l.2 Y z k').sum) 0 wE (Θ v u)) (v : ι) :
    V.URepGP X (fun l => GenSem.fluxG (edge l.1) s l.2 k (fun u => A u l) v) K
      (max wE (w + Dm))
      (∑ u : ι, ∑ d : Finset.Icc 2 Dm, ∑ _α : DerivativeWord2 (d.1 - 1),
        Θ v u * (dGK X s ^ (d.1 - 1) * CA u)) := by
  have h : V.URepGP X (fun l => ∑ u : ι, ∑ d : Finset.Icc 2 Dm,
      ∑ α : DerivativeWord2 (d.1 - 1), GenSem.wordG s (fun Y z =>
        ((edge l.1 v u d).map fun γ => γ.map 1 * γ.coeff α l.2 Y z k).sum) (d.1 - 1) α (A u l)) K
      (max wE (w + Dm))
      (∑ u : ι, ∑ d : Finset.Icc 2 Dm, ∑ _α : DerivativeWord2 (d.1 - 1),
        Θ v u * (dGK X s ^ (d.1 - 1) * CA u)) := by
    refine URepGP.sum hX _ fun u _ => URepGP.sum hX _ fun d _ => URepGP.sum hX _ fun α _ => ?_
    have hd := Finset.mem_Icc.mp d.2
    have hW := URepGP.dWordG hX hV hS s α (URepGP.constG hX (hA u))
      (fun l hl => gSupp_constG (hAsupp l hl u))
      (fun l hl => gSmooth_constG ((hAs l hl u).mono (by omega)))
    exact (URepGP.mulG hX (hE v u d α k) hW).mono hX le_rfl
      (max_le_max le_rfl (by omega)) le_rfl
  intro p
  exact (h p).congr fun l _ => by dsimp only; rw [fluxG_eq_agg]

/-- **The source operator** costs one more graded derivative. -/
theorem URepGP.sourceG (hX : X.Ok) (hV : V.Ok) (hS : slowC V X ≤ X.S)
    (edge : RealChain → ConstituentEdges Dm (fun _ : ι => ℝ)) (s : ℝ)
    {A : ι → RealChain × ℝ → CArr} {K w : ℕ} {CA : ι → ℝ≥0}
    (hA : ∀ u, V.URepArrP X (A u) K w (CA u)) (hAsupp : ∀ l ∈ V.W, ∀ u, ArrSupp K (A u l))
    (hAs : ∀ l ∈ V.W, ∀ u, ArrSmooth (1 + Dm) (A u l)) {wE : ℕ} {Θ : ι → ι → ℝ≥0}
    (hE : ∀ (v u : ι) (d : Finset.Icc 2 Dm) α k', V.IsURepP X (fun l Y z =>
      ((edge l.1 v u d).map fun γ => γ.map 1 * γ.coeff α l.2 Y z k').sum) 0 wE (Θ v u))
    (hEs : ∀ l ∈ V.W, ∀ (v u : ι) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ),
      γ ∈ edge l.1 v u d → ∀ α k',
        ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => γ.coeff α l.2 p.1 p.2 k'))
    (v : ι) :
    V.URepGP X (fun l => GenSem.sourceG (edge l.1) s l.2 (fun u => A u l) v) K
      (max wE (w + Dm) + 1)
      (((Finset.univ : Finset (Fin 2)).card : ℝ≥0) * (dGK X s *
        ∑ u : ι, ∑ d : Finset.Icc 2 Dm, ∑ _α : DerivativeWord2 (d.1 - 1),
          Θ v u * (dGK X s ^ (d.1 - 1) * CA u))) := by
  unfold GenSem.sourceG
  have hk : ∀ k : Fin 2, V.URepGP X (fun l => GenSem.dG s k
      (GenSem.fluxG (edge l.1) s l.2 k (fun u => A u l) v)) K (max wE (w + Dm) + 1)
      (dGK X s * ∑ u : ι, ∑ d : Finset.Icc 2 Dm, ∑ _α : DerivativeWord2 (d.1 - 1),
        Θ v u * (dGK X s ^ (d.1 - 1) * CA u)) := fun k =>
    URepGP.dG hX hV hS
      (URepGP.fluxG hX hV hS edge s k hA hAsupp (fun l hl u => (hAs l hl u).mono (by omega)) hE v)
      (fun l hl p => (fluxG_gSupp (edge l.1) s l.2 k (fun u => hAsupp l hl u) v).1 p)
      (fun l hl => fluxG_gSmooth (edge l.1) s l.2 k (r := 1) (hAs l hl)
        (fun v u d γ hγ α => hEs l hl v u d γ hγ α k) v) s k
  have := URepGP.sum hX (Finset.univ : Finset (Fin 2)) fun k _ => hk k
  rwa [Finset.sum_const, nsmul_eq_mul] at this
end

/-! **Ledger: the graded array of `A_n^{(hh)}`.** The quantitative form of
`UEnv.URepArr.liftAArr`. The lift coefficients of the earlier pairs `(hh', k)` are graded with
* degree `k` (the entry of tested order `m` has received at most `k - m` slow derivatives);
* fast weight `liftWt D_m hh' k = k + hh'(D_m + 1)`;
* size `β hh' k · P hh' v u`, where `P hh` is a path weight of grade `hh` of the edge sizes
  (`∑_u Θ v u · P (hh-1) u w ≤ P hh v w`): each source edge contributes its size exactly once.
Then `A_n^{(hh)}` has degree `n`, fast weight `liftWt D_m hh n` and size
`liftAc X D_m β hh n · P hh v w`, with constants free of the cell contrast `0 ≤ η ≤ 1`
(the drift enters as the normalized `√η · 𝐛`). -/

section
open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.Majorant

/-! ### Constants -/

theorem cellB1C_le_one (X : GCtx) {η : ℝ} (hη1 : η ≤ 1) (C : ℝ≥0) :
    cellB1C X η C ≤ cellB1C X 1 C := by
  have h : Real.toNNReal |-Real.sqrt η| ≤ Real.toNNReal |-Real.sqrt 1| := by
    refine Real.toNNReal_le_toNNReal ?_
    rw [abs_neg, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hη1
  unfold cellB1C
  gcongr

theorem cellB2C_le_one (X : GCtx) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (C : ℝ≥0) :
    cellB2C X η C ≤ cellB2C X 1 C := by
  have h : Real.toNNReal |-η| ≤ Real.toNNReal |-(1 : ℝ)| := by
    refine Real.toNNReal_le_toNNReal ?_
    rw [abs_neg, abs_neg, abs_of_nonneg hη0, abs_one]
    exact hη1
  unfold cellB2C
  gcongr

theorem dGK_sqrt_le_one (X : GCtx) {η : ℝ} (hη1 : η ≤ 1) : dGK X (Real.sqrt η) ≤ dGK X 1 := by
  have h : Real.toNNReal |Real.sqrt η| ≤ Real.toNNReal |(1 : ℝ)| := by
    refine Real.toNNReal_le_toNNReal ?_
    rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_one]
    calc Real.sqrt η ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hη1
      _ = 1 := Real.sqrt_one
  unfold dGK
  gcongr

theorem cellB1C_mul (X : GCtx) (η : ℝ) (c p : ℝ≥0) :
    cellB1C X η (c * p) = cellB1C X η c * p := by
  unfold cellB1C
  ring

theorem cellB2C_mul (X : GCtx) (η : ℝ) (c p : ℝ≥0) :
    cellB2C X η (c * p) = cellB2C X η c * p := by
  unfold cellB2C
  ring

/-- The fast weight of the lift coefficient `(hh, n)`. -/
def liftWt (Dm hh n : ℕ) : ℕ := n + hh * (Dm + 1)

theorem liftWt_mono (Dm : ℕ) {hh hh' n n' : ℕ} (h1 : hh' ≤ hh) (h2 : n' ≤ n) :
    liftWt Dm hh' n' ≤ liftWt Dm hh n := by
  unfold liftWt
  exact Nat.add_le_add h2 (Nat.mul_le_mul_right _ h1)

theorem liftWt_pred (Dm hh : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    liftWt Dm hh (n - 1) + 1 ≤ liftWt Dm hh n := by
  unfold liftWt
  omega

theorem liftWt_pred_grade (Dm : ℕ) {hh n k : ℕ} (hh1 : 1 ≤ hh) (hk : k ≤ n) :
    liftWt Dm (hh - 1) k + Dm + 1 ≤ liftWt Dm hh n := by
  obtain ⟨h', rfl⟩ : ∃ h', hh = h' + 1 := ⟨hh - 1, by omega⟩
  unfold liftWt
  rw [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
  omega

/-- The sum of the word costs of the source edges of the orders `2 ≤ d ≤ D_m`. -/
def edgeWordC (X : GCtx) (Dm : ℕ) : ℝ≥0 :=
  ∑ d : Finset.Icc 2 Dm, ∑ _α : DerivativeWord2 (d.1 - 1), dGK X 1 ^ (d.1 - 1)

/-- The size constant of `A_n^{(hh)}` from the size constants `β` of the earlier coefficients. -/
def liftAc (X : GCtx) (Dm : ℕ) (β : ℕ → ℕ → ℝ≥0) (hh n : ℕ) : ℝ≥0 :=
  cellB1C X 1 (β hh (n - 1)) + (if 2 ≤ n then cellB2C X 1 (β hh (n - 2)) else 0) +
    (if hh = 0 then 0 else ∑ j ∈ Finset.range (min Dm n + 1),
      2 * (dGK X 1 * (edgeWordC X Dm * β (hh - 1) (n - j))))

variable {V : UEnv (RealChain × ℝ)} {X : GCtx} {ι : Type} {Dm : ℕ}

/-! ### Graded coefficients -/

/-- **The lift coefficients of the earlier pairs are graded**: every pair `(hh', k)` with
`hh' ≤ hh` and `hh' + k < hh + n`. -/
def CoeffRepBelowP (V : UEnv (RealChain × ℝ)) (X : GCtx) (Dm : ℕ)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (P : ℕ → ι → ι → ℝ≥0)
    (β : ℕ → ℕ → ℝ≥0) (hh n : ℕ) : Prop :=
  ∀ hh' k, hh' ≤ hh → hh' + k < hh + n → ∀ m α (v u : ι),
    V.IsURepP X (fun l Y z => Cc l.1 hh' k m α l.2 Y z v u 1) (k - m) (liftWt Dm hh' k)
      (β hh' k * P hh' v u)

theorem CoeffRepBelowP.mono {Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)}
    {P : ℕ → ι → ι → ℝ≥0} {β : ℕ → ℕ → ℝ≥0} {hh n hh₁ n₁ : ℕ}
    (h : V.CoeffRepBelowP X Dm Cc P β hh n) (h1 : hh₁ ≤ hh) (h2 : hh₁ + n₁ ≤ hh + n) :
    V.CoeffRepBelowP X Dm Cc P β hh₁ n₁ :=
  fun hh' k hk1 hk2 => h hh' k (by omega) (by omega)

theorem urepArrP_entryArr (hX : X.Ok) {Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)}
    {hh' k w' : ℕ} {C : ι → ι → ℝ≥0}
    (h : ∀ m α (v u : ι), V.IsURepP X (fun l Y z => Cc l.1 hh' k m α l.2 Y z v u 1) (k - m) w'
      (C v u)) (w v : ι) :
    V.URepArrP X (fun l => GenSem.entryArr (Cc l.1 hh' k) k w l.2 v) k w' (C v w) := by
  intro m α
  by_cases hm : m ≤ k
  · exact (h m α v w).congr fun τ _ Y _ z => by simp [GenSem.entryArr, hm]
  · exact ((isURepP_zero hX V _ _).mono hX le_rfl le_rfl (by simp)).congr fun τ _ Y _ z => by
      simp [GenSem.entryArr, hm]

theorem urepArrP_cArr {Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)} {hh' k w' : ℕ}
    {C : ι → ι → ℝ≥0}
    (h : ∀ m α (v u : ι), V.IsURepP X (fun l Y z => Cc l.1 hh' k m α l.2 Y z v u 1) (k - m) w'
      (C v u)) (v u : ι) :
    V.URepArrP X (fun l => GenSem.cArr (Cc l.1 hh' k) l.2 v u) k w' (C v u) := fun m α => h m α v u

variable [Fintype ι]

/-- The source-edge sum against a path weight: each edge contributes its size once. -/
theorem sum_edge_le (X : GCtx) (Dm : ℕ) {g : ℝ≥0} (hg : g ≤ dGK X 1) (Θv P' : ι → ℝ≥0)
    (b Ptot : ℝ≥0) (hP : ∑ u, Θv u * P' u ≤ Ptot) :
    ∑ u : ι, ∑ d : Finset.Icc 2 Dm, ∑ _α : DerivativeWord2 (d.1 - 1),
        Θv u * (g ^ (d.1 - 1) * (b * P' u)) ≤ edgeWordC X Dm * b * Ptot := by
  have h1 : ∀ u : ι, ∑ d : Finset.Icc 2 Dm, ∑ _α : DerivativeWord2 (d.1 - 1),
      Θv u * (g ^ (d.1 - 1) * (b * P' u)) ≤ Θv u * P' u * (b * edgeWordC X Dm) := by
    intro u
    unfold edgeWordC
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun α _ => ?_
    have : g ^ (d.1 - 1) ≤ dGK X 1 ^ (d.1 - 1) := pow_le_pow_left₀ zero_le hg _
    calc Θv u * (g ^ (d.1 - 1) * (b * P' u)) ≤ Θv u * (dGK X 1 ^ (d.1 - 1) * (b * P' u)) := by
          gcongr
      _ = Θv u * P' u * (b * dGK X 1 ^ (d.1 - 1)) := by ring
  calc ∑ u : ι, ∑ d : Finset.Icc 2 Dm, ∑ _α : DerivativeWord2 (d.1 - 1),
        Θv u * (g ^ (d.1 - 1) * (b * P' u))
      ≤ ∑ u : ι, Θv u * P' u * (b * edgeWordC X Dm) := Finset.sum_le_sum fun u _ => h1 u
    _ = (∑ u : ι, Θv u * P' u) * (b * edgeWordC X Dm) := by rw [Finset.sum_mul]
    _ ≤ Ptot * (b * edgeWordC X Dm) := by gcongr
    _ = edgeWordC X Dm * b * Ptot := by ring

/-- **`A_n^{(hh)}` of the test field is graded of degree `n`.** -/
theorem URepArrP.liftAArr (hX : X.Ok) (hV : V.Ok) (hS : slowC V X ≤ X.S)
    (Q : RealChain → LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} (hn : 1 ≤ n) {η : ℝ}
    (hη : ∀ l ∈ V.W, (Q l.1).η = η) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hGr : ∀ i j, V.IsURepP X (fun l Y _ => (Q l.1).G l.2 Y i j) 0 0 X.Kg)
    (hvr : ∀ k, V.IsURepP X (fun l _ z => Real.sqrt η * (Q l.1).v l.2 z k) 0 0 X.Kd)
    {Θ : ι → ι → ℝ≥0}
    (hed : ∀ (v u : ι) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (k : Fin 2),
      V.IsURepP X (fun l Y z =>
        (((Q l.1).edge v u d).map fun γ => γ.map 1 * γ.coeff α l.2 Y z k).sum) 0 0 (Θ v u))
    {P : ℕ → ι → ι → ℝ≥0} (hP : ∀ hh v w, 1 ≤ hh → ∑ u, Θ v u * P (hh - 1) u w ≤ P hh v w)
    {β : ℕ → ℕ → ℝ≥0} (hC : V.CoeffRepBelowP X Dm Cc P β hh n)
    (hreg : ∀ l ∈ V.W, LiftRegular (Q l.1) (Cc l.1) w l.2 hh n (n + Dm + 2)) (v : ι) :
    V.URepArrP X (fun l => GenSem.liftAArr (Q l.1) (Cc l.1) w hh n l.2 v) n (liftWt Dm hh n)
      (liftAc X Dm β hh n * P hh v w) := by
  have hsm : ∀ l ∈ V.W, ∀ hh' k, hh' ≤ hh → k ≤ n → ∀ u,
      ArrSmooth (n + Dm + 2) (GenSem.entryArr (Cc l.1 hh' k) k w l.2 u) :=
    fun l hl hh' k h1 h2 u => arrSmooth_entryArr _ _ _ _ _ ((hreg l hl).coeff hh' h1 k h2 · · u)
  have hG : ∀ l ∈ V.W, ∀ i j,
      ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => (Q l.1).G l.2 p.1 i j) :=
    fun l hl i j => ((hreg l hl).metric i j).of_le (by exact_mod_cast (by omega : 1 ≤ n + Dm + 2))
  -- the `ℬ₁` part
  have p1 : V.URepArrP X (fun l => GenSem.cellB1Arr (Q l.1).η (Q l.1).G (Q l.1).v l.2
      (GenSem.entryArr (Cc l.1 hh (n - 1)) (n - 1) w l.2 v)) n (liftWt Dm hh n)
      (cellB1C X 1 (β hh (n - 1)) * P hh v w) := by
    have h := URepArrP.cellB1Arr hX hV hS (G := fun A => (Q A).G) (vel := fun A => (Q A).v)
      (η := η) hGr hvr (urepArrP_entryArr hX (hC hh (n - 1) le_rfl (by omega)) w v)
      (fun l _ => arrSupp_entryArr _ _ _ _ _)
      (fun l hl => (hsm l hl hh (n - 1) le_rfl (by omega) v).mono (by omega)) hG
    refine (h.mono hX (by omega) (liftWt_pred Dm hh hn) ?_).congr fun l hl => by
      simp only [hη l hl]
    rw [← cellB1C_mul]
    exact cellB1C_le_one X hη1 _
  -- the `ℬ₂` part
  have p2 : V.URepArrP X (fun l => if 2 ≤ n then GenSem.cellB2Arr (Q l.1).η (Q l.1).G l.2
      (GenSem.entryArr (Cc l.1 hh (n - 2)) (n - 2) w l.2 v) else 0) n (liftWt Dm hh n)
      ((if 2 ≤ n then cellB2C X 1 (β hh (n - 2)) else 0) * P hh v w) := by
    by_cases h2 : 2 ≤ n
    · simp only [h2, ite_true]
      have h := URepArrP.cellB2Arr hX hV hS (G := fun A => (Q A).G) (η := η) hGr
        (urepArrP_entryArr hX (hC hh (n - 2) le_rfl (by omega)) w v)
        (fun l _ => arrSupp_entryArr _ _ _ _ _)
        (fun l hl => (hsm l hl hh (n - 2) le_rfl (by omega) v).mono (by omega)) hG
      refine (h.mono hX (by omega) (liftWt_mono Dm le_rfl (by omega)) ?_).congr fun l hl => by
        simp only [hη l hl]
      rw [← cellB2C_mul]
      exact cellB2C_le_one X hη0 hη1 _
    · simp only [h2, ite_false, zero_mul]
      exact urepArrP_zero hX V _ _
  -- the source part
  have p3 : V.URepArrP X (fun l => if hh = 0 then 0 else ∑ j ∈ Finset.range (min Dm n + 1),
      GenSem.sourceG (Q l.1).edge (Real.sqrt (Q l.1).η) l.2
        (fun u => GenSem.entryArr (Cc l.1 (hh - 1) (n - j)) (n - j) w l.2 u) v j) n
      (liftWt Dm hh n)
      ((if hh = 0 then 0 else ∑ j ∈ Finset.range (min Dm n + 1),
        2 * (dGK X 1 * (edgeWordC X Dm * β (hh - 1) (n - j)))) * P hh v w) := by
    by_cases h0 : hh = 0
    · simp only [h0, ite_true, zero_mul]
      exact urepArrP_zero hX V _ _
    · simp only [h0, ite_false]
      rw [Finset.sum_mul]
      refine URepArrP.sum hX _ fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      have hjn : j ≤ n := by omega
      have h := URepGP.sourceG hX hV hS (fun A => (Q A).edge) (Real.sqrt η)
        (A := fun u l => GenSem.entryArr (Cc l.1 (hh - 1) (n - j)) (n - j) w l.2 u)
        (CA := fun u => β (hh - 1) (n - j) * P (hh - 1) u w)
        (fun u => urepArrP_entryArr hX (hC (hh - 1) (n - j) (by omega) (by omega)) w u)
        (fun l _ u => arrSupp_entryArr _ _ _ _ _)
        (fun l hl u => (hsm l hl (hh - 1) (n - j) (by omega) (by omega) u).mono (by omega))
        hed (fun l hl v u d γ hγ α k => ((hreg l hl).edge v u d γ hγ α k).of_le
          (by exact_mod_cast (by omega : 1 ≤ n + Dm + 2))) v j
      refine (h.mono hX (by omega) ?_ ?_).congr fun l hl => by simp only [hη l hl]
      · have := liftWt_pred_grade Dm (n := n) (k := n - j) (by omega : 1 ≤ hh) (by omega)
        rw [max_eq_right (Nat.zero_le _)]
        omega
      · simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
        have hg := dGK_sqrt_le_one X hη1
        have hsum := sum_edge_le X Dm hg (fun u => Θ v u) (fun u => P (hh - 1) u w)
          (β (hh - 1) (n - j)) (P hh v w) (hP hh v w (by omega))
        calc 2 * (dGK X (Real.sqrt η) * ∑ u : ι, ∑ d : Finset.Icc 2 Dm,
              ∑ _α : DerivativeWord2 (d.1 - 1), Θ v u * (dGK X (Real.sqrt η) ^ (d.1 - 1) *
                (β (hh - 1) (n - j) * P (hh - 1) u w)))
            ≤ 2 * (dGK X 1 * (edgeWordC X Dm * β (hh - 1) (n - j) * P hh v w)) := by
              gcongr
          _ = 2 * (dGK X 1 * (edgeWordC X Dm * β (hh - 1) (n - j))) * P hh v w := by ring
  have hall := ((p1.add hX p2).sub hX p3)
  refine (hall.mono hX le_rfl le_rfl (le_of_eq ?_)).congr fun l _ => ?_
  · unfold liftAc
    ring
  · rfl
end

/-! **Ledger: the graded slow-flux array.** The quantitative form of
`UEnv.URepArr.fluxXArr`: the coefficient array of the slow flux of `𝐀_n^{(hh)}` has degree `n - 1`
(the flux of a mean of cell degree `n` is an operator of degree `n - 1`: its coefficient of tested
order `d - 1` is bounded at the reserve cost `n - d`), fast weight `liftWt D_m hh n` and size
`fluxXc X D_m β hh n · P hh v w`. -/

section
open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.Majorant

theorem toNNReal_abs_sqrt_le_one {η : ℝ} (hη1 : η ≤ 1) : Real.toNNReal |Real.sqrt η| ≤ 1 := by
  rw [Real.toNNReal_le_one, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt η ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hη1
    _ = 1 := Real.sqrt_one

theorem toNNReal_abs_le_one {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) : Real.toNNReal |η| ≤ 1 := by
  rw [Real.toNNReal_le_one, abs_of_nonneg hη0]
  exact hη1

/-- The size constant of the slow flux of `𝐀_n^{(hh)}`. -/
def fluxXc (X : GCtx) (Dm : ℕ) (β : ℕ → ℕ → ℝ≥0) (hh n : ℕ) : ℝ≥0 :=
  X.Kd * β hh (n - 1) + 2 * (X.Kg * (Real.toNNReal (2 * Real.pi) * β hh (n - 1))) +
    (if 2 ≤ n then 2 * (X.Kg * (X.S * β hh (n - 2) + β hh (n - 2))) else 0) +
    (if hh = 0 then 0 else ∑ j ∈ Finset.Icc 1 (min Dm n), edgeWordC X Dm * β (hh - 1) (n - j))

variable {V : UEnv (RealChain × ℝ)} {X : GCtx} {ι : Type} [Fintype ι] {Dm : ℕ}

/-- **The slow-flux array `fluxXArr` is graded of degree `n - 1`.** -/
theorem URepArrP.fluxXArr (hX : X.Ok) (hV : V.Ok) (hS : slowC V X ≤ X.S)
    (Q : RealChain → LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} (hn : 1 ≤ n) {η : ℝ}
    (hη : ∀ l ∈ V.W, (Q l.1).η = η) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hGr : ∀ i j, V.IsURepP X (fun l Y _ => (Q l.1).G l.2 Y i j) 0 0 X.Kg)
    (hvr : ∀ k, V.IsURepP X (fun l _ z => Real.sqrt η * (Q l.1).v l.2 z k) 0 0 X.Kd)
    {Θ : ι → ι → ℝ≥0}
    (hed : ∀ (v u : ι) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (k : Fin 2),
      V.IsURepP X (fun l Y z =>
        (((Q l.1).edge v u d).map fun γ => γ.map 1 * γ.coeff α l.2 Y z k).sum) 0 0 (Θ v u))
    {P : ℕ → ι → ι → ℝ≥0} (hP : ∀ hh v w, 1 ≤ hh → ∑ u, Θ v u * P (hh - 1) u w ≤ P hh v w)
    {β : ℕ → ℕ → ℝ≥0} (hC : V.CoeffRepBelowP X Dm Cc P β hh n)
    (hreg : ∀ l ∈ V.W, LiftRegular (Q l.1) (Cc l.1) w l.2 hh n (n + Dm + 2)) (v : ι)
    (κ : Fin 2) :
    V.URepArrP X (fun l => GenSem.fluxXArr (Q l.1) (Cc l.1) w hh n l.2 v κ) (n - 1)
      (liftWt Dm hh n) (fluxXc X Dm β hh n * P hh v w) := by
  have hsm : ∀ l ∈ V.W, ∀ hh' k, hh' ≤ hh → k ≤ n → ∀ u,
      ArrSmooth (n + Dm + 2) (GenSem.entryArr (Cc l.1 hh' k) k w l.2 u) :=
    fun l hl hh' k h1 h2 u => arrSmooth_entryArr _ _ _ _ _ ((hreg l hl).coeff hh' h1 k h2 · · u)
  have hsq := toNNReal_abs_sqrt_le_one hη1
  have hab := toNNReal_abs_le_one hη0 hη1
  have hB1 := urepArrP_entryArr hX (hC hh (n - 1) le_rfl (by omega)) w v
  have hw1 : liftWt Dm hh (n - 1) + 1 ≤ liftWt Dm hh n := liftWt_pred Dm hh hn
  -- fluxXA
  have pA : V.URepArrP X (fun l => GenSem.fluxXA (Q l.1) (Cc l.1) w hh n l.2 v κ) (n - 1)
      (liftWt Dm hh n) (X.Kd * β hh (n - 1) * P hh v w) := by
    refine ((URepArrP.mulArr hX (hvr κ) hB1).mono hX le_rfl
      (max_le (Nat.zero_le _) (by omega)) (le_of_eq (by ring))).congr fun l hl => ?_
    simp only [GenSem.fluxXA, hη l hl]
  -- fluxXB
  have pB : V.URepArrP X (fun l => GenSem.fluxXB (Q l.1) (Cc l.1) w hh n l.2 v κ) (n - 1)
      (liftWt Dm hh n) (2 * (X.Kg * (Real.toNNReal (2 * Real.pi) * β hh (n - 1))) * P hh v w) := by
    have h := (URepArrP.sum_le hX (Finset.univ : Finset (Fin 2)) fun j _ =>
      URepArrP.mulArr hX (hGr κ j) (hB1.fastArr hX j)).smul hX (Real.sqrt η)
    refine (h.mono hX le_rfl (max_le (Nat.zero_le _) hw1) ?_).congr fun l hl => ?_
    · simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
      calc Real.toNNReal |Real.sqrt η| * (2 * (X.Kg * (Real.toNNReal (2 * Real.pi) *
            (β hh (n - 1) * P hh v w))))
          ≤ 1 * (2 * (X.Kg * (Real.toNNReal (2 * Real.pi) * (β hh (n - 1) * P hh v w)))) :=
            mul_le_mul' hsq le_rfl
        _ = _ := by ring
    · simp only [GenSem.fluxXB, hη l hl]
  -- fluxXC
  have pC : V.URepArrP X (fun l => GenSem.fluxXC (Q l.1) (Cc l.1) w hh n l.2 v κ) (n - 1)
      (liftWt Dm hh n)
      ((if 2 ≤ n then 2 * (X.Kg * (X.S * β hh (n - 2) + β hh (n - 2))) else 0) * P hh v w) := by
    by_cases h2 : 2 ≤ n
    · have hB2 := urepArrP_entryArr hX (hC hh (n - 2) le_rfl (by omega)) w v
      have h := ((URepArrP.sum_le hX (Finset.univ : Finset (Fin 2)) fun j _ =>
        URepArrP.mulArr hX (hGr κ j) (hB2.slowArr hX hV.hζ hV.hρ hV.hU hS
          (fun l _ => arrSupp_entryArr _ _ _ _ _) (fun l hl =>
            ((hsm l hl hh (n - 2) le_rfl (by omega) v).mono (by omega : 1 ≤ n + Dm + 2)).slow)
          j)).smul hX η).neg hX
      refine (h.mono hX (by omega)
        (max_le (Nat.zero_le _) (liftWt_mono Dm le_rfl (by omega))) ?_).congr fun l hl => ?_
      · simp only [h2, ↓reduceIte, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
        calc Real.toNNReal |η| * (2 * (X.Kg * (X.S * (β hh (n - 2) * P hh v w) +
              β hh (n - 2) * P hh v w)))
            ≤ 1 * (2 * (X.Kg * (X.S * (β hh (n - 2) * P hh v w) + β hh (n - 2) * P hh v w))) :=
              mul_le_mul' hab le_rfl
          _ = _ := by ring
      · simp only [GenSem.fluxXC, h2, ite_true, hη l hl]
    · simp only [h2, ↓reduceIte, zero_mul]
      refine (urepArrP_zero hX V _ _).congr fun l hl => ?_
      simp [GenSem.fluxXC, h2]
  -- fluxXD
  have pD : V.URepArrP X (fun l => GenSem.fluxXD (Q l.1) (Cc l.1) w hh n l.2 v κ) (n - 1)
      (liftWt Dm hh n)
      ((if hh = 0 then 0 else ∑ j ∈ Finset.Icc 1 (min Dm n),
        edgeWordC X Dm * β (hh - 1) (n - j)) * P hh v w) := by
    by_cases h0 : hh = 0
    · simp only [h0, ↓reduceIte, zero_mul]
      refine (urepArrP_zero hX V _ _).congr fun l hl => ?_
      simp [GenSem.fluxXD]
    · simp only [h0, ↓reduceIte]
      rw [Finset.sum_mul]
      have hsumD : V.URepArrP X (fun l => ∑ j ∈ Finset.Icc 1 (min Dm n), Real.sqrt η •
          GenSem.fluxG (Q l.1).edge (Real.sqrt η) l.2 κ
            (fun u => GenSem.entryArr (Cc l.1 (hh - 1) (n - j)) (n - j) w l.2 u) v (j - 1))
          (n - 1) (liftWt Dm hh n)
          (∑ j ∈ Finset.Icc 1 (min Dm n), edgeWordC X Dm * β (hh - 1) (n - j) * P hh v w) := by
        refine URepArrP.sum hX (Finset.Icc 1 (min Dm n)) fun j hj => ?_
        have hj' := Finset.mem_Icc.mp hj
        have hjn : j ≤ n := by omega
        have hF := URepGP.fluxG hX hV hS (fun A => (Q A).edge) (Real.sqrt η) κ
          (A := fun u l => GenSem.entryArr (Cc l.1 (hh - 1) (n - j)) (n - j) w l.2 u)
          (CA := fun u => β (hh - 1) (n - j) * P (hh - 1) u w)
          (fun u => urepArrP_entryArr hX (hC (hh - 1) (n - j) (by omega) (by omega)) w u)
          (fun l _ u => arrSupp_entryArr _ _ _ _ _)
          (fun l hl u => (hsm l hl (hh - 1) (n - j) (by omega) (by omega) u).mono (by omega))
          hed v (j - 1)
        refine (hF.smul hX (Real.sqrt η)).mono hX (by omega) ?_ ?_
        · have := liftWt_pred_grade Dm (n := n) (k := n - j) (by omega : 1 ≤ hh) (by omega)
          rw [max_eq_right (Nat.zero_le _)]
          omega
        · have hsum := sum_edge_le X Dm (dGK_sqrt_le_one X hη1) (fun u => Θ v u)
            (fun u => P (hh - 1) u w) (β (hh - 1) (n - j)) (P hh v w) (hP hh v w (by omega))
          calc Real.toNNReal |Real.sqrt η| * ∑ u : ι, ∑ d : Finset.Icc 2 Dm,
                ∑ _α : DerivativeWord2 (d.1 - 1), Θ v u * (dGK X (Real.sqrt η) ^ (d.1 - 1) *
                  (β (hh - 1) (n - j) * P (hh - 1) u w))
              ≤ 1 * (edgeWordC X Dm * β (hh - 1) (n - j) * P hh v w) := mul_le_mul' hsq hsum
            _ = edgeWordC X Dm * β (hh - 1) (n - j) * P hh v w := one_mul _
      exact hsumD.congr fun l hl => by
        simp only [GenSem.fluxXD, h0, ite_false, hη l hl]
  refine ((((pA.sub hX pB).add hX pC).sub hX pD).mono hX le_rfl le_rfl (le_of_eq ?_)).congr
    fun l _ => ?_
  · unfold fluxXc
    ring
  · rfl
end

end AVRegularity.Providers.GenSem.UEnv
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.GenSem

/-! **Ledger: the graded cell source and the graded lift step.** The quantitative form of
`UEnv.URepArr.srcArr`, `UEnv.isURep_cellSource` and `LiftGenSetup.coeff_step`:
* the cell source `srcArr` of the pair `(hh, n)` has degree `n`, fast weight `liftWt D_m hh n`
  and size `srcCc X D_m β hh n · P hh v w`: the composition terms pair a coefficient of grade
  `hh'` with a mean of grade `hh''`, `hh' + hh'' = hh`, and the path weights multiply
  (`∑_u P a v u · P b u w ≤ P (a + b) v w`);
* the transverse inverse of the transverse primitive (`cellInvOf`) costs the constant
  `(4/3) cGain π⁻¹` and neither reserve nor fast weight (`prof_cellInvOf`);
* hence the lift coefficient `(hh, n)` is graded with size `cInvC · srcCc · P hh v u`
  (`LiftGenSetup.coeff_stepP`). -/

section
open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.Majorant

section Supp

variable {ι : Type} [Fintype ι] {Dm : ℕ}

/-- For `n ≥ 1` the array of `A_n^{(hh)}` vanishes above the order `n`. -/
theorem arrSupp_liftAArr_pos (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) (hh : ℕ) {n : ℕ} (hn : 1 ≤ n) (t : ℝ)
    (v : ι) : ArrSupp n (liftAArr Q Cc w hh n t v) := by
  unfold liftAArr
  refine ArrSupp.sub (ArrSupp.add ?_ ?_) ?_
  · exact (arrSupp_cellB1Arr Q.η Q.G Q.v t (arrSupp_entryArr _ _ _ _ _)).mono (by omega)
  · split_ifs
    · exact (arrSupp_cellB2Arr Q.η Q.G t (arrSupp_entryArr _ _ _ _ _)).mono (by omega)
    · exact ArrSupp.zero _
  · split_ifs
    · exact ArrSupp.zero _
    · refine ArrSupp.sum _ fun j hj => ?_
      have hjn : j ≤ n := by
        have := Finset.mem_range.mp hj
        omega
      have := (sourceG_gSupp Q.edge (Real.sqrt Q.η) t
        (A := fun u => entryArr (Cc (hh - 1) (n - j)) (n - j) w t u)
        (fun u => arrSupp_entryArr _ _ _ _ _) v).1 j
      rw [show n - j + j = n by omega] at this
      exact this

end Supp

/-- The constant of the transverse inverse of a transverse primitive: `(4/3) cGain π⁻¹`
(the inverse takes the supremum of its flux over the history). -/
def cInvC : ℝ≥0 :=
  Real.toNNReal (4 / 3) * cGain.toNNReal * Real.toNNReal Real.pi⁻¹

/-- **The transverse inverse of the transverse primitive** keeps the reserve and the fast weight
and costs `cInvC`; its history supremum uses the profile of the source at every
time (`X.Ok.hT`). -/
theorem prof_cellInvOf {X : GCtx} (hX : X.Ok) (D : OCData) {i : ℕ} {p : ℤ} {e : Gen .cell i p}
    (hs : Gen.SolvedFree X.leaf e) {r w : ℕ} {C : ℝ≥0}
    (hn : ∀ t ∈ X.T, X.Prof (fun mres L => genNorm D X.κ X.Δ X.a₀ X.leaf e X.a₀ mres L t) r w C) :
    Gen.SolvedFree X.leaf (cellInvOf D e) ∧ ∀ t ∈ X.T,
      X.Prof (fun mres L => genNorm D X.κ X.Δ X.a₀ X.leaf (cellInvOf D e) X.a₀ mres L t) r w
        ((cInvC * C : ℝ≥0) : ℝ≥0∞) := by
  refine ⟨Or.inr ⟨fun j => ?_, trivial⟩, fun t ht mres L hm hL => ?_⟩
  · show Gen.SolvedFree X.leaf (if j = transverseIndex p then Gen.transPrim e
      else Gen.time (s := .cell) (i := i) (p := p) (.const 0))
    split_ifs
    · exact Or.inr hs
    · trivial
  · show genNorm D X.κ X.Δ X.a₀ X.leaf (cellInvOf D e) X.a₀ mres L t ≤ _
    unfold cellInvOf
    rw [genNorm_cellInv_eq _ _ _ _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx),
      genNorm_const_eq _ _ _ _ _ 0 (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx)]
    simp only [↓reduceIte, abs_zero, ENNReal.ofReal_zero, zero_add]
    have h : ∀ s ∈ Set.Icc (D.slotStart i p) t,
        genNorm D X.κ X.Δ X.a₀ X.leaf (Gen.transPrim e) X.a₀ mres (L + 1) s ≤
          ENNReal.ofReal Real.pi⁻¹ * (C : ℝ≥0∞) := by
      intro s _
      rw [genNorm_transPrim_succ_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx)]
      exact mul_le_mul_right (hn s (hX.hT s) mres L hm hL) _
    calc ENNReal.ofReal (4 / 3) * cGain *
          ⨆ s ∈ Set.Icc (D.slotStart i p) t,
            genNorm D X.κ X.Δ X.a₀ X.leaf (Gen.transPrim e) X.a₀ mres (L + 1) s
        ≤ ENNReal.ofReal (4 / 3) * cGain * (ENNReal.ofReal Real.pi⁻¹ * (C : ℝ≥0∞)) :=
          mul_le_mul_right (iSup₂_le h) _
      _ = ((cInvC * C : ℝ≥0) : ℝ≥0∞) := by
          unfold cInvC
          rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal cGain_ne_top]
          simp only [ENNReal.ofReal]
          ring

namespace UEnv

variable {V : UEnv (RealChain × ℝ)} {X : GCtx} {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

/-- The size constant of the cell source of the pair `(hh, n)`. -/
def srcCc (X : GCtx) (Dm : ℕ) (β : ℕ → ℕ → ℝ≥0) (hh n : ℕ) : ℝ≥0 :=
  (liftAc X Dm β hh n + liftAc X Dm β hh n) +
    ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, ∑ m ∈ Finset.range (j + 1),
      ((Finset.univ : Finset (DerivativeWord2 m)).card : ℝ≥0) *
        (β p.1 j * ((X.S + 1) ^ m * liftAc X Dm β p.2 (n - j)))

omit [DecidableEq ι] in
/-- The composition sum against the path weights: the weights of the two grades multiply. -/
theorem comp_sum_le (J : ℕ) (c : ℕ → ℝ≥0) (b s a : ℝ≥0) (P1 P2 : ι → ℝ≥0) (Ptot : ℝ≥0)
    (hP : ∑ u, P1 u * P2 u ≤ Ptot) :
    ∑ u : ι, ∑ m ∈ Finset.range (J + 1), c m * (b * P1 u * (s ^ m * (a * P2 u))) ≤
      (∑ m ∈ Finset.range (J + 1), c m * (b * (s ^ m * a))) * Ptot := by
  have h1 : ∀ u : ι, ∑ m ∈ Finset.range (J + 1), c m * (b * P1 u * (s ^ m * (a * P2 u))) =
      P1 u * P2 u * ∑ m ∈ Finset.range (J + 1), c m * (b * (s ^ m * a)) := by
    intro u
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  calc ∑ u : ι, ∑ m ∈ Finset.range (J + 1), c m * (b * P1 u * (s ^ m * (a * P2 u)))
      = (∑ u : ι, P1 u * P2 u) * ∑ m ∈ Finset.range (J + 1), c m * (b * (s ^ m * a)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun u _ => h1 u
    _ ≤ Ptot * ∑ m ∈ Finset.range (J + 1), c m * (b * (s ^ m * a)) := by gcongr
    _ = _ := mul_comm _ _

omit [DecidableEq ι] in
/-- **The cell source `srcArr` is graded of degree `n`.** -/
theorem URepArrP.srcArr (hX : X.Ok) (hV : V.Ok) (hS : slowC V X ≤ X.S)
    (Q : RealChain → LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} (hn : 1 ≤ n) {η : ℝ}
    (hη : ∀ l ∈ V.W, (Q l.1).η = η) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hGr : ∀ i j, V.IsURepP X (fun l Y _ => (Q l.1).G l.2 Y i j) 0 0 X.Kg)
    (hvr : ∀ k, V.IsURepP X (fun l _ z => Real.sqrt η * (Q l.1).v l.2 z k) 0 0 X.Kd)
    {Θ : ι → ι → ℝ≥0}
    (hed : ∀ (v u : ι) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (k : Fin 2),
      V.IsURepP X (fun l Y z =>
        (((Q l.1).edge v u d).map fun γ => γ.map 1 * γ.coeff α l.2 Y z k).sum) 0 0 (Θ v u))
    {P : ℕ → ι → ι → ℝ≥0} (hP : ∀ hh v w, 1 ≤ hh → ∑ u, Θ v u * P (hh - 1) u w ≤ P hh v w)
    (hP2 : ∀ a b v w, ∑ u, P a v u * P b u w ≤ P (a + b) v w)
    {β : ℕ → ℕ → ℝ≥0} (hC : V.CoeffRepBelowP X Dm Cc P β hh n)
    (hL₀ : liftWt Dm hh n ≤ X.L₀)
    (hreg : ∀ l ∈ V.W, ∀ u, LiftRegular (Q l.1) (Cc l.1) u l.2 hh n (n + Dm + 2)) (v : ι) :
    V.URepArrP X (fun l => GenSem.srcArr (Q l.1) (Cc l.1) w hh n l.2 v) n (liftWt Dm hh n)
      (srcCc X Dm β hh n * P hh v w) := by
  have hA := URepArrP.liftAArr hX hV hS Q Cc w hn hη hη0 hη1 hGr hvr hed hP hC
    (fun l hl => hreg l hl w) v
  have part1 := (hA.sub hX ((hA.meanArr hX hL₀).mono hX le_rfl (Nat.zero_le _) le_rfl)).neg hX
  have part2 : V.URepArrP X (fun l => ∑ j ∈ Finset.Icc 1 (n - 2),
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, ∑ u : ι,
        GenSem.compArr j (GenSem.cArr (Cc l.1 p.1 j) l.2 v u)
          (GenSem.meanArr (GenSem.liftAArr (Q l.1) (Cc l.1) w p.2 (n - j) l.2 u)) 0) n
      (liftWt Dm hh n)
      ((∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, ∑ m ∈ Finset.range (j + 1),
        ((Finset.univ : Finset (DerivativeWord2 m)).card : ℝ≥0) *
          (β p.1 j * ((X.S + 1) ^ m * liftAc X Dm β p.2 (n - j)))) * P hh v w) := by
    rw [Finset.sum_mul]
    refine URepArrP.sum hX _ fun j hj => ?_
    rw [Finset.sum_mul]
    refine URepArrP.sum hX _ fun p hp => ?_
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hB' := URepArrP.liftAArr hX hV hS Q Cc w (by omega : 1 ≤ n - j) hη hη0 hη1 hGr hvr hed hP
      (hC.mono (by omega : p.2 ≤ hh) (by omega))
      (fun l hl => (hreg l hl w).mono (by omega) (by omega) (by omega))
    have hB := fun u => (hB' u).meanArr hX
      ((liftWt_mono Dm (by omega : p.2 ≤ hh) (by omega : n - j ≤ n)).trans hL₀)
    have hCa := fun u => urepArrP_cArr (hC p.1 j (by omega) (by omega)) v u
    have hcomp := fun u => URepArrP.compArr hX hV.hζ hV.hρ hV.hU hS j 0 (hCa u) (hB u)
      (fun l _ => arrSupp_meanArr (arrSupp_liftAArr_pos (Q l.1) (Cc l.1) w p.2
        (by omega : 1 ≤ n - j) l.2 u))
      (fun l _ m α Y z z' => rfl)
      (fun l hl => arrSlowSmooth_meanArr (arrSmooth_liftAArr (Q l.1) (Cc l.1) w (r := j)
        ((hreg l hl w).mono (by omega) (by omega) (by omega)) u))
    have hsum := URepArrP.sum hX (Finset.univ : Finset ι) fun u _ => hcomp u
    refine hsum.mono hX (by omega)
      (max_le (liftWt_mono Dm (by omega : p.1 ≤ hh) (by omega : j ≤ n)) (Nat.zero_le _)) ?_
    have := comp_sum_le j (fun m => ((Finset.univ : Finset (DerivativeWord2 m)).card : ℝ≥0))
      (β p.1 j) (X.S + 1) (liftAc X Dm β p.2 (n - j)) (fun u => P p.1 v u) (fun u => P p.2 u w)
      (P hh v w) (by rw [← hp']; exact hP2 p.1 p.2 v w)
    exact this
  refine ((part1.add hX part2).mono hX le_rfl le_rfl (le_of_eq ?_)).congr fun l _ => ?_
  · unfold srcCc
    ring
  · rfl

/-- The normalization by `(m!)⁻¹` of the sum over the permutations. -/
theorem factorial_norm (m : ℕ) (C : ℝ≥0) :
    Real.toNNReal |((m.factorial : ℝ))⁻¹| *
      (((Finset.univ : Finset (Equiv.Perm (Fin m))).card : ℝ≥0) * C) = C := by
  have hpos : (0 : ℝ) ≤ ((m.factorial : ℝ))⁻¹ := by positivity
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin, abs_of_nonneg hpos,
    Real.toNNReal_inv, Real.toNNReal_natCast, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero m), one_mul]

/-- **The normalized cell source of a monomial field at its centre is graded.** -/
theorem isURepP_cellSource (hX : X.Ok) (hV : V.Ok) (hS : slowC V X ≤ X.S)
    (Q : RealChain → LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (u : ι) {hh n : ℕ} (hn : 1 ≤ n) {η : ℝ}
    (hη : ∀ l ∈ V.W, (Q l.1).η = η) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hGr : ∀ i j, V.IsURepP X (fun l Y _ => (Q l.1).G l.2 Y i j) 0 0 X.Kg)
    (hvr : ∀ k, V.IsURepP X (fun l _ z => Real.sqrt η * (Q l.1).v l.2 z k) 0 0 X.Kd)
    {Θ : ι → ι → ℝ≥0}
    (hed : ∀ (v u : ι) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (k : Fin 2),
      V.IsURepP X (fun l Y z =>
        (((Q l.1).edge v u d).map fun γ => γ.map 1 * γ.coeff α l.2 Y z k).sum) 0 0 (Θ v u))
    {P : ℕ → ι → ι → ℝ≥0} (hP : ∀ hh v w, 1 ≤ hh → ∑ u, Θ v u * P (hh - 1) u w ≤ P hh v w)
    (hP2 : ∀ a b v w, ∑ u, P a v u * P b u w ≤ P (a + b) v w)
    {β : ℕ → ℕ → ℝ≥0} (hC : V.CoeffRepBelowP X Dm Cc P β hh n)
    (hL₀ : liftWt Dm hh n ≤ X.L₀)
    (hreg : ∀ l ∈ V.W, ∀ w, LiftRegular (Q l.1) (Cc l.1) w l.2 hh n (n + Dm + 2)) {m : ℕ}
    (hm : m ≤ n + 1) (I : DerivativeWord2 m) (v : ι) :
    V.IsURepP X (fun l Y z => ((m.factorial : ℝ))⁻¹ *
      liftCellSource (Q l.1) (Cc l.1) (fun _ => monoField u Y I) hh n l.2 Y z v) (n - m)
      (liftWt Dm hh n) (srcCc X Dm β hh n * P hh v u) := by
  have hsrc := URepArrP.srcArr hX hV hS Q Cc u hn hη hη0 hη1 hGr hvr hed hP hP2 hC hL₀ hreg v
  have h : V.IsURepP X (fun l Y z => ∑ σ : Equiv.Perm (Fin m),
      GenSem.srcArr (Q l.1) (Cc l.1) u hh n l.2 v m (I ∘ σ) Y z) (n - m) (liftWt Dm hh n)
      (((Finset.univ : Finset (Equiv.Perm (Fin m))).card : ℝ≥0) *
        (srcCc X Dm β hh n * P hh v u)) :=
    IsURepP.sum_le hX _ fun σ _ => hsrc m (I ∘ σ)
  have h2 := (h.smul hX ((m.factorial : ℝ))⁻¹).mono hX le_rfl le_rfl
    (le_of_eq (factorial_norm m (srcCc X Dm β hh n * P hh v u)))
  exact h2.congr fun l hl Y _ z => by
    rw [liftCellSource_monoField (Q l.1) (Cc l.1) u (hreg l hl u) Y z v I hm]

end UEnv

namespace LiftGenSetup

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ} {D : OCData} {bw : ℝ} {j₀ : ℕ}
  {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {𝒜 : Set RealChain} {ρ : ℝ}
  {edge : RealChain → ConstituentEdges Dm (fun _ : ι => ℝ)} {U : RealChain → Set (Vec 2)}
  {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ} {Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)}

/-- **The coefficient from its source**: if `e_src` represents the normalized cell source, the
transverse inverse `cellInvOf D e_src` represents the coefficient (the second half of
`LiftGenSetup.coeff_step`, for a given source expression). -/
theorem coeff_of_source (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc)
    {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N) {m' : ℕ} (hm : m' ≤ n)
    (I : DerivativeWord2 m') (v u : ι) {e_src : Gen .cell m k}
    (he : (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).URep (fun l Y z => ((m'.factorial : ℝ))⁻¹ *
      liftCellSource (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1)
        (fun _ => monoField u Y I) hh n l.2 Y z v) e_src) :
    (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).URep (fun l Y z => Cc l.1 hh n m' I l.2 Y z v u 1)
      (cellInvOf D e_src) := by
  obtain ⟨hsch, hfs, f, hd, hv, hinv⟩ := he
  have hval : ∀ l ∈ (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).W, ∀ Y ∈ U l.1, ∀ z,
      Cc l.1 hh n m' I l.2 Y z v u 1 =
        transverseInverseSem D m k
          (fun j => if j = transverseIndex k then transversePrimitiveSem k f
            else GenSort.ofTime .cell (TimeLetter.eval D (.const 0)))
          (D.slotStart m k) (GenSort.ofTime .cell (TimeLetter.eval D (.const 0)))
          (D.cellScaleSq m * l.2) (l.1.recenter D (ρ • Y)) z := by
    intro l hl Y hY z
    exact hS.coeff_eq_cellInv hl.1 hhH hn1 hnN hm I v u hY (f := f)
      (fun τ hτ z => hv (l.1, τ) ⟨hl.1, hτ⟩ Y hY z)
      (fun τ hτ z s => (hv (l.1, τ) ⟨hl.1, hτ⟩ Y hY _).symm.trans
        ((hinv (l.1, τ) ⟨hl.1, hτ⟩ Y hY z s).trans (hv (l.1, τ) ⟨hl.1, hτ⟩ Y hY z)))
      l.2 hl.2 z
  refine ⟨isScheduled_cellInvOf D hsch, fromSeed_cellInvOf D hfs, _,
    denotes_cellInvOf D _ _ hd, hval, fun l hl Y hY z s => ?_⟩
  show Cc l.1 hh n m' I l.2 Y (z + s • basisVec (parIdx k)) v u 1 = Cc l.1 hh n m' I l.2 Y z v u 1
  rw [hval l hl Y hY, hval l hl Y hY]
  exact transverseInverseSem_phase D m k _ _ _ _ _ z s

/-- **The graded step of the lift induction.** -/
theorem coeff_stepP (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc) {X : GCtx}
    (hX : X.Ok) (hSl : UEnv.slowC (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁) X ≤ X.S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1) {Θ : ι → ι → ℝ≥0}
    (hed : ∀ (v u : ι) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (c : Fin 2),
      (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURepP X (fun l Y z =>
        (((familyLiftData D m k l.1 ρ (edge l.1)).edge v u d).map
          fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u))
    {P : ℕ → ι → ι → ℝ≥0} (hP : ∀ hh v w, 1 ≤ hh → ∑ u, Θ v u * P (hh - 1) u w ≤ P hh v w)
    (hP2 : ∀ a b v w, ∑ u, P a v u * P b u w ≤ P (a + b) v w) {β : ℕ → ℕ → ℝ≥0}
    {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N)
    (hC : (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).CoeffRepBelowP X Dm Cc P β hh n)
    (hL₀ : UEnv.liftWt Dm hh n ≤ X.L₀) {m' : ℕ} (hm : m' ≤ n) (I : DerivativeWord2 m')
    (v u : ι) :
    (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURepP X (fun l Y z => Cc l.1 hh n m' I l.2 Y z v u 1)
      (n - m') (UEnv.liftWt Dm hh n) (cInvC * UEnv.srcCc X Dm β hh n * P hh v u) := by
  set V := liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁ with hVdef
  have hGr : ∀ a b, V.IsURepP X
      (fun l Y _ => (familyLiftData D m k l.1 ρ (edge l.1)).G l.2 Y a b) 0 0 X.Kg := fun a b =>
    (UEnv.isURepP_metric hX V a b).congr fun _ _ _ _ _ => rfl
  have hvr : ∀ c, V.IsURepP X (fun l _ z => Real.sqrt (D.kap m / D.kap (m - 1)) *
      (familyLiftData D m k l.1 ρ (edge l.1)).v l.2 z c) 0 0 X.Kd := fun c =>
    (UEnv.isURepP_drift hX V (fun l => l.2) (fun _ => rfl) hS.hc.ne' c).congr
      fun _ _ _ _ _ => rfl
  obtain ⟨e_src, he, hsf, hnorm⟩ := UEnv.isURepP_cellSource hX hS.ok hSl
    (fun A => familyLiftData D m k A ρ (edge A)) Cc u hn1 (η := D.kap m / D.kap (m - 1))
    (fun _ _ => rfl) hη0 hη1 hGr hvr hed hP hP2 hC hL₀
    (fun l hl w => hS.reg l.1 hl.1 hh hhH n hn1 hnN l.2 hl.2 w) (by omega : m' ≤ n + 1) I v
  have hc := hS.coeff_of_source hhH hn1 hnN hm I v u he
  obtain ⟨hsf', hnorm'⟩ := prof_cellInvOf hX D hsf hnorm
  refine ⟨cellInvOf D e_src, hc, hsf', fun t ht => ?_⟩
  rw [mul_assoc]
  exact hnorm' t ht

end LiftGenSetup
end

/-! **Ledger: the lift coefficients are graded.** The quantitative form of
`LiftGenSetup.coeffRep`: every lift coefficient `(hh, n)` of a lift setup whose source-edge
aggregates have sizes `Θ v u` is graded with
* degree `n`: the entry of tested order `m'` has received at most `n - m'` slow derivatives;
* fast weight `liftWt D_m hh n = n + hh(D_m + 1)`;
* size `liftB X D_m hh n · pathW Θ hh v u`, where `pathW Θ hh = Θ^hh` is the matrix power of the
  edge sizes (the sum over the paths of `hh` edges from `u` to `v` of the products of their
  sizes: each edge of a path contributes exactly once), and the constant `liftB` is defined by
  recursion on the rank `hh + n` from the constants `S, K_g, K_d` of the context only. -/

section
open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.Majorant

/-- The path weight of grade `hh` of the edge sizes: the matrix power `Θ^hh`. -/
def pathW {ι : Type} [Fintype ι] [DecidableEq ι] (Θ : ι → ι → ℝ≥0) (hh : ℕ) (v u : ι) : ℝ≥0 :=
  ((Matrix.of Θ) ^ hh) v u

section PathW

variable {ι : Type} [Fintype ι] [DecidableEq ι] (Θ : ι → ι → ℝ≥0)

theorem pathW_zero (v u : ι) : pathW Θ 0 v u = if v = u then 1 else 0 := by
  simp [pathW, Matrix.one_apply]

theorem pathW_succ (hh : ℕ) (v w : ι) (h : 1 ≤ hh) :
    ∑ u, Θ v u * pathW Θ (hh - 1) u w ≤ pathW Θ hh v w := by
  obtain ⟨h', rfl⟩ : ∃ h', hh = h' + 1 := ⟨hh - 1, by omega⟩
  refine le_of_eq ?_
  simp only [pathW, Nat.add_sub_cancel]
  rw [pow_succ', Matrix.mul_apply]
  rfl

theorem pathW_add (a b : ℕ) (v w : ι) :
    ∑ u, pathW Θ a v u * pathW Θ b u w ≤ pathW Θ (a + b) v w := by
  refine le_of_eq ?_
  simp only [pathW]
  rw [pow_add, Matrix.mul_apply]

end PathW

/-- The size constants of the lift coefficients up to the rank `r`. -/
def liftBfun (X : GCtx) (Dm : ℕ) : ℕ → ℕ → ℕ → ℝ≥0
  | 0, hh, n => if hh = 0 ∧ n = 0 then 1 else 0
  | r + 1, hh, n =>
      if hh + n ≤ r then liftBfun X Dm r hh n
      else cInvC * UEnv.srcCc X Dm (liftBfun X Dm r) hh n

/-- **The size constant of the lift coefficient `(hh, n)`.** -/
def liftB (X : GCtx) (Dm hh n : ℕ) : ℝ≥0 := liftBfun X Dm (hh + n) hh n

namespace LiftGenSetup

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ} {D : OCData} {bw : ℝ} {j₀ : ℕ}
  {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {𝒜 : Set RealChain} {ρ : ℝ}
  {edge : RealChain → ConstituentEdges Dm (fun _ : ι => ℝ)} {U : RealChain → Set (Vec 2)}
  {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ} {Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)}

/-- The graded coefficients up to the rank `r`. -/
theorem coeffRepP_aux (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc) {X : GCtx}
    (hX : X.Ok) (hSl : UEnv.slowC (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁) X ≤ X.S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1) {Θ : ι → ι → ℝ≥0}
    (hed : ∀ (v u : ι) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (c : Fin 2),
      (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURepP X (fun l Y z =>
        (((familyLiftData D m k l.1 ρ (edge l.1)).edge v u d).map
          fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u))
    (hL₀ : UEnv.liftWt Dm H N ≤ X.L₀) :
    ∀ r hh n, hh + n ≤ r → hh ≤ H → ∀ m' (α : DerivativeWord2 m') (v u : ι),
      (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURepP X
        (fun l Y z => Cc l.1 hh n m' α l.2 Y z v u 1) (n - m') (UEnv.liftWt Dm hh n)
        (liftBfun X Dm r hh n * pathW Θ hh v u) := by
  set V := liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁ with hVdef
  have hzero : ∀ {hh n m' : ℕ} (α : DerivativeWord2 m') (v u : ι) (C : ℝ≥0),
      (∀ A ∈ 𝒜, ∀ τ ∈ Set.Icc t₀ t₁, ∀ Y ∈ U A, ∀ z, Cc A hh n m' α τ Y z v u 1 = 0) →
      V.IsURepP X (fun l Y z => Cc l.1 hh n m' α l.2 Y z v u 1) (n - m') (UEnv.liftWt Dm hh n)
        C := fun α v u C h =>
    ((UEnv.isURepP_zero hX V _ _).mono hX le_rfl le_rfl (by simp)).congr fun l hl Y hY z =>
      h l.1 hl.1 l.2 hl.2 Y hY z
  intro r
  induction r with
  | zero =>
    intro hh n hr hhH m' α v u
    obtain rfl : hh = 0 := by omega
    obtain rfl : n = 0 := by omega
    by_cases hm0 : m' = 0
    · subst hm0
      refine (((UEnv.isURepP_const hX V (if v = u then 1 else 0)).mono hX (Nat.zero_le _)
        (Nat.zero_le _) (le_of_eq ?_))).congr fun l hl Y hY z => hS.coeff_id hl.1 hl.2 α hY z v u
      rw [pathW_zero]
      simp only [liftBfun, and_self, ↓reduceIte, one_mul]
      split_ifs <;> simp
    · exact hzero α v u _ fun A hA τ _ Y hY z => by
        rw [(hS.loc A hA).zeroM 0 hhH 0 m' (by omega) α τ Y hY z v u]; simp
  | succ r ih =>
    intro hh n hr hhH m' α v u
    by_cases hle : hh + n ≤ r
    · simp only [liftBfun, hle, ↓reduceIte]
      exact ih hh n hle hhH m' α v u
    · simp only [liftBfun, hle, ↓reduceIte]
      by_cases hnN : N < n
      · exact hzero α v u _ fun A hA τ _ Y hY z => by
          rw [(hS.loc A hA).zeroN hh hhH n hnN m' α τ Y hY z v u]; simp
      by_cases hn0 : n = 0
      · subst hn0
        exact hzero α v u _ fun A hA τ _ Y hY z => by
          rw [(hS.loc A hA).zero0 hh (by omega) hhH m' α τ Y hY z v u]; simp
      by_cases hm : m' ≤ n
      · have hC : V.CoeffRepBelowP X Dm Cc (pathW Θ) (liftBfun X Dm r) hh n :=
          fun hh' k' h1 h2 m'' α' v' u' => ih hh' k' (by omega) (by omega) m'' α' v' u'
        exact hS.coeff_stepP hX hSl hη0 hη1 hed (fun hh v w h => pathW_succ Θ hh v w h)
          (pathW_add Θ) hhH (by omega) (by omega) hC
          ((UEnv.liftWt_mono Dm hhH (by omega : n ≤ N)).trans hL₀) hm α v u
      · exact hzero α v u _ fun A hA τ _ Y hY z => by
          rw [(hS.loc A hA).zeroM hh hhH n m' (by omega) α τ Y hY z v u]; simp

/-- **Every lift coefficient is graded**, with a size constant depending only on the constants of
the context, times the path weight of the edge sizes. -/
theorem coeffRepP (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc) {X : GCtx}
    (hX : X.Ok) (hSl : UEnv.slowC (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁) X ≤ X.S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1) {Θ : ι → ι → ℝ≥0}
    (hed : ∀ (v u : ι) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (c : Fin 2),
      (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURepP X (fun l Y z =>
        (((familyLiftData D m k l.1 ρ (edge l.1)).edge v u d).map
          fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u))
    (hL₀ : UEnv.liftWt Dm H N ≤ X.L₀) {hh : ℕ} (hhH : hh ≤ H) (n m' : ℕ)
    (α : DerivativeWord2 m') (v u : ι) :
    (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURepP X
      (fun l Y z => Cc l.1 hh n m' α l.2 Y z v u 1) (n - m') (UEnv.liftWt Dm hh n)
      (liftB X Dm hh n * pathW Θ hh v u) :=
  hS.coeffRepP_aux hX hSl hη0 hη1 hed hL₀ (hh + n) hh n le_rfl hhH m' α v u

end LiftGenSetup
end

end AVRegularity.Providers.GenSem
end
