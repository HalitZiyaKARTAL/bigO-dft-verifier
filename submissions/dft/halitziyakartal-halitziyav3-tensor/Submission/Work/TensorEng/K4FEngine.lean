import Submission.Work.TensorEng.EngOf
import Submission.Work.TensorProto.K4FRate

/-!
# The engine theorem of the 2730-fold tensor power of a raw K4 (keep303, all-fresh) unit

Interface for the end-to-end assembly: any bundled certified unit `A` on 73 label coordinates whose paid ranks and
target ranks are the raw P4-L-fresh inventories (`K4F.PK4F`, `K4F.TK4F`; p3-port's `rawHist` / `rawTgt`) gives
OpenAI's `hills_program` shape at every `zE ∈ (1 - 327/125000, 1]` (`327/125000 = 0.002616`) (`k4f_engine`): the unit is tensored 2730 times,
completed to `14^2730` and split at `13^2730` (`EngOf.tensor_engine`), with the moment fact `K4F.strict`.

-- changed for the tensor-power extension (26159999/10000000000); see Submission.lean
-/

set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace TensorEng
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.MX OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty Matrix Finset
open TensorProto (mom tens tpow padT strictT strictP)

noncomputable section

namespace BU

lemma card_σ_pow (A : BU) (n : ℕ) : Fintype.card (A.pow n).σ = Fintype.card A.σ ^ (n + 1) := by
  induction n with
  | zero =>
    show Fintype.card A.σ = Fintype.card A.σ ^ (0 + 1)
    rw [zero_add, pow_one]
  | succ n ih =>
    show Fintype.card ((A.pow n).σ × A.σ) = _
    rw [Fintype.card_prod, ih]
    ring

end BU

lemma K4F_mem_ofHist_of {l : List (ℕ × ℕ)} {b : ℕ × ℕ} (hb : b ∈ l) (h : 0 < b.2) :
    b.1 ∈ TensorProto.K4F.ofHist l := by
  induction l with
  | nil => simp at hb
  | cons a l ih =>
    have e : TensorProto.K4F.ofHist (a :: l) = Multiset.replicate a.2 a.1 + TensorProto.K4F.ofHist l := by
      simp [TensorProto.K4F.ofHist]
    rw [e, Multiset.mem_add]
    rcases List.mem_cons.1 hb with h' | h'
    · subst h'; exact Or.inl (Multiset.mem_replicate.2 ⟨by omega, rfl⟩)
    · exact Or.inr (ih h')

/-- Multiplicities of a histogram multiset. -/
lemma K4F_count_ofHist (l : List (ℕ × ℕ)) (r : ℕ) :
    (TensorProto.K4F.ofHist l).count r = BlockAccounting.histFn l r := by
  induction l with
  | nil => simp [TensorProto.K4F.ofHist, BlockAccounting.histFn]
  | cons b l ih =>
    have e : TensorProto.K4F.ofHist (b :: l) = Multiset.replicate b.2 b.1 + TensorProto.K4F.ofHist l := by
      simp [TensorProto.K4F.ofHist]
    rw [e, Multiset.count_add, ih, Multiset.count_replicate]
    unfold BlockAccounting.histFn
    rw [List.filter_cons]
    by_cases h : b.1 = r
    · subst h; simp [Nat.add_comm]
    · simp [h, Ne.symm h]

/-- The paid ranks of a unit from its word histogram. -/
lemma BU.ranks_eq_of_hist (A : BU) (l : List (ℕ × ℕ))
    (h : ∀ r, GWord.hist A.u.wd r = BlockAccounting.histFn l r) : A.ranks = TensorProto.K4F.ofHist l := by
  ext r
  rw [K4F_count_ofHist, ← h, hist_eq_count]
  exact Multiset.coe_count r _

/-- The target ranks of a unit from the counts of its live roles. -/
lemma BU.tgts_eq_of_card (A : BU) (l : List (ℕ × ℕ))
    (h : ∀ r, (Finset.univ.filter fun s : A.σ => A.u.tr s = r).card = BlockAccounting.histFn l r) :
    A.tgts = TensorProto.K4F.ofHist l := by
  ext r
  rw [K4F_count_ofHist, ← h, card_filter_tr]
  all_goals rfl

universe u

/-- **The tensor engine of the raw K4 unit**, saving `327/125000 = 0.002616` at the rate point. -/
theorem k4f_engine (A : BU) (hPr : A.ranks = TensorProto.K4F.ofHist TensorProto.K4F.PK4F)
    (hTg : A.tgts = TensorProto.K4F.ofHist TensorProto.K4F.TK4F) (hR : A.RanksOK) (hT : A.TgtsOK)
    (hα : Fintype.card A.α = 73) (hσ : 0 < Fintype.card A.σ) {zE : ℝ}
    (h12 : 1 - (327 : ℝ) / 125000 < zE) (hzE : zE ≤ 1) (m : Bool) (cl : Paint) {ι : Type u} (k : ι → ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope zE (k i)) := by
  have hmom := TensorProto.K4F.strict
  rw [← hPr, ← hTg] at hmom
  have hL : 14 ^ 2730 ≤ Fintype.card (A.pow 2729).α := by
    rw [BU.card_pow, hα]
    exact Nat.pow_le_pow_left (by norm_num) _
  have hJ : 0 < 13 ^ 2730 := by positivity
  have hJL : 13 ^ 2730 < 14 ^ 2730 := Nat.pow_lt_pow_left (by norm_num) (by norm_num)
  have hσ' : 0 < Fintype.card (A.pow 2729).σ := by
    rw [BU.card_σ_pow]
    exact pow_pos hσ _
  have h3 : 3 ≤ Fintype.card (A.pow 2729).α := by
    rw [BU.card_pow, hα]
    calc 3 ≤ 73 := by norm_num
      _ ≤ 73 ^ (2729 + 1) := Nat.le_self_pow (by norm_num) 73
  have hatt : 14 ^ 2730 ∈ strictT A.tgts (2729 + 1) (14 ^ 2730) := by
    rw [hTg]
    have h4 : 4 ∈ TensorProto.K4F.ofHist TensorProto.K4F.TK4F :=
      K4F_mem_ofHist_of (b := (4, 234)) (by decide) (by norm_num)
    exact TensorProto.mem_padT (TensorProto.pow_mem_tpow h4 (2729 + 1))
      (Nat.pow_le_pow_left (by norm_num) _)
  exact A.tensor_engine 2729 (13 ^ 2730) (14 ^ 2730) hL hJ hJL hR hT hσ' h3 hatt hmom (by norm_num) h12 hzE
    m cl k v

/-- Paid ranks of a proper word are `≥ 1` and `< u`. -/
lemma rk_bounds_of_proper {α ρ : Type*} {u : ℕ} {w : GWord α ρ} (hP : w.Proper u) {r : ℕ}
    (hr : r ∈ w.filterMap GMove.rk?) : 1 ≤ r ∧ r < u := by
  obtain ⟨mv, hmv, hmr⟩ := List.mem_filterMap.1 hr
  have h := hP mv hmv
  cases mv with
  | old mv =>
    cases mv with
    | localM g => cases hmr
    | shift l z => cases hmr
    | block l rk z ind =>
      have e : rk = r := Option.some.inj hmr
      subst e
      exact h
  | perm l G => cases hmr
  | phase l z c => cases hmr

/-- **The tensor engine from a RAW certificate** in the shape of p3-port's `rawCert` (one copy): a word on 73 label
coordinates with block targets whose live target ranks and paid ranks are the raw P4-L-fresh inventories. -/
theorem k4f_engine_of_raw {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] [Fintype σ]
    [DecidableEq σ] (e : σ → ρ) (tr : σ → ℕ) (tz : ∀ l, Fin (tr l) → Space α) (wd : GWord α ρ)
    (he : Function.Injective e) (hind : ∀ l, LinearIndependent F (tz l)) (hP : wd.Proper (Fintype.card α))
    (hw : GLiveKernelM e (fun l => blockMat (tz l)) wd) (hα : Fintype.card α = 73) (hσ : 0 < Fintype.card σ)
    (htr : ∀ l, 1 ≤ tr l ∧ tr l ≤ 73)
    (hcnt : ∀ r, (Finset.univ.filter fun l => tr l = r).card = BlockAccounting.histFn TensorProto.K4F.TK4F r)
    (hhist : ∀ r, wd.hist r = BlockAccounting.histFn TensorProto.K4F.PK4F r) {zE : ℝ}
    (h12 : 1 - (327 : ℝ) / 125000 < zE) (hzE : zE ≤ 1) (m : Bool) (cl : Paint) {ι : Type u} (k : ι → ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope zE (k i)) := by
  let A : BU := ⟨α, ρ, σ, ⟨e, he, tr, tz, hind, wd, hw⟩⟩
  have hR : A.RanksOK := fun r hr => rk_bounds_of_proper hP hr
  have hT : A.TgtsOK := fun l => ⟨(htr l).1, by show tr l ≤ Fintype.card α; rw [hα]; exact (htr l).2⟩
  exact k4f_engine A (BU.ranks_eq_of_hist A _ hhist) (BU.tgts_eq_of_card A _ hcnt) hR hT hα hσ h12 hzE m cl k v

/-! ### `G` copies of the unit

All multiplicities of the raw inventories scaled by `G`: the strictified inventories are scaled by `G ^ v`
(`tpow_nsmul`, `strictP_nsmul`, `strictT_nsmul`) and so are their moments (`mom_nsmul`); the moment fact transfers. -/

lemma bind_nsmul_left (k : ℕ) (s : Multiset ℕ) (f : ℕ → Multiset ℕ) : (k • s).bind f = k • s.bind f := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, Multiset.add_bind, ih, succ_nsmul]

lemma bind_nsmul_right (k : ℕ) (s : Multiset ℕ) (f : ℕ → Multiset ℕ) :
    s.bind (fun a => k • f a) = k • s.bind f := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => rw [Multiset.cons_bind, Multiset.cons_bind, ih, nsmul_add]

lemma tens_nsmul (k k' : ℕ) (A B : Multiset ℕ) : tens (k • A) (k' • B) = (k * k') • tens A B := by
  unfold TensorProto.tens
  rw [bind_nsmul_left]
  have h : (fun a => Multiset.map (fun b => a * b) (k' • B)) = fun a => k' • Multiset.map (fun b => a * b) B := by
    funext a
    rw [Multiset.map_nsmul]
  rw [h, bind_nsmul_right, smul_smul]

lemma tpow_nsmul (k : ℕ) (A : Multiset ℕ) (v : ℕ) : tpow (k • A) v = (k ^ v) • tpow A v := by
  induction v with
  | zero => simp [TensorProto.tpow]
  | succ v ih =>
    show tens (tpow (k • A) v) (k • A) = (k ^ (v + 1)) • tens (tpow A v) A
    rw [ih, tens_nsmul, pow_succ]

lemma strictP_nsmul (k : ℕ) (T P : Multiset ℕ) (v J L : ℕ) :
    strictP (k • T) (k • P) v J L = (k ^ v) • strictP T P v J L := by
  unfold TensorProto.strictP TensorProto.splitAll TensorProto.comp
  rw [tpow_nsmul, tpow_nsmul, bind_nsmul_left, ← nsmul_add, bind_nsmul_left]

lemma strictT_nsmul (k : ℕ) (T : Multiset ℕ) (v L : ℕ) :
    strictT (k • T) v L = (k ^ v) • strictT T v L := by
  unfold TensorProto.strictT TensorProto.padT
  rw [tpow_nsmul, Multiset.map_nsmul]

lemma mom_nsmul (t : ℝ) (k : ℕ) (s : Multiset ℕ) : mom t (k • s) = k * mom t s := by
  unfold TensorProto.mom
  rw [Multiset.map_nsmul, Multiset.sum_nsmul, nsmul_eq_mul]

/-- The paid ranks of a unit from its word histogram, `G` copies. -/
lemma BU.ranks_eq_of_histG (A : BU) (l : List (ℕ × ℕ)) (G : ℕ)
    (h : ∀ r, GWord.hist A.u.wd r = G * BlockAccounting.histFn l r) :
    A.ranks = G • TensorProto.K4F.ofHist l := by
  ext r
  rw [Multiset.count_nsmul, K4F_count_ofHist, ← h, hist_eq_count]
  exact Multiset.coe_count r _

/-- The target ranks of a unit from the counts of its live roles, `G` copies. -/
lemma BU.tgts_eq_of_cardG (A : BU) (l : List (ℕ × ℕ)) (G : ℕ)
    (h : ∀ r, (Finset.univ.filter fun s : A.σ => A.u.tr s = r).card = G * BlockAccounting.histFn l r) :
    A.tgts = G • TensorProto.K4F.ofHist l := by
  ext r
  rw [Multiset.count_nsmul, K4F_count_ofHist, ← h, card_filter_tr]
  all_goals rfl

/-- **The tensor engine of `G` copies of the raw K4 unit**, saving `327/125000 = 0.002616` at the rate point. -/
theorem k4f_engine_G (A : BU) (G : ℕ) (hG : 1 ≤ G)
    (hPr : A.ranks = G • TensorProto.K4F.ofHist TensorProto.K4F.PK4F)
    (hTg : A.tgts = G • TensorProto.K4F.ofHist TensorProto.K4F.TK4F) (hR : A.RanksOK) (hT : A.TgtsOK)
    (hα : Fintype.card A.α = 73) (hσ : 0 < Fintype.card A.σ) {zE : ℝ}
    (h12 : 1 - (327 : ℝ) / 125000 < zE) (hzE : zE ≤ 1) (m : Bool) (cl : Paint) {ι : Type u} (k : ι → ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope zE (k i)) := by
  have hmom0 := TensorProto.K4F.strict
  have hGv : (0 : ℝ) ≤ ((G ^ 2730 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmom : mom (1 - ((327:ℝ)/125000)) (strictP A.tgts A.ranks (2729 + 1) (13 ^ 2730) (14 ^ 2730))
      ≤ mom (1 - ((327:ℝ)/125000)) (strictT A.tgts (2729 + 1) (14 ^ 2730)) := by
    rw [hPr, hTg, strictP_nsmul, strictT_nsmul, mom_nsmul, mom_nsmul]
    exact mul_le_mul_of_nonneg_left hmom0 hGv
  have hL : 14 ^ 2730 ≤ Fintype.card (A.pow 2729).α := by
    rw [BU.card_pow, hα]
    exact Nat.pow_le_pow_left (by norm_num) _
  have hJ : 0 < 13 ^ 2730 := by positivity
  have hJL : 13 ^ 2730 < 14 ^ 2730 := Nat.pow_lt_pow_left (by norm_num) (by norm_num)
  have hσ' : 0 < Fintype.card (A.pow 2729).σ := by
    rw [BU.card_σ_pow]
    exact pow_pos hσ _
  have h3 : 3 ≤ Fintype.card (A.pow 2729).α := by
    rw [BU.card_pow, hα]
    calc 3 ≤ 73 := by norm_num
      _ ≤ 73 ^ (2729 + 1) := Nat.le_self_pow (by norm_num) 73
  have hatt : 14 ^ 2730 ∈ strictT A.tgts (2729 + 1) (14 ^ 2730) := by
    rw [hTg, strictT_nsmul, Multiset.mem_nsmul_of_ne_zero (pow_ne_zero _ (by omega))]
    have h4 : 4 ∈ TensorProto.K4F.ofHist TensorProto.K4F.TK4F :=
      K4F_mem_ofHist_of (b := (4, 234)) (by decide) (by norm_num)
    exact TensorProto.mem_padT (TensorProto.pow_mem_tpow h4 (2729 + 1))
      (Nat.pow_le_pow_left (by norm_num) _)
  exact A.tensor_engine 2729 (13 ^ 2730) (14 ^ 2730) hL hJ hJL hR hT hσ' h3 hatt hmom (by norm_num) h12 hzE
    m cl k v

/-- **The tensor engine from a RAW certificate of `G` copies** (p3-port's `rawCert` shape): a word on 73 label
coordinates with block targets whose live target ranks and paid ranks are `G` copies of the raw P4-L-fresh
inventories. -/
theorem k4f_engine_of_rawG {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] [Fintype σ]
    [DecidableEq σ] (e : σ → ρ) (tr : σ → ℕ) (tz : ∀ l, Fin (tr l) → Space α) (wd : GWord α ρ) (G : ℕ)
    (he : Function.Injective e) (hind : ∀ l, LinearIndependent F (tz l)) (hP : wd.Proper (Fintype.card α))
    (hw : GLiveKernelM e (fun l => blockMat (tz l)) wd) (hG : 1 ≤ G) (hα : Fintype.card α = 73)
    (htr : ∀ l, 1 ≤ tr l ∧ tr l ≤ 73)
    (hcnt : ∀ r, (Finset.univ.filter fun l => tr l = r).card = G * BlockAccounting.histFn TensorProto.K4F.TK4F r)
    (hhist : ∀ r, wd.hist r = G * BlockAccounting.histFn TensorProto.K4F.PK4F r) {zE : ℝ}
    (h12 : 1 - (327 : ℝ) / 125000 < zE) (hzE : zE ≤ 1) (m : Bool) (cl : Paint) {ι : Type u} (k : ι → ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope zE (k i)) := by
  let A : BU := ⟨α, ρ, σ, ⟨e, he, tr, tz, hind, wd, hw⟩⟩
  have hR : A.RanksOK := fun r hr => rk_bounds_of_proper hP hr
  have hT : A.TgtsOK := fun l => ⟨(htr l).1, by show tr l ≤ Fintype.card α; rw [hα]; exact (htr l).2⟩
  have hσ : 0 < Fintype.card σ := by
    have h1 := Finset.card_le_univ (Finset.univ.filter fun l : σ => tr l = 73)
    rw [hcnt 73, show BlockAccounting.histFn TensorProto.K4F.TK4F 73 = 224 from rfl] at h1
    omega
  exact k4f_engine_G A G hG (BU.ranks_eq_of_histG A _ G hhist) (BU.tgts_eq_of_cardG A _ G hcnt) hR hT hα hσ
    h12 hzE m cl k v

end

end TensorEng
