import Submission.Work.Mixed.Bridge.CoreF
import Submission.Work.Mixed.HeadM3

/-!
# The full cut of heads of three ranks: the four-target rule and the bridge to the mixed engine

The full-cut bridge of Work/Mixed/Bridge/CoreF.lean for a heads-first certificate whose heads come in three groups
(`L2`, `L3`, `L4`, of ranks 16, 32 and 48, each head the block of ALL the lines `S l` of its frame `A l`):
* `MX.Rule.fourTarget`, `MX.Rule.fourTarget_rateQ`: the mixed rule with four job sizes (`card α`, `card α - 16`,
  `card α - 32`, `card α - 48`) and its rate fact from the moment form;
* `Eng.bridge_fourTarget`: `BridgeHyp` for an engine whose live roles have those four target ranks;
* `fullEng3`, `full_bundle3`, `full_engine3`: the engine of the cut word (`MX.cut_heads_full3`, then every block of
  rank 25 split into ranks 24 and 1), its rule, `BridgeHyp`, rate fact, and the engine theorem (Theorem 1G,
  `Eng.engine_seam_final`).
-- changed for the head-cut extension (1959540039/1000000000000); see Submission.lean
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving

namespace MX
namespace Rule

/-- The mixed rule of a cut word with four targets: `W` arrays of `m` axes; `H1`, `H2`, `H3` of them (the cut heads)
with targets `k1`, `k2`, `k3`, the others with the full target `m`; separated (`rmax < k3`). -/
def fourTarget (m k1 k2 k3 W H1 H2 H3 P rmax : ℕ) (rk : Fin P → ℕ) (hrk1 : ∀ j, 1 ≤ rk j)
    (hrk : ∀ j, rk j ≤ rmax) (hsep : rmax < k3) (h32 : k3 ≤ k2) (h21 : k2 ≤ k1) (h1m : k1 ≤ m) (h2 : 2 ≤ k3)
    (hH : 1 ≤ H3) : Rule where
  K := 4
  kr := ![m, k1, k2, k3]
  Wk := ![W - H1 - H2 - H3, H1, H2, H3]
  m := m
  P := P
  rk := rk
  kmin := k3
  rmax := rmax
  kmin_le := by intro k; fin_cases k <;> (simp; try omega)
  kr_le := by intro k; fin_cases k <;> (simp; try omega)
  rk_pos := hrk1
  rk_le := hrk
  sep := hsep
  two_le_kmin := h2
  kmin_att := ⟨3, by simp, by simpa using hH⟩

/-- The rate fact of the four-target rule from its normalised (moment) form, by histogram of the paid ranks. -/
theorem fourTarget_rateQ_hist {m k1 k2 k3 W H1 H2 H3 P rmax : ℕ} {rk : Fin P → ℕ} (hrk1 : ∀ j, 1 ≤ rk j)
    (hrk : ∀ j, rk j ≤ rmax) (hsep : rmax < k3) (h32 : k3 ≤ k2) (h21 : k2 ≤ k1) (h1m : k1 ≤ m) (h2 : 2 ≤ k3)
    (hH : 1 ≤ H3) {z : ℝ}
    (h : ∑ r ∈ Finset.range (rmax + 1), ((Finset.univ.filter fun j => rk j = r).card : ℝ) * ((r : ℝ) / m) ^ z
      ≤ ((W - H1 - H2 - H3 : ℕ) : ℝ) + (H1 : ℝ) * ((k1 : ℝ) / m) ^ z + (H2 : ℝ) * ((k2 : ℝ) / m) ^ z
        + (H3 : ℝ) * ((k3 : ℝ) / m) ^ z) :
    (fourTarget m k1 k2 k3 W H1 H2 H3 P rmax rk hrk1 hrk hsep h32 h21 h1m h2 hH).RateQ z 1 := by
  have hm : (m : ℝ) ≠ 0 := by
    have : 0 < m := by omega
    exact_mod_cast this.ne'
  have e : ∑ j : Fin P, ((rk j : ℝ) / m) ^ z = ∑ r ∈ Finset.range (rmax + 1),
      ((Finset.univ.filter fun j : Fin P => rk j = r).card : ℝ) * ((r : ℝ) / m) ^ z :=
    (fourTarget m k1 k2 k3 W H1 H2 H3 P rmax rk hrk1 hrk hsep h32 h21 h1m h2 hH).sum_rk_hist
      (fun r => ((r : ℝ) / m) ^ z)
  have key : ∑ j : Fin P, ((rk j : ℝ) / m) ^ z ≤
      ∑ k : Fin 4, ((![W - H1 - H2 - H3, H1, H2, H3] k : ℕ) : ℝ) * (((![m, k1, k2, k3] k : ℕ) : ℝ) / m) ^ z := by
    rw [Fin.sum_univ_four, e]
    show _ ≤ ((W - H1 - H2 - H3 : ℕ) : ℝ) * ((m : ℝ) / m) ^ z + (H1 : ℝ) * ((k1 : ℝ) / m) ^ z
      + (H2 : ℝ) * ((k2 : ℝ) / m) ^ z + (H3 : ℝ) * ((k3 : ℝ) / m) ^ z
    rw [div_self hm, Real.one_rpow, mul_one]
    linarith [h]
  exact rateQ_of_normalized _ key

end Rule
end MX

namespace RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ] (E : Eng α ρ σ)

/-- **`BridgeHyp` for the four-target rule**: every live role has target rank `mx` (full), `k1`, `k2` or `k3` (cut),
the four distinct, with `H1`, `H2`, `H3` roles of the three cut ranks. -/
theorem bridge_fourTarget (k1 k2 k3 rmax H1 H2 H3 : ℕ) (hrk1 : ∀ j : Fin E.nB, 1 ≤ E.rkI j)
    (hrk : ∀ j : Fin E.nB, E.rkI j ≤ rmax) (hsep : rmax < k3) (h32 : k3 < k2) (h21 : k2 < k1) (h1m : k1 < E.mx)
    (h2 : 2 ≤ k3) (hH : 1 ≤ H3)
    (htq4 : ∀ x, x < E.W → E.tq x = E.mx ∨ E.tq x = k1 ∨ E.tq x = k2 ∨ E.tq x = k3)
    (hH1 : ((range E.W).filter (fun x => E.tq x = k1)).card = H1)
    (hH2 : ((range E.W).filter (fun x => E.tq x = k2)).card = H2)
    (hH3 : ((range E.W).filter (fun x => E.tq x = k3)).card = H3) :
    E.BridgeHyp (MX.Rule.fourTarget E.mx k1 k2 k3 E.W H1 H2 H3 E.nB rmax (fun j => E.rkI j) hrk1 hrk hsep
        h32.le h21.le h1m.le h2 hH)
      (fun x => (if E.tq x = k1 then 1 else if E.tq x = k2 then 2 else if E.tq x = k3 then 3 else 0 : Fin 4)) k3 := by
  refine ⟨rfl, rfl, fun j => rfl, fun x hx => ?_, fun k => ?_, rfl⟩
  · show E.tq x = (![E.mx, k1, k2, k3] : Fin 4 → ℕ)
      (if E.tq x = k1 then 1 else if E.tq x = k2 then 2 else if E.tq x = k3 then 3 else 0)
    rcases htq4 x hx with h | h | h | h
    · have n1 : E.tq x ≠ k1 := by omega
      have n2 : E.tq x ≠ k2 := by omega
      have n3 : E.tq x ≠ k3 := by omega
      rw [if_neg n1, if_neg n2, if_neg n3, h]; rfl
    · rw [if_pos h, h]; rfl
    · have n1 : E.tq x ≠ k1 := by omega
      rw [if_neg n1, if_pos h, h]; rfl
    · have n1 : E.tq x ≠ k1 := by omega
      have n2 : E.tq x ≠ k2 := by omega
      rw [if_neg n1, if_neg n2, if_pos h, h]; rfl
  · -- the typ map takes value `k` exactly on the roles of the corresponding target rank
    let typ : ℕ → Fin 4 := fun x =>
      if E.tq x = k1 then 1 else if E.tq x = k2 then 2 else if E.tq x = k3 then 3 else 0
    have c1 : ((range E.W).filter (fun x => typ x = 1)).card = H1 := by
      rw [← hH1]; congr 1; apply Finset.filter_congr; intro x hx
      simp only [typ]
      split_ifs <;> constructor <;> intro h <;>
        first | rfl | assumption | exact absurd h (by decide) | (exfalso; omega)
    have c2 : ((range E.W).filter (fun x => typ x = 2)).card = H2 := by
      rw [← hH2]; congr 1; apply Finset.filter_congr; intro x hx
      simp only [typ]
      split_ifs <;> constructor <;> intro h <;>
        first | rfl | assumption | exact absurd h (by decide) | (exfalso; omega)
    have c3 : ((range E.W).filter (fun x => typ x = 3)).card = H3 := by
      rw [← hH3]; congr 1; apply Finset.filter_congr; intro x hx
      simp only [typ]
      split_ifs <;> constructor <;> intro h <;>
        first | rfl | assumption | exact absurd h (by decide) | (exfalso; omega)
    have hsum : ∑ k : Fin 4, ((range E.W).filter (fun x => typ x = k)).card = E.W := by
      rw [← Finset.card_eq_sum_card_fiberwise (f := typ) (s := range E.W) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
      simp
    rw [Fin.sum_univ_four, c1, c2, c3] at hsum
    fin_cases k
    · exact (by intro a b c d w hw; omega : ∀ a b c d w : ℕ, a + b + c + d = w → a = w - b - c - d) _ _ _ _ _ hsum
    · exact c1
    · exact c2
    · exact c3

end Eng
end
end RAM

namespace PB
open Binary Matrix Finset GF MX RAM
noncomputable section

universe U

section CutF3
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- **The full-cut engine of three head groups**: word `fullWord .. 24 1 body` (heads removed, free shifts, every
block of rank 25 split into ranks 24 and 1), targets `cutTgt (L2 ++ L3 ++ L4) A S`. -/
def fullEng3 (e : σ → ρ) (he : Function.Injective e) (L2 L3 L4 : List σ) (hL : (L2 ++ L3 ++ L4).Nodup)
    (z2 : σ → Fin 16 → Space α) (z3 : σ → Fin 32 → Space α) (z4 : σ → Fin 48 → Space α)
    (ind2 : ∀ l, LinearIndependent F (z2 l)) (ind3 : ∀ l, LinearIndependent F (z3 l))
    (ind4 : ∀ l, LinearIndependent F (z4 l)) (A : σ → OBase α) (S : σ → Finset α)
    (hz2 : ∀ l ∈ L2, ∀ x, bph (z2 l) x = bph ((A l).fam (S l)) x)
    (hz3 : ∀ l ∈ L3, ∀ x, bph (z3 l) x = bph ((A l).fam (S l)) x)
    (hz4 : ∀ l ∈ L4, ∀ x, bph (z4 l) x = bph ((A l).fam (S l)) x)
    (hS : ∀ l ∈ L2 ++ L3 ++ L4, 1 ≤ (S l).card ∧ (S l).card ≤ 48)
    (body : GWord α ρ) (hP : body.Proper (Fintype.card α))
    (hk : GLiveKernel e (headWord e L2 (fun _ => 16) z2 ind2 ++ (headWord e L3 (fun _ => 32) z3 ind3
      ++ (headWord e L4 (fun _ => 48) z4 ind4 ++ body))))
    (rmax : ℕ) (hwr : ∀ mv ∈ fullWord e (L2 ++ L3 ++ L4) A S 24 1 body, ∀ r, mv.rk? = some r → r ≤ rmax)
    (hsep : rmax + 48 < Fintype.card α) (hσ : 0 < Fintype.card σ) : Eng α ρ σ where
  X := Layout.someLayout α
  R := Layout.someLayout ρ
  Q := Layout.someLayout σ
  e := e
  he := he
  tr := fun l => (cutTgt (L2 ++ L3 ++ L4) A S l).1
  tz := fun l => (cutTgt (L2 ++ L3 ++ L4) A S l).2
  tind := cutTgt_indep (L2 ++ L3 ++ L4) A S
  tr_le := fun l => by
    show (cutTgt (L2 ++ L3 ++ L4) A S l).1 ≤ (Layout.someLayout α).n
    rw [← Layout.card (Layout.someLayout α), cutTgt_rank]
    split_ifs <;> omega
  tr_pos := fun l => by
    show 1 ≤ (cutTgt (L2 ++ L3 ++ L4) A S l).1
    rw [cutTgt_rank]
    split_ifs with hl
    · have := (hS l hl).2; omega
    · omega
  wd := fullWord e (L2 ++ L3 ++ L4) A S 24 1 body
  hP := by
    rw [← Layout.card (Layout.someLayout α)]
    exact fullWord_proper e (L2 ++ L3 ++ L4) A S (by norm_num) (by norm_num) (by omega) (by omega) body hP
  sep := fun mv hmv r hr l => by
    have h1 := hwr mv hmv r hr
    show r < (cutTgt (L2 ++ L3 ++ L4) A S l).1
    rw [cutTgt_rank]
    split_ifs with hl
    · have := (hS l hl).2; omega
    · omega
  W_pos := by rw [← Layout.card (Layout.someLayout σ)]; exact hσ
  three := by rw [← Layout.card (Layout.someLayout α)]; omega
  hw := MX.GLiveKernelM.splitWord 24 1
    (cut_heads_full3 he L2 L3 L4 hL z2 z3 z4 ind2 ind3 ind4 A S hz2 hz3 hz4 body hk)

/-- the target ranks of the three-group cut engine: `card α` off the heads, `card α - |S l|` on them. -/
lemma tq3_cases (E : Eng α ρ σ) (L2 L3 L4 : List σ) (A : σ → OBase α) (S : σ → Finset α)
    (htr : ∀ l, E.tr l = (cutTgt (L2 ++ L3 ++ L4) A S l).1)
    (hS2 : ∀ l ∈ L2, (S l).card = 16) (hS3 : ∀ l ∈ L3, (S l).card = 32) (hS4 : ∀ l ∈ L4, (S l).card = 48) :
    ∀ x, x < E.W → E.tq x = E.mx ∨ E.tq x = E.mx - 16 ∨ E.tq x = E.mx - 32 ∨ E.tq x = E.mx - 48 := by
  intro x hx
  have h1 := tq_of_lt E ⟨x, hx⟩
  simp only at h1
  rw [h1, htr, cutTgt_rank, mx_eq]
  split_ifs with hl
  · rcases List.mem_append.mp hl with h' | h'
    · rcases List.mem_append.mp h' with h'' | h''
      · right; left; rw [hS2 _ h'']
      · right; right; left; rw [hS3 _ h'']
    · right; right; right; rw [hS4 _ h']
  · left; rfl

/-- the number of live roles with target `card α - c` is the length of the head list of rank `c`. -/
lemma card_tq3 (E : Eng α ρ σ) (L2 L3 L4 : List σ) (hL : (L2 ++ L3 ++ L4).Nodup) (A : σ → OBase α)
    (S : σ → Finset α) (htr : ∀ l, E.tr l = (cutTgt (L2 ++ L3 ++ L4) A S l).1)
    (hS2 : ∀ l ∈ L2, (S l).card = 16) (hS3 : ∀ l ∈ L3, (S l).card = 32) (hS4 : ∀ l ∈ L4, (S l).card = 48)
    (hα : 48 < Fintype.card α) (L : List σ) (c : ℕ) (hc : c = 16 ∨ c = 32 ∨ c = 48)
    (hLc : ∀ l, (l ∈ L2 ++ L3 ++ L4 ∧ (S l).card = c) ↔ l ∈ L) (hLn : L.Nodup) :
    ((Finset.range E.W).filter (fun x => E.tq x = E.mx - c)).card = L.length := by
  rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range (fun x => if E.tq x = E.mx - c then 1 else 0) E.W]
  have h1 : ∀ i : Fin E.W, (if E.tq i = E.mx - c then 1 else 0)
      = (fun l => if E.tr l = E.mx - c then 1 else 0) (E.Q.index.symm i) := by
    intro i
    rw [tq_of_lt]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [Equiv.sum_comp E.Q.index.symm (fun l => if E.tr l = E.mx - c then 1 else 0)]
  have h2 : ∀ l, (if E.tr l = E.mx - c then 1 else 0) = if l ∈ L then 1 else 0 := by
    intro l
    rw [htr, cutTgt_rank, mx_eq]
    by_cases hl : l ∈ L2 ++ L3 ++ L4
    · rw [if_pos hl]
      have hcard : (S l).card = 16 ∨ (S l).card = 32 ∨ (S l).card = 48 := by
        rcases List.mem_append.mp hl with h' | h'
        · rcases List.mem_append.mp h' with h'' | h''
          · exact Or.inl (hS2 _ h'')
          · exact Or.inr (Or.inl (hS3 _ h''))
        · exact Or.inr (Or.inr (hS4 _ h'))
      by_cases hsc : (S l).card = c
      · rw [if_pos (by rw [hsc]), if_pos ((hLc l).1 ⟨hl, hsc⟩)]
      · rw [if_neg (by omega), if_neg (fun h => hsc ((hLc l).2 h).2)]
    · rw [if_neg hl, if_neg (fun h => hl ((hLc l).2 h).1), if_neg (by omega)]
  rw [Finset.sum_congr rfl (fun l _ => h2 l), Finset.sum_boole]
  have h3 : (Finset.univ.filter fun l : σ => l ∈ L) = L.toFinset := by
    ext l; simp
  rw [h3, List.toFinset_card_of_nodup hLn]
  simp

/-- The moment fact for one unit (four targets) gives, for `G` copies, the hypothesis `h` of
`MX.Rule.fourTarget_rateQ_hist` (the four-target form of `rate_scaled`). -/
theorem rate_scaled4 {P : ℕ} (rk : Fin P → ℕ) {m rmax G W0 H2 H3 H4 W L2 L3 L4 k2 k3 k4 : ℕ} {z : ℝ}
    (cut : List (ℕ × ℕ)) (hcutr : ∀ q ∈ cut, q.1 ≤ rmax)
    (hmom : BlockAccounting.moment m z cut ≤ ((W0 - H2 - H3 - H4 : ℕ) : ℝ) + BlockAccounting.T m z k2 H2
      + BlockAccounting.T m z k3 H3 + BlockAccounting.T m z k4 H4)
    (hcnt : ∀ r, (Finset.univ.filter fun j => rk j = r).card = G * BlockAccounting.histFn cut r)
    (hW : W = G * W0) (h2 : L2 = G * H2) (h3 : L3 = G * H3) (h4 : L4 = G * H4) :
    ∑ r ∈ Finset.range (rmax + 1), ((Finset.univ.filter fun j => rk j = r).card : ℝ) * ((r : ℝ) / m) ^ z
      ≤ ((W - L2 - L3 - L4 : ℕ) : ℝ) + (L2 : ℝ) * ((k2 : ℝ) / m) ^ z + (L3 : ℝ) * ((k3 : ℝ) / m) ^ z
        + (L4 : ℝ) * ((k4 : ℝ) / m) ^ z := by
  simp_rw [hcnt]
  have e1 : ∑ r ∈ Finset.range (rmax + 1), (((G * BlockAccounting.histFn cut r : ℕ) : ℝ)) * ((r : ℝ) / m) ^ z
      = (G : ℝ) * BlockAccounting.moment m z cut := by
    have := BlockAccounting.sum_histFn cut (fun r => ((r : ℝ) / m) ^ z) (Finset.range (rmax + 1))
      (fun q hq => Finset.mem_range.mpr (by have := hcutr q hq; omega))
    unfold BlockAccounting.moment
    rw [← this, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    push_cast
    ring
  rw [e1, hW, h2, h3, h4]
  have e2 : ((G * W0 - G * H2 - G * H3 - G * H4 : ℕ) : ℝ) = (G : ℝ) * ((W0 - H2 - H3 - H4 : ℕ) : ℝ) := by
    rw [← Nat.mul_sub, ← Nat.mul_sub, ← Nat.mul_sub]
    push_cast
    ring
  rw [e2]
  unfold BlockAccounting.T at hmom
  have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg G
  have hm2 := mul_le_mul_of_nonneg_left hmom hG0
  push_cast at hm2 ⊢
  linarith [hm2]

/-- **THE BUNDLE, three head groups (full cut)**: from the heads-first certificate (heads of ranks 16, 32, 48 on the
lists `L2`, `L3`, `L4`, each the block of all its lines `S l`), the profile identity of the cut (`hcut`: the unit
profile `U` less the heads, every block of rank 25 split into 24 + 1, is the profile `cut`) and the moment fact for
one unit, the hypothesis bundle of `Eng.engine_seam_final`. -/
theorem full_bundle3 (e : σ → ρ) (he : Function.Injective e) (L2 L3 L4 : List σ) (hL : (L2 ++ L3 ++ L4).Nodup)
    (z2 : σ → Fin 16 → Space α) (z3 : σ → Fin 32 → Space α) (z4 : σ → Fin 48 → Space α)
    (ind2 : ∀ l, LinearIndependent F (z2 l)) (ind3 : ∀ l, LinearIndependent F (z3 l))
    (ind4 : ∀ l, LinearIndependent F (z4 l)) (A : σ → OBase α) (S : σ → Finset α)
    (hz2 : ∀ l ∈ L2, ∀ x, bph (z2 l) x = bph ((A l).fam (S l)) x)
    (hz3 : ∀ l ∈ L3, ∀ x, bph (z3 l) x = bph ((A l).fam (S l)) x)
    (hz4 : ∀ l ∈ L4, ∀ x, bph (z4 l) x = bph ((A l).fam (S l)) x)
    (hS2 : ∀ l ∈ L2, (S l).card = 16) (hS3 : ∀ l ∈ L3, (S l).card = 32) (hS4 : ∀ l ∈ L4, (S l).card = 48)
    (body : GWord α ρ) (hP : body.Proper (Fintype.card α))
    (hk : GLiveKernel e (headWord e L2 (fun _ => 16) z2 ind2 ++ (headWord e L3 (fun _ => 32) z3 ind3
      ++ (headWord e L4 (fun _ => 48) z4 ind4 ++ body))))
    {G W0 H2 H3 H4 : ℕ} {U : List (ℕ × ℕ)} (cut : List (ℕ × ℕ))
    (hcost : ∀ φ, body.costR φ = (G : ℝ) * listCost φ U
      - ((L2.length : ℝ) * φ 16 + (L3.length : ℝ) * φ 32 + (L4.length : ℝ) * φ 48))
    (hcut : ∀ r, BlockAccounting.histFn cut r + (if r = 16 then H2 else 0) + (if r = 32 then H3 else 0)
        + (if r = 48 then H4 else 0) + (if r = 25 then BlockAccounting.histFn U 25 else 0)
      = BlockAccounting.histFn U r + (if r = 24 then BlockAccounting.histFn U 25 else 0)
        + (if r = 1 then BlockAccounting.histFn U 25 else 0))
    (hl2 : L2.length = G * H2) (hl3 : L3.length = G * H3) (hl4 : L4.length = G * H4)
    (hσ : Fintype.card σ = G * W0) (hG : 1 ≤ G) (hH4 : 1 ≤ H4) (hα : Fintype.card α = 73)
    (hcutr : ∀ q ∈ cut, q.1 ≤ 24) {z1 : ℝ}
    (hmom : BlockAccounting.moment 73 z1 cut
      ≤ ((W0 - H2 - H3 - H4 : ℕ) : ℝ) + BlockAccounting.T 73 z1 57 H2 + BlockAccounting.T 73 z1 41 H3
        + BlockAccounting.T 73 z1 25 H4) :
    ∃ (E : Eng α ρ σ) (R : MX.Rule) (typ : ℕ → Fin R.K),
      E.mx = 73 ∧ E.BridgeHyp R typ 25 ∧ R.RateQ z1 1 := by
  -- the histogram of the full-cut word is G copies of `cut`
  have hb : ∀ r, body.hist r + G * ((if r = 16 then H2 else 0) + (if r = 32 then H3 else 0)
      + (if r = 48 then H4 else 0)) = G * BlockAccounting.histFn U r := by
    intro r
    have h := hist_eq_price hcost r
    beta_reduce at h
    have hl : listCost (ind r) U = (BlockAccounting.histFn U r : ℝ) := listCost_ind U r
    rw [hl, hl2, hl3, hl4] at h
    simp only [ind] at h
    have : ((body.hist r + G * ((if r = 16 then H2 else 0) + (if r = 32 then H3 else 0)
        + (if r = 48 then H4 else 0)) : ℕ) : ℝ) = ((G * BlockAccounting.histFn U r : ℕ) : ℝ) := by
      push_cast
      by_cases h16 : r = 16
      · subst h16; simp at h ⊢ <;> linarith
      · by_cases h32 : r = 32
        · subst h32; simp at h ⊢ <;> linarith
        · by_cases h48 : r = 48
          · subst h48; simp at h ⊢ <;> linarith
          · simp [h16, h32, h48, Ne.symm h16, Ne.symm h32, Ne.symm h48] at h ⊢ <;> linarith
    exact_mod_cast this
  have hhist : ∀ r, (fullWord e (L2 ++ L3 ++ L4) A S 24 1 body).hist r = G * BlockAccounting.histFn cut r := by
    intro r
    rw [fullWord_hist e (L2 ++ L3 ++ L4) A S (by norm_num) (by norm_num) body r]
    have h25 := hb 25
    have hr := hb r
    have hc := congrArg (fun t => G * t) (hcut r)
    simp only [Nat.mul_add, mul_ite, Nat.mul_zero, show (24 + 1 : ℕ) = 25 from rfl] at hc hr h25 ⊢
    by_cases e25 : r = 25
    · subst e25
      generalize G * BlockAccounting.histFn cut 25 = X at *
      generalize G * BlockAccounting.histFn U 25 = Y at *
      generalize G * H2 = P2 at *
      generalize G * H3 = P3 at *
      generalize G * H4 = P4 at *
      generalize body.hist 25 = B at *
      (try split_ifs at hc hr h25 ⊢) <;> omega
    · generalize G * BlockAccounting.histFn cut r = X at *
      generalize G * BlockAccounting.histFn U r = Y at *
      generalize G * BlockAccounting.histFn U 25 = Z at *
      generalize G * H2 = P2 at *
      generalize G * H3 = P3 at *
      generalize G * H4 = P4 at *
      generalize body.hist r = B at *
      generalize body.hist 25 = B25 at *
      (try split_ifs at hc hr h25 ⊢) <;> omega
  have hwr := ranks_le_of_hist hhist hcutr
  have hσ0 : 0 < Fintype.card σ := by
    have hlen : 0 < L4.length := by
      rw [hl4]; exact Nat.mul_pos (by omega) (by omega)
    obtain ⟨l0, -⟩ := List.exists_mem_of_length_pos hlen
    exact Fintype.card_pos_iff.mpr ⟨l0⟩
  have hS : ∀ l ∈ L2 ++ L3 ++ L4, 1 ≤ (S l).card ∧ (S l).card ≤ 48 := by
    intro l hl
    rcases List.mem_append.mp hl with h' | h'
    · rcases List.mem_append.mp h' with h'' | h''
      · rw [hS2 _ h'']; exact ⟨by norm_num, by norm_num⟩
      · rw [hS3 _ h'']; exact ⟨by norm_num, by norm_num⟩
    · rw [hS4 _ h']; exact ⟨by norm_num, by norm_num⟩
  let E := fullEng3 e he L2 L3 L4 hL z2 z3 z4 ind2 ind3 ind4 A S hz2 hz3 hz4 hS body hP hk 24 hwr (by omega) hσ0
  have hmx : E.mx = 73 := (mx_eq E).trans hα
  have htr : ∀ l, E.tr l = (cutTgt (L2 ++ L3 ++ L4) A S l).1 := fun l => rfl
  obtain ⟨h12, h3n, d123⟩ := List.nodup_append.mp hL
  obtain ⟨h1n, h2n, d12⟩ := List.nodup_append.mp h12
  have hL2c : ∀ l, (l ∈ L2 ++ L3 ++ L4 ∧ (S l).card = 16) ↔ l ∈ L2 := by
    intro l
    constructor
    · rintro ⟨hl, hc⟩
      rcases List.mem_append.mp hl with h' | h'
      · rcases List.mem_append.mp h' with h'' | h''
        · exact h''
        · rw [hS3 _ h''] at hc; omega
      · rw [hS4 _ h'] at hc; omega
    · intro h; exact ⟨List.mem_append_left _ (List.mem_append_left _ h), hS2 _ h⟩
  have hL3c : ∀ l, (l ∈ L2 ++ L3 ++ L4 ∧ (S l).card = 32) ↔ l ∈ L3 := by
    intro l
    constructor
    · rintro ⟨hl, hc⟩
      rcases List.mem_append.mp hl with h' | h'
      · rcases List.mem_append.mp h' with h'' | h''
        · rw [hS2 _ h''] at hc; omega
        · exact h''
      · rw [hS4 _ h'] at hc; omega
    · intro h; exact ⟨List.mem_append_left _ (List.mem_append_right _ h), hS3 _ h⟩
  have hL4c : ∀ l, (l ∈ L2 ++ L3 ++ L4 ∧ (S l).card = 48) ↔ l ∈ L4 := by
    intro l
    constructor
    · rintro ⟨hl, hc⟩
      rcases List.mem_append.mp hl with h' | h'
      · rcases List.mem_append.mp h' with h'' | h''
        · rw [hS2 _ h''] at hc; omega
        · rw [hS3 _ h''] at hc; omega
      · exact h'
    · intro h; exact ⟨List.mem_append_right _ h, hS4 _ h⟩
  have hα48 : 48 < Fintype.card α := by omega
  have c2 := card_tq3 E L2 L3 L4 hL A S htr hS2 hS3 hS4 hα48 L2 16 (Or.inl rfl) hL2c h1n
  have c3 := card_tq3 E L2 L3 L4 hL A S htr hS2 hS3 hS4 hα48 L3 32 (Or.inr (Or.inl rfl)) hL3c h2n
  have c4 := card_tq3 E L2 L3 L4 hL A S htr hS2 hS3 hS4 hα48 L4 48 (Or.inr (Or.inr rfl)) hL4c h3n
  rw [hmx] at c2 c3 c4
  have hrk1 : ∀ j : Fin E.nB, 1 ≤ E.rkI j := rkI_pos E
  have hrk : ∀ j : Fin E.nB, E.rkI j ≤ 24 := rkI_le E hwr
  have htq : ∀ x, x < E.W → E.tq x = E.mx ∨ E.tq x = 57 ∨ E.tq x = 41 ∨ E.tq x = 25 := by
    intro x hx
    have := tq3_cases E L2 L3 L4 A S htr hS2 hS3 hS4 x hx
    rw [hmx] at this ⊢
    exact this
  have hH4' : 1 ≤ L4.length := by
    rw [hl4]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hB := E.bridge_fourTarget 57 41 25 24 L2.length L3.length L4.length hrk1 hrk (by norm_num) (by norm_num)
    (by norm_num) (by rw [hmx]; norm_num) (by norm_num) hH4' htq c2 c3 c4
  refine ⟨E, _, _, hmx, hB, ?_⟩
  refine MX.Rule.fourTarget_rateQ_hist hrk1 hrk (by norm_num) (by norm_num) (by norm_num) (by rw [hmx]; norm_num)
    (by norm_num) hH4' ?_
  -- the moment fact for G copies
  have hcnt : ∀ r, (Finset.univ.filter fun j : Fin E.nB => E.rkI j = r).card = G * BlockAccounting.histFn cut r :=
    fun r => (card_rkI E r).trans (hhist r)
  have hW : E.W = G * W0 := (W_eq E).trans hσ
  rw [hmx]
  exact rate_scaled4 (fun j : Fin E.nB => E.rkI j) (m := 73) (rmax := 24) cut hcutr hmom hcnt hW hl2 hl3 hl4

/-- **THE FULL-CUT ENGINE THEOREM, three head groups** (the `hillsZ_program` shape at every `zE ∈ (z1, 1]`). -/
theorem full_engine3 (e : σ → ρ) (he : Function.Injective e) (L2 L3 L4 : List σ) (hL : (L2 ++ L3 ++ L4).Nodup)
    (z2 : σ → Fin 16 → Space α) (z3 : σ → Fin 32 → Space α) (z4 : σ → Fin 48 → Space α)
    (ind2 : ∀ l, LinearIndependent F (z2 l)) (ind3 : ∀ l, LinearIndependent F (z3 l))
    (ind4 : ∀ l, LinearIndependent F (z4 l)) (A : σ → OBase α) (S : σ → Finset α)
    (hz2 : ∀ l ∈ L2, ∀ x, bph (z2 l) x = bph ((A l).fam (S l)) x)
    (hz3 : ∀ l ∈ L3, ∀ x, bph (z3 l) x = bph ((A l).fam (S l)) x)
    (hz4 : ∀ l ∈ L4, ∀ x, bph (z4 l) x = bph ((A l).fam (S l)) x)
    (hS2 : ∀ l ∈ L2, (S l).card = 16) (hS3 : ∀ l ∈ L3, (S l).card = 32) (hS4 : ∀ l ∈ L4, (S l).card = 48)
    (body : GWord α ρ) (hP : body.Proper (Fintype.card α))
    (hk : GLiveKernel e (headWord e L2 (fun _ => 16) z2 ind2 ++ (headWord e L3 (fun _ => 32) z3 ind3
      ++ (headWord e L4 (fun _ => 48) z4 ind4 ++ body))))
    {G W0 H2 H3 H4 : ℕ} {U : List (ℕ × ℕ)} (cut : List (ℕ × ℕ))
    (hcost : ∀ φ, body.costR φ = (G : ℝ) * listCost φ U
      - ((L2.length : ℝ) * φ 16 + (L3.length : ℝ) * φ 32 + (L4.length : ℝ) * φ 48))
    (hcut : ∀ r, BlockAccounting.histFn cut r + (if r = 16 then H2 else 0) + (if r = 32 then H3 else 0)
        + (if r = 48 then H4 else 0) + (if r = 25 then BlockAccounting.histFn U 25 else 0)
      = BlockAccounting.histFn U r + (if r = 24 then BlockAccounting.histFn U 25 else 0)
        + (if r = 1 then BlockAccounting.histFn U 25 else 0))
    (hl2 : L2.length = G * H2) (hl3 : L3.length = G * H3) (hl4 : L4.length = G * H4)
    (hσ : Fintype.card σ = G * W0) (hG : 1 ≤ G) (hH4 : 1 ≤ H4) (hα : Fintype.card α = 73)
    (hcutr : ∀ q ∈ cut, q.1 ≤ 24) {z1 zE : ℝ}
    (hmom : BlockAccounting.moment 73 z1 cut
      ≤ ((W0 - H2 - H3 - H4 : ℕ) : ℝ) + BlockAccounting.T 73 z1 57 H2 + BlockAccounting.T 73 z1 41 H3
        + BlockAccounting.T 73 z1 25 H4)
    (hz1 : 0 < z1) (h12 : z1 < zE) (hzE : zE ≤ 1)
    (m : Bool) (cl : Paint) {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope zE (k i)) := by
  obtain ⟨E, R, typ, hmx, hB, hR⟩ :=
    full_bundle3 e he L2 L3 L4 hL z2 z3 z4 ind2 ind3 ind4 A S hz2 hz3 hz4 hS2 hS3 hS4 body hP hk cut hcost hcut
      hl2 hl3 hl4 hσ hG hH4 hα hcutr hmom
  exact E.engine_seam_final hB E.mx le_rfl hR hz1 h12 hzE m cl k v

end CutF3
end
end PB
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.MX.Rule.fourTarget_rateQ_hist
#print axioms OAI.PowerSaving.RAM.Eng.bridge_fourTarget
#print axioms OAI.PowerSaving.PB.full_bundle3
#print axioms OAI.PowerSaving.PB.full_engine3
