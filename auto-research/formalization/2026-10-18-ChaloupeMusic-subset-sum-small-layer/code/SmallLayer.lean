import Mathlib

/-!
# An averaged small-layer lemma

Lean formalization of Section 3 ("An averaged small-layer lemma": Lemmas 3.1, 3.2, 3.3 and
Corollary D) of A. Kapila, *Subset Sum in time O(2^{0.4877 n})*, file
`subset-sum/PROOF_0.4877.tex` of `a-kapila/maths-proofs` at commit
`44c34961b56784c220a6e913cc068d57dc37c5a3`, lines 223-277.

Notation of the note, and how it is rendered here:

* `w` : integer weights on a finite index set, equal weights allowed — `w : ι → ℤ`;
* `Σ_j(V) = {w(T) : T ⊆ V, |T| = j}` — `layer w V j`;
* `Σ(V) = ⋃_j Σ_j(V)` — `sums w V` (the image of the whole powerset);
* `a_j(V) = |Σ_j(V)| / C(|V|, j)` — `density w V j`;
* `d(V) = |V| - log₂ |Σ(V)|` — `deficiency w V`;
* `𝔼_S f(S)` for `S` a uniform `r`-subset of `U` — `avg U r f`.

Only `propext`, `Classical.choice` and `Quot.sound` are used.
-/

open Finset

namespace SmallLayer

variable {ι : Type*} [DecidableEq ι] (w : ι → ℤ)

/-- `Σ_j(V)`: the sums of the `j`-subsets of `V`. -/
def layer (V : Finset ι) (j : ℕ) : Finset ℤ :=
  (V.powersetCard j).image fun T => ∑ i ∈ T, w i

/-- `Σ(V)`: the subset sums of `V`. -/
def sums (V : Finset ι) : Finset ℤ :=
  V.powerset.image fun T => ∑ i ∈ T, w i

/-- `a_j(V) = |Σ_j(V)| / C(|V|, j)`. -/
noncomputable def density (V : Finset ι) (j : ℕ) : ℝ :=
  (layer w V j).card / (V.card.choose j : ℝ)

/-- `d(V) = |V| - log₂ |Σ(V)|`. -/
noncomputable def deficiency (V : Finset ι) : ℝ :=
  V.card - Real.logb 2 (sums w V).card

/-- The expectation of `f(S)` for `S` a uniform `r`-subset of `U`. -/
noncomputable def avg (U : Finset ι) (r : ℕ) (f : Finset ι → ℝ) : ℝ :=
  (∑ S ∈ U.powersetCard r, f S) / (U.card.choose r : ℝ)

/-! ## Uniform averages -/

omit [DecidableEq ι] in
/-- `avg U r f` is the plain average of `f` over the `r`-subsets of `U`, that is the expectation
of `f(S)` for `S` uniform among them. -/
lemma avg_eq (U : Finset ι) (r : ℕ) (f : Finset ι → ℝ) :
    avg U r f = (∑ S ∈ U.powersetCard r, f S) / (U.powersetCard r).card := by
  rw [avg, card_powersetCard]

omit [DecidableEq ι] in
lemma avg_mono {U : Finset ι} {r : ℕ} {f g : Finset ι → ℝ}
    (h : ∀ S ∈ U.powersetCard r, f S ≤ g S) : avg U r f ≤ avg U r g := by
  unfold avg
  gcongr with S hS
  exact h S hS

omit [DecidableEq ι] in
lemma avg_const {U : Finset ι} {r : ℕ} (hr : r ≤ U.card) (c : ℝ) :
    avg U r (fun _ => c) = c := by
  have hpos : (0 : ℝ) < U.card.choose r := by exact_mod_cast Nat.choose_pos hr
  unfold avg
  rw [sum_const, card_powersetCard, nsmul_eq_mul]
  field_simp

omit [DecidableEq ι] in
lemma avg_div (U : Finset ι) (r : ℕ) (f : Finset ι → ℝ) (c : ℝ) :
    avg U r (fun S => f S / c) = avg U r f / c := by
  unfold avg
  rw [← sum_div]
  ring

/-! ## Counting -/

/-- The `s`-subsets of `U` that contain a fixed `K ⊆ U` number `C(|U| - |K|, s - |K|)`. -/
lemma card_supersets {U K : Finset ι} {s : ℕ} (hKU : K ⊆ U) (hKs : K.card ≤ s) :
    ((U.powersetCard s).filter (K ⊆ ·)).card = (U.card - K.card).choose (s - K.card) := by
  rw [← card_sdiff_of_subset hKU, ← card_powersetCard]
  apply card_nbij' (fun S => S \ K) (fun B => B ∪ K)
  · intro S hS
    simp only [mem_coe, mem_filter, mem_powersetCard] at hS ⊢
    exact ⟨sdiff_subset_sdiff hS.1.1 le_rfl, by rw [card_sdiff_of_subset hS.2, hS.1.2]⟩
  · intro B hB
    simp only [mem_coe, mem_filter, mem_powersetCard] at hB ⊢
    have hdisj : Disjoint B K := disjoint_of_subset_left hB.1 sdiff_disjoint
    refine ⟨⟨union_subset (hB.1.trans sdiff_subset) hKU, ?_⟩, subset_union_right⟩
    rw [card_union_of_disjoint hdisj, hB.2]
    omega
  · intro S hS
    simp only [mem_coe, mem_filter, mem_powersetCard] at hS
    exact sdiff_union_of_subset hS.2
  · intro B hB
    simp only [mem_coe, mem_powersetCard] at hB
    exact union_sdiff_cancel_right (disjoint_of_subset_left hB.1 sdiff_disjoint)

/-- `C(n, p) · C(n - p, q) = C(n, q) · C(n - q, p)`. No hypothesis is needed: when `p + q > n`
both sides vanish. -/
lemma choose_mul_choose_comm (n p q : ℕ) :
    n.choose p * (n - p).choose q = n.choose q * (n - q).choose p := by
  have h1 := Nat.choose_mul (n := n) (k := p + q) (s := p) (Nat.le_add_right p q)
  have h2 := Nat.choose_mul (n := n) (k := p + q) (s := q) (Nat.le_add_left q p)
  rw [Nat.add_sub_cancel_left] at h1
  rw [Nat.add_sub_cancel] at h2
  rw [← h1, ← h2, Nat.choose_symm_add]

/-- `C(n, a) ≤ C(n, b)` for `a ≤ b ≤ n / 2`. -/
lemma choose_le_choose_of_le_half {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n / 2) :
    n.choose a ≤ n.choose b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- A uniform `p`-subset `B` of a uniform `q`-subset of `U` is a uniform `p`-subset of `U`:
the double sum counts each `p`-subset `C(|U| - p, q - p)` times. -/
lemma sum_nested (U : Finset ι) {p q : ℕ} (hpq : p ≤ q) (f : Finset ι → ℝ) :
    ∑ A ∈ U.powersetCard q, ∑ B ∈ A.powersetCard p, f B
      = ∑ B ∈ U.powersetCard p, ((U.card - p).choose (q - p) : ℝ) * f B := by
  have h1 : ∀ A ∈ U.powersetCard q,
      A.powersetCard p = (U.powersetCard p).filter (· ⊆ A) := by
    intro A hA
    have hAU := (mem_powersetCard.1 hA).1
    ext B
    simp only [mem_powersetCard, mem_filter]
    exact ⟨fun h => ⟨⟨h.1.trans hAU, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  rw [sum_congr rfl fun A hA => by rw [h1 A hA, sum_filter], sum_comm]
  refine sum_congr rfl fun B hB => ?_
  have hB' := mem_powersetCard.1 hB
  rw [← sum_filter, sum_const, nsmul_eq_mul, card_supersets hB'.1 (by omega), hB'.2]

/-- For `W` a uniform `p`-subset of `V` and `S` a uniform `σ`-subset of `V \ W`, the set `S` is a
uniform `σ`-subset of `V`: the double sum counts each `σ`-subset `C(|V| - σ, p)` times. -/
lemma sum_disjoint (V : Finset ι) (p σ : ℕ) (f : Finset ι → ℝ) :
    ∑ W ∈ V.powersetCard p, ∑ S ∈ (V \ W).powersetCard σ, f S
      = ∑ S ∈ V.powersetCard σ, ((V.card - σ).choose p : ℝ) * f S := by
  have h1 : ∀ W ∈ V.powersetCard p,
      (V \ W).powersetCard σ = (V.powersetCard σ).filter (fun S => Disjoint W S) := by
    intro W _
    ext S
    simp only [mem_powersetCard, mem_filter, subset_sdiff]
    exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2.symm⟩, fun h => ⟨⟨h.1.1, h.2.symm⟩, h.1.2⟩⟩
  rw [sum_congr rfl fun W hW => by rw [h1 W hW, sum_filter], sum_comm]
  refine sum_congr rfl fun S hS => ?_
  have hS' := mem_powersetCard.1 hS
  have h2 : (V.powersetCard p).filter (fun W => Disjoint W S) = (V \ S).powersetCard p := by
    ext W
    simp only [mem_powersetCard, mem_filter, subset_sdiff]
    tauto
  rw [← sum_filter, sum_const, nsmul_eq_mul, h2, card_powersetCard,
    card_sdiff_of_subset hS'.1, hS'.2]

omit [DecidableEq ι] in
lemma choose_pos_real {n r : ℕ} (h : r ≤ n) : (0 : ℝ) < n.choose r := by
  exact_mod_cast Nat.choose_pos h

/-- Averaging identity behind the last line of the proof of Corollary D. -/
lemma avg_nested (M : Finset ι) {σ v : ℕ} (hσv : σ ≤ v) (hvM : v ≤ M.card) (f : Finset ι → ℝ) :
    avg M v (fun V => avg V σ f) = avg M σ f := by
  unfold avg
  have e : ∀ V ∈ M.powersetCard v, (∑ S ∈ V.powersetCard σ, f S) / (V.card.choose σ : ℝ)
      = (∑ S ∈ V.powersetCard σ, f S) / (v.choose σ : ℝ) := fun V hV => by
    rw [(mem_powersetCard.1 hV).2]
  rw [sum_congr rfl e, ← sum_div, sum_nested M hσv f, ← mul_sum, div_div]
  have hid : (v.choose σ * M.card.choose v : ℝ)
      = (M.card - σ).choose (v - σ) * M.card.choose σ := by
    have := Nat.choose_mul (n := M.card) (k := v) (s := σ) hσv
    rw [mul_comm (M.card.choose σ)] at this
    exact_mod_cast (by rw [mul_comm]; exact this)
  rw [hid, mul_div_mul_left _ _ (choose_pos_real (by omega)).ne']

/-- Averaging identity used in the case `t ≥ k` of Corollary D. -/
lemma avg_disjoint (V : Finset ι) {p σ : ℕ} (h : p + σ ≤ V.card) (f : Finset ι → ℝ) :
    avg V p (fun W => avg (V \ W) σ f) = avg V σ f := by
  unfold avg
  have e : ∀ W ∈ V.powersetCard p,
      (∑ S ∈ (V \ W).powersetCard σ, f S) / ((V \ W).card.choose σ : ℝ)
        = (∑ S ∈ (V \ W).powersetCard σ, f S) / ((V.card - p).choose σ : ℝ) := fun W hW => by
    rw [card_sdiff_of_subset (mem_powersetCard.1 hW).1, (mem_powersetCard.1 hW).2]
  rw [sum_congr rfl e, ← sum_div, sum_disjoint V p σ f, ← mul_sum, div_div]
  have hid : ((V.card - p).choose σ * V.card.choose p : ℝ)
      = (V.card - σ).choose p * V.card.choose σ := by
    have := choose_mul_choose_comm V.card p σ
    exact_mod_cast (by rw [mul_comm, this, mul_comm])
  rw [hid, mul_div_mul_left _ _ (choose_pos_real (by omega)).ne']

/-! ## Lemma 3.1 (covering) -/

lemma covering_count (V : Finset ι) {k t : ℕ} (hkt : k ≤ t) :
    t.choose (t - k) * (layer w V t).card
      ≤ ∑ W ∈ V.powersetCard (t - k), (layer w (V \ W) k).card := by
  have hrep : ∀ x ∈ layer w V t, ∃ T ∈ V.powersetCard t, ∑ i ∈ T, w i = x := by
    intro x hx
    simpa [layer] using hx
  choose! T hT hTx using hrep
  have hW : ∀ W ∈ V.powersetCard (t - k),
      ((layer w V t).filter (fun x => W ⊆ T x)).card ≤ (layer w (V \ W) k).card := by
    intro W hW
    apply card_le_card_of_injOn (fun x => x - ∑ i ∈ W, w i)
    · intro x hx
      rw [mem_coe, mem_filter] at hx
      rw [mem_coe, layer, mem_image]
      have hTV := mem_powersetCard.1 (hT x hx.1)
      refine ⟨T x \ W, mem_powersetCard.2 ⟨sdiff_subset_sdiff hTV.1 le_rfl, ?_⟩, ?_⟩
      · rw [card_sdiff_of_subset hx.2, hTV.2, (mem_powersetCard.1 hW).2]
        omega
      · rw [sum_sdiff_eq_sub hx.2, hTx x hx.1]
    · intro x _ y _ hxy
      simpa using hxy
  calc t.choose (t - k) * (layer w V t).card
      = ∑ x ∈ layer w V t, ((V.powersetCard (t - k)).filter (fun W => W ⊆ T x)).card := by
        have : ∀ x ∈ layer w V t,
            ((V.powersetCard (t - k)).filter (fun W => W ⊆ T x)).card = t.choose (t - k) := by
          intro x hx
          have hTV := mem_powersetCard.1 (hT x hx)
          have : (V.powersetCard (t - k)).filter (fun W => W ⊆ T x)
              = (T x).powersetCard (t - k) := by
            ext W
            simp only [mem_powersetCard, mem_filter]
            exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hTV.1, h.2⟩, h.1⟩⟩
          rw [this, card_powersetCard, hTV.2]
        rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_comm]
    _ = ∑ W ∈ V.powersetCard (t - k), ((layer w V t).filter (fun x => W ⊆ T x)).card := by
        simp only [card_filter]
        exact sum_comm
    _ ≤ _ := sum_le_sum hW

/-- **Lemma 3.1 (covering).** Let `0 ≤ k ≤ t ≤ |V|` and let `W` be a uniform `(t-k)`-subset of
`V`. Then `a_t(V) ≤ 𝔼_W a_k(V \ W)`. -/
theorem covering (V : Finset ι) {k t : ℕ} (hkt : k ≤ t) (htV : t ≤ V.card) :
    density w V t ≤ avg V (t - k) (fun W => density w (V \ W) k) := by
  have hcount : (t.choose (t - k) * (layer w V t).card : ℝ)
      ≤ ∑ W ∈ V.powersetCard (t - k), ((layer w (V \ W) k).card : ℝ) := by
    exact_mod_cast covering_count w V hkt
  unfold avg density
  have e : ∀ W ∈ V.powersetCard (t - k),
      ((layer w (V \ W) k).card : ℝ) / ((V \ W).card.choose k : ℝ)
        = ((layer w (V \ W) k).card : ℝ) / ((V.card - (t - k)).choose k : ℝ) := fun W hW => by
    rw [card_sdiff_of_subset (mem_powersetCard.1 hW).1, (mem_powersetCard.1 hW).2]
  rw [sum_congr rfl e, ← sum_div, div_div]
  have hid : ((V.card - (t - k)).choose k * V.card.choose (t - k) : ℝ)
      = V.card.choose t * t.choose (t - k) := by
    have := Nat.choose_mul (n := V.card) (k := t) (s := t - k) (Nat.sub_le t k)
    rw [show t - (t - k) = k by omega] at this
    exact_mod_cast (by rw [mul_comm, this])
  have hp1 := choose_pos_real htV
  have hp2 := choose_pos_real (Nat.sub_le t k)
  rw [hid, div_le_div_iff₀ hp1 (mul_pos hp1 hp2)]
  nlinarith

/-! ## Lemma 3.2 (sampling) -/

lemma sampling_count (V : Finset ι) {k s : ℕ} (hks : k ≤ s) :
    (V.card - k).choose (s - k) * (layer w V k).card
      ≤ ∑ S ∈ V.powersetCard s, (layer w S k).card := by
  have hrep : ∀ x ∈ layer w V k, ∃ K ∈ V.powersetCard k, ∑ i ∈ K, w i = x := by
    intro x hx
    simpa [layer] using hx
  choose! K hK hKx using hrep
  have hS : ∀ S ∈ V.powersetCard s,
      ((layer w V k).filter (fun x => K x ⊆ S)).card ≤ (layer w S k).card := by
    intro S _
    apply card_le_card
    intro x hx
    rw [mem_filter] at hx
    rw [layer, mem_image]
    exact ⟨K x, mem_powersetCard.2 ⟨hx.2, (mem_powersetCard.1 (hK x hx.1)).2⟩, hKx x hx.1⟩
  calc (V.card - k).choose (s - k) * (layer w V k).card
      = ∑ x ∈ layer w V k, ((V.powersetCard s).filter (fun S => K x ⊆ S)).card := by
        have : ∀ x ∈ layer w V k,
            ((V.powersetCard s).filter (fun S => K x ⊆ S)).card = (V.card - k).choose (s - k) := by
          intro x hx
          have hKV := mem_powersetCard.1 (hK x hx)
          rw [card_supersets hKV.1 (by omega), hKV.2]
        rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_comm]
    _ = ∑ S ∈ V.powersetCard s, ((layer w V k).filter (fun x => K x ⊆ S)).card := by
        simp only [card_filter]
        exact sum_comm
    _ ≤ _ := sum_le_sum hS

/-- **Lemma 3.2 (sampling).** Let `k ≤ s ≤ |V|` and let `S` be a uniform `s`-subset of `V`.
Then `𝔼_S a_k(S) ≥ a_k(V)`. -/
theorem sampling (V : Finset ι) {k s : ℕ} (hks : k ≤ s) (hsV : s ≤ V.card) :
    density w V k ≤ avg V s (fun S => density w S k) := by
  have hcount : ((V.card - k).choose (s - k) * (layer w V k).card : ℝ)
      ≤ ∑ S ∈ V.powersetCard s, ((layer w S k).card : ℝ) := by
    exact_mod_cast sampling_count w V hks
  unfold avg density
  have e : ∀ S ∈ V.powersetCard s,
      ((layer w S k).card : ℝ) / (S.card.choose k : ℝ)
        = ((layer w S k).card : ℝ) / (s.choose k : ℝ) := fun S hS => by
    rw [(mem_powersetCard.1 hS).2]
  rw [sum_congr rfl e, ← sum_div, div_div]
  have hid : (s.choose k * V.card.choose s : ℝ) = V.card.choose k * (V.card - k).choose (s - k) := by
    have := Nat.choose_mul (n := V.card) (k := s) (s := k) hks
    exact_mod_cast (by rw [mul_comm, this])
  have hp1 := choose_pos_real (n := V.card) (r := k) (by omega)
  have hp2 := choose_pos_real (n := V.card - k) (r := s - k) (by omega)
  rw [hid, div_le_div_iff₀ hp1 (mul_pos hp1 hp2)]
  nlinarith

/-! ## Lemma 3.3 (a good layer) -/

omit [DecidableEq ι] in
lemma zero_mem_sums (V : Finset ι) : (0 : ℤ) ∈ sums w V :=
  mem_image.2 ⟨∅, empty_mem_powerset V, sum_empty⟩

omit [DecidableEq ι] in
lemma sums_card_pos (V : Finset ι) : 0 < (sums w V).card :=
  card_pos.2 ⟨0, zero_mem_sums w V⟩

lemma sums_eq_biUnion (V : Finset ι) :
    sums w V = (range (V.card + 1)).biUnion (layer w V) := by
  rw [sums, powerset_card_biUnion, biUnion_image]
  rfl

omit [DecidableEq ι] in
lemma layer_card_le_choose (V : Finset ι) (j : ℕ) : (layer w V j).card ≤ V.card.choose j :=
  card_powersetCard j V ▸ card_image_le

/-- Complementation: `Σ_{|V| - j}(V) = w(V) - Σ_j(V)`, so the layer `|V| - j` is at least as
large as the layer `j`. -/
lemma layer_card_le_compl (V : Finset ι) (j : ℕ) :
    (layer w V j).card ≤ (layer w V (V.card - j)).card := by
  apply card_le_card_of_injOn (fun x => (∑ i ∈ V, w i) - x)
  · intro x hx
    rw [mem_coe, layer, mem_image] at hx
    obtain ⟨T, hT, rfl⟩ := hx
    rw [mem_coe, layer, mem_image]
    rw [mem_powersetCard] at hT
    exact ⟨V \ T, mem_powersetCard.2 ⟨sdiff_subset, by rw [card_sdiff_of_subset hT.1, hT.2]⟩,
      sum_sdiff_eq_sub hT.1⟩
  · intro x _ y _ hxy
    simpa using hxy

/-- **Lemma 3.3 (a good layer), first claim.** Some `t` with `2t ≤ |V|` has
`|Σ(V)| ≤ (|V| + 1) |Σ_t(V)|`. -/
theorem good_layer (V : Finset ι) :
    ∃ t, 2 * t ≤ V.card ∧ (sums w V).card ≤ (V.card + 1) * (layer w V t).card := by
  obtain ⟨j, hj, hjle⟩ : ∃ j ∈ range (V.card + 1),
      (sums w V).card ≤ (V.card + 1) * (layer w V j).card := by
    by_contra h
    push Not at h
    have hlt := sum_lt_sum_of_nonempty nonempty_range_add_one h
    rw [← mul_sum, sum_const, card_range, smul_eq_mul] at hlt
    have hlt' := Nat.lt_of_mul_lt_mul_left hlt
    have hle : (sums w V).card ≤ ∑ j ∈ range (V.card + 1), (layer w V j).card := by
      rw [sums_eq_biUnion]
      exact card_biUnion_le
    omega
  rw [mem_range] at hj
  by_cases h2 : 2 * j ≤ V.card
  · exact ⟨j, h2, hjle⟩
  · exact ⟨V.card - j, by omega,
      hjle.trans (Nat.mul_le_mul_left _ (layer_card_le_compl w V j))⟩

omit [DecidableEq ι] in
/-- `2^{-d(V)} = |Σ(V)| / 2^{|V|}`. -/
lemma two_rpow_neg_deficiency (V : Finset ι) :
    (2 : ℝ) ^ (-deficiency w V) = (sums w V).card / 2 ^ V.card := by
  have hpos : (0 : ℝ) < (sums w V).card := by exact_mod_cast sums_card_pos w V
  unfold deficiency
  rw [neg_sub, Real.rpow_sub (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hpos,
    Real.rpow_natCast]

omit [DecidableEq ι] in
/-- The "in particular" of Lemma 3.3, for any layer that satisfies its first claim. -/
lemma density_of_good (V : Finset ι) {t : ℕ} (ht : t ≤ V.card)
    (hgood : (sums w V).card ≤ (V.card + 1) * (layer w V t).card) :
    (2 : ℝ) ^ (-deficiency w V) / (V.card + 1) ≤ density w V t := by
  have hgood' : ((sums w V).card : ℝ) ≤ (V.card + 1) * (layer w V t).card := by
    exact_mod_cast hgood
  have hC : (V.card.choose t : ℝ) ≤ 2 ^ V.card := by exact_mod_cast Nat.choose_le_two_pow _ _
  have hCpos := choose_pos_real ht
  rw [two_rpow_neg_deficiency, div_div, density]
  calc ((sums w V).card : ℝ) / (2 ^ V.card * (V.card + 1))
      ≤ (layer w V t).card / 2 ^ V.card := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) V.card]
    _ ≤ (layer w V t).card / V.card.choose t := by
        gcongr

/-- **Lemma 3.3 (a good layer).** Some `t` with `2t ≤ |V|` has `|Σ(V)| ≤ (|V| + 1) |Σ_t(V)|`;
in particular `a_t(V) ≥ 2^{-d(V)} / (|V| + 1)`. -/
theorem good_layer_density (V : Finset ι) :
    ∃ t, 2 * t ≤ V.card ∧ (sums w V).card ≤ (V.card + 1) * (layer w V t).card ∧
      (2 : ℝ) ^ (-deficiency w V) / (V.card + 1) ≤ density w V t := by
  obtain ⟨t, ht, hgood⟩ := good_layer w V
  exact ⟨t, ht, hgood, density_of_good w V (by omega) hgood⟩

/-! ## Corollary D (averaged small layer) -/

/-- The bound of Corollary D for one fixed `v`-set `V`. -/
theorem fixed_set (V : Finset ι) {k σ : ℕ} (h1 : 2 * k ≤ σ) (h2 : 2 * σ ≤ V.card + 2 * k)
    (h4 : σ.choose k * V.card.choose k ≤ 2 ^ V.card) :
    (2 : ℝ) ^ (-deficiency w V) / (V.card + 1) ≤ avg V σ (fun S => density w S k) := by
  have hσV : σ ≤ V.card := by omega
  have hkσ : k ≤ σ := by omega
  obtain ⟨t, ht, hgood, hdens⟩ := good_layer_density w V
  rcases le_or_gt k t with hkt | hkt
  · -- Case `t ≥ k`: Lemma 3.1, then Lemma 3.2 on each `V \ W`, then average over `W`.
    have hroom : (t - k) + σ ≤ V.card := by omega
    calc (2 : ℝ) ^ (-deficiency w V) / (V.card + 1)
        ≤ density w V t := hdens
      _ ≤ avg V (t - k) (fun W => density w (V \ W) k) := covering w V hkt (by omega)
      _ ≤ avg V (t - k) (fun W => avg (V \ W) σ (fun S => density w S k)) := by
          apply avg_mono
          intro W hW
          have hc : (V \ W).card = V.card - (t - k) := by
            rw [card_sdiff_of_subset (mem_powersetCard.1 hW).1, (mem_powersetCard.1 hW).2]
          exact sampling w (V \ W) hkσ (by omega)
      _ = avg V σ (fun S => density w S k) := avg_disjoint V hroom _
  · -- Case `t < k`: then `|Σ(V)| ≤ (|V| + 1) C(|V|, k)`, and every `a_k(S) ≥ 1 / C(σ, k)`.
    have hlayer : (sums w V).card ≤ (V.card + 1) * V.card.choose k :=
      hgood.trans (Nat.mul_le_mul_left _ ((layer_card_le_choose w V t).trans
        (choose_le_choose_of_le_half hkt.le (by omega))))
    have hlayer' : ((sums w V).card : ℝ) ≤ (V.card + 1) * V.card.choose k := by
      exact_mod_cast hlayer
    have h4' : (σ.choose k * V.card.choose k : ℝ) ≤ 2 ^ V.card := by exact_mod_cast h4
    have hσk := choose_pos_real hkσ
    calc (2 : ℝ) ^ (-deficiency w V) / (V.card + 1)
        ≤ 1 / σ.choose k := by
          rw [two_rpow_neg_deficiency, div_div, div_le_div_iff₀ (by positivity) hσk]
          nlinarith
      _ = avg V σ (fun _ => 1 / σ.choose k) := (avg_const hσV _).symm
      _ ≤ avg V σ (fun S => density w S k) := by
          apply avg_mono
          intro S hS
          have hS' := mem_powersetCard.1 hS
          have hne : (layer w S k).Nonempty :=
            (powersetCard_nonempty.2 (by omega)).image _
          rw [density, hS'.2]
          gcongr
          exact_mod_cast hne.card_pos

/-- **Corollary D (averaged small layer).** Let `M` be a finite index set with integer weights.
Let `k, σ, v` be integers with `2k ≤ σ`, `2σ ≤ v + 2k`, `v ≤ |M|` and `C(σ, k) C(v, k) ≤ 2^v`.
Let `S` be a uniform `σ`-subset and `V` a uniform `v`-subset of `M`. Then
`𝔼_S a_k(S) ≥ 𝔼_V 2^{-d(V)} / (v + 1)`. -/
theorem corollaryD (M : Finset ι) {k σ v : ℕ} (h1 : 2 * k ≤ σ) (h2 : 2 * σ ≤ v + 2 * k)
    (h3 : v ≤ M.card) (h4 : σ.choose k * v.choose k ≤ 2 ^ v) :
    avg M v (fun V => (2 : ℝ) ^ (-deficiency w V)) / (v + 1)
      ≤ avg M σ (fun S => density w S k) := by
  rw [← avg_div, ← avg_nested M (by omega : σ ≤ v) h3]
  apply avg_mono
  intro V hV
  have hVc := (mem_powersetCard.1 hV).2
  have := fixed_set w V (k := k) (σ := σ) h1 (by omega) (by rw [hVc]; exact h4)
  rw [hVc] at this
  exact this

end SmallLayer
